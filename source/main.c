#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <unistd.h>
#include <errno.h>
#include <limits.h>
#include <math.h>

#include <ps5/kernel.h>

#include "sbl.h"
#include "authmgr.h"
#include "self.h"
#include "elf.h"

#ifdef LOG_TO_SOCKET
#define PC_IP   "10.0.3.3"
#define PC_PORT 5655
#endif
struct tailored_offsets
{
    uint64_t offset_dmpml4i;
    uint64_t offset_dmpdpi;
    uint64_t offset_pml4pml4i;
    uint64_t offset_mailbox_base;
    uint64_t offset_mailbox_flags;
    uint64_t offset_mailbox_meta;
    uint64_t offset_authmgr_handle;
    uint64_t offset_sbl_sxlock;
    uint64_t offset_sbl_mb_mtx;
    uint64_t offset_g_message_id;
    uint64_t offset_datacave_1;
    uint64_t offset_datacave_2;
};

uint64_t g_kernel_data_base;
char *g_bump_allocator_base;
char *g_bump_allocator_cur;
uint64_t g_bump_allocator_len;

char *g_dump_queue_buf = NULL;
int g_dump_queue_buf_pos = 0;
#define G_DUMP_QUEUE_BUF_SIZE 1 * 1024 * 1024 // 1MB

void *bump_alloc(uint64_t len)
{
    void *ptr;
    if (g_bump_allocator_cur + len >= (g_bump_allocator_base + g_bump_allocator_len)) {
        return NULL;
    }

    ptr = (void *) g_bump_allocator_cur;
    g_bump_allocator_cur += len;

    // Zero init to avoid stupid bugs
    (void)memset(ptr, 0, len);

    return ptr;
}

void *bump_calloc(uint64_t count, uint64_t len)
{
    uint64_t total_len;

    total_len = count * len;
    return bump_alloc(total_len);
}

void bump_reset()
{
    g_bump_allocator_cur = g_bump_allocator_base;
}

void sock_print(int sock, char *str)
{
#ifdef LOG_TO_SOCKET   
	size_t size;

	size = strlen(str);
	write(sock, str, size);
#else
    printf("%s", str);
#endif
}

static void _mkdir(const char *dir) {
    char tmp[PATH_MAX];
    char *p = NULL;
    size_t len;

    snprintf(tmp, sizeof(tmp),"%s",dir);
    len = strlen(tmp);
    if (tmp[len - 1] == '/')
        tmp[len - 1] = 0;
    for (p = tmp + 1; *p; p++)
        if (*p == '/') {
            *p = 0;
            mkdir(tmp, 0777);
            *p = '/';
        }
    mkdir(tmp, 0777);
}

uint64_t get_authmgr_sm(int sock, struct tailored_offsets *offsets)
{
    uint64_t authmgr_sm_handle;

    kernel_copyout(g_kernel_data_base + offsets->offset_authmgr_handle, &authmgr_sm_handle, sizeof(authmgr_sm_handle));
    return authmgr_sm_handle;
}

int self_verify_header(int sock, uint64_t authmgr_handle, char *data, uint64_t size, struct tailored_offsets *offsets)
{
    int err;
    uint64_t data_blob_va;
    uint64_t data_blob_pa;

    // Get mailbox physical/virtual address
    data_blob_va   = g_kernel_data_base + offsets->offset_datacave_2;
    data_blob_pa   = pmap_kextract(sock, data_blob_va);

    // Copy header in
    kernel_copyin(data, data_blob_va, size);

    // We must finalize the context to 'reset' it
    err = _sceSblAuthMgrSmFinalize(sock, authmgr_handle, 0);
    if (err != 0)
        return err;

    // Submit request and return service ID
    return _sceSblAuthMgrVerifyHeader(sock, authmgr_handle, data_blob_pa, size);
}

struct self_block_segment *self_decrypt_segment(
    int sock,
    int authmgr_handle,
    int service_id,
    char *file_data,
    struct sce_self_segment_header *segment,
    int segment_idx,
    struct tailored_offsets *offsets)
{
    int err;
    void *out_segment_data;
    void **digests;
    char *cur_digest;
    struct self_block_segment *segment_info;
    struct sce_self_block_info *cur_block_info;
    struct sce_self_block_info **block_infos;
    struct sbl_chunk_table_header *chunk_table;
    struct sbl_chunk_table_entry *chunk_entry;
    uint64_t chunk_table_va;
    uint64_t data_blob_va;
    uint64_t chunk_table_pa;
    uint64_t data_blob_pa;
    char chunk_table_buf[0x1000] = {};

    struct sce_self_segment_header *target_segment;
    target_segment = (struct sce_self_segment_header *) (file_data +
                        sizeof(struct sce_self_header) + (SELF_SEGMENT_ID(segment) * sizeof(struct sce_self_segment_header)));

    // Copy segment data into data cave #1
    data_blob_va   = g_kernel_data_base + offsets->offset_datacave_2;
    data_blob_pa   = pmap_kextract(sock, data_blob_va);

    if (segment->compressed_size < 0x1000)
        kernel_copyin(file_data + segment->offset, data_blob_va, segment->compressed_size);
    else {
        for (int bytes = 0; bytes < segment->compressed_size; bytes += 0x1000) {
            if (segment->compressed_size - bytes < 0x1000)
                kernel_copyin(file_data + segment->offset + bytes, data_blob_va + bytes, (segment->compressed_size - bytes));
            else
                kernel_copyin(file_data + segment->offset + bytes, data_blob_va + bytes, 0x1000);
        }
    }

    // Construct chunk table
    chunk_table = (struct sbl_chunk_table_header *) (chunk_table_buf);
    chunk_entry = (struct sbl_chunk_table_entry *) (chunk_table_buf + sizeof(struct sbl_chunk_table_header));

    chunk_table->first_pa = data_blob_pa;
    chunk_table->used_entries = 1;
    chunk_table->data_size = segment->compressed_size;

    chunk_entry->pa = data_blob_pa;
    chunk_entry->size = segment->compressed_size;

    chunk_table_va = g_kernel_data_base + offsets->offset_datacave_1;
    chunk_table_pa = pmap_kextract(sock, chunk_table_va);

    // Copy out chunk table into data cave #2
    kernel_copyin(chunk_table, chunk_table_va, 0x30);

    // Request segment decryption
    for (int tries = 0; tries < 3; tries++) {
        err = _sceSblAuthMgrSmLoadSelfSegment(sock, authmgr_handle, service_id, chunk_table_pa, segment_idx);
        if (err == 0)
            break;
        sleep(1);
    }

    if (err != 0)
        return NULL;

    out_segment_data = mmap(NULL, segment->uncompressed_size, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    if (out_segment_data == NULL)
        return NULL;

    // Copy out decrypted content
    kernel_copyout(data_blob_va, out_segment_data, segment->uncompressed_size);

    // Track segment info for use later
    segment_info = bump_alloc(sizeof(struct self_block_segment));
    if (segment_info == NULL)
        return NULL;

    segment_info->data = out_segment_data;
    segment_info->size = segment->uncompressed_size;

    
    if (SELF_SEGMENT_HAS_BLOCKINFO(segment)){
        if (SELF_SEGMENT_HAS_DIGESTS(segment)){
            segment_info->block_count = segment_info->size / (0x20 + 0x8);
        } else {
            segment_info->block_count = segment_info->size / 0x8;
        }
    } else {
        segment_info->block_count = ceil((double)target_segment->uncompressed_size / SELF_SEGMENT_BLOCK_SIZE(target_segment));
    }

    // Keep track of block digests
    digests = bump_calloc(segment_info->block_count, sizeof(void *));
    if (digests == NULL)
        return NULL;

    if (SELF_SEGMENT_HAS_DIGESTS(segment)) {
        cur_digest = (char *) out_segment_data;
        for (int i = 0; i < segment_info->block_count; i++) {
            digests[i] = (void *) cur_digest;
            cur_digest += 0x20;
        }
    }
    segment_info->digests = digests;

    // Keep track of block extent information
    block_infos = bump_calloc(segment_info->block_count, sizeof(struct sce_self_block_info *));
    if (block_infos == NULL)
        return NULL;

    if (SELF_SEGMENT_HAS_BLOCKINFO(segment)) {
        cur_block_info = (struct sce_self_block_info *)out_segment_data;
        if (SELF_SEGMENT_HAS_DIGESTS(segment)) {
            cur_block_info = (struct sce_self_block_info *) (out_segment_data + (0x20 * segment_info->block_count));
        }

        for (int i = 0; i < segment_info->block_count; i++) {
            block_infos[i] = cur_block_info++;
        }
    } else {
        for (int i = 0; i < segment_info->block_count; i++) {
            block_infos[i] = bump_alloc(sizeof(struct sce_self_block_info));
            if (block_infos[i] == NULL)
                return NULL;

            block_infos[i]->offset = i * SELF_SEGMENT_BLOCK_SIZE(target_segment);
         
            if (i == segment_info->block_count - 1) {
                block_infos[i]->len = target_segment->uncompressed_size % SELF_SEGMENT_BLOCK_SIZE(target_segment);
            } else {
                block_infos[i]->len = SELF_SEGMENT_BLOCK_SIZE(target_segment);
            }
        }
    }

    segment_info->extents = block_infos;
    return segment_info;
}
// ELF block max size: 0x4000 is the max segment chunk size handled (4 * 0x1000)
void *self_decrypt_block(
    int sock,
    int authmgr_handle,
    int service_id,
    char *file_data,
    struct sce_self_segment_header *segment,
    int segment_idx,
    struct self_block_segment *block_segment,
    int block_idx,
    struct tailored_offsets *offsets)
{
    int err;
    uint64_t data_blob_va;
    uint64_t data_out_va;
    uint64_t data_blob_pa;
    uint64_t data_out_pa;
    uint64_t input_addr;
    void *out_block_data;

    data_out_va  = g_kernel_data_base + offsets->offset_datacave_1;
    data_out_pa  = pmap_kextract(sock, data_out_va);

    data_blob_va = g_kernel_data_base + offsets->offset_datacave_2;
    data_blob_pa = pmap_kextract(sock, data_blob_va);

    // Calculate input address and size
    input_addr = (uint64_t) (file_data + segment->offset + block_segment->extents[block_idx]->offset);

    // Segmented copy into data cave #1
    for (int i = 0; i < 4; i++) {
        kernel_copyin((void *) (input_addr + (i * 0x1000)), data_blob_va + (i * 0x1000), 0x1000);
    }
    
    // Request segment decryption
    for (int tries = 0; tries < 50; tries++) {
        err = _sceSblAuthMgrSmLoadSelfBlock(
            sock,
            authmgr_handle,
            service_id,
            data_blob_pa,
            data_out_pa,
            segment,
            SELF_SEGMENT_ID(segment),
            block_segment,
            block_idx
        );
        if (err == 0)
            break;

        usleep(200000);
    }

    if (err != 0)
    {
        SOCK_LOG(sock, "[!] failed to decrypt block %d, err: %d\n", block_idx, err);
        return NULL;
    }

    out_block_data = mmap(NULL, 0x4000, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    if (out_block_data == NULL)
        return NULL;

    uint8_t *dbg = (uint8_t *)out_block_data;    
    // Segmented copy out decrypted content
    for (int i = 0; i < 4; i++) {
        kernel_copyout(data_out_va + (i * 0x1000), out_block_data + (i * 0x1000), 0x1000);
    }

   
    SOCK_LOG(sock, "  [!] Dump preview (block %d): %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x\n",
        block_idx,
        dbg[0], dbg[1], dbg[2], dbg[3],
        dbg[4], dbg[5], dbg[6], dbg[7],
        dbg[8], dbg[9], dbg[10], dbg[11],
        dbg[12], dbg[13], dbg[14], dbg[15]);


    return out_block_data;
}

int decrypt_self(int sock, uint64_t authmgr_handle, char *path, int out_fd, struct tailored_offsets *offsets)
{
    int err;
    int service_id;
    int written_bytes;
    int self_file_fd;
    struct stat self_file_stat;
    void *self_file_data;
    void *out_file_data;
    struct elf64_hdr *elf_header;
    struct elf64_phdr *start_phdrs;
    struct elf64_phdr *cur_phdr;
    struct sce_self_header *header;
    struct sce_self_segment_header *segment;
    struct sce_self_segment_header *target_segment;
    struct self_block_segment **block_segments;
    struct self_block_segment *block_info;
    void **block_data;
    uint64_t tail_block_size;
    uint64_t final_file_size;

    err = 0;

    // Open SELF file for reading
    self_file_fd = open(path, 0, 0);
    if (self_file_fd < 0) {
        SOCK_LOG(sock, "[!] failed to open %s\n", path);
        close(out_fd);
        return self_file_fd;
    }

    fstat(self_file_fd, &self_file_stat);
    self_file_data = mmap(NULL, self_file_stat.st_size, PROT_READ, MAP_SHARED, self_file_fd, 0);
    if (self_file_data == NULL || self_file_data == MAP_FAILED) {
        SOCK_LOG(sock, "[!] file mmap failed, failling back to reading the file\n");
        // some games give errno 12, but reading in the file works, weird
        self_file_data = mmap(NULL, self_file_stat.st_size, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
        size_t total_read = 0;
        while (total_read < self_file_stat.st_size) {
            size_t read_bytes = read(self_file_fd, self_file_data + total_read, self_file_stat.st_size - total_read);
            if (read_bytes == 0) {
                break;
            } else if (read_bytes < 0) {
                SOCK_LOG(sock, "[!] failed to read %s\n", path);
                err = -30;
                goto cleanup_in_file_data;
            }

            total_read += read_bytes;
        }
        SOCK_LOG(sock, "[+] read file into memory\n");
    }

    SOCK_LOG(sock, "[+] decrypting %s...\n", path);

    // Verify SELF header and get a context handle
    header = (struct sce_self_header *) self_file_data;
    service_id = self_verify_header(
        sock,
        authmgr_handle,
        self_file_data,
        header->header_size + header->metadata_size,
        offsets);

    if (service_id < 0) {
        SOCK_LOG(sock, "[!] failed to acquire a service ID\n");
        err = -1;
        goto cleanup_in_file_data;
    }

    // Get ELF headers
    elf_header  = (struct elf64_hdr *) (self_file_data + sizeof(struct sce_self_header) +
                    (sizeof(struct sce_self_segment_header) * header->segment_count));
    start_phdrs = (struct elf64_phdr *) ((char *) (elf_header) + sizeof(struct elf64_hdr));

    // Calculate final file size from all PT_LOAD segments (works best for PS4 SELF)
    cur_phdr = start_phdrs;
    final_file_size = 0;

    for (int i = 0; i < elf_header->e_phnum; i++) {
        if (cur_phdr->p_type == PT_LOAD) {
            uint64_t end_offset = cur_phdr->p_offset + cur_phdr->p_memsz;;
            if (end_offset > final_file_size) {
                final_file_size = end_offset;
            }
        }
        cur_phdr++;
    }

    SOCK_LOG(sock, "  [+] Calculated final file size: 0x%lx\n", final_file_size);

    

    out_file_data = mmap(NULL, final_file_size, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    if (out_file_data == NULL || (intptr_t)out_file_data == -1) {
        err = -12;
        goto cleanup_in_file_data;
    }

    // Copy ELF headers over
    memcpy(out_file_data, elf_header, sizeof(struct elf64_hdr));
    memcpy(out_file_data + sizeof(struct elf64_hdr), start_phdrs, elf_header->e_phnum * sizeof(struct elf64_phdr));

    // Digest
    memcpy(
        out_file_data + sizeof(struct elf64_hdr) + (elf_header->e_phnum * sizeof(struct elf64_phdr)),
        (char *) (start_phdrs) + (elf_header->e_phnum * sizeof(struct elf64_phdr)),
        0x40
    );

    // Allocate array to hold block info
    block_segments = bump_calloc(header->segment_count, sizeof(struct self_block_segment *));
    if (block_segments == NULL) {
        err = -12;
        goto cleanup_out_file_data;
    }

    // Decrypt block info segments
    for (int i = 0; i < header->segment_count; i++) {
        segment = (struct sce_self_segment_header *) (self_file_data +
                sizeof(struct sce_self_header) + (i * sizeof(struct sce_self_segment_header)));

        if (SELF_SEGMENT_HAS_DIGESTS(segment)) {
            uint32_t seg_id = SELF_SEGMENT_ID(segment); // 👈 AÑADIR AQUÍ

            if (seg_id >= header->segment_count) {      // 👈 Y ESTO
                SOCK_LOG(sock, "[!] segment ID %u out of range\n", seg_id);
                continue;
            }

            if (block_segments[seg_id] != NULL) {
                SOCK_LOG(sock, "[!] segment ID %u already processed, skipping duplicate\n", seg_id);
                continue;
            }
            
            target_segment = (struct sce_self_segment_header *) (self_file_data +
                sizeof(struct sce_self_header) + (SELF_SEGMENT_ID(segment) * sizeof(struct sce_self_segment_header)));
            SOCK_LOG(sock, "  [?] decrypting block info segment for %lu\n", SELF_SEGMENT_ID(target_segment));
            block_segments[SELF_SEGMENT_ID(segment)] = self_decrypt_segment(
                sock,
                authmgr_handle,
                service_id,
                self_file_data,
                segment,
                SELF_SEGMENT_ID(target_segment),
                offsets
            );

            if (block_segments[SELF_SEGMENT_ID(segment)] == NULL) {
                SOCK_LOG(sock, "[!] failed to decrypt segment info for segment %lu\n", SELF_SEGMENT_ID(segment));
                err = -11;
                goto cleanup_out_file_data;
            }
        }
    }

    // Decrypt regular blocked-segments to file
    for (int i = 0; i < header->segment_count; i++) {
        segment = (struct sce_self_segment_header *) (self_file_data +
                sizeof(struct sce_self_header) + (i * sizeof(struct sce_self_segment_header)));

        // Skip segments that have no actual data blocks (e.g., metadata-only)
        if (!SELF_SEGMENT_HAS_BLOCKS(segment)) {
            SOCK_LOG(sock, "  [-] segment %d has no blocks, skipping\n", i);
            continue;
        }

        cur_phdr = NULL;
        for (int p = 0; p < elf_header->e_phnum; p++) {
            struct elf64_phdr *ph = &start_phdrs[p];
            if (ph->p_type == PT_LOAD && ph->p_memsz == segment->uncompressed_size) {
                cur_phdr = ph;
                break;
            }
        }

        if (cur_phdr == NULL) {
            SOCK_LOG(sock, "[!] No PT_LOAD segment matching uncompressed size for segment %d\n", i);
            continue;
        }

        // Verificamos si se encontró algún segmento ELF
        // if (phnum == header->segment_count) {
        //     SOCK_LOG(sock, "[!] ELF segment not found for segment %d\n", i);
        //     continue;
        // }

        // Get block info for this segment
        block_info = block_segments[i];
        if (block_info == NULL) {
            SOCK_LOG(sock, "[!] we don't have block info for segment %d\n", i);
            continue;
        }

        // Allocate array to hold decrypted block data
        block_data = bump_calloc(block_info->block_count, sizeof(void *));
        if (block_data == NULL) {
            err = -12;
            goto cleanup_out_file_data;
        }

        // Get tail block size
        tail_block_size = segment->uncompressed_size % SELF_SEGMENT_BLOCK_SIZE(segment);

        for (int block = 0; block < block_info->block_count; block++) {
            SOCK_LOG(sock, "  [?] %s: decrypting segment=%d, block=%d/%lu\n", path, i, block + 1, block_info->block_count);
        
            block_data[block] = self_decrypt_block(
                sock,
                authmgr_handle,
                service_id,
                self_file_data,
                segment,
                i,
                block_info,
                block,
                offsets
            );
        
            if (block_data[block] == NULL) {
                SOCK_LOG(sock, "[!] failed to decrypt block %d\n", block);
                err = -11;
                goto cleanup_out_file_data;
            }

            // DEBUG: Mostrar los primeros 16 bytes del bloque
            uint8_t *block_bytes = (uint8_t *)block_data[block];
            SOCK_LOG(sock, "      First 16 bytes: %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x\n",
                block_bytes[0], block_bytes[1], block_bytes[2], block_bytes[3],
                block_bytes[4], block_bytes[5], block_bytes[6], block_bytes[7],
                block_bytes[8], block_bytes[9], block_bytes[10], block_bytes[11],
                block_bytes[12], block_bytes[13], block_bytes[14], block_bytes[15]);
        
            // Calcular tamaño del bloque actual
            size_t size = (block == block_info->block_count - 1 && tail_block_size > 0)
                ? tail_block_size
                : SELF_SEGMENT_BLOCK_SIZE(segment);
        
            // Calcular destino y copiar
            void *out_addr = out_file_data + cur_phdr->p_offset + (block * SELF_SEGMENT_BLOCK_SIZE(segment));
        
            // Loguear antes de escribir
            SOCK_LOG(sock, "  [>] writing block %d to offset 0x%lx (size: 0x%lx)\n",
                block,
                cur_phdr->p_offset + (block * SELF_SEGMENT_BLOCK_SIZE(segment)),
                size);
        
            memcpy(out_addr, block_data[block], size);
        
            munmap(block_data[block], SELF_SEGMENT_BLOCK_SIZE(segment));
        }
        
    }

    // Validación: chequeo que todos los segmentos PT_LOAD fueron correctamente desencriptados
    for (int i = 0; i < elf_header->e_phnum; i++) {
        struct elf64_phdr *ph = &start_phdrs[i];
        if (ph->p_type == PT_LOAD) {
            void *segment_start = out_file_data + ph->p_offset;

            // Verificamos si hay datos no escritos (todo cero) en este segmento
            int is_zero = 1;
            for (uint64_t j = 0; j < ph->p_filesz; j++) {
                if (((uint8_t *)segment_start)[j] != 0) {
                    is_zero = 0;
                    break;
                }
            }

            if (is_zero) {
                SOCK_LOG(sock, "[!] Warning: Segment %d at offset 0x%lx appears to be all zero (possibly missing decryption?)\n", i, ph->p_offset);
            }
        }
    }

    SOCK_LOG(sock, "[?] writing decrypted SELF to file...\n");
    written_bytes = write(out_fd, out_file_data, final_file_size);
    if (written_bytes != final_file_size) {
        SOCK_LOG(sock, "[!] failed to dump to file, %d != %lu (%d).\n", written_bytes, final_file_size, errno);
        err = -5;
    }

    SOCK_LOG(sock, "  [+] wrote 0x%08x bytes...\n", written_bytes);

    if (written_bytes != final_file_size) {
        SOCK_LOG(sock, "[!] Final file size mismatch! Expected: 0x%lx, Written: 0x%x\n", final_file_size, written_bytes);
        err = -6;
    }
    

cleanup_out_file_data:
    munmap(out_file_data, final_file_size);
cleanup_in_file_data:
    munmap(self_file_data, self_file_stat.st_size);
    close(self_file_fd);
    close(out_fd);

    // Reset the bump allocator
    bump_reset();

    return err;
}

int dump_queue_init(int sock)
{
    if (g_dump_queue_buf != NULL && g_dump_queue_buf != MAP_FAILED) {
        return 0;
    }

    g_dump_queue_buf = mmap(NULL, G_DUMP_QUEUE_BUF_SIZE, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    if (g_dump_queue_buf == NULL || g_dump_queue_buf == MAP_FAILED) {
        SOCK_LOG(sock, "[!] failed to allocate buffer for directory entries\n");
        exit(-1);
    }

    return 0;
}

int dump_queue_reset()
{
    if (g_dump_queue_buf == NULL) {
        return 0;
    }

    g_dump_queue_buf_pos = 0;
    g_dump_queue_buf[0] = '\0';
    return 0;
}

int dump_queue_add_file(int sock, char *path)
{
    dump_queue_init(sock);

    //static const char* allowed_exts[] = { ".elf", ".self", ".prx", ".sprx", ".bin" };
    static const char* allowed_exts[] = { ".bin" };
    static const int allowed_exts_count = sizeof(allowed_exts) / sizeof(allowed_exts[0]);

    int len = strlen(path);

    // skip app0, we only want app0-patch0-union
    // if (len >= 35 && strncmp(path, "/mnt/sandbox/pfsmnt/", 20) == 0 && (strncmp(path + 29, "-app0/", 6) == 0 || strncmp(path + 29, "-patch0/", 8) == 0)) {
    // #if DEBUG
    //         SOCK_LOG(sock, "[!] ignoring app0/patch0: %s\n", path);
    // #endif
    //     return -1;
    // }
    
    char* dot = strrchr(path, '.'); // find last dot
    if (dot == NULL) {
        return -2;
    }

    int allowed = 0;
    for (int i = 0; i < allowed_exts_count; i++) {
        if (strcasecmp(dot, allowed_exts[i]) == 0) {
            allowed = 1;
            break;
        }
    }

    if (!allowed) {
#if DEBUG
        SOCK_LOG(sock, "[!] unsupported file type: %s\n", path);
#endif
        return -3;
    }

    int fd = open(path, O_RDONLY, 0);
    if (fd < 0) {
        SOCK_LOG(sock, "[!] failed to open file: %s\n", path);
        return -4;
    }

    uint32_t magic = 0;
    read(fd, &magic, sizeof(magic));
    close(fd);
    
    int new_g_dump_queue_buf_pos = g_dump_queue_buf_pos + len + 1;
    if (new_g_dump_queue_buf_pos >= G_DUMP_QUEUE_BUF_SIZE) {
        SOCK_LOG(sock, "[!] dump queue buffer full\n");
        exit(-2);
    }

    memcpy(g_dump_queue_buf + g_dump_queue_buf_pos, path, len + 1);

#if DEBUG
    SOCK_LOG(sock, "[+] added to dump queue: %s\n", path);
#endif

    g_dump_queue_buf_pos = new_g_dump_queue_buf_pos;

    // null terminate the next entry so we know to break
    g_dump_queue_buf[g_dump_queue_buf_pos] = '\0';
    
    return 0;
}

#define DENTS_BUF_SIZE 0x10000
int dump_queue_add_dir(int sock, char* path, int recursive)
{
    int dir_fd = open(path, O_RDONLY, 0);
    if (dir_fd < 0) {
        SOCK_LOG(sock, "[!] failed to open directory: %s\n", path);
        return -1;
    }

    // char dents[DENTS_BUF_SIZE] = {0};
    char* dents = malloc(DENTS_BUF_SIZE);
    while (1)
    {
        int n = getdents(dir_fd, dents, DENTS_BUF_SIZE);
        if (n < 0) {
            SOCK_LOG(sock, "[!] failed to get directory entries: %s\n", path);
            close(dir_fd);
            free(dents);
            return -1;
        }

        if (n == 0) {
            break;
        }

        struct dirent* entry = (struct dirent*)dents;
        while ((char*)entry < dents + n)
        {
            if (entry->d_type == DT_REG) {
                char full_path[PATH_MAX];
                sprintf(full_path, "%s/%s", path, entry->d_name);
                dump_queue_add_file(sock, full_path);
            }
            else if (recursive && entry->d_type == DT_DIR) {
                if (entry->d_name[0] != '.') {
                    char full_path[PATH_MAX];
                    sprintf(full_path, "%s/%s", path, entry->d_name);
                    dump_queue_add_dir(sock, full_path, recursive);
                }
            }

            entry = (struct dirent*)((char*)entry + entry->d_reclen);
        }
    }

    close(dir_fd);
    free(dents);
    return 0;    
}


int dump(int sock, uint64_t authmgr_handle, struct tailored_offsets *offsets, const char *out_dir_path)
{
    if (g_dump_queue_buf == NULL) {
        return -1;
    }

    int err = 0;
    int out_fd;
    char* entry;
    char out_file_path[PATH_MAX];
    struct stat out_file_stat;
    uint64_t spinlock_lock = 0x13371337;
    uint64_t spinlock_unlock = 0;

    uintptr_t sbl_sxlock_addr = g_kernel_data_base + offsets->offset_sbl_sxlock + 0x18;
    kernel_copyout(sbl_sxlock_addr, &spinlock_unlock, sizeof(spinlock_unlock));

  
    SOCK_LOG(sock, "  [!] block 0x%x -> first bytes: %02x %02x %02x %02x\n", block_idx, dbg[0], dbg[1], dbg[2], dbg[3]);


    // Lock the SBL spinlock BKL style
    for (int i = 0; i < 0x100; i++) {
        kernel_copyin(&spinlock_lock, sbl_sxlock_addr, sizeof(spinlock_lock));
        usleep(1000);
    }

    entry = g_dump_queue_buf;
    while (*entry != '\0') {
        SOCK_LOG(sock, "[+] processing %s\n", entry);
        int entry_len = strlen(entry);

        sprintf((char *) &out_file_path, "%s%s", out_dir_path, entry);

        // Check if output file already exists and is non-zero size, if so skip it
        out_fd = open(out_file_path, O_RDONLY, 0);
        if (out_fd >= 0) {
            fstat(out_fd, &out_file_stat);
            close(out_fd);
            if (out_file_stat.st_size > 0) {
                SOCK_LOG(sock, "[!] %s already exists and is non-zero size, skipping\n", out_file_path);
                entry = (char *) entry + entry_len + 1;
                continue;
            }
        }

//        for (int i = 0; i < 0x100; i++) {
//            kernel_copyin(&spinlock_lock, g_kernel_data_base + offsets->offset_sbl_sxlock + 0x18, 0x8);
//            usleep(100);
//        }

        char parent_dir[PATH_MAX];
        int last_slash = strrchr(out_file_path, '/') - out_file_path;
        strncpy(parent_dir, out_file_path, last_slash);
        parent_dir[last_slash] = '\0';
        _mkdir(parent_dir);

        // Decrypt
        out_fd = open(out_file_path, O_WRONLY | O_CREAT, 0644);
        if (out_fd < 0) {
            SOCK_LOG(sock, "[!] failed to open %s for writing, errno: %d\n", out_file_path, errno);
            entry = (char *) entry + entry_len + 1;
            continue;
        }
        err = decrypt_self(sock, authmgr_handle, entry, out_fd, offsets);
        if (err == -11) {
            // Give 2 more attempts
            for (int attempt = 0; attempt < 5; attempt++) {
                out_fd = open(out_file_path, O_WRONLY | O_CREAT, 0644);
                err = decrypt_self(sock, authmgr_handle, entry, out_fd, offsets);
                if (err == 0)
                    break;
            }
        }

        if (err != 0) {
            // unlink(out_file_path);
            SOCK_LOG(sock, "[!] keeping partial file: %s\n", entry);
        }

        if (err == -5) {
            goto out;
        }
        
        entry = (char *) entry + entry_len + 1;
    }

    SOCK_LOG(sock, "[+] done\n");

out:
    kernel_copyin(&spinlock_unlock, sbl_sxlock_addr, sizeof(spinlock_unlock));

    return err;
}

int dump_eboot_from_disc(int sock) {
    DIR *dir;
    struct dirent *entry;
    char patch_path[PATH_MAX];
    char app0_path[PATH_MAX];

    dir = opendir("/mnt/sandbox/pfsmnt");
    if (dir == NULL) {
        SOCK_LOG(sock, "[!] failed to open pfsmnt\n");
        return -1;
    }

    while ((entry = readdir(dir)) != NULL) {
        if (entry->d_type == DT_DIR) {
            // Primero intentamos con -patch0
            if (strstr(entry->d_name, "-patch0")) {
                snprintf(patch_path, sizeof(patch_path), "/mnt/sandbox/pfsmnt/%s/eboot.bin", entry->d_name);
                SOCK_LOG(sock, "[+] found patch0 eboot: %s\n", patch_path);
                closedir(dir);
                return dump_queue_add_file(sock, patch_path);
            }
        }
    }

    rewinddir(dir); // volver a empezar el bucle

    while ((entry = readdir(dir)) != NULL) {
        if (entry->d_type == DT_DIR) {
            if (strstr(entry->d_name, "-app0")) {
                snprintf(app0_path, sizeof(app0_path), "/mnt/sandbox/pfsmnt/%s/eboot.bin", entry->d_name);
                SOCK_LOG(sock, "[+] found app0 eboot: %s\n", app0_path);
                closedir(dir);
                return dump_queue_add_file(sock, app0_path);
            }
        }
    }

    closedir(dir);
    SOCK_LOG(sock, "[!] no eboot found in patch0 or app0\n");
    return -2;
}

int main()
{
	int sock = -1;
    uint64_t authmgr_handle;
    struct tailored_offsets offsets;

#ifdef LOG_TO_SOCKET
    int ret;
	struct sockaddr_in addr;
	// Open a debug socket to log to PC
	sock = socket(AF_INET, SOCK_STREAM, 0);
	if (sock < 0) {
		return -1;
	}

	inet_pton(AF_INET, PC_IP, &addr.sin_addr);
	addr.sin_family = AF_INET;
	addr.sin_len    = sizeof(addr);
	addr.sin_port   = htons(PC_PORT);

	ret = connect(sock, (const struct sockaddr *) &addr, sizeof(addr));
	if (ret < 0) {
		return -1;
	}
#endif

    // Initialize bump allocator
    g_bump_allocator_len  = 0x100000;
    g_bump_allocator_base = mmap(NULL, g_bump_allocator_len, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    if (g_bump_allocator_base == NULL) {
        SOCK_LOG(sock, "[!] failed to allocate backing space for bump allocator\n");
        goto out;
    }

    g_bump_allocator_cur = g_bump_allocator_base;

    g_kernel_data_base = KERNEL_ADDRESS_DATA_BASE;

    // Tailor
    uint32_t version = kernel_get_fw_version() & 0xffff0000;
    printf("[+] firmware version 0x%x\n", version);

    // See README for porting notes
    switch (version) {
        case 0x3000000:
        case 0x3100000:
        case 0x3200000:
        case 0x3210000:
            offsets.offset_authmgr_handle = 0xC9EE50;
            offsets.offset_sbl_mb_mtx     = 0x2712A98;
            offsets.offset_mailbox_base   = 0x2712AA0;
            offsets.offset_sbl_sxlock     = 0x2712AA8;
            offsets.offset_mailbox_flags  = 0x2CF5F98;
            offsets.offset_mailbox_meta   = 0x2CF5D38;
            offsets.offset_dmpml4i        = 0x31BE4A0;
            offsets.offset_dmpdpi         = 0x31BE4A4;
            offsets.offset_pml4pml4i      = 0x31BE1FC;
            offsets.offset_g_message_id   = 0x0008000;
            offsets.offset_datacave_1     = 0x8720000;
            offsets.offset_datacave_2     = 0x8724000;
            break;
        case 0x4000000:
        case 0x4020000:
        case 0x4030000:
        case 0x4500000:
        case 0x4510000:
            offsets.offset_authmgr_handle = 0xD0FBB0;
            offsets.offset_sbl_mb_mtx     = 0x2792AB8;
            offsets.offset_mailbox_base   = 0x2792AC0;
            offsets.offset_sbl_sxlock     = 0x2792AC8;
            offsets.offset_mailbox_flags  = 0x2D8DFC0;
            offsets.offset_mailbox_meta   = 0x2D8DD60;
            offsets.offset_dmpml4i        = 0x3257D00;
            offsets.offset_dmpdpi         = 0x3257D04;
            offsets.offset_pml4pml4i      = 0x3257A5C;
            offsets.offset_g_message_id   = 0x0008000;
            offsets.offset_datacave_1     = 0x8720000;
            offsets.offset_datacave_2     = 0x8724000;
            break;
        case 0x5000000:
        case 0x5020000:
        case 0x5100000:
            offsets.offset_authmgr_handle = 0x0DFF410;
            offsets.offset_sbl_mb_mtx     = 0x28C3038;
            offsets.offset_mailbox_base   = 0x28C3040;
            offsets.offset_sbl_sxlock     = 0x28C3048;
            offsets.offset_mailbox_flags  = 0x2EADFC0;
            offsets.offset_mailbox_meta   = 0x2EADD60;
            offsets.offset_dmpml4i        = 0x3398D24;
            offsets.offset_dmpdpi         = 0x3398D28;
            offsets.offset_pml4pml4i      = 0x3397A2C;
            offsets.offset_g_message_id   = 0x4270000;
            offsets.offset_datacave_1     = 0x8730000;
            offsets.offset_datacave_2     = 0x8734000;
            break;
        case 0x5500000:
            offsets.offset_authmgr_handle = 0x0DFF410;
            offsets.offset_sbl_mb_mtx     = 0x28C3038;
            offsets.offset_mailbox_base   = 0x28C3040;
            offsets.offset_sbl_sxlock     = 0x28C3048;
            offsets.offset_mailbox_flags  = 0x2EA9FC0;
            offsets.offset_mailbox_meta   = 0x2EA9D60;
            offsets.offset_dmpml4i        = 0x3394D24;
            offsets.offset_dmpdpi         = 0x3394D28;
            offsets.offset_pml4pml4i      = 0x3393A2C;
            offsets.offset_g_message_id   = 0x4270000;
            offsets.offset_datacave_1     = 0x8730000;
            offsets.offset_datacave_2     = 0x8734000;
            break;
        case 0x6000000:
        case 0x6020000:
        case 0x6500000:
            offsets.offset_authmgr_handle = 0x0E1F8D0;
            offsets.offset_sbl_mb_mtx     = 0x280F3A8;
            offsets.offset_mailbox_base   = 0x280F3B0;
            offsets.offset_sbl_sxlock     = 0x280F3B8;
            offsets.offset_mailbox_flags  = 0x2DF9FC0;
            offsets.offset_mailbox_meta   = 0x2DF9D60;
            offsets.offset_dmpml4i        = 0x32E45F4;
            offsets.offset_dmpdpi         = 0x32E45F8;
            offsets.offset_pml4pml4i      = 0x32E32FC;
            offsets.offset_g_message_id   = 0x4270000;
            offsets.offset_datacave_1     = 0x8730000;
            offsets.offset_datacave_2     = 0x8734000;
            break;
        case 0x7000000:
        case 0x7010000:
            offsets.offset_authmgr_handle = 0x0E20270;
            offsets.offset_sbl_mb_mtx     = 0x27FF808;
            offsets.offset_mailbox_base   = 0x27FF810;
            offsets.offset_sbl_sxlock     = 0x27FF818;
            offsets.offset_mailbox_flags  = 0x2CCDFC0;
            offsets.offset_mailbox_meta   = 0x2CCDD60;
            offsets.offset_dmpml4i        = 0x2E2CAE4;
            offsets.offset_dmpdpi         = 0x2E2CAE8;
            offsets.offset_pml4pml4i      = 0x2E2B79C;
            offsets.offset_g_message_id   = 0x4270000;
            offsets.offset_datacave_1     = 0x5060000;
            offsets.offset_datacave_2     = 0x5064000;
            break;
        case 0x7200000:
        case 0x7400000:
        case 0x7600000:
        case 0x7610000:
            offsets.offset_authmgr_handle = 0x0E20330;
            offsets.offset_sbl_mb_mtx     = 0x27FF808;
            offsets.offset_mailbox_base   = 0x27FF810;
            offsets.offset_sbl_sxlock     = 0x27FF818;
            offsets.offset_mailbox_flags  = 0x2CCDFC0;
            offsets.offset_mailbox_meta   = 0x2CCDD60;
            offsets.offset_dmpml4i        = 0x2E2CAE4;
            offsets.offset_dmpdpi         = 0x2E2CAE8;
            offsets.offset_pml4pml4i      = 0x2E2B79C;
            offsets.offset_g_message_id   = 0x4270000;
            offsets.offset_datacave_1     = 0x5060000;
            offsets.offset_datacave_2     = 0x5064000;
            break;
        default:
            SOCK_LOG(sock, "[!] unsupported firmware, dumping then bailing!\n");
            char *dump_buf = mmap(NULL, 0x7800 * 0x1000, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);

            for (int pg = 0; pg < 0x7800; pg++) {
                kernel_copyout(g_kernel_data_base + (pg * 0x1000), dump_buf + (pg * 0x1000), 0x1000);
            }

            int dump_fd = open("/mnt/usb0/PS5/data_dump.bin", O_WRONLY | O_CREAT, 0644);
            write(dump_fd, dump_buf, 0x7800 * 0x1000);
            close(dump_fd);
            SOCK_LOG(sock, "  [+] dumped\n");
            goto out;
    }

    // Initialize SBL offsets
    init_sbl(
        g_kernel_data_base,
        offsets.offset_dmpml4i,
        offsets.offset_dmpdpi,
        offsets.offset_pml4pml4i,
        offsets.offset_mailbox_base,
        offsets.offset_mailbox_flags,
        offsets.offset_mailbox_meta,
        offsets.offset_sbl_mb_mtx,
        offsets.offset_g_message_id);

    authmgr_handle = get_authmgr_sm(sock, &offsets);
    SOCK_LOG(sock, "[+] got auth manager: %lu\n", authmgr_handle);

    // Example:
    // dump_queue_add_file(sock, "/system/common/lib/libkernel_sys.sprx");
    // dump_queue_add_dir(sock, "/system/vsh", 0);          // 0 -> non-recursive
    // dump_queue_add_dir(sock, "/mnt/sandbox/pfsmnt", 1);  // 1 -> recursive
    
    // dump_queue_add_file (which is also used by dump_queue_add_dir) will skip files in 
    // `/mnt/sandbox/pfsmnt/*-app0/` and `/mnt/sandbox/pfsmnt/*-patch0/`
    // i did this so when i pass in `/mnt/sandbox/pfsmnt` it will only dump `/mnt/sandbox/pfsmnt/PPSA01487-app0-patch0-union`
    // bc for ps5 games, `app0` and `app0-patch0-union` has the same files
    
    // Para PS4 disco:
    //dump_queue_add_dir(sock, "/mnt/sandbox/pfsmnt/XXXXXXXX-app0", 1);
    //dump_queue_add_dir(sock, "/mnt/sandbox/pfsmnt/XXXXXXXX-patch0", 1);
    //ps5   
    //dump_queue_add_dir(sock, "/mnt/sandbox/pfsmnt", 1);
    dump_eboot_from_disc(sock);
    dump(sock, authmgr_handle, &offsets, "/data/dump");

    //dump(sock, authmgr_handle, &offsets, "/data/dump");

out:
#ifdef LOG_TO_SOCKET
	close(sock);
#endif
	return 0;
}
