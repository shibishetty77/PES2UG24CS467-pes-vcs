// object.c — Content-addressable object store
//
// Every piece of data (file contents, directory listings, commits) is stored
// as an "object" named by its SHA-256 hash. Objects are stored under
// .pes/objects/XX/YYYYYY... where XX is the first two hex characters of the
// hash (directory sharding).
//
// PROVIDED functions: compute_hash, object_path, object_exists, hash_to_hex, hex_to_hash
// TODO functions:     object_write, object_read

#include "pes.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>

// ─── PROVIDED ────────────────────────────────────────────────────────────────

void hash_to_hex(const ObjectID *id, char *hex_out) {
    for (int i = 0; i < HASH_SIZE; i++) {
        sprintf(hex_out + i * 2, "%02x", id->hash[i]);
    }
    hex_out[HASH_HEX_SIZE] = '\0';
}

int hex_to_hash(const char *hex, ObjectID *id_out) {
    if (strlen(hex) < HASH_HEX_SIZE) return -1;
    for (int i = 0; i < HASH_SIZE; i++) {
        unsigned int byte;
        if (sscanf(hex + i * 2, "%2x", &byte) != 1) return -1;
        id_out->hash[i] = (uint8_t)byte;
    }
    return 0;
}

static uint32_t sha256_rotr(uint32_t x, uint32_t n) {
    return (x >> n) | (x << (32 - n));
}

static uint32_t sha256_load_be32(const uint8_t *p) {
    return ((uint32_t)p[0] << 24) |
           ((uint32_t)p[1] << 16) |
           ((uint32_t)p[2] << 8) |
           (uint32_t)p[3];
}

static void sha256_store_be32(uint32_t x, uint8_t *p) {
    p[0] = (uint8_t)(x >> 24);
    p[1] = (uint8_t)(x >> 16);
    p[2] = (uint8_t)(x >> 8);
    p[3] = (uint8_t)x;
}

static void sha256_transform(uint32_t state[8], const uint8_t block[64]) {
    static const uint32_t k[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    };

    uint32_t w[64];
    for (int i = 0; i < 16; i++) {
        w[i] = sha256_load_be32(block + i * 4);
    }
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = sha256_rotr(w[i - 15], 7) ^ sha256_rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
        uint32_t s1 = sha256_rotr(w[i - 2], 17) ^ sha256_rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }

    uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
    uint32_t e = state[4], f = state[5], g = state[6], h = state[7];

    for (int i = 0; i < 64; i++) {
        uint32_t s1 = sha256_rotr(e, 6) ^ sha256_rotr(e, 11) ^ sha256_rotr(e, 25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t temp1 = h + s1 + ch + k[i] + w[i];
        uint32_t s0 = sha256_rotr(a, 2) ^ sha256_rotr(a, 13) ^ sha256_rotr(a, 22);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t temp2 = s0 + maj;

        h = g;
        g = f;
        f = e;
        e = d + temp1;
        d = c;
        c = b;
        b = a;
        a = temp1 + temp2;
    }

    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

void compute_hash(const void *data, size_t len, ObjectID *id_out) {
    uint32_t state[8] = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    };

    size_t original_len = len;
    const uint8_t *bytes = (const uint8_t *)data;
    while (len >= 64) {
        sha256_transform(state, bytes);
        bytes += 64;
        len -= 64;
    }

    uint8_t block[128] = {0};
    memcpy(block, bytes, len);
    block[len] = 0x80;

    uint64_t bit_len = (uint64_t)original_len * 8;
    size_t pad_block_len = (len < 56) ? 64 : 128;
    for (int i = 0; i < 8; i++) {
        block[pad_block_len - 1 - i] = (uint8_t)(bit_len >> (i * 8));
    }

    sha256_transform(state, block);
    if (pad_block_len == 128) {
        sha256_transform(state, block + 64);
    }

    for (int i = 0; i < 8; i++) {
        sha256_store_be32(state[i], id_out->hash + i * 4);
    }
}

// Get the filesystem path where an object should be stored.
// Format: .pes/objects/XX/YYYYYYYY...
// The first 2 hex chars form the shard directory; the rest is the filename.
void object_path(const ObjectID *id, char *path_out, size_t path_size) {
    char hex[HASH_HEX_SIZE + 1];
    hash_to_hex(id, hex);
    snprintf(path_out, path_size, "%s/%.2s/%s", OBJECTS_DIR, hex, hex + 2);
}

int object_exists(const ObjectID *id) {
    char path[512];
    object_path(id, path, sizeof(path));
    return access(path, F_OK) == 0;
}

// ─── TODO: Implement these ──────────────────────────────────────────────────

// Write an object to the store.
//
// Object format on disk:
//   "<type> <size>\0<data>"
//   where <type> is "blob", "tree", or "commit"
//   and <size> is the decimal string of the data length
//
// Steps:
//   1. Build the full object: header ("blob 16\0") + data
//   2. Compute SHA-256 hash of the FULL object (header + data)
//   3. Check if object already exists (deduplication) — if so, just return success
//   4. Create shard directory (.pes/objects/XX/) if it doesn't exist
//   5. Write to a temporary file in the same shard directory
//   6. fsync() the temporary file to ensure data reaches disk
//   7. rename() the temp file to the final path (atomic on POSIX)
//   8. Open and fsync() the shard directory to persist the rename
//   9. Store the computed hash in *id_out

// HINTS - Useful syscalls and functions for this phase:
//   - sprintf / snprintf : formatting the header string
//   - compute_hash       : hashing the combined header + data
//   - object_exists      : checking for deduplication
//   - mkdir              : creating the shard directory (use mode 0755)
//   - open, write, close : creating and writing to the temp file
//                          (Use O_CREAT | O_WRONLY | O_TRUNC, mode 0644)
//   - fsync              : flushing the file descriptor to disk
//   - rename             : atomically moving the temp file to the final path
//

//
// Returns 0 on success, -1 on error.
int object_write(ObjectType type, const void *data, size_t len, ObjectID *id_out) {
    const char *type_name;
    switch (type) {
        case OBJ_BLOB:   type_name = "blob"; break;
        case OBJ_TREE:   type_name = "tree"; break;
        case OBJ_COMMIT: type_name = "commit"; break;
        default: return -1;
    }

    char header[64];
    int header_len = snprintf(header, sizeof(header), "%s %zu", type_name, len);
    if (header_len < 0 || (size_t)header_len + 1 > sizeof(header)) return -1;

    size_t full_len = (size_t)header_len + 1 + len;
    uint8_t *full = malloc(full_len);
    if (!full) return -1;

    memcpy(full, header, (size_t)header_len);
    full[header_len] = '\0';
    if (len > 0) memcpy(full + header_len + 1, data, len);

    ObjectID id;
    compute_hash(full, full_len, &id);
    if (id_out) *id_out = id;

    if (object_exists(&id)) {
        free(full);
        return 0;
    }

    char hex[HASH_HEX_SIZE + 1];
    hash_to_hex(&id, hex);

    char shard_dir[512];
    snprintf(shard_dir, sizeof(shard_dir), "%s/%.2s", OBJECTS_DIR, hex);
    if (mkdir(shard_dir, 0755) != 0 && errno != EEXIST) {
        free(full);
        return -1;
    }

    char final_path[512];
    object_path(&id, final_path, sizeof(final_path));

    char tmp_path[1024];
    snprintf(tmp_path, sizeof(tmp_path), "%s/tmp-%ld", shard_dir, (long)getpid());

    int fd = open(tmp_path, O_CREAT | O_WRONLY | O_TRUNC, 0644);
    if (fd < 0) {
        free(full);
        return -1;
    }

    size_t written = 0;
    while (written < full_len) {
        ssize_t n = write(fd, full + written, full_len - written);
        if (n < 0) {
            if (errno == EINTR) continue;
            close(fd);
            unlink(tmp_path);
            free(full);
            return -1;
        }
        written += (size_t)n;
    }

    free(full);

    if (fsync(fd) != 0 || close(fd) != 0) {
        unlink(tmp_path);
        return -1;
    }

    if (rename(tmp_path, final_path) != 0) {
        unlink(tmp_path);
        return -1;
    }

    int dir_fd = open(shard_dir, O_RDONLY);
    if (dir_fd >= 0) {
        fsync(dir_fd);
        close(dir_fd);
    }

    return 0;
}

// Read an object from the store.
//
// Steps:
//   1. Build the file path from the hash using object_path()
//   2. Open and read the entire file
//   3. Parse the header to extract the type string and size
//   4. Verify integrity: recompute the SHA-256 of the file contents
//      and compare to the expected hash (from *id). Return -1 if mismatch.
//   5. Set *type_out to the parsed ObjectType
//   6. Allocate a buffer, copy the data portion (after the \0), set *data_out and *len_out
//
// HINTS - Useful syscalls and functions for this phase:
//   - object_path        : getting the target file path
//   - fopen, fread, fseek: reading the file into memory
//   - memchr             : safely finding the '\0' separating header and data
//   - strncmp            : parsing the type string ("blob", "tree", "commit")
//   - compute_hash       : re-hashing the read data for integrity verification
//   - memcmp             : comparing the computed hash against the requested hash
//   - malloc, memcpy     : allocating and returning the extracted data
//
// The caller is responsible for calling free(*data_out).
//
// The caller is responsible for calling free(*data_out).
// Returns 0 on success, -1 on error (file not found, corrupt, etc.).
int object_read(const ObjectID *id, ObjectType *type_out, void **data_out, size_t *len_out) {
    if (!id || !type_out || !data_out || !len_out) return -1;

    char path[512];
    object_path(id, path, sizeof(path));

    FILE *f = fopen(path, "rb");
    if (!f) return -1;

    if (fseek(f, 0, SEEK_END) != 0) {
        fclose(f);
        return -1;
    }

    long file_size = ftell(f);
    if (file_size <= 0) {
        fclose(f);
        return -1;
    }
    rewind(f);

    uint8_t *full = malloc((size_t)file_size);
    if (!full) {
        fclose(f);
        return -1;
    }

    size_t read_len = fread(full, 1, (size_t)file_size, f);
    fclose(f);
    if (read_len != (size_t)file_size) {
        free(full);
        return -1;
    }

    ObjectID actual;
    compute_hash(full, read_len, &actual);
    if (memcmp(actual.hash, id->hash, HASH_SIZE) != 0) {
        free(full);
        return -1;
    }

    uint8_t *null_byte = memchr(full, '\0', read_len);
    if (!null_byte) {
        free(full);
        return -1;
    }

    size_t header_len = (size_t)(null_byte - full);
    uint8_t *space = memchr(full, ' ', header_len);
    if (!space || space == full || space + 1 >= null_byte) {
        free(full);
        return -1;
    }

    size_t type_len = (size_t)(space - full);
    ObjectType parsed_type;
    if (type_len == 4 && memcmp(full, "blob", 4) == 0) {
        parsed_type = OBJ_BLOB;
    } else if (type_len == 4 && memcmp(full, "tree", 4) == 0) {
        parsed_type = OBJ_TREE;
    } else if (type_len == 6 && memcmp(full, "commit", 6) == 0) {
        parsed_type = OBJ_COMMIT;
    } else {
        free(full);
        return -1;
    }

    char size_buf[32];
    size_t size_len = (size_t)(null_byte - space - 1);
    if (size_len == 0 || size_len >= sizeof(size_buf)) {
        free(full);
        return -1;
    }
    memcpy(size_buf, space + 1, size_len);
    size_buf[size_len] = '\0';

    char *endptr;
    errno = 0;
    unsigned long long parsed_size = strtoull(size_buf, &endptr, 10);
    if (errno != 0 || *endptr != '\0' || parsed_size > (unsigned long long)SIZE_MAX) {
        free(full);
        return -1;
    }

    size_t data_len = read_len - header_len - 1;
    if ((size_t)parsed_size != data_len) {
        free(full);
        return -1;
    }

    uint8_t *data = malloc(data_len + 1);
    if (!data) {
        free(full);
        return -1;
    }
    if (data_len > 0) memcpy(data, null_byte + 1, data_len);
    data[data_len] = '\0';

    free(full);

    *type_out = parsed_type;
    *data_out = data;
    *len_out = data_len;
    return 0;
}
