#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* Trace identity is independent of the writable region. The source promise is
 * seven initialized bytes (or zero); requested identity is not its extent. */
struct byte_owner {
    uint8_t bytes[7];
    size_t identity;
};
static void record(const char *event, size_t identity) {
    const char *path = getenv("ASH_OWNER_TRACE");
    if (path == NULL) abort();
    FILE *file = fopen(path, "a");
    if (file == NULL || fprintf(file, "%s:%zu\n", event, identity) < 0 || fclose(file) != 0) abort();
}
void *ash_owner_acquire(size_t identity) {
    record("acquire", identity);
    if (identity == 0) return NULL;
    struct byte_owner *owner = calloc(1, sizeof(*owner));
    if (owner != NULL) {
        owner->identity = identity;
        owner->bytes[0] = 5;
        owner->bytes[1] = 255;
    }
    return owner;
}
void ash_owner_release(void *raw) {
    struct byte_owner *owner = raw;
    if (owner == NULL) abort();
    record("release", owner->identity);
    free(owner);
}
