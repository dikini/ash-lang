#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

struct ash_owner {
    size_t size;
};

int64_t ash_owner_negative_input(void) {
    return -1;
}

static void record(const char *event, size_t size) {
    const char *path = getenv("ASH_OWNER_TRACE");
    if (path == NULL) {
        abort();
    }
    FILE *file = fopen(path, "a");
    if (file == NULL || fprintf(file, "%s:%zu\n", event, size) < 0 || fclose(file) != 0) {
        abort();
    }
}

void *ash_owner_acquire(size_t size) {
    record("acquire", size);
    if (size == 0) {
        return NULL;
    }
    struct ash_owner *owner = malloc(sizeof(*owner));
    if (owner != NULL) {
        owner->size = size;
    }
    return owner;
}

void ash_owner_release(void *raw) {
    struct ash_owner *owner = raw;
    if (owner == NULL) {
        abort();
    }
    record("release", owner->size);
    free(owner);
}
