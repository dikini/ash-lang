/* UNBUILT source-only candidate. The admitted contract must establish live,
 * compatible Current provenance; these functions cannot authenticate pointers. */
#include "owner.h"
#include <stdlib.h>

void *ash_checked_owner_acquire(size_t capacity, size_t initialized) {
    static const unsigned char pattern[8] = {5, 255, 0, 65, 66, 67, 0, 9};
    if (capacity != 8 || initialized != 8) return NULL;
    unsigned char *bytes = calloc(8, sizeof(*bytes));
    if (bytes == NULL) return NULL;
    for (size_t i = 0; i < 8; ++i) bytes[i] = pattern[i];
    return bytes;
}

void ash_checked_owner_release(void *current) {
    free(current);
}

void *ash_checked_owner_view(void *current, size_t key) {
    return key == 0 ? current : NULL;
}

size_t ash_checked_owner_length(void *current, size_t key) {
    return current != NULL && key == 0 ? 8 : 0;
}
