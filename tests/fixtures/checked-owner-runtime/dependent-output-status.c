#include "owner.h"
#include <stdlib.h>

/* Compile/link-only implementation of the exact four original ABI shapes.
 * This fixture is never executed and supplies no SQLite behavior evidence. */
int sqlite3_open_v2(const unsigned char *input, void **output, int flags, const unsigned char *vfs) {
    if (input == NULL || flags != 6 || vfs != NULL) return 7;
    *output = calloc(1, 1);
    return *output == NULL ? 7 : 0;
}
int sqlite3_close(void *owner) {
    free(owner);
    return 0;
}
int sqlite3_prepare_v2(void *parent, const unsigned char *input, int length, void **output, const unsigned char **tail) {
    if (parent == NULL || input == NULL || length < 0) return 7;
    *output = calloc(1, 1);
    *tail = input + (length == 0 ? 0 : length - 1);
    return *output == NULL ? 7 : 0;
}
int sqlite3_finalize(void *owner) {
    free(owner);
    return 0;
}
