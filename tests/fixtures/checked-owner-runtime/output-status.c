#include "owner.h"
#include <stdlib.h>

/* Compile/link-only implementation of the exact two-role test declaration.
 * It is neither SQLite implementation evidence nor selected-call execution. */
int sqlite3_open_v2(const unsigned char *input, void **output, int flags, const unsigned char *vfs) {
    if (input == NULL || flags != 6 || vfs != NULL) return 7;
    *output = calloc(1, 1);
    return *output == NULL ? 7 : 0;
}
int sqlite3_close(void *owner) {
    free(owner);
    return 0;
}
