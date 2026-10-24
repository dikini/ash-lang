#ifndef ASH_CHECKED_DEPENDENT_OUTPUT_STATUS_H
#define ASH_CHECKED_DEPENDENT_OUTPUT_STATUS_H
int sqlite3_open_v2(const unsigned char *input, void **output, int flags, const unsigned char *vfs);
int sqlite3_close(void *owner);
int sqlite3_prepare_v2(void *parent, const unsigned char *input, int length, void **output, const unsigned char **tail);
int sqlite3_finalize(void *owner);
#endif
