#ifndef ASH_CHECKED_OUTPUT_STATUS_H
#define ASH_CHECKED_OUTPUT_STATUS_H
int sqlite3_open_v2(const unsigned char *input, void **output, int flags, const unsigned char *vfs);
int sqlite3_close(void *owner);
#endif
