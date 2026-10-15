
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
extern int sqlite3_initialize(void);
extern int sqlite3_open_v2(const char *, void **, int, const char *);
extern int sqlite3_close(void *);
extern int sqlite3_prepare_v2(void *, const char *, int, void **, const char **);
extern int sqlite3_finalize(void *);
extern int sqlite3_bind_int64(void *, int, int64_t);
extern int sqlite3_bind_text(void *, int, const char *, int, void (*)(void *));
extern int sqlite3_step(void *);
extern int sqlite3_errcode(void *);
extern const char *sqlite3_errmsg(void *);
static void trace(const char *operation, int status, int output) {
    const char *path = getenv("ASH_SQLITE_TRACE");
    if (!path) abort();
    FILE *file = fopen(path, "a");
    if (!file) abort();
    if (output < 0) fprintf(file, "%s %d\n", operation, status);
    else fprintf(file, "%s %d %d\n", operation, status, output);
    if (fclose(file)) abort();
}
int probe_initialize(void) {
    int status = getenv("ASH_SQLITE_INITIALIZE_FAILURE") ? 77 : sqlite3_initialize();
    trace("initialize", status, -1);
    return status;
}
int probe_open(const char *path, void **output, int flags, const char *vfs) {
    if (*output || flags != 6 || vfs != NULL) abort();
    int status = sqlite3_open_v2(path, output, flags, vfs);
    trace("open", status, *output != NULL);
    return status;
}
int probe_close(void *owner) {
    int status = sqlite3_close(owner);
    trace("close", status, -1);
    return status;
}
int probe_prepare(void *owner, const char *sql, int length, void **output, const char **tail) {
    if (*output) abort();
    int status = sqlite3_prepare_v2(owner, sql, length, output, tail);
    trace("prepare", status, *output != NULL);
    return status;
}
int probe_finalize(void *owner) {
    int status = sqlite3_finalize(owner);
    trace("finalize", status, -1);
    return status;
}
int probe_bind_int(void *owner, int index, int64_t value) {
    int status = sqlite3_bind_int64(owner, index, value);
    trace("bind_int", status, -1);
    return status;
}
int probe_bind_text(void *owner, int index, const char *text, int length, void (*destructor)(void *)) {
    int status = sqlite3_bind_text(owner, index, text, length, destructor);
    trace("bind_text", status, -1);
    return status;
}
int probe_step(void *owner) {
    int status = sqlite3_step(owner);
    trace("step", status, -1);
    return status;
}
int probe_errcode(void *owner) {
    int status = sqlite3_errcode(owner);
    trace("errcode", status, -1);
    return status;
}
const char *probe_errmsg(void *owner) {
    const char *value = sqlite3_errmsg(owner);
    trace("errmsg", 0, value != NULL);
    return value;
}
extern int sqlite3_column_count(void *);
extern int sqlite3_column_type(void *, int);
extern int64_t sqlite3_column_int64(void *, int);
extern int sqlite3_bind_blob(void *, int, const void *, int, void (*)(void *));
extern int sqlite3_clear_bindings(void *);
int probe_column_count(void *owner) {
    int count = sqlite3_column_count(owner);
    trace("column_count", count, -1);
    return count;
}
int probe_column_type(void *owner, int index) {
    int kind = sqlite3_column_type(owner, index);
    trace("column_type", kind, -1);
    return kind;
}
int64_t probe_column_int(void *owner, int index) {
    int64_t value = sqlite3_column_int64(owner, index);
    trace("column_int", 0, -1);
    return value;
}
int probe_bind_blob(void *owner, int index, const void *bytes, int length, void (*destructor)(void *)) {
    int status = sqlite3_bind_blob(owner, index, bytes, length, destructor);
    trace("bind_blob", status, -1);
    return status;
}
int probe_clear_bindings(void *owner) {
    int status = sqlite3_clear_bindings(owner);
    trace("clear_bindings", status, -1);
    return status;
}
extern int sqlite3_reset(void *);
int probe_reset(void *owner) {
    int status = sqlite3_reset(owner);
    trace("reset", status, -1);
    return status;
}
extern const void *sqlite3_column_blob(void *, int);
extern int sqlite3_column_bytes(void *, int);
const void *probe_column_blob(void *owner, int index) {
    const void *bytes = sqlite3_column_blob(owner, index);
    trace("column_blob", index, bytes != NULL);
    return bytes;
}
int probe_column_bytes(void *owner, int index) {
    int length = sqlite3_column_bytes(owner, index);
    trace("column_bytes", index, length);
    return length;
}
