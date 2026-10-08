/* The pinned upstream header checks every Rust-declared ABI signature. */
#include "sqlite3.h"
#include <limits.h>
_Static_assert(SQLITE_VERSION_NUMBER == 3046001, "expected SQLite 3.46.1 header");
_Static_assert(CHAR_BIT == 8, "expected 8-bit bytes");
_Static_assert(sizeof(int) == 4, "expected 32-bit C int");
_Static_assert(sizeof(sqlite3_int64) == 8, "expected 64-bit SQLite integer");
_Static_assert(sizeof(void *) == 8, "expected 64-bit pointer");
static const char *(*check_version)(void) = sqlite3_libversion;
static const char *(*check_source)(void) = sqlite3_sourceid;
static const char *(*check_options)(int) = sqlite3_compileoption_get;
static int (*check_initialize)(void) = sqlite3_initialize;
static int (*check_open)(const char *, sqlite3 **, int, const char *) = sqlite3_open_v2;
static int (*check_prepare)(sqlite3 *, const char *, int, sqlite3_stmt **, const char **) = sqlite3_prepare_v2;
static int (*check_bind_integer)(sqlite3_stmt *, int, sqlite3_int64) = sqlite3_bind_int64;
static int (*check_bind_blob)(sqlite3_stmt *, int, const void *, int, void (*)(void *)) = sqlite3_bind_blob;
static int (*check_bind_text)(sqlite3_stmt *, int, const char *, int, void (*)(void *)) = sqlite3_bind_text;
static int (*check_bind_null)(sqlite3_stmt *, int) = sqlite3_bind_null;
static int (*check_step)(sqlite3_stmt *) = sqlite3_step;
static int (*check_count)(sqlite3_stmt *) = sqlite3_column_count;
static int (*check_type)(sqlite3_stmt *, int) = sqlite3_column_type;
static sqlite3_int64 (*check_integer)(sqlite3_stmt *, int) = sqlite3_column_int64;
static const void *(*check_blob)(sqlite3_stmt *, int) = sqlite3_column_blob;
static const unsigned char *(*check_text)(sqlite3_stmt *, int) = sqlite3_column_text;
static int (*check_bytes)(sqlite3_stmt *, int) = sqlite3_column_bytes;
static int (*check_reset)(sqlite3_stmt *) = sqlite3_reset;
static int (*check_clear)(sqlite3_stmt *) = sqlite3_clear_bindings;
static int (*check_finalize)(sqlite3_stmt *) = sqlite3_finalize;
static int (*check_close)(sqlite3 *) = sqlite3_close;
static int (*check_errcode)(sqlite3 *) = sqlite3_errcode;
static const char *(*check_errmsg)(sqlite3 *) = sqlite3_errmsg;
/* Keep SQLite's implementation-defined destructor sentinel out of Rust. */
int ash_sqlite_bind_blob_copy(sqlite3_stmt *stmt, int index, const void *bytes, int len) {
    return sqlite3_bind_blob(stmt, index, bytes, len, SQLITE_TRANSIENT);
}

int ash_sqlite_bind_text_copy(sqlite3_stmt *stmt, int index, const char *text, int len) {
    return sqlite3_bind_text(stmt, index, text, len, SQLITE_TRANSIENT);
}
