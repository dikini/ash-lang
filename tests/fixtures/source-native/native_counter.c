/* Ordinary pointer fixture; no shim around another library. */
#include <stdio.h>
#include <stdlib.h>

static void *owned;

static void record_call(int tag) {
    const char *path = getenv("ASH_NATIVE_COUNTER_TRACE");
    if (path == NULL) abort();
    FILE *trace = fopen(path, "ab");
    if (trace == NULL) abort();
    int written = fputc(tag, trace);
    int closed = fclose(trace);
    if (written == EOF || closed != 0) abort();
}

void *fixture_make(void) {
    record_call('m');
    if (owned != NULL) abort();
    unsigned char *allocation = malloc(3);
    if (allocation == NULL) abort();
    allocation[0] = 'a';
    allocation[1] = 'b';
    allocation[2] = 'c';
    owned = allocation;
    return allocation;
}

void *fixture_fail(void) {
    record_call('f');
    return NULL;
}

void *fixture_echo(void *address) {
    record_call('e');
    return address;
}

void fixture_release(void *address) {
    record_call('r');
    if (address == NULL || address != owned) abort();
    free(owned);
    owned = NULL;
}

/* Caller promises exactly three readable bytes. Do not retain, mutate or free. */
const void *fixture_echo_bytes(const unsigned char *bytes) {
    record_call('b');
    return bytes[0] == 'a' && bytes[1] == 'b' && bytes[2] == 'c'
        ? bytes : NULL;
}

/* Flat tuple order is observable: Address first, ordinary readonly Bytes second. */
void *fixture_pair(void *address, const unsigned char *bytes) {
    record_call('p');
    if (address != owned || address == NULL) abort();
    return bytes[0] == 'a' && bytes[1] == 'b' && bytes[2] == 'c'
        ? address : NULL;
}
