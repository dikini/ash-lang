/* Ordinary native library fixture, not a runtime shim or header checker. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static void record_call(int tag) {
    const char *path = getenv("ASH_NATIVE_COUNTER_TRACE");
    if (path == NULL) {
        abort();
    }
    FILE *trace = fopen(path, "ab");
    if (trace == NULL) {
        abort();
    }
    int written = fputc(tag, trace);
    int closed = fclose(trace);
    if (written == EOF || closed != 0) {
        abort();
    }
}

int8_t ash_counter_echo_i8(int8_t value) {
    record_call('i');
    return value;
}

uint64_t ash_counter_max_u64(void) {
    record_call('u');
    return UINT64_MAX;
}

void ash_counter_void(void) {
    record_call('v');
}

uint64_t ash_counter_echo_u64(uint64_t value) {
    record_call('w');
    return value;
}
