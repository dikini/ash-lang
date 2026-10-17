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

/* Inspect the declared non-callable bit pattern; never invoke it. This checks
   the bounded GNU64 function-address ABI assumption against the real C type. */
#include <string.h>
int32_t ash_counter_noncallable_sentinel(void (*sentinel)(void *)) {
    uintptr_t bits = 0;
    _Static_assert(sizeof(sentinel) == sizeof(bits), "GNU64 function-address width");
    memcpy(&bits, &sentinel, sizeof(bits));
    record_call('s');
    return bits == UINTPTR_MAX ? 7 : -1;
}
