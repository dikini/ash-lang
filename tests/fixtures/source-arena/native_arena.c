#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct allocation {
    void *pointer;
    size_t identity;
};

static struct allocation allocations[16];
static size_t attempted;

static FILE *trace(const char *variable) {
    const char *path = getenv(variable);
    if (path == NULL) {
        abort();
    }
    FILE *file = fopen(path, "a");
    if (file == NULL) {
        abort();
    }
    return file;
}

static void close_trace(FILE *file, int written) {
    if (written < 0 || fclose(file) != 0) {
        abort();
    }
}

int64_t ash_arena_negative_input(void) {
    FILE *file = trace("ASH_ARENA_INPUT_TRACE");
    close_trace(file, fprintf(file, "negative-one\n"));
    return -1;
}

int64_t ash_arena_minimum_input(void) {
    FILE *file = trace("ASH_ARENA_INPUT_TRACE");
    close_trace(file, fprintf(file, "minimum-i64\n"));
    return INT64_MIN;
}

void *ash_arena_calloc(size_t count, size_t width) {
    size_t identity = ++attempted;
    if (identity > sizeof(allocations) / sizeof(allocations[0])) {
        abort();
    }
    const char *injection = getenv("ASH_ARENA_REFUSE_FIRST");
    FILE *file = trace("ASH_ARENA_TRACE");
    if (identity == 1 && injection != NULL && strcmp(injection, "1") == 0) {
        close_trace(file, fprintf(file, "injected-refusal:%zu:%zu:%zu\n", identity, count, width));
        return NULL;
    }
    close_trace(file, fprintf(file, "calloc:%zu:%zu:%zu\n", identity, count, width));
    void *pointer = calloc(count, width);
    file = trace("ASH_ARENA_TRACE");
    if (pointer == NULL) {
        close_trace(file, fprintf(file, "native-null:%zu\n", identity));
        return NULL;
    }
    allocations[identity - 1] = (struct allocation){pointer, identity};
    close_trace(file, fprintf(file, "allocated:%zu\n", identity));
    return pointer;
}

void ash_arena_free(void *pointer) {
    if (pointer == NULL) {
        abort();
    }
    for (size_t index = 0; index < attempted; ++index) {
        if (allocations[index].pointer == pointer) {
            FILE *file = trace("ASH_ARENA_TRACE");
            close_trace(file, fprintf(file, "free:%zu\n", allocations[index].identity));
            allocations[index].pointer = NULL;
            free(pointer);
            return;
        }
    }
    abort();
}
