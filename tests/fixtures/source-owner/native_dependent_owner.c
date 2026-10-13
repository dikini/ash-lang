#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

struct ash_parent {
    unsigned char bytes[128];
    size_t identity;
    size_t children;
};

struct ash_child {
    struct ash_parent *parent;
    size_t identity;
};

static void record(const char *event, size_t identity) {
    const char *path = getenv("ASH_OWNER_TRACE");
    assert(path != NULL);
    FILE *file = fopen(path, "a");
    assert(file != NULL);
    fprintf(file, "%s:%zu\n", event, identity);
    assert(fclose(file) == 0);
}

struct ash_parent *ash_parent_acquire(size_t identity) {
    struct ash_parent *parent = calloc(1, sizeof(*parent));
    assert(parent != NULL);
    assert(identity <= sizeof(parent->bytes));
    parent->identity = identity;
    parent->children = 0;
    record("parent-acquire", identity);
    return parent;
}

struct ash_child *ash_child_acquire(struct ash_parent *parent, size_t identity) {
    assert(parent != NULL);
    struct ash_child *child = malloc(sizeof(*child));
    assert(child != NULL);
    child->parent = parent;
    child->identity = identity;
    parent->children += 1;
    record("child-acquire", identity);
    return child;
}

void ash_child_hold(struct ash_child *child, struct ash_parent *parent) {
    assert(child != NULL && child->parent == parent && parent->children != 0);
    record("child-retain", child->identity);
}

void ash_child_release(struct ash_child *child, struct ash_parent *parent) {
    assert(child != NULL && child->parent == parent && parent->children != 0);
    record("child-release", child->identity);
    record("parent-final-byte", parent->bytes[0]);
    parent->children -= 1;
    free(child);
}

void ash_parent_release(struct ash_parent *parent) {
    assert(parent != NULL && parent->children == 0);
    record("parent-release", parent->identity);
    free(parent);
}
