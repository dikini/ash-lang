struct ash_grand {
    struct ash_child *child;
    size_t identity;
};

struct ash_grand *ash_grand_acquire(struct ash_child *child, size_t identity) {
    assert(child != NULL);
    struct ash_grand *grand = malloc(sizeof(*grand));
    assert(grand != NULL);
    grand->child = child;
    grand->identity = identity;
    child->children += 1;
    record("grand-acquire", identity);
    return grand;
}

void ash_grand_hold(struct ash_grand *grand, struct ash_child *child) {
    assert(grand != NULL && grand->child == child && child->children != 0);
    record("grand-retain", grand->identity);
}

void ash_grand_release(struct ash_grand *grand, struct ash_child *child) {
    assert(grand != NULL && grand->child == child && child->children != 0);
    record("grand-release", grand->identity);
    child->children -= 1;
    free(grand);
}
