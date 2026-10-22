#ifndef ASH_CHECKED_OWNER_FIXTURE_H
#define ASH_CHECKED_OWNER_FIXTURE_H
#include <stddef.h>
void *ash_checked_owner_acquire(size_t capacity, size_t initialized);
void ash_checked_owner_release(void *current);
void *ash_checked_owner_view(void *current, size_t key);
size_t ash_checked_owner_length(void *current, size_t key);
#endif
