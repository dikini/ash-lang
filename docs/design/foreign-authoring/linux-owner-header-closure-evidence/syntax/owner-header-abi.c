/* Compile-only header/type/target check. No main, linkage or execution. */
#include <stdlib.h>
#include <stddef.h>
#include <stdint.h>
#include <limits.h>
#if !defined(__x86_64__) || !defined(__linux__) || !defined(__GLIBC__)
#error Unsupported fixed target/header family
#endif
_Static_assert(CHAR_BIT == 8, "eight-bit C byte required");
_Static_assert(sizeof(size_t) == 8 && SIZE_MAX == UINT64_MAX, "size_t is unsigned64");
_Static_assert(sizeof(void *) == 8 && _Alignof(void *) == 8, "x86-64 pointer shape");
_Static_assert(_Generic(&malloc, void *(*)(size_t): 1, default: 0), "malloc prototype");
_Static_assert(_Generic(&free, void (*)(void *): 1, default: 0), "free prototype");
