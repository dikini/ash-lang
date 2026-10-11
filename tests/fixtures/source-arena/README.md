# Source-authored arena lifecycle fixture

The production [arena library](../../../libraries/arena.ash) declares direct
`calloc`/`free` contracts. It checks capacity and slot count with both
`Foreign.checked_i64` and `Foreign.checked_size_t` before acquisition, admitting
each field from zero through the GNU64 profile's maximum signed integer. Zero
logical capacity uses one physical byte. Private source data retains logical
capacity and slots; the usage handler returns their initial counts.

`entry.ash` checks normal, zero, repeated and nested scopes, negative and
out-of-profile fields, and the maximum admitted slot count. Negative inputs come
from ordinary owner-free native scalar replies; no negative Ash literal or
foreign constant publication is required. Invalid configurations have diverging
client bodies, so completing the program within the test deadline demonstrates
that those bodies were skipped.

The public test substitutes only the two allocator symbol names in a temporary
copy before source compilation. `native_arena.c` traces wrappers that call real
libc `calloc` and `free`; it tracks returned pointers and rejects unmatched or
duplicate release. Native input generation has a separate trace. An explicit
injected-refusal run returns NULL before calling libc and is checked separately
from real successful allocations.

The test compiles through the public driver, removes Ash sources, builds one
generated executable with the native-host cache, and runs both scenarios. It
checks returned observations, actual calls, no acquisition for invalid
configuration and inner-before-outer release. A separate preparation case keeps
the production symbols unchanged. Run on Linux x86-64 GNU with Rust, `cc` and
`ar`:

```sh
CARGO_BUILD_JOBS=1 cargo test -p ash --all-features \
    --test source_arena_execution -- --test-threads=1
```

This is the bounded lifecycle delivery in
[TASK-0039](../../../docs/tasks/TASK-0039-ash-arena-lifecycle.md). It does not expose
initialized byte access, typed allocations, references, storage families,
dependent owners or additional capture/discard behavior.
