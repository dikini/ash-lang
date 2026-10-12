# Ash foreign libraries

These source libraries use the generic foreign contract, resource and generated
bridge path. The compiler supplies common mechanisms; the library defines its
configuration and lifecycle policy. [AD-0013](../docs/decisions/AD-0013-generated-native-bridges-and-program-builds.md)
records the build boundary. The active `ffi-ash` milestone has not yet integrated
these additions into Main.

## Arena lifecycle

[arena.ash](arena.ash) provides an opaque arena scope backed by libc `calloc` and
`free` on Linux x86-64 GNU. `ArenaConfig(capacity, slots)` admits both fields from
zero through `2^63 - 1`. A logical zero capacity allocates one physical byte.
The initial usage tuple is `(used bytes, capacity, object count, object slots)`.
Allocation refusal executes no body; normal completion releases exactly once.
Slots are logical configuration, without typed object storage.

From the repository root, create a client:

```sh
mkdir -p /tmp/ash-arena-demo
cat > /tmp/ash-arena-demo/entry.ash <<'ASH'
import @ffi.arena as Memory
main : Unit -> Memory.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, Int, Int, Int)>
main () = resource Memory.Arena<Fresh> arena = (Memory.ArenaConfig (64, 4)) {
    Memory.usage arena
}
ASH
CARGO_BUILD_JOBS=1 cargo run --bin ash -- build \
    --root ffi=libraries --output /tmp/ash-arena-demo/program \
    /tmp/ash-arena-demo/entry.ash
/tmp/ash-arena-demo/program
```

On successful allocation, the result is `Completed((0, 64, 0, 4), Closed)`.
The host needs the matching checkout, Rust toolchain and cached dependencies;
no additional native archive is needed for libc. Ordinary interpreted execution
refuses missing native bindings before evaluating the program.

The [connected arena evidence](../tests/fixtures/source-arena/README.md) observes
real allocations and exact releases separately from injected failure. Typed
allocation, references, layout evidence, borrowing and storage families remain
outside this library checkpoint. SQLite and native-buffer migration remain
separate milestone tasks.
