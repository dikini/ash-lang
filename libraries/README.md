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
outside this library checkpoint. SQLite remains a separate milestone task.


## Native buffer

[native_buffer.ash](native_buffer.ash) declares `calloc`/`free` and the ordinary
`Buffer<R>` resource for `x86_64-unknown-linux-gnu`. Its `acquired_only` report
preserves `Failure(Error)` for refused acquisition and `Success(body_value)`
after normal completion. A body returning `Outcome<T>` stays nested. Cell
behavior is unchanged; buffer names carry no compiler-owned authority.

From the repository root:

```sh
mkdir -p /tmp/ash-buffer-demo
cat > /tmp/ash-buffer-demo/entry.ash <<'ASH'
import @ffi.native_buffer as Buffer
main : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>
main () = resource Buffer.Buffer<R> bytes = 4 {
    match Buffer.write (bytes, 0, 42) {
        Buffer.Success(()) => Buffer.read (bytes, 0)
        Buffer.Failure(error) => Buffer.Failure error
    }
}
ASH
CARGO_BUILD_JOBS=1 cargo run --bin ash -- build \
    --root ffi=libraries --cargo-target-dir target/ffi-native-hosts \
    --output /tmp/ash-buffer-demo/program /tmp/ash-buffer-demo/entry.ash
/tmp/ash-buffer-demo/program
```

Successful allocation prints `Success(Success(42))`. No additional native archive
is needed for libc. Positive lengths through `2^63 - 1` are eligible, subject to
allocation and work/storage admission. Zero, negative or unrepresentable lengths
return `Failure(InvalidLength)` before C; native null returns
`Failure(AllocationFailed)` without a body. New bytes are zeroed. Read uses
zero-based bounds; write checks index before byte range `[0, 255]`, and refuses
without mutation. Internal work/storage exhaustion is terminal. There is no
implicit retry or new normal-runtime size cap.

Capture/resume moves the same owner. Owned discard finishes it once in structural
order with needed outer resources live and skips its abandoned body result.
Cleanup may acquire an inner buffer, which completes normally with its own
report. The [counted native fixtures](../tests/native_buffer_source.rs) use real
static/shared wrappers around libc, with release identity independent of bytes.
Injected callback/refusal evidence remains separate from those C observations.

### Native-buffer migration

| Former builtin spelling | Ordinary source spelling |
| --- | --- |
| `import @builtin.native_buffer as Buffer` | `import @ffi.native_buffer as Buffer`, with `--root ffi=libraries` |
| `resource native_buffer<R> b = length { body }` | `resource Buffer.Buffer<R> b = length { body }` |
| `Buffer.Handle<R>` | `Buffer.Buffer<R>` |
| `Buffer.Provider<R>` | `Buffer.Provider<Buffer.Buffer<R>>` |
| `Buffer.Ops<R>` | `Buffer.Ops<Buffer.Buffer<R>>` |
| `Buffer.Outcome<T>`, `Success`, `Failure`, error cases | Same public result/error spellings, with the imported source identities |

Facades may re-export the original resource declaration and its API. Targeted
imports and renaming preserve that declaration; copied API shapes do not grant
its permission. Recompile migrated callers with the matching compiler/runtime;
old Core/images are not compatible library artifacts. The old builtin module,
parser designator, special dispatch and native-buffer adapter crate are removed.
Common byte primitives and guard storage remain shared mechanisms.

The broader generated-native carrier still rejects ordinary local newtypes and
non-resource lexical dictionaries. Their legal source/Core capture checks remain
covered; that unsupported-build diagnostic is not native buffer parity. This
port adds neither privileged State/native wrappers, source-given forwarding,
copy windows, SQLite, header checking nor general macro evaluation.
