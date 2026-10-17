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
outside this library checkpoint. The SQLite library below has its own lifecycle and copy profile.

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

## Copying SQLite

[sqlite.ash](sqlite.ash) is the ordinary passive source library for Linux x86-64
GNU. It declares the SQLite symbols, owner dependencies, constants and non-callable
TRANSIENT sentinel. Ash code supplies path/SQL validation, statement protocol,
copying and completion policy. Generated typed bridges call SQLite directly;
there is no product SQLite registration or adapter dependency.

A minimal imported client is:

```ash
import @ffi.sqlite as Sqlite
main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>> ! {Sqlite.Initialize}
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
    resource Sqlite.Statement<S, C> stmt = (db, "SELECT 42") {
        match Sqlite.step stmt {
            Sqlite.Row => Sqlite.column_int (stmt, 0)
            Sqlite.Done => Sqlite.Err Sqlite.MissingRow
            Sqlite.StepError(error) => Sqlite.Err error
        }
    }
}
```

It prints `Completed(Completed(Ok(42), Closed), Closed)`. Body results stay nested;
refused acquisition skips the body. Statement finalization precedes connection
close. Capture/resume preserves the same owners; owned discard runs needed source
cleanup before releasing each owner once and skips the abandoned body.

SQLite needs an explicit native input. The CLI has no native-link option; use the
Rust build API and the matching installed SQLite library:

```rust
use ash::build::{BuildConfiguration, NativeLinkInput, build_path};
use ash::driver::RunConfiguration;
use ash::module::ModuleRoots;
use std::path::Path;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let source = RunConfiguration {
        entry: "entry.ash".into(),
        roots: ModuleRoots::new([("ffi", Path::new("libraries"))])?,
    };
    let mut build = BuildConfiguration::new("./program".into());
    build.native_inputs.push(NativeLinkInput::SharedLibrary(
        "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0".into(),
    ));
    let program = build_path(source, build)?;
    println!("{}", program.executable().display());
    Ok(())
}
```

Run the resulting executable separately. The native binary and system loader must
match the declared profile and authored foreign assumptions; linking is not a
header/ABI proof. The optional [`ash check-ffi`](../docs/tools/ash.md#optional-c-header-checking)
authoring tool separately checks supplied headers against the authored facts;
its C assertions produce no runtime object or executable authority.
The [generated-host tests](../tests/sqlite_library.rs) use this API with the real
shared SQLite library and separate static observation wrappers. They remove Ash
sources before building and image/facts files before execution.

The public operations cover integer/text/blob binding, step, reset, clear and
independent column copies. NULL and empty values remain distinct. Copied text uses
strict UTF-8 and may contain NUL; bound text rejects interior NUL. Input-width,
column/storage-kind and phase refusals occur before the relevant C operation.
FLOAT columns refuse rather than add an Ash Float type. SQL permits one statement
followed only by the retained ASCII whitespace policy. Database-name interior NUL
refuses before SQLite initialization. Initialization otherwise occurs once per
connection acquisition; the library does not shut down the process-wide SQLite
runtime.

`Sqlite.diagnostic db` copies the current native message and status. Ordinary
bounded-copy refusal produces `DiagnosticUnavailable(code)` without inventing an
empty message or changing the code; actual work/storage exhaustion is terminal.
Native step/binding status and statement completion are separate results. A
consumed finalize error does not retain or retry that statement. Retained or
blocked completion revokes source access under the common quarantine policy;
there is no `close_v2` substitution.

### SQLite migration

| Former experiment spelling or path | Source-library replacement |
| --- | --- |
| `import sqlite as Sqlite` with a Rust registration | `import @ffi.sqlite as Sqlite`, root `ffi=libraries`, explicit native build input |
| `Provider.Scope<I, E, T>` | `Sqlite.Scope<I, E, T>` with the same nested report structure |
| `resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText sql)` | `resource Sqlite.Statement<S, C> stmt = (db, sql)`, using the enclosing connection identity `C` |
| `StatementOps<S, C>` / `StatementProvider<S, C>` | `StatementOps<Sqlite.Statement<S, C>>` / `StatementProvider<Sqlite.Statement<S, C>>` |
| Compiler `foreign::sqlite_manifest` / `sqlite_binding` / copying C shim | Passive source declarations and generated typed native bridges |

Connection operations/provider use `ConnectionOps<C>` / `ConnectionProvider<C>`.
Ordinary diagnostic callbacks therefore carry the owner identity rather than
native State as an effect argument. The State-returning `borrow` operation is for
exact original lifecycle phases; it grants no ordinary callable or native-wrapper
permission. State-returning callables and native calls outside their checked phase
still refuse.

The [ported clients](../tests/fixtures/sqlite-product/) retain copying, imported
row helpers, statement reuse, repeated/simultaneous identities, file persistence,
control resume/discard and error/refusal cases. The old DN-0036 Rust/C adapter and
programs remain explicit experiment comparators in `foreign-adapter` and
`tests/fixtures/provider-experiments`; the compiler no longer exports their
SQLite manifest. Generic foreign/arena experiment mechanisms remain separate.
Generated-native local newtype/dictionary limitations and signed-64 literal image
limits remain; ordinary Int arithmetic can still produce wider mathematical
values and checked foreign narrowing still refuses them.
