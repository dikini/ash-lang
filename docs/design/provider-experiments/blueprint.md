# SQLite copying provider authoring blueprint

This is a draft handoff under [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
It describes the selected copying API for the SQLite workstream, including
TEXT operations. It defines no current Ash semantics or production
foreign ABI. The copying and file-session programs remain under verification;
their final execution, observations, and integration checks remain pending.
The short Unicode TEXT entry passes the public driver and host example locally;
it supplements the required larger programs and is not a delivered API checkpoint.
Use [execution](execution.md) for recorded verification, not this blueprint as a
completion report. The selected candidate account is in
[semantics](semantics.md#selected-copying-values-and-literals-sqlite-workstream);
[contracts](contracts.md) records the foreign comparison obligations.

## Reproduce the boundary

The reusable source entry points live in the
[SQLite example package](examples/sqlite-copying/README.md). The
[copying test](../../../tests/provider_sqlite_copying.rs) and
[session test](../../../tests/provider_sqlite_sessions.rs) create owned temporary
directories, copy the source fixtures, and run the existing public driver. The
session supplies an isolated file path. It creates a table, executes `BEGIN`
and `COMMIT`, reuses an INSERT statement, collects rows through an imported
generic helper, closes, and reopens through a fresh connection. These are
ordinary SQL statements; no transaction resource or query shortcut is added.
Execution status belongs to [execution](execution.md).

The [SQLite control test](../../../tests/provider_sqlite_control.rs) supplies
capture/resume and owned-discard programs, also copied into the reusable package.
Resume continues the copied query with the original live owners. Owned discard
runs source cleanup using the outer connection, then finalizes the statement and
closes the connection without publishing the abandoned body or scope result.
Recorded normal-limit public-driver and host runs verify both programs after
the shared control import. The
[current SQLite checkpoint](execution.md#current-sqlite-checkpoint) identifies
the checked commits, fresh program runs and remaining delivery requirements.
The preserved code checkpoint is `b0fa2a5`. Its later shared native-preparation
and architecture-test imports do not rerun the original four SQLite programs;
their last recorded execution is at the value-context extension import `618842d`.

Receipts 136 and 150 record earlier fourteen-operation candidates with fourteen
passes and three typing failures. Receipt 154 traces those earlier inputs:
copying exhausts during value propagation and persistence during callable type
admission. These are historical boundaries, not fresh traces of the later
committed shared repairs. The
[earlier compiler evidence](execution.md#explicit-callable-metadata-presence)
retains their measurements. The shared repairs are committed and integrated;
the complete SQLite delivery still requires normal-limit acceptance of copying,
its NUL-input alternative and persistence.

The host authors two manifests with distinct registration identities:
`provider_manifest` for `@foreign.provider` and `sqlite_manifest` for
`@foreign.sqlite`. It installs them in `ForeignRegistrations`, obtains the exact
SQLite manifest, builds `sqlite_binding`, installs that binding in
`ForeignRuntime`, and calls `run_path_with_foreign_runtime` with those
registrations and runtime. See the
[manifest schema](../../../src/foreign.rs),
[generic runtime boundary](../../../src/foreign/runtime.rs), and
[executable SQLite binding](../../../foreign-adapter/src/ash_bindings.rs).

The reusable [host example](../../../foreign-adapter/examples/sqlite_session.rs)
accepts an ordinary Ash entry path. From the worktree root, run:

```sh
CARGO_BUILD_JOBS=1 cargo run --locked -p ash-foreign-adapter --example sqlite_session -- tests/fixtures/provider-experiments/sqlite-copying/text-entry.ash
```

The short
`tests/fixtures/provider-experiments/sqlite-copying/text-entry.ash` passes this
host locally. The larger `copying-entry.ash` still awaits the required common
compiler-cost repair and combined verification. The example prints the source value and type, native
status-call/data-query events, copied input/output byte sizes, and the retained
owner count. The runtime count reports quarantined owners; it alone does not
prove that source finishers ran. `FinishDispatched` records admitted binding
finish calls separately from raw native guard destruction, while actual native
calls and completion reports establish their respective outcomes. The host
supplies no SQL or session shortcut. The public session fixture
contains `__SQLITE_FILE__`; its host test substitutes an owned absolute path.
The packaged session example uses `"session.sqlite3"` and the package README
runs it from an owned temporary directory. The larger copying and
file-session examples remain pending while common resolves the measured compiler
work refusal. The [measurement account](execution.md#sqlite-compiler-work-measurement-receipt-109)
records earlier compiled inputs and exact refused charges. Use the current
SQLite checkpoint above for the latest verified inputs and outcomes.

Imports are passive. Importing the source SQLite module, `@foreign.sqlite`, or
`@builtin.bytes`/`@builtin.string` does not open a database or initialize SQLite.
The host binding authenticates the exact admitted manifest before dispatching
its operations. Source names and a matching user-authored signature cannot
create that registration, publish a native owner, or select a resource instance
from an address. The builtin bytes and string modules use their separate
compiler-owned module identities; their ordinary functions require no native
SQLite registration.

## Native build inputs

[build.rs](../../../foreign-adapter/build.rs) admits only
`x86_64-unknown-linux-gnu`. It compiles the
[C bridge](../../../foreign-adapter/sqlite_bridge.c) with `cc -std=c11`,
`-Werror=incompatible-pointer-types`, `-fPIC`, and `-Ivendor`, then archives the
object with `ar`. The bridge checks function-pointer signatures against the
[vendored upstream header](../../../foreign-adapter/vendor/sqlite3.h), pins
`SQLITE_VERSION_NUMBER` to `3046001`, and asserts 8-bit bytes, 32-bit C `int`,
64-bit `sqlite3_int64`, and 64-bit pointers. The BLOB and TEXT shims keep SQLite's
`SQLITE_TRANSIENT` destructor sentinel in C.

The adapter links the local shim statically and `libsqlite3.so.0` dynamically,
using the exact library filename. This is a Linux experiment setup; it is not
an ABI or portability claim for other targets. Rust parameter indices, column
indices, and byte lengths require checked conversions to the selected C types.
Ash integers retain their arbitrary range at the generic foreign boundary;
the SQLite binding checks the selected signed 64-bit integer boundary.

[environment.json](environment.json) records the initial runtime path, library
hash, SQLite version/source ID and compile options, header/archive hashes, and
toolchain. Those observations belong to the recorded checkout and date. They
must be refreshed when reproducing the final workstream. The initial distro
runtime reports SQLite 3.46.1 with an `alt1` source ID; it is not claimed to be
byte-identical to the pinned upstream header's source archive. Compile-time
signature and width checks and runtime metadata answer different questions.
The adapter calls `sqlite3_initialize` before open. It never calls
`sqlite3_shutdown` or substitutes `sqlite3_close_v2` for refused close.

## Author source values, effects, and handlers

The selected source values are builtin `Bytes` and `String`, both ordinary,
immutable, and independent of native owners. They replace the initial recursive
byte-list encoding. `@builtin.bytes` supplies empty bytes, checked byte append,
byte length, and equality. `@builtin.string` supplies UTF-8 encoding/decoding,
byte length, and equality. Decoding exposes an ordinary invalid-UTF-8 alternative.
Neither API introduces a native address, retained view, or completion operation.

The selected copying module uses these distinct positions:

| Position | Selected representation |
| --- | --- |
| Source SQL wrapper | `SqlText(String)` |
| File configuration | `File(String)`; `InMemory` remains nullary |
| Native diagnostic | `NativeFailure(Int, String)` |
| BLOB or SQL null | `BytesOrNull = NullBytes \| BlobBytes(Bytes)` |
| TEXT or SQL null | `TextOrNull = NullText \| TextValue(String)` |

SQL and paths reject embedded NUL before native use. Bound TEXT rejects NUL
because SQLite does not define general expression behavior for such values.
Returned TEXT uses the explicit native byte length and preserves embedded NUL
when those bytes form valid UTF-8. Malformed native UTF-8 produces a conversion
failure rather than replacement characters. Empty TEXT, empty BLOB, and SQL null
remain distinct. Bound BLOB/TEXT inputs are copied before the call returns;
column outputs become independent Ash storage before publication.

The source [SQLite module](../../../tests/fixtures/provider-experiments/sqlite-copying/sqlite.ash)
authors `Connection<R>` and `Statement<S, C>` resource definitions. Each
resource links its input, private state family, result envelope, provider
interface, exact effect interface, native interpretation, acquisition,
completion, and handlers. The selected source `StatementOps` and its provider methods expose
integer, bytes, and text binding/column access, stepping, reset, and clear
bindings. The handlers convert native results into source `Ok`, `Err`, `Row`,
`Done`, and `StepError` reports. They forward operations using the installed
state and selected effect identities, rather than choosing an instance from
the spelling or the operand's native address.

The native manifest preserves existing operation ordinals and appends TEXT:

| Effect | Ordinal | Operation |
| --- | --- | --- |
| Connection | 0 | `open` |
| Connection | 1 | `diagnostic` |
| Connection | 2 | `close` |
| Statement | 0 | `prepare` |
| Statement | 1 | `bind_int` |
| Statement | 2 | `step` |
| Statement | 3 | `column_int` |
| Statement | 4 | `finalize` |
| Statement | 5 | `bind_bytes` |
| Statement | 6 | `column_bytes` |
| Statement | 7 | `reset` |
| Statement | 8 | `clear_bindings` |
| Statement | 9 | `bind_text` |
| Statement | 10 | `column_text` |

This is fourteen operations across two effects. Native `prepare` takes the
underlying `String`; the source acquisition handler unwraps `SqlText`.
`bind_text` takes `(StatementState<S, C>, Int, TextOrNull)` and returns
`Result<Unit>`; `column_text` takes `(StatementState<S, C>, Int)` and returns
`Result<TextOrNull>`. TEXT introduces no retained argument or output-view
relationship.

## Keep outcomes and owner disposition separate

The source [provider module](../../../tests/fixtures/provider-experiments/sqlite-copying/provider.ash)
retains `NotAcquired(I)` or `Completed(T, Completion<E>)`. Completion distinguishes
`Closed`, `ConsumedError(E)`, and `RetainedError(E)`. The body outcome remains
available alongside its completion reports, including nested statement and
connection reports. The native `Acquire` and `Finish` data constructors alone
do not confer owner authority.

Failed open or unpublished preparation disposes any partial native owner under
an internal guard. Empty SQL reports no acquired statement. Finalize consumes
a statement even when it reports the preceding execution failure. Close can
refuse and leave the connection live. Keep the corresponding report and exact
owner; do not automatically retry, use a consumed pointer, or conceal refusal
through deferred close. Dependent statements complete before their connection.
The adapter's private Rust guards make native destruction safe; they do not
establish Ash scope checking or grant source ownership transport.

Reset restores the admitted execution protocol while preserving bindings. Clear
bindings replaces the bound values with null and remains a separate operation.
Column access requires a current row and a checked column index; binding
requires preparation/reset. The selected source failures must distinguish
invalid path, SQL, integer, index, byte/text input, column kind, and protocol
state where the admitted error family has corresponding alternatives. The
selected adapter leaves source `AllocationFailure` reserved and unused: actual
SQLite NOMEM remains `NativeFailure` with its native code when the complete
source report is admitted. Native diagnostic admission precedes the separate
cumulative Ash codec and envelope checks, which may still refuse publication.
Host copy work refusal and fallible payload reservation failure are terminal
internal outcomes. The adapter checks requested column kind before conversion
and column byte length before independent payload allocation. Diagnostic
copying has an explicit per-connection limit: it probes at most the admitted
payload plus one terminator byte before UTF-8 validation and reservation.
Oversize refusal records only the proven minimum length, not a fabricated
complete length. Diagnostic refusal preserves the exact native operation and
status in native error metadata. Status-returning calls also record their codes
in observations; standalone diagnostic queries record `errcode`/`errmsg` access
without recording the sampled numeric code. Native codes remain native codes
even when their report cannot be published. Deterministic injected reports stay
labelled separately. These diagnostic additions pass independent source review
and the focused native checks recorded in execution. Their combined integration
remains pending.

## Identify what each layer establishes

| Evidence category | Responsibility |
| --- | --- |
| Authored | Resource definitions, effect/provider method signatures, handler conversions, native manifest relationships, result envelopes, and foreign pre/postconditions. |
| Inferred | Exact requested effect instances and outward rows, captures, and dependencies carried by selected values and state operands. |
| Checked | Module/registration identity, owner-state relationships, handler coverage, Core facts and transformed Core, nonescaping dependent access, representation/range/protocol validation at the native boundary. |
| Observed | Actual SQLite calls and status codes, data-query calls, copied byte counts, report order, and persistence through close/reopen. |
| Assumed | Upstream API contracts, audited target widths and compatible runtime signatures, validity of SQLite-owned storage during synchronous copying, and host execution of native code. |

An observation does not prove an arbitrary foreign library's contract. A Rust
borrow-checker result does not prove Ash typing. The
[generic row helper](../../../tests/fixtures/provider-experiments/sqlite-copying/rows.ash)
uses exact statement/provider parameters and a caller-supplied row decoder;
its typed rows and provider constraints are authored explicitly. The remaining
compiler work refusal is a common compiler requirement; the ordinary
helper-module partition comparison also refuses at the unchanged limit before
native execution. It does not supply a cost repair.

## Verification and extension handoff

Run the following from the worktree root after the selected API and fixtures
have converged. These are reproduction commands, not claims that this draft has
passed them:

```sh
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test bytes_strings --test packed_core --test string_literals
CARGO_BUILD_JOBS=1 cargo test --locked -p ash-foreign-adapter --test sqlite_text
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test provider_sqlite_copying --test provider_sqlite_sessions
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test provider_sqlite_control
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test provider_sqlite_source
CARGO_BUILD_JOBS=1 cargo xtask verify
```

The session host test must compare the complete body/completion envelope,
actual calls and copied sizes, finalize-before-close order, and first
close-before-second-open order. Native helper tests separately cover TEXT/BLOB
copying, null and empty values, invalid native UTF-8, range/protocol checks,
consuming finalize, and refused close. Shared-value tests cover source literals,
passive builtin imports, ordinary callable application, independent malformed
Core rejection, and transform revalidation. Record actual commands, revision,
inputs, and outcomes in the experiment evidence before changing this draft's
pending status.

To extend the copying API, first add the operation's upstream contract and
positive/negative comparison cases. Update the manifest, source effect and
provider methods, handlers, executable dispatch, independent checks, and
observations together. Preserve existing ordinals and verify the exact manifest
before execution. Return semantic gaps to DN-0036's design work; a local adapter
choice does not settle language semantics.

This slice excludes floating point, retained inputs, scoped output views,
foreign callbacks, concurrency, asynchronous execution, dynamic loading, and
a universal ABI. A borrowed native view needs its own access interval,
invalidation and alias rules; a live owner alone is insufficient. Packed data
has work bounds and fallible payload reservations, while final shared `Arc`
publication retains the evaluator's existing host-termination allocation limit.
Native input `CString` construction, `Rc` guards, and observation storage also
retain host allocation assumptions. Independent byte-copy observations precede
source-value admission and do not count successful publications.
No actual native NOMEM result or full allocator accounting is claimed.
Successful reproduction remains experimental evidence. Product adoption still
requires the proposal/decision/task path and specification, correspondence,
review, and verification obligations described by DN-0036.
