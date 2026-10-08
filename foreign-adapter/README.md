# Ash foreign adapter experiment

`ash-foreign-adapter` supplies the native SQLite copying baseline and physical
arena backing for the bounded
[provider experiment](../docs/design/provider-experiments/plan.md). It is a
member of Ash's root Cargo workspace and uses the root lockfile. Its safe Rust
API and tests describe native behavior, not Ash language semantics or verified
source contracts.

The adapter opens connections, prepares one SQL statement, binds integers,
copies BLOB and TEXT inputs with `SQLITE_TRANSIENT`, binds null, steps, copies
admitted columns, resets, clears bindings, finalizes, and closes. Integers cross the
boundary as `sqlite3_int64`; the evaluator must check Ash integer range before
calling the adapter. Returned columns distinguish integers, empty/nonempty
BLOBs, valid UTF-8 TEXT, and SQL null. Floating-point columns remain outside the
selected profile. SQL, paths, and bound TEXT reject embedded NUL; returned TEXT
uses its explicit byte length and preserves embedded NUL. Malformed UTF-8 returns
a conversion error without replacement. Empty TEXT and BLOB remain distinct
from null. Non-whitespace input after the first SQL statement is rejected, including a
trailing SQL comment. Empty SQL returns no statement.

`Connection::diagnostic(&self)` returns a copied `Diagnostic { code, message }`
for the live connection's current status, including `SQLITE_OK`. This datum
does not assert that an operation failed; `NativeError` continues to describe
an actual failed operation. A closed owner returns `Error::Protocol` before
any native query. Reading the diagnostic neither consumes the connection nor
changes the statement protocol, and its copied message remains usable after
later native calls and connection completion.

`open_observed_with_diagnostic_limit` admits an explicit diagnostic payload bound.
The ordinary native API retains its unlimited policy; the selected Ash binding
supplies the existing type-work bound. Copying probes at most that payload plus
one terminator byte, then checks UTF-8 and reserves independent storage. Refusal
reports a proven minimum length rather than truncating or scanning the complete
oversized message. `Error::DiagnosticCopyRefused` retains the exact operation,
native status and separate work/storage/encoding cause. Finalization remains
consuming and refused close remains retaining even if its report cannot be
copied. The binding maps known copy work/storage refusal to terminal generic
failure rather than a source allocation error. Native NOMEM remains a native
status when the complete source report is admitted; actual NOMEM is not claimed
observed. Native diagnostic admission precedes the separate cumulative Ash codec
and envelope checks, which may still refuse publication.

## Native inputs

The experiment currently supports `x86_64-unknown-linux-gnu` only. The build
requires `cc`, `ar`, and the installed `libsqlite3.so.0` soname. It does not
require a development package or pkg-config and makes no global setup changes.

The vendored `sqlite3.h` comes from the official
[SQLite 3.46.1 amalgamation](https://www.sqlite.org/2024/sqlite-amalgamation-3460100.zip).
The archive SHA-256 is
`77823cb110929c2bcb0f5d48e4833b5c59a8a6e40cdea3936b99e199dbbe5784`;
the header SHA-256 is
`89b62c671c5964e137409ce034941b7b05a3af2c9875aba41f47f9483d0c2515`.
The included upstream header retains SQLite's public-domain notice.

`build.rs` compiles the small C shim against that header. C assignments check
the selected function signatures; static assertions check the header version,
8-bit bytes, 32-bit C `int`, 64-bit `sqlite3_int64`, and 64-bit pointers. The C
shim supplies the `SQLITE_TRANSIENT` sentinel without manufacturing an invalid
Rust function pointer. Rust links the shim statically and the installed SQLite
soname dynamically. No SQLite source implementation is bundled.

[environment.json](../docs/design/provider-experiments/environment.json)
records the runtime library checksum, reported source identifier, compile
options, compiler configuration, ABI observations, and checks. The selected
distribution runtime reports 3.46.1 with an `alt1` source identifier; it is not
claimed identical to official upstream source. The native smoke test checks
the actual linked runtime and `SELECT ?1` with integer `42`. The recorded
inputs establish only this target's tested native baseline.

## Ownership and unsafe audit

Connections and statements are unique public Rust owners. Native pointers are
private and neither owner is cloneable. Statements keep an internal `Rc`
connection guard so the evaluator can store owned Rust values without a
self-referential borrow. That guard permits safe native cleanup when Rust
owners drop out of order. It does not authorize extending an Ash resource
scope, escaping a source state token, or transporting an arena owner. Ash
checking and the evaluator own those obligations. The adapter API is
single-threaded and exposes no callbacks, native views, retained input, or
raw-pointer access.

Open guards any returned partial connection before publishing it. Preparation
guards any returned statement before reporting failure, checking unused SQL,
or publishing it. Diagnostics are copied while the connection is live. Native
initialization is host-wide and idempotent; the adapter never shuts down shared
SQLite state.

The pinned header and [SQLite error API](https://www.sqlite.org/c3ref/errcode.html)
identify `sqlite3_errcode` and `sqlite3_errmsg` as error-code-preserving queries.
The adapter validates the live pointer, samples the code, and copies the message
without an intervening SQLite call. SQLite owns the original message buffer and
may overwrite or deallocate it on later calls. This uses the existing ABI;
the single-threaded owners expose no competing native access during the copy.

`Statement::finalize(self)` consumes the statement even when SQLite reports its
previous execution error. `Connection::close(&mut self)` calls actual
`sqlite3_close`: a refusal retains the callable connection. It never substitutes
`sqlite3_close_v2`. Drop finalizes an unfinished statement once; the last
internal connection guard then attempts close. Explicit completion returns its
report, while Drop records its native outcome through the observation set.
`FinishDispatched` separately records admitted executable-binding finish calls;
native guard destruction emits no such event. Dispatch alone does not prove
successful native completion or source report publication.

Binding requires a prepared/reset statement. Stepping a completed or failed
statement requires explicit reset; the wrapper does not rely on SQLite's
automatic reset behavior. Column access admits row state and C-integer indices
before native queries. It uses `column_count` to check bounds before column
type/value access. Integer, TEXT and BLOB extraction checks the requested
storage kind before conversion, acquiring the column's value pointer/length, or
copying. Bounded column copying checks the native byte length before fallible
reservation. A null BLOB pointer is accepted as empty only after checking
native exhaustion and zero length. Output bytes copy before any invalidating
operation; the adapter API never exposes a native view.

Fallible output and diagnostic payload reservations do not contain all host
allocation failures. Input `CString` construction, `Rc` guards, observation
storage and snapshots, and final shared `Arc` publication retain existing host
termination assumptions. Copy counters measure independent byte copying; a
copied invalid UTF-8 payload can still be rejected before source publication.

Every unsafe block identifies its pointer, lifetime, state, or buffer
invariant. Input lengths and indices use checked C integer conversions. The Ash
binding preserves arbitrary source integers until this checked boundary. A
representable positive parameter index outside the prepared statement is an
actual SQLite `SQLITE_RANGE` failure; it is not rejected by a parameter-count
shortcut. The pinned header checks the C ABI declarations, but neither
signatures nor passing tests prove arbitrary foreign implementations obey
SQLite's documented contract.

## Physical arena backing

The [arena module](src/arena.rs) owns one fixed-capacity, 64-byte-aligned payload
block and a bounded object-record table. Publication checks size, alignment,
padding and record capacity before initialization. Failed or panicking Rust
initialization rolls back the unpublished reservation; existing objects retain
their bytes and identities. Published objects never move and remain immutable.
Zero-sized objects still consume distinct record slots.

Allocation keys contain non-owning owner/object identities. Reading checks
the owner, published object, expected layout tag and record extent before
returning a Rust slice borrowed from the arena. Keys and layout tags do not
authenticate an Ash type, resource lifetime or access capability. The initializer
is a Rust host callback, not a callback into Ash or a foreign callback interface.

Publication commits when the Rust initializer returns success. A later Ash
bridge must prepare its result and authority before that point; the native API
offers no post-publication rollback. Checked Ash layouts, encoding, dependencies
and source completion remain unimplemented. Native identity exhaustion also
needs the selected terminal bridge treatment rather than a source allocation
refusal.

Logical counters include padding and published object slots. Physical counters
report requested backing and table layouts plus inline owner metadata; they do
not measure allocator overhead, codec scratch space or resident memory. Private
tests inject partial allocation failures and exhausted identities. Actual host
allocation exhaustion was not observed.

## Observations and checks

`Observations` records actual status-returning native calls and native data
queries separately. It also records successful copied TEXT/BLOB input/output bytes.
Diagnostic reads record `errcode` and `errmsg` as queries, including an OK status.
It does not measure SQLite's internal allocation events, peak memory, diagnostic
copies, or Rust metadata costs. Native `NOMEM` and BLOB conversion allocation
failure were not observed. Private test-only publication and native-result
injection are labeled separately from actual native failure. Suspect null BLOB
and zero byte-length results check `sqlite3_errcode` before another SQLite API;
injected result tests exercise that classification without forcing exhaustion.

Run from the root workspace:

```bash
CARGO_BUILD_JOBS=1 cargo test --locked -p ash-foreign-adapter
CARGO_BUILD_JOBS=1 cargo clippy --locked -p ash-foreign-adapter --all-targets --no-deps -- -D warnings
CARGO_BUILD_JOBS=1 RUSTDOCFLAGS="-D warnings" cargo doc --locked -p ash-foreign-adapter --no-deps
```

The initial SQLite recheck after shared integration passes 59 tests: forty unit
cases, nine physical-arena integration cases and ten copying-TEXT cases. Scoped
Clippy and formatting pass at that checkpoint. The later finish-observer recheck
passes the short public TEXT program and adapter rustdoc with warnings denied.
A fresh complete adapter run with the observer passes all sixty cases: forty
unit cases, nine arena cases, and eleven copying-TEXT cases, with no skips. The observer also passes scoped all-target Clippy
with warnings denied; inherited dependency warnings remain visible. The
[native recheck](../docs/design/provider-experiments/execution.md#complete-native-recheck-with-the-finish-observer)
records this checkpoint; the
[source-program comparison](../docs/design/provider-experiments/execution.md#sqlite-import-and-diagnostic-source-reductions-2026-10-05)
records the remaining compiler work failures. The SQLite
tests cover the native portions of S-01 through S-05: independent
connections and activations, partial failed open, malformed and empty SQL,
copying bytes, empty/null distinctions, row protocol checks, integer bounds,
reset/clear behavior, consumed finalization errors, retained BUSY refusal,
statement-before-connection cleanup, and temporary-file persistence. Temporary
fixtures exclusively own their directories. Two publication tests and two
result-classification tests use explicit injection after actual native success.
Diagnostic tests cover an actual preparation failure, successful status, copies
after later native calls and close, preservation of live owners, and closed-owner
rejection without native queries. Bounded diagnostic tests cover oversized
report refusal before decoding/reservation, exact Unicode and empty admission,
partial acquisition cleanup, retained close refusal and consumed finalization.
The public TEXT tests cover Unicode, embedded NUL output, invalid UTF-8, distinct
null/empty values, copy limits, checked input/protocol errors and persistence.

The arena tests cover actual backing allocation, alignment and capacity,
non-owning keys, failed initialization rollback, stable publication and cleanup.
They include seven private invariant/fault tests and nine
[public API tests](tests/arena.rs). They do not establish an Ash-source M case.

These tests supplement the required source-to-Core-to-native suites. They do
not establish source rejection, public provider authenticity, imported helper
contracts, captured control, arena access, or retained storage behavior. Those
remain in the existing compiler/runtime and later experiment slices.

## Ordinary Ash host example

The [Ash fixtures](../tests/fixtures/provider-experiments/sqlite-copying/) and
[public-driver harness](../tests/support/sqlite_copying.rs) supply the source
library, authenticated manifests and executable binding. SQLite also supplies a
[blueprint](../docs/design/provider-experiments/blueprint.md) and
[reusable source package](../docs/design/provider-experiments/examples/sqlite-copying/README.md). The short Unicode
TEXT entry executes through the host example:

```sh
CARGO_BUILD_JOBS=1 cargo run --locked -p ash-foreign-adapter --example sqlite_session -- tests/fixtures/provider-experiments/sqlite-copying/text-entry.ash
```

It returns complete closed statement/connection reports, observes thirteen
copied input and output bytes, and leaves no retained native owner. All five
[packaged entries](../docs/design/provider-experiments/examples/sqlite-copying/README.md)
now pass through this host, including full copying, file persistence/reopen,
capture/resume and owned discard. The
[delivery evidence](../docs/design/provider-experiments/sqlite-copying-delivery-2026-10-08/README.md)
records fresh host and forwarding checks, and the matched reuse of Common's
seventeen original public tests. Earlier sixty-case adapter execution evidence
remains historical. Strict affected adapter and public-test Clippy passes with
warnings denied.

The host prints the public driver's measured source, final-elaborator and Core
work on success and partial failure. It distinguishes nominal and hard phase
budgets, completion, assessments and optimization targets; absent phases are
unobserved. The selected programs fit calibrated public-driver allowances.
This is an admission-policy change, not evidence that their compiler work was
reduced. Standalone/explicit budgets and validation remain unchanged. Final
integrated whole-workspace verification remains pending, and this bounded
DN-0036 delivery does not define current Ash semantics.
