# SQLite copying source examples

These modules are an experimental handoff under
[DN-0036](../../../DN-0036-foreign-library-and-memory-provider-experiments.md).
Their candidate types, literals, resources, and foreign operations do not define
current Ash semantics or a production foreign ABI. Verification and current
limitations belong to the [execution record](../../execution.md#current-checkpoint).

The modules are copied from the
[public source fixtures](../../../../../tests/fixtures/provider-experiments/sqlite-copying/).
`session-entry.ash` replaces the host-injected path with `"session.sqlite3"`.
`text-entry.ash` is the directly verified Unicode TEXT bind/copy example.
`copying-entry.ash` exercises copied Unicode text, arbitrary blobs, nulls, empty
values, and text containing NUL. `rows.ash` supplies an ordinary generic row
collector. `session-entry.ash` uses ordinary SQL for transactions, reuses an
INSERT statement, and reads the file through a fresh connection. The entries
preserve source lifecycle reports.

`control-resume.ash` captures the live statement and connection, resumes, and
copies a Unicode TEXT/BLOB row without reacquisition. `control-discard.ash`
discards that owned continuation: source cleanup queries the outer connection
before statement finalization and connection close. Both control entries pass
the public driver in common's fourteen-operation candidate receipt 136,
including their copied-value and finish-dispatch assertions. That receipt passes
fourteen public cases, including the original reset/clear program, and retains
three typing failures: copying, its NUL-input alternative and persistence.
The candidate remains uncommitted and unmerged; this worktree still awaits the
matching shared contract. The
[execution record](../../execution.md#typed-original-preparation-and-recovered-reset-program)
records the passing assertions and remaining delivery requirements.

Receipt 150 retains fourteen passes and the same three typing failures after
the shared callable-metadata repair. The fresh receipt 154 trace shows copying
completing its type universe and exhausting during value propagation;
persistence exhausts while admitting a callable type into its universe.
The [current compiler evidence](../../execution.md#explicit-callable-metadata-presence)
records these boundaries. Neither receipt establishes integrated verification.

The [host example](../../../../../foreign-adapter/examples/sqlite_session.rs)
registers the authenticated provider and SQLite manifests and executable binding.
It prints source values and types, native observations, copy sizes, and retained
owner counts. The commands below are reproduction inputs, not verification
claims. Required larger programs currently exhaust the compiler work budget
before native execution. The [measurement account](../../execution.md#sqlite-compiler-work-measurement-receipt-109)
distinguishes the Rust harness, compiled Ash inputs and charged analysis work.

From the repository root, copy the package into an owned temporary directory and
run the host with an absolute manifest path:

```sh
ash_repo=$(pwd -P)
sqlite_example_dir=$(mktemp -d)
cp "$ash_repo"/docs/design/provider-experiments/examples/sqlite-copying/*.ash "$sqlite_example_dir"/
(
    cd "$sqlite_example_dir" || exit
    CARGO_BUILD_JOBS=1 cargo run --locked --manifest-path "$ash_repo/Cargo.toml" -p ash-foreign-adapter --example sqlite_session -- "$sqlite_example_dir/text-entry.ash"
    CARGO_BUILD_JOBS=1 cargo run --locked --manifest-path "$ash_repo/Cargo.toml" -p ash-foreign-adapter --example sqlite_session -- "$sqlite_example_dir/copying-entry.ash"
    CARGO_BUILD_JOBS=1 cargo run --locked --manifest-path "$ash_repo/Cargo.toml" -p ash-foreign-adapter --example sqlite_session -- "$sqlite_example_dir/session-entry.ash"
    CARGO_BUILD_JOBS=1 cargo run --locked --manifest-path "$ash_repo/Cargo.toml" -p ash-foreign-adapter --example sqlite_session -- "$sqlite_example_dir/control-resume.ash"
    CARGO_BUILD_JOBS=1 cargo run --locked --manifest-path "$ash_repo/Cargo.toml" -p ash-foreign-adapter --example sqlite_session -- "$sqlite_example_dir/control-discard.ash"
)
```

The session database belongs to this temporary directory. Use a fresh directory
for another session run because the entry creates its table. Keep the directory
while reviewing its source, observations, and database, then remove it when done.

Check the value and observations together. A successful host exit means the
driver returned a value; that value can still contain a source `Err`,
`NotAcquired`, or completion error. Each program's required outcome is:

| Entry | Required source result and observations |
| --- | --- |
| `text-entry.ash` | Nested closed reports containing `Ok(TextValue("héllo 世界"))`; one open/prepare/finalize/close and 13 copied bytes in each direction. |
| `copying-entry.ash` | `CopySession` retains both closed reports and all eight copied fields, including empty values, nulls and embedded-NUL output; copied input sizes `[13, 2, 0, 0]` and output sizes `[13, 2, 0, 0, 11]`. |
| `session-entry.ash` | `SessionReports` retains every statement and connection report; both queries return the same three rows. Two opens/closes and six prepares/finalizes, with the first close before the second open. |
| `control-resume.ash` | Nested closed reports containing `Ok(CopiedRow(TextValue("héllo 世界"), BlobBytes([0, 255])))`; one open/prepare/finalize/close, two steps and output copy sizes `[13, 2]`. |
| `control-discard.ash` | `42`, with no abandoned body or scope result; one `errcode` and `errmsg` query before finalization, one finalize before close, no step or row copy. |

`FinishDispatched` must precede each corresponding native finalize/close call.
It distinguishes admitted binding finish from native guard destruction. The
native status code and source completion report establish separate outcomes;
dispatch alone does not establish successful completion. The printed retained
owner count is sampled before runtime destruction. These entries require zero
retained owners and no `close_v2` call, but those observations alone do not prove
that source finishers ran.

The public tests compare the required source results and native observations:

```sh
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_control
```

Run that verification after common support and the String/TEXT manifest are
integrated, in the agreed Cargo window. The required larger copying and file
session cases still refuse during typing in candidate receipt 150. Profile 109
and its traces describe earlier compiler inputs; receipt 154 records the fresh
failure boundaries. Keep the remaining failures in the execution record
until the complete programs pass. The commands
and expected outcomes above do not establish integrated verification.
