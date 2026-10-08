# SQLite copying source examples

These modules are an experimental handoff under
[DN-0036](../../../DN-0036-foreign-library-and-memory-provider-experiments.md).
Their candidate types, literals, resources, and foreign operations do not define
current Ash semantics or a production foreign ABI. Verification and current
limitations belong to the [execution record](../../execution.md#current-sqlite-checkpoint).

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
the public driver and actual host after the verified shared repair import.
All five packaged entries now pass through the actual host with their required
source results, native lifecycle and copy observations, and zero retained owners.
The original seventeen public copying/session/control cases pass in Common's
matched source evidence; SQLite reuses that evidence and freshly passes the
supplementary forwarding regression. The
[delivery record](../../sqlite-copying-delivery-2026-10-08/README.md) distinguishes
these checks and records the exact source comparison. Final integrated
whole-workspace verification remains pending.

The public driver uses calibrated, separate source, final-elaborator and Core
budgets. These larger allowances admit the programs; they do not establish a
compiler-cost reduction. The host prints actual charged units, nominal and hard
budgets, completion flags, assessments and optimization targets. An absent
measurement is unobserved. All fifteen measured phases in the five-entry run
complete within their nominal budgets, without an accepted deficit.

The [host example](../../../../../foreign-adapter/examples/sqlite_session.rs)
registers the authenticated provider and SQLite manifests and executable binding.
It prints source values and types, native observations, copy sizes, and retained
owner counts. The commands below are reproduction inputs, not verification
claims. The [measurement account](../../execution.md#sqlite-compiler-work-measurement-receipt-109)
distinguishes the Rust harness, compiled Ash inputs and charged analysis work.

From the repository root, build with Cargo in the workspace to select its
pinned Rust toolchain. Then run the binary against a private copy of the package:

```sh
(
    ash_repo=$(pwd -P)
    CARGO_BUILD_JOBS=1 cargo build --locked -p ash-foreign-adapter --example sqlite_session || exit
    sqlite_example_dir=$(mktemp -d) || exit
    cp "$ash_repo"/docs/design/provider-experiments/examples/sqlite-copying/*.ash "$sqlite_example_dir"/ || exit
    printf 'Example directory: %s\n' "$sqlite_example_dir"
    cd "$sqlite_example_dir" || exit
    sqlite_example_status=0
    for sqlite_entry in text-entry.ash copying-entry.ash session-entry.ash control-resume.ash control-discard.ash
    do
        "$ash_repo/target/debug/examples/sqlite_session" "$sqlite_example_dir/$sqlite_entry" || sqlite_example_status=1
    done
    exit "$sqlite_example_status"
)
```

The recipe runs every entry and returns a failing status if any entry fails.
The recorded five-entry run satisfies every required outcome below.

The session database belongs to the printed temporary directory. Use a fresh directory
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

Run these checks in the SQLite worktree in the agreed Cargo window. Keep the
original tests and complete native assertions. The selected API remains a
DN-0036 experiment; the [current execution record](../../execution.md#current-sqlite-checkpoint)
records the preserving imports, evidence reuse and pending final integration.
