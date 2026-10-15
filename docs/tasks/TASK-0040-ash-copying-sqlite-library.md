# TASK-0040: Ash copying SQLite library

- ID: `TASK-0040`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #6](https://github.com/dikini/ash-lang/issues/6)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Verified TASK-0036/TASK-0037 common source/Core/runtime/build and contrasting
TASK-0038 library evidence. The [retained minimal arena](https://github.com/dikini/ash-lang/issues/5)
supplies contrasting lifecycle evidence. Native SQLite binaries/headers are
explicit build/check inputs, not source authority.

## Work

1. Declare SQLite symbols, representations, constants, TRANSIENT sentinel, owners,
   diagnostic/column windows and consumption/retention assumptions entirely in Ash.
2. Implement source protocol state, diagnostics, partial acquisition, preparation
   tail offsets, bind/step/reset, scalar/text/blob copying and result conversions.
3. Complete source connection/statement resource lifecycle with finalization before
   close, distinct consumed/retained errors and blocked-dependent reports.
4. Migrate all retained realistic copying/persistence programs to the source library;
   remove handwritten manifests/adapters and runtime C shim from the product path.
5. Publish reproducible build/run/header-check guidance and tested limitations.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

### Approved larger-workload gas and diagnostic policy

The human approved source checking `100*S` over the canonical loaded closure,
including builtins, and initially native startup `11*B` over framed image plus
expected facts. The human subsequently approved preparation `51P`, final
elaboration `33S`, independent compiler Core `108S`, then startup `22B`; see [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
and the scoped observations in [DN-0050](../design/DN-0050-native-program-gas-estimates.md).
Paid census and all phase work share one cumulative meter, with no extra source
ten-percent margin, reset or spent-work top-up. Other compiler allowances and
all authority/depth/stack checks remain unchanged. Each new compiler phase pays
its own resident-source census inside its total; standalone Core defaults and
native startup are separate. Independent local review cleared the bounded
`51P` / `33S` / `108S` revision. Its normal full copying and simultaneous-statement
hosts and buffer/blob controls passed. Persistence completed all compiler and
preparation phases, then exhausted startup `11B`; the exact-host diagnostic
measured 6,072,727 units before evaluation with `B = 347,557`. The human approved
`22B` (7,646,254 units, +25.91% over that observation). Focused checks and independent local review cleared this startup-only revision.
The normal file-backed persistence host then passed without an override, retaining
the complete reports and close/reopen oracle. Its new startup use was not measured;
the earlier diagnostic total is not transferred as current headroom. No full-port
or criterion completion follows from these bounded reviews.

The approved SQLite source fallback maps ordinary bounded diagnostic-copy
refusal to diagnostic-unavailable while keeping the native status. It does not
catch resource exhaustion, truncate diagnostics, fabricate an empty message or
reverse ownership. This is an intentional change from the old Rust bound-failure
policy under [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md).
Focused source checking now passes full copying and persistence under `100S`;
the earlier final-elaboration persistence refusal was superseded by the complete
measurements and bounded compiler-policy revision above.
Predecessor product TEXT/empty/NULL/invalid-UTF8/embedded-NUL, TRANSIENT binding/copy
and retained control-resume hosts passed under the then-current `100S`/`24P`/`11B`.
The migrated product suite passed under `100S`/`33S`/`108S`/`51P`/`22B`. The human subsequently approved final elaboration `161S` after the unchanged compact generic regressions exhausted `33S`, then compiler Core `345S` after the deep generic witness exhausted `108S`; other policies and checks remain unchanged.
The new final coefficient follows complete diagnostic totals of 228,879 for the
96-level prerequisite chain (`S=1,781`) and 260,085 for the 256-argument nominal
application (`S=2,759`), including the paid census. The diagnostics stopped before
independent Core; normal full-pipeline and retaining evidence remain separate.
The complete deep-generic Core diagnostic measured 490,324 units with `S=1,781`,
including its paid census after all validator loans were reconciled. It stopped
before evaluation; the approved `345S` revision preserves fresh validation,
capture, all other budgets and existing checks.
The ordinary product diagnostic policy passes both independent-value and real
window fixtures, including one failed-open partial guard closed exactly once.
Actual copy work/storage refusal remains terminal in the mechanism tests.
These are focused results. Bounded policy/fallback independent review passed;
whole-port review, retaining verification and #6 acceptance remain separate.

### Integrated checkpoint and Source policy

The preserving [PR #28 repair](https://github.com/dikini/ash-lang/pull/28) passed
independent current-head and retained review. Issue #6 C4 was restored and the
issue closed at 6/6; milestone acceptance returned to 26/36. The reopening record
below describes the earlier correction and is historical.

The subsequent integrated checkpoint at `7997564` failed Source checking for an
unchanged 283-byte recursive-hook regression before evaluation. Its 26-case
`copying_sqlite_source` target passed, but the separate 34-case `sqlite_library`
target and later targets/rustdoc were not reached. A single finite Source-only
diagnostic measured 42,836 units including census, and stopped before linking,
Final/Core checking or evaluation. Independent review cleared that measurement
and accounting. Under the user's delegated autonomous judgment, the project lead
adopted Source `200S`; the 25% reserve minimum is 190. [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
governs this coefficient-only revision and [DN-0050](../design/DN-0050-native-program-gas-estimates.md)
records its fit and limitations. The hook bytes, activation depth and result-`13`
oracle remain unchanged. Focused normal execution, implementation review,
retention and a fresh integrated checkpoint are separate obligations; the
earlier failed checkpoints do not become passes.

## Verification

Run existing copying/persistence programs through generated hosts. Observe
Completed(Completed(Ok(42),Closed),Closed), independent text/blob copies, NULL
versus empty, repeated/imported/simultaneous identities, reset/rebind, partial
acquisition cleanup, finalization-before-close and retained-owner quarantine.
Exercise exact view/index/extent correspondence and pre-call invalid-access
rejection. Distinguish real SQLite errors from injected failures, and record
source/native-input pins and commands on integrated delivery.

## Discoveries

SQLite requires source private protocol data, input-relative tail extraction
and separate diagnostic/column windows. Source contracts must express these
roles; Rust adapters cannot remain the library policy.

A Connection diagnostic window exposed a declaration-category loss: lexical
window identities are allocated after generic declarations, so their identity
order need not follow source order. Body-free resource facts now retain exact
phase, family, binder and source-occurrence records. Admission matches the
complete acquire/finish/handler window inventory before checking each original
forest. The private image commits these records in canonical expected facts;
missing, duplicate, donor, wrong-phase/family/span and prefix mutations refuse.
The category binds no dormant sibling identity and grants no native access.

Real product diagnostic operations copy SQLite's message and preserve native
status, including diagnostic-unavailable after bounded-copy refusal. Counted
invalid-SQL preparation cases preserve status 1, create no statement owner and
close the parent once. These clients use the exact associated operation. An
ordinary callable carrying controlled native State in its effect row remains
refused; the wider callable-wrapper boundary is unchanged. The connected cases
are in [sqlite_library.rs](../../tests/sqlite_library.rs); this evidence does not
substitute for retaining verification or independent review of the full port.

The actual five-method imported SQLite workload exposed native preparation and
startup demand beyond the previous fixed allowance. The accepted
[AD-0013 gas policy](../decisions/AD-0013-generated-native-bridges-and-program-builds.md#native-preparation-and-startup-gas)
uses paid resident source/node sizing for preparation and framed image/fact bytes
for startup. Focused normal product, buffer and TRANSIENT/blob hosts passed;
source-compiler budgets and authority/depth/stack checks remain unchanged.
[DN-0050](../design/DN-0050-native-program-gas-estimates.md) retains calibration
errors, amplification refusal and current scope. This predecessor evidence does not substitute for the later migrated product
suite or whole-port review of the SQLite foundations.

Larger column handlers exposed repeated original byte-call mapping in source
capture. Each graph now lazily builds one paid ordered relation index; queries
retain their exact call shape, canonical module and role checks. The index
belongs to that immutable graph invocation and transfers no checking authority.
Window-reply capture had a separate repeated graph/forest walk. It now retains
raw original request/window coordinates once per graph, preserving the first
query's mapping/error order and each query's codec, conflict and marker checks.
Focused identity, retry, control, copy and window/key refusals pass. The larger
text and TRANSIENT hosts exhausted their startup allowance at that revision;
they later passed under the approved `11B` policy. Predecessor observations
retain their original source and accounting scope.

Window resolution and mixed expression dispatch also increased fixed compiler
frames on ordinary cleanup paths. Window-only resolver temporaries and source
expression visits now have separate frames from ordinary work completion.
The existing 256 KiB cleanup success and partial-failure witness remains intact;
compiler work, syntax depth and stack allowances are unchanged.
The owning capture regression also exposed fixed frame growth when an ordinary
unit node entered lowering that reserved source-resource temporaries. Those
source-resource phase temporaries now live in a separate non-inlined function;
the original lowering/check/charge order is unchanged. The existing 64 KiB deep
capture success/refusal/retry test passes without increasing its stack. A second
64 KiB partial-initialization witness exposed compound Type/Row walker temporaries
on a scalar metadata root. The complete iterative walker and Forall shielding
now use a separate non-inlined function; scalar dispatch retains its original
charges. That success/refusal/retry witness also passes at its unchanged stack.

The larger persistence client also exposed repeated non-strict zonking of
already closed ordinary Core metadata. A builder-local marker now retains only
fully inference-free pure-node metadata after a paid complete check. Mutable
rows, rewrites, cleanup completion and rollback invalidate the affected marks;
dialect operations remain conservative. Generic rewrites, strict finalization
and independent Core checks still run in full. Focused closure, invalidation,
budget and connected capture/stack tests pass, but the unchanged persistence
client still exhausted the historical source allowance at that revision. The
later approved policies admit complete source, final and Core checking and
preparation, followed by normal file-backed persistence under `22B`.

Source lifecycle copying now uses the caller's actual cumulative work ledger
for both forest construction and direct clause/argument work. The earlier
temporary remaining-credit meter omitted in-flight failed copying work from
the outer diagnostic. Exact, one-short, prefix and failure tests verify the
corrected accounting and restoration of the builder's prior meter. This
correction changes neither compiler allowances nor the remaining persistence
verification obligation.
After these repairs, a separately authorized finite diagnostic completed the
unchanged persistence fixture's source phase at 2,946,584 charged units,
including entry and provenance checks. Its then-normal 1,369,702-unit allowance
refused the workload. That diagnostic stopped before later phases and did not
itself change policy. Under the subsequently approved `100S` policy, current
source checking completed at 2,950,458 of 4,320,900, then the historical final
elaboration allowance refused at 432,537. The later complete measurements and
approved policies above supersede that refusal; normal persistence now passes.

The retained resume workload exposed a separate private-image registry error.
Original lifecycle forests were reconstructed against the combined client
registry instead of their defining checker view. Images now record exact fact
categories, opaque exposure and defining module/source pairs in canonical
expectations. Original forests rebuild their own registry and retain fresh
validation; each template owns its checking session, and caller cell methods
are not injected into its original catalog. Main keeps its full registry and
lexical method catalog. All 15 owning image checks pass, including visibility,
client-parameter, prefix, budget, retry, cell, dependency and control cases.
At that revision the saved generated resume host completed source, Core and
preparation, then exhausted the historical startup allowance before capture,
binding or native evaluation. A separate finite diagnostic completed final native
admission at 1,697,083 charged units and stopped before evaluation. The normal
allowance was 1,449,154. The later normal retained control-resume host passes
under the approved `11B` policy; the predecessor diagnostic total does not
transfer across later implementation changes.

A connection-only client exposed unused statement-window binders in its
defining registry. The supported image inventory now accounts for variables
from the exact retained original view, including those unused by the selected
forest. Canonical facts, header associations and fresh original/main checks
remain required; unrelated main variables still refuse. The normal generated
connection host passes. Counted product-source variants also verify real open
success, partial-open cleanup and NUL rejection before initialization. A separate
initialization-failure injection is labelled as such. The retained initializer
with a cell executes once, and hiding the report still closes the owner once.
These current checks do not transfer the saved resume diagnostic's exact cost
across the later paid inventory change.

The retained repeated-session client now runs through a generated host with
ordinary generic statement helpers. Counted real SQLite calls show one prepare,
finalize and connection close per session, with both nested result reports
preserved. At that revision, the simultaneous-statement client passed source, final
elaboration and independent Core, then exhausted preparation before host build;
it now passes through normal native execution under the approved policies. Their effect and provider actuals contain the declared statement
access handle, not native State; no privileged callable exception is needed.

At that revision, the full copying client also passed source, final elaboration
and independent Core under `100S`, then exhausted preparation at the final host-output
allocation and copy. The observed next charge is a lower bound on complete demand. At that revision neither
this client nor the simultaneous-statement client had native parity. Complete
diagnostics later measured copying preparation at 1,148,886 and simultaneous
preparation at 1,059,089. Persistence completed final elaboration and independent
Core at 1,165,115 and 3,852,068, then preparation at 2,071,102. These finite
measurements stopped before host compilation or native calls and motivated the
approved `51P` / `33S` / `108S` policy; they are not normal native passes.

The SQL-tail classifier follows the retained Rust library's
`u8::is_ascii_whitespace` policy: bytes 9, 10, 12, 13 and 32 are whitespace;
vertical tab (11) is not. A pure source/Core test checks that correspondence.
A separate ordinary source probe checks tail traversal over copied bytes,
including empty, negative/end/out-of-range offsets, NUL and multibyte boundaries,
without installing a native runtime.

### Source library and caller migration

The product library is [sqlite.ash](../../libraries/sqlite.ash). Source fixtures
now import it explicitly and name both statement and connection identities. The
ported copying, repeated/simultaneous, persistence, generic forwarding and control
clients use generated typed bridges with explicit SQLite inputs. Source-free real
hosts also cover protocol/storage/index refusals, copied reset/clear values,
empty/multiple/NUL SQL, genuine syntax and range errors, and a genuine UNIQUE
constraint error whose consumed finalize report remains distinct from its body.
Test-only static wrappers observe calls; only labelled initialization failure is
injected. No old adapter event is reported as a generated-host observation.

The connection provider/effect uses the owner identity `C`, while its original
`borrow` operation retains the exact native State signature. This permits ordinary
diagnostic cleanup without placing State in its callable effect row. The connected
owned-discard host returns the retained `42` oracle, copies the diagnostic before
finalization/close and performs no abandoned step. Explicit/inferred State-returning
callables still refuse, and an ordinary native wrapper refuses outside its exact
checked lifecycle phase. This is a library API adaptation, not new privilege.

The compiler's public `foreign::sqlite_manifest` is removed. Historical schema
and adapter/shim code live in the experiment-only `foreign-adapter` crate; generic
compiler unit tests can retain that schema under `cfg(test)`. Generated product
hosts have no adapter dependency or `ash_sqlite_*` shim. Historical Rust/C programs
remain comparison evidence rather than product authority. The [library guide](../../libraries/README.md#sqlite-migration)
records API migration and build inputs. Whole-port independent review, retaining
verification and acceptance remain pending.

The generated image still refuses integer literals beyond signed 64-bit range.
The oversized-column refusal client constructs its identical mathematical integer
with ordinary multiplication/addition instead of widening that unrelated image
profile. The foreign range refusal and pre-call ordering remain checked.

### Whole-port review and blocked-owner repair

The migrated product suite passes all 34 cases, including file-backed persistence,
copied text/blob/NULL/empty, protocol and error handling, repeated/simultaneous
identities and normal/resume/discard completion. This is focused candidate
verification, not a fresh workspace gate or retained acceptance.

Whole-port review found that ordinary scalar Borrow checked consumption but not
blocked-owner quarantine. Independent Core flow and the selected runtime boundary
now both reject blocked access. A source discriminator rejects the blocked
branch while retaining permitted completing diagnostics and live-enclosing access.
A separate private runtime-state injection proves zero Borrow callbacks despite a
retained teardown address, exactly-once disposal and fresh legal retry. It is not
real C evidence. A legal dynamic-key generated SQLite pair separately proves that
a mismatched key returns ordinary conversion refusal before the extent callback;
the matching key queries once, and both executions finalize/close once.

Whole-port review, final affected checks, publication, retention and criterion
acceptance remain pending. The normative specification now records the implemented
accepted input/output/access/window and bounded independent byte/string profile;
privileged callable wrappers, source `given`, retained input pointers and general
storage APIs remain excluded.

## Deviations

The human approved diagnostic-unavailable fallback for an ordinary bounded-copy
conversion refusal while retaining the original native status. This intentionally
changes the old Rust bound-failure policy; actual work/storage exhaustion stays
terminal. [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md) records
that delta. Return any further semantic gap to the governing proposal rather
than resolving it locally; keep excluded features outside this task.

## Post-merge PR #27 review correction

The [post-merge review](https://github.com/dikini/ash-lang/pull/27#pullrequestreview-5533587489)
found two defects in retaining merge `3ab09d6`:

- [P1](https://github.com/dikini/ash-lang/pull/27#discussion_r4283337255):
  implicit finish capture followed acquisition data instead of replacement
  payloads. A closure could retain the closing owner through completion, or
  remain in private data when finish discarded that data. Independent callbacks
  remain legal; an explicit `data_of` read already rejected the unsafe capture.
- [P2](https://github.com/dikini/ash-lang/pull/27#discussion_r4283337268):
  an acquired handler's Current/Enclosing scalar Borrow checked the emptied
  pre-acquisition receipt vector. The public generated host refused before the
  valid query callback, while releasing the child and parent.

Author runs 690 and 688 reproduced these defects before production repairs.
The corrective implementation gives finish its current payload while preserving
immutable acquisition-time handler aliases, and includes private payloads in
focused ownership checks. Acquired borrows select exact guard-retained lineage;
pre-acquisition receipts and ordinary versus finishing liveness checks remain
separate. The existing semantic rules and approved budgets do not change.

Run 694 passes both reported regressions, including the real native query and
exact child/parent cleanup. Run 693 checks late payload captures, imported graphs,
distinct creations, paid exact/short/prefix admission and fresh retries. The
independent-callback native control returns `(7, 42)`: the handler returns its
acquisition-time callback to the ordinary body, while finish returns the latest
replacement callback. Calling a local private-data callback inside the handler
is outside the bounded lifecycle carrier; that earlier fixture failed Source
owner-flow checking before Core or native execution. Correcting the fixture adds
no lifecycle-call permission. Runs 697 and 698 pass the native control and all 68
affected owner tests. Broader SQLite checks also exposed an existing test-C
composition error: specialized statement and bind-refusal wrappers collided with
the shared trace, and their column-scalar declarations used different C types.
Those local fixtures now use distinct wrapper names and the shared `int64_t`
type, preserving the native forwarding, invalid-tail injection, zero-bind-entry
oracle and release assertions. Focused author verification does not replace
independent repair review, retained verification or original acceptance. Original
issue #6 C4 is reopened; the other five checks remain, and acceptance is 25/36.
Restoration requires the preserving repair delivery and independent retained
verification. The named checkpoint and Main advancement remain held.
