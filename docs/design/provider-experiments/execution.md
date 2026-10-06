# Provider experiment execution record

> Active experiment tracking for [the plan](plan.md), governed by
> [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> Candidate P-1 is specified in [semantics](semantics.md#selected-first-execution-contract).
> This record assigns work and evidence. It has no independent semantic or
> architectural authority and leaves the current tree when this work finishes.

## SQLite copying workstream (2026-10-05)

Authorized implementation starts from integration commit `53db4eb` in
`.worktree/sqlite-provider`, branch `codex/sqlite-provider`. Completed batches
merge with both histories into `codex/provider-experiments`; `main` is excluded.
Unrelated integration and root drafts remain outside this workstream.

The shared capability batch connects distinct packed `Bytes` and UTF-8 `String`,
string literals, compiler-owned pure callables, independent Core validation,
transforms, evaluation and observation. The frontend owns literal admission;
Core/runtime owns constants and intrinsic execution; the coordinator owns shared
types, builtin module authentication, checking and convergence. Native TEXT
support is independent adapter work until the shared batch is delivered.

The shared batch also removes the experiment's integer-list byte family: its
Bytes import conflicts with the built-in type spelling, demonstrated by nine
old SQLite source failures in the first connected run. Codec and fixtures must
migrate together before shared integration. SQL/path migration follows in the
copying batch, which admits
String SQL/paths/diagnostics, and adds TEXT/BLOB/null operations and statement
reuse. The session batch exercises imported helpers, multiple rows, ordinary
transaction SQL, completion and file persistence. The handoff batch records
reusable modules, embedding instructions, observed evidence and adoption gates.

One coordinator runs heavy Cargo checks with one build job. Each batch requires
public-program evidence, required negative Core/source cases, independent
contract/ownership review, unsigned commit and merge, then integrated checks.
Receipts and limits are recorded here as those gates complete. This execution
record has no language authority; candidate contracts belong in `semantics.md`.

### Shared copying-value batch verification

The implementation checkpoint passes `CARGO_BUILD_JOBS=1 cargo test --locked
-p ash --lib`: 1,537 cases pass, and the inherited advanced callback case remains
ignored. `CARGO_BUILD_JOBS=1 cargo check --locked -p ash --all-targets` passes.
The selected public command passes 203 cases across architecture, Bytes/String,
Core validation, foreign admission, polymorphism, SQLite, resource scope and
literal suites. The ordinary `examples/bytes-string.ash` entry returns
`(true, 14, 14) : (Bool, Int, Int)` through the CLI.

Independent reviews cover canonical intrinsic signatures, immutable sharing,
transformed Core, native ownership and cumulative codec work. They found and
verified repairs for packed-payload admission and repeated large-integer copy
amplification. Fresh library checks also found two migration regressions: a
Core test helper assumed a nominal Bytes family, and invalid built-in operands
to `state_of` reported an internal error. The helper now selects the packed
type; the checker reports the existing argument diagnostic while preserving
resource failures and pending-evidence rollback. No ownership assertion changed.

Formatting, changed relative links and candidate authority labels pass review.
The host-allocation assumption remains explicit in candidate semantics. Existing
compiler dead-code warnings remain visible. Unsigned integration and its checks
are recorded by the coordinating task after this implementation checkpoint.

## Shared capture lookup handoff (2026-10-05)

The SQLite workstream transferred unsigned commit
`0ac9c747e0e266b35f094a67ac2b64e62d88b83c`, based on verified original
integration `8adf4b2`. Its only implementation file is
`src/core/capture/value.rs`. Common owns shared compiler, Core, capture,
provider checking and generic runtime changes after this handoff. SQLite owns
its native adapter, SQLite manifest contract, Ash library, fixtures, examples
and documentation. Cargo and integration windows are serial and explicit.

The exact-port and canonical requirement/method indices preserve all original
matching positions, duplicates, order, specialized destination contexts and
lexical fallback. Construction and lookups remain fallible and cumulatively
charged. The default work limit remains 327680. Independent identity, ownership
and accounting review passes; this is a lookup repair, not new effect or
resource semantics.

Common merge `41410a9a423dade8b53237c9b06b8ac2d43ee309` preserves both
histories. Its fresh all-targets check and 1,539 library cases pass; the inherited
advanced callback is still ignored in this isolated baseline. Common's 56
uncommitted Batch 3 files remain separately pinned and stashed. SQLite's 45
pending files remain archived, pinned and uncommitted. No pending SQLite API or
common control source is part of the isolated lookup delivery.

The supplied realistic SQLite evidence passes 127 capture cases, three of six
copying cases and an earlier six of seven session cases. Larger copying/reuse
and persistence programs still refuse at the unchanged work limit. The next
measured refusal is watcher membership work, not a completed copying program.
The pending String/TEXT manifest and adapter snapshot is reproduction evidence;
it is not a delivered native API. Generic codec failure classification also
remains a separate reviewed snapshot with phase-precision repairs required.

Fresh connected verification passes all 193 cases across eleven selected
binaries, including all forty-one architecture checks, independent Core
validation, owner rows, resource modules/runtime and the ten SQLite and four
arena lifecycle cases. Formatting and changed-document review pass. Inherited
compiler dead-code warnings remain visible in this isolated baseline. Original
unsigned integration and its fresh checks are recorded under
`~/.codex/ash-provider-evidence/common-resource-support-2026-10-04/shared-capture-lookup-29/`.
Batch 3 resumes after this separate shared checkpoint. Its required control,
validation and cost repairs must pass before its delivery integrates; no
unchanged-limit or complete-program claim is inferred from the lookup repair.

## Current checkpoint

Latest integrated common code checkpoint is `5991e3d882b4a161c137fb826e73e79c149d550a`,
merging common commit `183e9d506f0e3a41833f29b3e614616345169074` with an unsigned
merge preserving both histories. Receipt 186 passes the complete unfiltered
`CARGO_BUILD_JOBS=1 cargo xtask verify` in the original worktree. All four
original common deliveries and this separate preparation-cost delivery are
complete. The ten shared source/regression files and tracking are merged into
`codex/provider-experiments`; `main` is unchanged.

The pending String/TEXT manifest, adapter, source library and larger programs
remain preserved SQLite-owned work. Their seventeen-case evidence remains
fourteen passes and three typing-resource refusals in copied Unicode/BLOB/null
results, bound NUL input and transaction/reopen persistence. Partial work
reductions establish no full-program fit. Work and depth limits remain unchanged.
The next canonical-preparation measurement is a proposal, not delivered code or
proof that a larger typing quota is necessary.
The following Batch 0–2 and dated intermediate Batch 3 entries retain historical
evidence; later delivery records supersede their earlier control-failure summaries.

The 2026-10-04 common-support workstream supersedes the paused task below.
The recovery commit preserves compiler, native adapter, fixtures and tracking
without claiming a build or executed resource instance. Separate proof-tooling
changes and DN-0038 drafts remain unstaged in the original worktree. Historical
proof links below name their recorded main revision. Fresh checks govern every
new delivery; the paused task is not a concurrent writer.

Batch 0 is complete on the original `codex/provider-experiments` branch at
unsigned merge `c38b9d2f8c34077353be8d0a0a94b117867ce737`, integrating common
commit `38898f385c98d09a35412a31c05d783bea9b5b1e` from recovery checkpoint
`167bd8c`. Both histories and unrelated working changes are preserved.
Ordered Type and row arguments reach source checking, publication, inference,
evidence, capture, Core validation and transforms. The original worktree passes
the explicit all-targets compiler check, the full library suite and selected
public/module/independent-validation/deep regression suites.

Fresh receipts are kept under
`~/.codex/ash-provider-evidence/common-resource-support-2026-10-04/`.
The common checkpoint passes 1,523 library cases, with one advanced callback case
still ignored, and all 99 additional workspace binaries outside architecture.
All six original interface resource regressions, all four method resource cases,
and the 24-scope 256-KiB fresh-child regression pass at unchanged limits.
Architecture has forty full fresh48 passes plus the repaired token-only
prerequisite assertion passing fresh49. Original-worktree receipts are
`batch-0-integrated-check.log` and `batch-0-integrated-tests.log`; integration
identity, commands, source pins and limitations are recorded in
`batch-0-integration.md` and its companion JSON. Formatting and independent
contract, source quality and changed-documentation reviews pass.

Batch 1 is complete on the original branch at unsigned merge
`7c97a454a930c7cc732ce43f1f25c15ef2eea7f7`, integrating common commit
`4ba09c1e7a9341f240d8c318add0be419aced5bb`. The real merge preserves both
histories and all twenty-one pinned unrelated original files. Independent
contract, source quality, native authentication memo and stack repair reviews
passed before integration.

The ten public SQLite tests execute
`Completed(Completed(Ok(42), Closed), Closed)` and actual statement finalization
before connection close. They cover imported/local definitions, repeated and
simultaneous activations, initializer-once, acquisition refusal without body or
finish, hidden report dependencies and static registration without executable
bindings. `batch-1-integrated-check.log` passes all-targets compilation in the
original worktree. `batch-1-integrated-tests.log` passes all 1,528 library cases
(one advanced callback remains explicitly ignored), all forty-one architecture
checks and selected SQLite, owner-row, resource, Core, effect and admission
suites. Cargo dependency records authenticate the original fixture root. Wider
common connected receipts10/12 cover the remaining affected suites.

The unchanged constrained positive and eleven authority mutations pass; the
64-KiB and 256-KiB deep regressions pass. Scoped memoization reuses only successful
native self-proof for an exact immutable declaration allocation. Direct equation
and expression-check dispatch avoids an unrelated 89-KiB debug frame without
changing checks or work accounting. Full integration identity, runnable command,
source pins, commands and limitations are retained in `batch-1-integration.md`
and its companion JSON. Independent SQLite work starts from this original
integration commit. Advanced captured-control cases remain Batch 3.

Batch 2 has executed evidence in `batch-2-arena-public-02.log`: all four public
cases pass, including actual usage `(0, 64, 0, 4)`, zero capacity, repeated and
nested native activations, release exactly once, native configuration refusal
without body or release, and dependent access escape rejection. The adapter
uses the existing arena backing through the common engine. Fresh `batch-2-connected-public-04.log` passes all four arena cases and all ten
SQLite cases together. The native backing suite required a byte-slice emptiness
assertion after the added compiler dependency introduced another PartialEq
implementation. `batch-2-native-05.log` passes thirty-two adapter unit cases and nine physical
arena cases. `batch-2-check-05.log` passes all-targets compilation; the strict
bidirectional carrier inventory passes in `batch-2-architecture-01.log`.
Independent arena manifest/runtime review and changed-document checks pass.
Batch 2 is complete on the original branch at unsigned merge
`53db4ebb050fdcb12df84857ab8b45adfa6b2cb6`, integrating common commit
`eb14326`. Original-worktree receipts `batch-2-integrated-public.log`,
`batch-2-integrated-native.log` and `batch-2-integrated-check.log` pass the same
four arena, ten SQLite, thirty-two adapter unit and nine physical arena cases,
and all-targets compilation. Public-test dependency records authenticate the
original fixture root; all twenty-one unrelated file pins remain unchanged.
`batch-2-integration.md` and its companion JSON retain commands, source hashes,
merge parents, runnable capability and limitations. Independent arena work starts
from this original integration commit. Typed allocation and references remain
excluded.

The imported S-01 receipt establishes executed library-defined scopes within
that program. It does not establish the selected open-row callback,
capture-dependent discard, retained dependency quarantine or complete copied
local dictionaries and nominals. One conditional handler callback test is
now admitted by the moving Batch 3 source, but its required distinct-capture
witness remains incomplete. Existing native adapter tests observe native
backing separately from an Ash session.

Batch 3's `batch-3-control-public-07.log` passes thirteen of fourteen control
cases and both retained-dependency cases. It establishes the formal open-Delta
callback under its existing lacks conditions, curried and closed implementation
contexts, capture/resume without reacquisition, owned discard with outer-resource
cleanup before statement finalization and connection close, repeated activations,
and ordinary-handler precedence. Genuine SQLite consumed completion failure
remains separate from injected consumed and retained reports. The finite
same-sigma/same-epsilon distinct-capture-demand witness still fails pending
actual request-port realization; no diverging prefix substitutes for it.

`batch-3-library-regressions-07.log` passes 1,534 library cases, with one new
static fixture failure and one advanced callback still ignored. The static
fixture omitted the required value graph and captured-segment cut. The corrected
fixture passes fresh `batch-3-static-fixture-09.log`; the full receipt is retained
as failed evidence. After connected actual-capture realization and source
warning cleanup, `batch-3-actual-c-check-15.log` passes all-targets compilation.
`batch-3-actual-c-public-15.log` passes thirteen of fifteen control cases; the
finite capture-demand witness and mixed local helper case still fail.
`batch-3-actual-c-library-16.log` passes 113 provider cases and fails the finite
witness and mixed publication rollback harness. No cases remain ignored in that
filtered run; the formal open-row admission case passes. These failures require
ordinary body-evidence closure and handler result-analysis investigation before
a new connected verification. No Batch 3 delivery is integrated.

The common branch now includes the independently verified packed-value delivery
from original unsigned merge `8adf4b2eb1ae4e031e4837fc9256411c51bcb3f5`.
Reconciliation retained both source histories and pinned the uncommitted common
changes before applying them. SQLite-specific SQL fixture arguments now use the
new built-in copying values; resource control topology is unchanged.

Fresh `batch-3-reconciled-check-21.log` passes all-targets compilation.
`batch-3-reconciled-public-21.log` passes fourteen of seventeen control cases,
including the repaired mixed local helper. Its failures are the finite captured
control witness, a latent ordinary method answer, and the lexical row fixture.
The latter initially omitted the current language's required local nominal key;
a corrected Token-key fixture reaches checking but still fails in
`batch-3-reconciled-lexical-23.log`. No new local-key semantics were introduced.
The unchanged constrained positive and eleven authority mutations pass in
`batch-3-reconciled-constrained-21.log`.

`batch-3-reconciled-library-23.log` passes 113 provider cases and fails the
finite witness and mixed publication rollback assertion. The separately attempted
owner-vector Core test matched zero cases and supplies no verification evidence;
its corrected invocation remains required. Debugger receipts23 place the finite
and latent-answer failures in final independent provider-scope admission. The
finite witness has already passed source capture realization and solved-row
comparison; final capture reconstruction fails before its row comparison. The
latent answer's final body type is Int, while copied lifecycle substitution
comparison fails. Exact graph domain and retained substitution investigation
remain implementation work, not semantic authority.

`batch-3-reconciled-retention-22.log` passes all three retained-dependency and
completion-conversion cases. The additional injected test observes actual Rust
storage destruction for consumed completion and the same retained storage until
safe dependency-ordered host teardown. A conversion failure produces a runtime
binding diagnostic without automatically retrying source completion. These are
moving-source receipts. Batch 3 remains uncommitted and unintegrated.

Both cases in `batch-3-retention-public-01.log` pass. A test-only generic native
binding owns unique Rust storage and explicitly injects retained dispositions.
The receipt establishes the same retained guard identities, transitive dependency
quarantine, revoked ordinary source access, no source retry and dependency-ordered
host destruction. Bindings receive retained-dependency obligations before native
transition and must retain or refuse safely; that contract remains a foreign
assumption. The test is separate from genuine SQLite behavior and does not prove
capture-dependent handler specialization. No Batch 3 delivery is integrated.

## Historical paused checkpoint (2026-10-03)

Execution stops at the user's requested pause after the current bounded work.
The sole source writer and external Core preparer have stopped. The external
`pause-checkpoint-2026-10-03-01.md` and companion JSON in the row-instance
evidence directory retain all 268 current measured inputs and exact resume
steps; root independently verified them against this worktree. HEAD and branch
remain unchanged. No build or language-server window is active for this task.
Core owned-admission revision 02 is applied; the separate Core kind/owner
proposal is saved but unapplied and awaits review. Latest source includes a
shared nested inference-occurs traversal and unrun refusal fixtures. Tagged
unification, dependency/evidence consumers, defining-fact retention and M1
verification remain unfinished. Resume requires fresh source-pin checks and
coordination; the last failed compiler receipt does not cover these later edits.

The user's 2026-10-03 execution direction prioritizes goal completion and
end-to-end, integration and need-driven regression evidence. S-01 remains the
immediate executable target. Continue its shared instance-bridge prerequisites
and batch connected changes; additional internal test granularity must answer a
required observation or an observed defect. The plan's
[verification policy](plan.md#verification-and-pause-conditions) governs new
tests and check scheduling without removing required evidence or review.

Type-only provider publication now passes fresh independent contract and quality
review on the verified v2 packet. Final broad evidence is 3,104 passes across 96
top-level binaries; full architecture passes all 40 cases. The first packet's
omitted measured bytecode input is preserved as failed packaging evidence; the
corrected packet includes every recorded input. Approval covers declaration
checking, static import/export certificates, separate defining-code linkage and
ordinary Core closure. Resource instances, owner rows and runtime remain pending.

The publisher has stopped source and Cargo work. The next sole GPT-6.1 Sol
owner completed read-only row M0 and instance B0 reconciliation against the
reviewed baseline. Root reviewed its concrete type and ownership mapping and
released M1: tagged owner arguments, saturated row-bearing resource types,
independent signatures, inherited-role metadata and all affected bounded walkers.
The existing row-free type route remains; both routes feed the later common
instance bridge. Association authentication remains separate from kind eligibility.

The external `row-instance-bridge-2026-10-03/m0-b0-reconciliation.md` and
`implementation-execution.md` record source seams, refusal guards, native
coordinates, evidence boundaries and ordered M1–M5/B1–B4 gates. Their root review
and M1 release are retained in `root-m0-b0-release.json` in the same evidence
directory. M1 authorizes source and test work; compiler and LSP launches use
separately coordinated serial windows. Mixed source admission, specialization,
ordinary Core and runtime still await their later checkpoints. Root owns
repository tracking. The frozen publication packet and its reviews remain
immutable evidence; reopened tracking does not rewrite that approval.

All 18 adopted proof-tooling files match `main` at `a2ced870`; Cargo uses one
build job. The task currently exposes 12 Rust analyzer tools and no direct Lean
LSP tools. The pinned stdio Lean adapter provides eight navigation tools and
has prior smoke evidence. Language servers stop before heavy builds. Validated
module receipts may avoid recompilation; the frozen integration checks remain
the proof acceptance gate.

A separate read-only authoring review produced external draft blueprint and
tooling reports in `ffi-blueprint-2026-10-03`. Root checked the public embedding
API and revised the drafts to distinguish static foreign registration from the
missing executable adapter binding. The native arena's documented preflight
obligation remains: successful initialization commits immediately. A later
containment test must use an admitted reference payload; unsupported closure
layout alone cannot prove owner containment. These reports are preparation,
not a completed authoring trial, source runtime case or adoption result.
Their exact hashes and scope are recorded in `root-draft-review.json`.

The plan review now makes executable registration and dispatch an explicit
B4/R1 deliverable: agree the typed binding and ownership handoff against the
validated Core interface, then observe native calls through the public driver.
Static manifests remain declaration authority only. Step 6 also retains
DN-0036's contrasting foreign-API walkthrough, and the verification section
links the adopted proof workflow. These execution requirements do not change
the selected semantics or M1 scope; historical preparation pins remain intact.

An early independent M1 helper review inspected the immutable
`row-instance-bridge-2026-10-03/m1-structural-review-01` snapshot. It identified
one leftover Type comparison of tagged arguments and an infallible worklist
allocation in budgeted equality. The writer corrected the comparison and
implemented charged fallible worklist reservation with refusal coverage; those
changes and tests remain uncompiled within the ongoing migration.
The snapshot and review remain unchanged. This was source inspection without
compilation; it does not establish M1 acceptance, partial-failure behavior or
small-stack conformance. The source, kind and independent Core gates remain
required after the complete migration.

Root reviewed external Core metadata and interface proposals against their
shared traversal, budget and disposal helpers. The sole writer applied both;
root verified the changed files against the approved proposed hashes. Complete
tagged arguments now reach these clone, rewrite, equality and Type-substitution
helpers, including nested row members and lacks metadata. The interface patch
preserves Type-only comparison paths and protects mapped arguments before
cumulative budget admission. This is inspected, uncompiled source progress.
The writer also applied the reviewed validator scanner proposal; root verified
its exact proposed hash. These scanners follow resource arguments, nested Type
payloads and rigid row tails while preserving existing dialect shortcuts.
The reviewed provider-state scanner is also applied and hash-verified; it
visits resource arguments and known/lacks payloads while retaining exact native
nominal state lookup. These source observations establish no runtime result.
The remaining bounded walkers, inference migration, coherent M1 tests and
ordered frozen reviews still precede source-instance or runtime admission.

A read-only substitution audit compares the moving kernel with the reviewed
Type-only publication archive. Root verified the saved source hashes and
historical archive. Inspection establishes no ownership defect in the new
guarded reconstruction; it does not prove refusal or small-stack behavior.
New root admission and retained tuple/row buffers add real work charges, and
tagged canonical comparisons can add further charges. Earlier interface
cost-preservation statements apply to helper overhead with its then-current
payload algorithm held fixed, not historical whole-kernel totals. Keep those
original proposals unchanged and measure the new exact and refusal costs.
The work ceilings and unchanged deep-disposal fixture remain required.

The read-only Core audit separates existing indirect resource authentication
from pending admission. Ordinary module validation already reaches original
certificate resource facts to check binder order, canonical records and family
relations. Exact owner-table/index coverage and unassociated effect/interface
signatures remain separate obligations. Saturated resource kind, argument tags
and lexical scope still need independent Core checks; structural traversal
alone establishes none of them. This audit is preparation, not a frozen pass.

The owned tagged zonk/rebuild batch reached one development-feedback checkpoint.
Root granted a serial window for `cargo check -p ash --all-targets` with
`CARGO_BUILD_JOBS=1`. Receipt 03 in the row-instance evidence directory records
exit 101, 262 library errors and one warning; all 268 measured inputs remained
unchanged during the run. The error groups identify remaining evidence,
resolved metadata, elaboration, capture/control and Core consumers. The library
failed to compile, so this run executed no tests and establishes no M1 pass.
The window is released; source work resumes in connected batches, with further
compiler and LSP launches requiring fresh coordination. The complete M1 gate
still requires the remaining migration, tests and frozen reviews.

Root and an independent reviewer then inspected the revised Core owned-admission
proposal. The first revision lacked a fresh fallible two-child reservation after
an arbitrary number of row-member tasks; that revision remains held as retained
evidence. Revision 02 adds the reservation in both charge modes. The sole writer
applied it, and root verified the exact approved source hash. Structured Type
admission now scans borrowed payloads beneath an iterative ownership guard,
including complete resource arguments and nested row payloads. Conditional
shared cloning preserves empty-effect function normalization. New traversal and
cloning costs remain real cumulative work, with behavior and refusal tests
pending. This source approval does not authenticate canonical owner kinds,
argument tags, saturation or lexical scope, and does not close M1.

The sole writer has released the untouched Core kind/effect admission clusters
for external patch preparation while retaining all repository source ownership.
That work must follow canonical signatures and complete simultaneous Type/row
substitution without recursive Type-to-row validation. Root review precedes
application. The writer continues connected inference, evidence and metadata
consumer changes; subsequent source is beyond receipt 03's failed compilation.

A read-only zlib walkthrough now tests the blueprint's description of a
contrasting API in `ffi-blueprint-2026-10-03/contrast-walkthrough`. Root reviewed
the typed role mapping, explicit output capacity, method effect rows and
adapter obligations against the native manual. The copying profile retains
no Ash argument; native-private scratch lifetime and unread-input checks remain
authored adapter obligations. Native compression finish and resource release
are distinct operations. This external draft is preparation, with no third
binding, native execution or completed authoring trial. Its original revision
and corrected draft hashes remain in the external audit and root review.

The user excludes cybersecurity work, including fuzzing. Verification uses
explicit deterministic compiler, library and runtime conformance cases from
the experiment contracts. Ordinary SQLite and arena integration remains part
of the plan; these cases test Ash behavior and foreign-library integration.
This is language development: the compiler must connect surface resource forms
to types, effects, Core operations and runtime ownership. Remaining uncertainty
concerns unproved language or implementation properties, such as scoped
dependencies, atomic publication or exactly-once completion. FFI memory
discipline is part of that language contract. Verification must explain the
specific missing evidence; it does not authorize cybersecurity work or a
security review.

As of 2026-10-02, the corrected B3 private checkpoint is independently reviewed.
The corrected local-call snapshot also passes independent contract and quality
review. Handler source drafts pass independent contract and quality review;
the staged independent handler entry now passes both reviews.
The row-contract amendment is independently reviewed and recorded in the
experimental semantics note. The completed slices below are experimental
components, not current language behavior or completed source cases.

On 2026-10-03, the previous implementation agent and Cargo process are absent.
The worktree and build cache survive, but the earlier temporary receipt and
freeze files are unavailable. Their recorded results remain historical evidence;
they are not fresh verification of the current source. A new sole GPT-6.1 Sol
owner resumes the conditional checkpoint. A durable recovery snapshot preserves
the starting source and documents; new command, log, exit and freeze records
are stored outside `/tmp`. The first recovered handler batch compiles and reports
53 passed, one failed and one ignored. The positive fixture loses observation of
an unused callable's latent pending row; charged latent observation corrects it.
The next handler batch passes 54 executed cases with one explicit ignored case.
Stronger retained assertions then expose a graph-layout assumption; correcting
it precedes wider checks. A capture stack regression in the wider run is traced
and repaired by completing value solving before typed graph construction. The
final library batch passes 1,480 tests with one explicit ignored case. The full
integration batch passes 1,576 tests across 94 targets, including all 40
architecture cases. A later work-accounting correction and test-block ordering
change pass the final library batch, scoped Clippy and 39 affected architecture
cases. The costly owner-API scan has earlier full-batch evidence; it was not
repeated in the affected batch. Historical source bodies are unavailable for
independent delta proof, so that result is qualified prior evidence. The durable
freeze matches the final library, Clippy and affected architecture code exactly;
rustdoc, formatting and diff checks also pass. Independent contract review
approves the private carrier's retained equations and defining-code
correspondence. Its exact-current costly owner-API scan passes, closing that
scanner gap. Independent quality review also approves the private carrier,
including measured fixture work boundaries and deep disposal. Ordinary
annotation validation and executable admission remain pending. The next slice
connects retained provider templates to the existing atomic module transaction;
specialization and public source execution still require their own evidence.

The sole source/Cargo owner is now integrating that module transaction. Combined
pending evidence batches remain unpublished until the existing final commit;
consuming lifecycle admission retains independently checked code, canonical
context and selected occurrence owners. Immutable defining source snapshots are
shared rather than copied for each ordinary module. Its first normal declaration
fails when export authentication lacks the abstract access-family kind. The
correction passes normal declaration checking. Receipt 54 passes six normal
cases covering grouped Connection/Statement publication, body-free exports after
defining-code disposal, an alias import diamond, imported helpers, a completed
local helper declared after its resource, and ordinary linked main. An earlier
affected provider batch passes 179 tests with one ignored formal-row case.
Public contracts retain no Core code; checked
modules retain defining code separately. A later focused case passes linking
and independent linked-evidence validation. Ordinary Core initially rejects its
missing resource-family/owner relation. After retaining and authenticating that
body-free relation, receipt 48 passes independent module Core validation and
evaluation, returning ordinary main's `42`. The alternate entry without a
module/source relation explicitly rejects. This proves ordinary code coexists
with provider declarations, not resource-instance or SQLite execution. These
receipts describe successive source revisions, not a reviewed final freeze.
Completed local facts are now consumed separately from lowered ABI. Later cases
retain exact local lifecycle selections and two selected handler-clause slots,
then authenticate retained code after resolved source ownership is consumed.
Receipt 60 passes eight normal cases, including actual late-clause mismatch,
pending original slots and fresh retry. Receipt 62 passes 155 cases selected by
`provider::tests`, with one ignored, including deep resource-fact partial-copy
refusal on a 256 KiB stack. This is a narrower filter than the earlier 179-case
provider batch. The normal transaction budget test initially exposes a one-unit
variation across fresh fixtures. Evidence catalog sorting charges comparisons
over allocation-address keys, so equivalent fixtures can incur different costs.
Precharging the full bounded sort window removes that accounting variation;
receipt 69 passes the focused exact, one-short, prefixed and fresh-retry case,
including pending original slots at late refusal. The next normal batch passes
11 cases but fails separate-code/canonical-closure authentication. Linked
evidence admission now authenticates the body-free certificate relation and
separately retained code before constructing kind environments. Receipt 71
passes all 12 normal cases, including that rejection and the shared-budget case.
Receipt 74 passes 13 normal cases. It extends exact-budget coverage to completed
local facts and runs a local constrained helper through ordinary linked Core to
main's `42`. Provider binders retain their checked identity and owner; only their
physical source-order comparison recognizes their separate resolver scope.
Receipt 75 also rejects an erased certificate relation directly in independently
validated ordinary Core. The separately admitted private template context keeps
its distinct prepublication checks; it grants no ordinary executable admission.
Receipt 79 passes 15 normal cases, including second-resource refusal with all
ten observed slots pending and a fresh valid retry. Nine dictionary slots commit
on success; the reserved StateAccess relation slot is authenticated separately.
Complete transaction evidence and independent publication reviews remain pending.

Later normal fixtures exercise nested generic imported helpers, polymorphic
method evidence and their prerequisite producers. They expose missing owner
kind scopes, then two retained-code correspondence gaps: method catalog
metadata and actual producer edges could change without rejection. Owner-domain
parameters now retain their checked IDs, order and kinds; bounded comparisons
use the original admitted body-free catalog and graph relations. Receipt 97
passes 17 normal cases after these corrections. It also preserves callable
source types and dictionary relations without repeating capture analysis at
each occurrence. This is template publication evidence, not specialization.

Receipt 102 passes 19 normal cases. Exact, one-short, prefixed and fresh-retry
checks cover type, constraint and coverage work for local and imported helpers.
Late defining-origin and native/state errors leave every observed source slot
pending. Actual client checking after dependency and defining-code disposal
passes, as does retained-program refusal when required code is missing.
Receipt 103 runs all 40 architecture cases: 37 pass and three fail. The failures
concern newly retained carrier inventory, a private borrowed trait that the
field scanner cannot resolve, and raw backing-storage transfer from a partial
assembly owner. They are compiler structure and disposal obligations.
Receipt 106 passes 20 normal cases after the private borrowed enum and consuming
assembly-transfer corrections. Its added injected reservation refusal occurs
at the pending publication append, preserves nine original pending slots and
charged work, and permits a fresh valid retry. It does not establish allocator
exhaustion behavior. Architecture corrections, current broad verification,
coherent freeze and ordered independent reviews remain pending.
A stronger public SQLite case then checks the complete library declarations,
instead of stopping at resolution. Receipt 111 reports three passes and one
failure: library checking returns `Internal(InvalidState)` before any client
resource instance. The smaller normal fixtures do not establish this complete
library boundary. Its cause must be localized and corrected before claiming
that the public driver stops only at pending instance support.
Receipt 113 localizes the failure to a generated function annotated as pure
although its body performs the native prepare operation. Retaining that body's
row corrects the annotation; receipt 114 then exposes the generated function's
state-bearing result, which the existing lifecycle validator rejects. Direct
single-arm newtype lowering avoids that unnecessary function while preserving
checked exhaustiveness. Receipt 115 passes all four public SQLite cases,
including actual checking/export of the complete library. Receipt 117 passes an
ordinary effectful newtype-pattern regression through final Core and evaluation.
No native function-transport authority or runtime instance support is added.

At a safe source/build checkpoint, the user requests adoption of main's proof
tooling. Eighteen tooling, documentation and toolchain files match merged commit
`a2ced870f491457a60e3131ac613f295ea77e441`; this worktree and goal are preserved.
[AD-0012](https://github.com/dikini/ash-lang/blob/a2ced870f491457a60e3131ac613f295ea77e441/docs/decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
now governs feedback and validated module reuse. Worktree Cargo defaults to one
build job. Rust navigation, hover, definition and diagnostics work through the
exposed LSP tools. No direct Lean tools are exposed in this task; the installed
eight-tool adapter is verified through stdio against a copied validated OneShot
workspace. Its goal, hover and intentional diagnostic checks exit zero in
4.20 seconds, with a sampled process-tree peak of about 1.15 GiB. A known pinned
Python subprocess-finalizer warning remains; no servers survive the check.
Both language servers stop before build ownership returns to the source owner.
Validated per-module receipt reuse and related-change batching apply to subsequent
proof work. Language-server feedback does not replace frozen integration,
source/import coherence, warning, report or axiom checks. No proof is changed or
new proof acceptance claimed by this adoption.

Receipt 118 passes 52 affected integration cases. The public entry test now
checks the complete preceding dependency/library graph before pinning the
remaining resource-instance checker guard. Receipt 119's costly architecture
scan is deliberately terminated before a known source correction; it provides
no complete architecture result. Receipt 120's broad library run aborts in a
deep parameter fixture and reports four earlier exact-budget failures. Focused
attribution identifies proportional origin retention and scoped parameter
checks missing from their expectations. The deep fixture now owns its original
parameters under iterative cleanup; the measured charges remain enforced.
Receipt 126 passes those four Core cases but aborts in another deep parameter
fixture, with ten preceding resolver/evidence failures still requiring diagnosis.
A completed raw parameter vector surviving a later clone refusal also requires
iterative ownership. Broad verification and a coherent reviewed publication
freeze remain outstanding; defaults and acceptance gates are unchanged.

Receipt 129 completes the broad library run without a parent abort: 1,488 pass,
19 fail and one is ignored. Nested child results are excluded from these counts.
The failures include exact work expectations and an evaluator test's small-stack
child. Receipt 130 narrows the resolved-module batch to 120 passes and two
failures. Retaining parameter spelling, origin and kinds consumes proportional
work; code/certificate closure can reject malformed facts before the older
registry path. These costs and refusal ordering require explicit attribution.
Receipts 131–132 localize the child overflow to compilation, during resolution
before checking or evaluation, on the unchanged 256 KiB stack. Its correction,
current broad acceptance and final architecture scan remain pending. The source
owner batches related corrections; no LSP runs during these compiler builds.
Receipt 135 traverses resolution after moving handler reentry outside the large
expression-dispatch frame, then overflows during checking. The original bounded
test still fails; checking needs its own causal trace before further correction.

Receipt 138 passes the original bounded fixture through checking, linking,
evidence, synthesis, final Core and evaluation, including repeated partial
failure. Direct block completion avoids keeping the large expression-task
dispatch frame live during row rebuilding. Diagnostic traces are then removed;
receipt 139's full library run passes 1,507 top-level tests with one ignored.
The stack bound, fixture, work limits and language checks are preserved.

Read-only acceptance preparation finds a separate boundary-evidence gap:
most retained-code and closure mutations stop at direct code authentication or
linked evidence. Only certificate erasure currently mutates valid synthesized
ordinary Core before independent rejection. The writer adds normal link and
after-synthesis certificate/source/native closure cases where their retained
representation supports them. Direct private/helper checks remain mechanism
evidence. Final broad and full architecture evidence must cover this next batch;
publication approval, row-aware work and source resource execution remain pending.

Receipt 140 passes eight closure mutations applied after valid linked evidence
and synthesis, while retaining provider certificates. Receipt 141 routes malformed
template/answer/root code through actual relinking and reports 19 normal passes,
but final Core accepts registered-foreign erasure. Retained certificates check
their defining native registry without comparing it to the final registry.
This is an observed implementation gap under the existing complete-linked-context
contract. The writer adds charged native-fact correspondence and retains the
negative case; receipt 139 does not verify that later correction.

Receipt 142 passes all 20 normal cases after charged correspondence with the
original sealed native-fact owners; foreign erasure and wrong module/source
relations independently reject at ordinary Core. Receipt 144's later full run
passes 1,508 top-level tests with one ignored. A subsequent explicit charge for
the three canonical native scans and Clippy cleanup are later source changes;
receipt 147 passes all-target Clippy with dead code explicitly allowed for this
unfinished slice. Receipt 148 adds valid formal/answer and native-owner negatives
and measures actual ordinary Validator type work at exact, one-short, prefixed
and fresh-retry limits. Module-relation construction precedes that meter.
Receipt 149 separately passes linked Type/constraint budget boundaries.

Self-review finds that some reinstalled-code fixtures lack main, permitting
rejection before the intended code boundary. Their earlier direct code refusals
remain mechanism evidence; relink attribution from receipts 143/148 is qualified.
Receipt 150 passes 22 normal cases after the method/native fixtures acquire main.
The writer then adds explicit positive check/link/evidence controls for each
mutation, fixes template/donor main fixtures, and adds a conflicting same-ID
imported-certificate versus same-owner reuse case. Receipt 151 passes all 22
normal cases with these controls. Receipt 152 localizes template, hidden-row,
root and donor-code refusal to link: the existing combination preflight checks
separate code against its defining export certificate. No donor acceptance is
observed and no production correction follows from that hypothesis. The
method/native assertions still allowed either link or evidence refusal in those
receipts; the writer now requires link InvalidState for every code mutation.
Receipt 153 verifies those precise assertions: the library passes 1,509 cases
with one ignored, main passes 18 and architecture passes 39 with the expensive
owner-API case deliberately deferred. The broad command exits 101 at
interface_resources: three cases reach type/kind exhaustion before their
expected constraint-work or cycle diagnosis. Later integration binaries do not
run. Cause analysis is pending; production limits and assertions remain intact.

User-directed host coordination held all further Cargo and LSP launches after
receipt 150 while the alignment task finishes its frozen serial Lean gate under
the shared build lock. Our goal and worktree remain unchanged. Source-only work
continued. Alignment explicitly released the window after reporting its frozen
integration pass. Root confirmed no active compiler or language server before
resuming serial Cargo. LSP remains stopped during our broad build window. Final
broad and architecture evidence, a coherent source/context freeze and fresh
independent publication reviews remain required. After terminal receipt 153 the
writer explicitly stops builds again, and root verifies an empty compiler/server
inventory before yielding alignment's requested short navigation/parent-check
window. Source-only diagnosis continues until explicit release.
Alignment releases that short window at 14:15 UTC; root verifies no active
compiler/server or Rust LSP workspace, then resumes serial Cargo for bounded
phase/ledger tracing. The final gates remain pending.
Receipt 154 reproduces all three failures and confirms accumulated type-work
exhaustion: the monomorphic cases fail in entry kind checking, the polymorphic
case in dependency checking. Retained-record and source-origin accounting remain
under review; diagnostic tracing is temporary, and no final pass follows.
Receipt 155 passes all six unchanged interface-resource fixtures after the
parameter clone's record charge covers its inline Source span. Spelling, kind
and dynamic origin charges remain; limits and assertions are unchanged. Tracing
is still present. A second short alignment repair window begins only after
writer BUILD HOLD and root's empty inventory check; final trace-free broad
verification and freeze/reviews remain pending.
After explicit alignment release and root's empty inventory check, formatter
receipt 156 passes. Actual library receipt 157 aborts in a stale exact-budget
fixture: its Source prefix still assumes the removed separate debit. Unexpected
success is recursively formatted before iterative test disposal. Constants and
test outcome guarding are corrected without changing depth, stack or limits;
full library receipt 158 is pending.
Receipt 158 completes with 1,504 passes, six fixed-budget failures and one
ignored. The original deep partial-clone case, all 22 normal provider cases and
the new origin-accounting case pass. Remaining Source-copy constants are
reconciled by actual copy count; depth, stack, limits and semantic assertions
remain unchanged. Full library receipt 159 is pending.
Receipt 159 passes 1,510 library cases with one ignored, including reconciled
exact-budget cases, all normal publication cases and origin accounting. Current
broad integration, full architecture and other final gates remain pending before
the coherent freeze and fresh ordered reviews.
Broad receipt 161 passes the repaired interface-resource cases and preceding
suites, then exits 101 on one stale method-parameter source-formula pin (three
other cases pass). Formula reconciliation and removal of obsolete test markers
follow only after terminal. Receipt 163 passes all four affected integration
cases. Settled broad receipt 165 is pending, including later integration
binaries that earlier failed commands did not run; final gates remain required.
Receipt 165 passes all 96 top-level binaries (3,104 passes, one ignored, one
architecture scanner filtered), including all later integrations. Clippy 166
then requires an equivalent test-only upper-bound spelling correction. That
single provider.rs change qualifies 165 as prior-source evidence. Current
Clippy, rustdoc, full architecture and final broad gates precede freeze/reviews.
Clippy 167 passes with its explicit dead-code allowance for the unfinished slice;
private-item rustdoc 168 denies warnings and passes, as do format/diff checks
169/170. Full architecture 171 runs all 40 cases, including the deferred scanner.
Final broad verification remains required on the corrected candidate before freeze.
Full architecture 171 fails its scanner on direct ImportedFacts backing-map
mutation (39 pass, one fail). The writer corrects the owner API without weakening
the test. BUILD HOLD and root's empty host/workspace inventory precede alignment's
requested frozen integration window. Source-only correction continues; full
architecture and current broad/final gates must cover the resulting source.
The source-only correction uses Occupied/Vacant entries at four related
certificate sites, preserving same-owner import reuse, conflict refusal and
fresh-only summary/link staging. Read-only review confirms unchanged precharges
and no scanner/native-policy changes. Atomicity belongs to the owning resolver/
publication transaction, not rollback of a directly called import helper. Gate
reruns await explicit build-window release.
Alignment releases the window after retaining a failed proof gate and 52 saved
successes. Root verifies empty active compiler/server/workspace inventories and
resumes serial provider gates on the Entry correction. No proof pass or final
publication freeze follows from this release.
Formatter 172 and all 22 focused normal publication cases in 173 pass on the
Entry correction. Current Clippy/full architecture/broad checks remain before
freeze. External packet preparation is read-only to repository source; actual
freeze requires matching final receipts, root documentation STOP and archived
manifest/current-byte verification.
Current Clippy 174 passes with its recorded dead-code allowance. Refined packet
preparation verifies recorded full hashes against archive/current bytes and
rechecks code inputs/inventory at the end; it remains uninvoked until final gates
and root documentation STOP.

Private-item rustdoc 175, format check 176 and diff check 177 pass on the same
Entry candidate. Full architecture 178 passes all 40 cases, including the
unchanged owner-API scanner. Final broad verification remains before freeze.
The writer holds builds before that batch for alignment's next exclusive proof
window; neither a passing architecture batch nor validated cached modules
replace the complete frozen acceptance gate. Root rechecks all 18 adopted
tooling files against the merged commit with no differences. The task exposes
12 Rust LSP tools and no direct Lean LSP tools; the eight-tool Lean adapter
remains available through its verified stdio route. No server is active.
Read-only preparation refreshes the acceptance matrix and row/instance handoff
memo against the Entry candidate, identifying no new targeted assertion gap.
The external review brief preserves exact input checks, budget exclusions,
source ownership and the distinction between publication and later instances.
Actual final review still requires broad verification, coherent freeze and STOP.
Final broad receipt 179 exits zero on the same 267 inputs as 173–178: 96
top-level binaries report 3,104 passes, no failures, one ignored fixture and one
filtered scanner. Full architecture 178 supplies that unchanged scanner's pass.
Root independently counts each top-level binary's final summary, excluding child
results. The writer explicitly holds source/Cargo/LSP; root finishes documentation
and stops edits for the coherent packet and fresh ordered reviews. The remaining
alignment dependency queries use a separate lightweight window. Publication
approval, row/instance implementation and the full experiment remain unfinished.

The ignored formal-row fixture crosses current owner-kind and application
rules, not just an accidental checker guard. The original Type-only P-1 had no
row arguments for resource, effect or interface applications; the selected
amendment below now supplies that experimental typing delta. The shared owner
checker remains unchanged until the separate implementation slice.
Actual c-dependent open demands at specialization are a separate possible
route; no typed source witness yet establishes that route for principal open D.
A read-only design report recommends explicit saturated row-valued arguments.
Independent semantic review approves a revised candidate for further evidence
work: resource, effect and interface signatures admit complete row slots
independently of resource associations; sealed authority remains a separate
checked relation. The candidate also specifies context-free tagged arguments and
inherited owner-row roles in generated evidence. A clarification labels unique
resource association for an EffectId as a new bounded candidate restriction.
Documentation integration passes independent contract and prose review. The
[complete owner row arguments](semantics.md#selected-complete-owner-row-arguments)
are selected as an informative amendment to experimental P-1; normative Ash and
the current Type-only publication implementation remain unchanged. Actual formal
open-D execution and distinct capture-dependent close-demand evidence remain
required and pending.

A separate read-only implementation plan for the selected row amendment passes
contract and quality review. Its six milestones start with the publication
owner's reviewed freeze and explicit source/Cargo handoff, then cover shared
kinded arguments, source admission, inherited evidence and publication, actual
callback demand, and imported specialization/execution. Its file observations
are not a coherent source freeze. Row implementation has not begun; the distinct
actual-c witness remains required even if the callback case succeeds.

The instance-specialization dependency plan also passes independent contract
then quality review as preparation. It makes the missing shared source-instance
checking, immutable specialization, occurrence relocation, final Core and runtime
boundaries explicit within row M2–M5. Type-only initializer inference tests use
that same bridge. Builtin scope metadata and singleton activation lookup do not
supply it. Both plans require reconciliation with the reviewed publication freeze
before implementation; their approval establishes no source or runtime success.

A proposed close-demand witness uses two match arms inside one lexical
Connection activation, preserving the exact fresh identity and substitution.
Both arms have real remainder {H,J}, but arm-specific armed cleanup actions
would give D={H} or D={J} and different normalized residuals. After consuming
discard's Unit result, a pure Type-polymorphic recursive helper can supply the
hidden answer through divergence. This resolves the design typing objection;
it proves neither actual client capture correspondence nor finite completion.
Specialization must authenticate each request's actual action and surviving
interpreter rather than derive c from the joined scalar row.

| Boundary | Verified state |
| --- | --- |
| Native SQLite and physical arena backing | Independently reviewed safe APIs, including copied connection diagnostics; 41 native tests pass with Clippy, rustdoc and formatting. |
| Declaration/instance front end and foreign registration | Independently reviewed parsing, resolution and canonical registration; public checking guards remain. |
| Private lifecycle templates with imported helpers | Independently reviewed Connection acquisition/finish and Statement acquisition with its enclosing Connection association. The last frozen batch passes 1,397 library and 566 integration tests; scoped Clippy passes. |
| B3 source data, prerequisite dictionaries and method-local parameters | Independent contract and quality review approve the corrected frozen checkpoint, including the interim local-call guard. It passes 1,413 library and 593 integration tests across 31 targets, scoped Clippy, formatting and diff checks. |
| Lawful local imported forwarding | Independent contract and quality re-review approve the corrected 1,420-library/593-integration freeze and close the wrapper cleanup finding. Higher-order transport and full handler/control support remain subsequent obligations. |
| Handler templates, atomic module publication, instances and complete control validation | The owned conditional template and capture draft passes independent private-carrier contract and quality review: 1,480 library tests pass with one formal-row case ignored. Prior integration and later affected checks are qualified above. Receipt 106 passes 20 normal publication cases, including local/imported helpers, retained selected-evidence relations, body-free exports/imports, all three shared work ledgers, ordinary linked main returning `42`, code/certificate refusals and late transaction rollback. Receipt 100 passes 164 cases under its narrower provider filter with one ignored. Receipt 103 leaves three architecture failures requiring correction and fresh verification. These moving receipts do not establish a final publication freeze or review. Specialization, instances and complete control validation remain pending. |
| Public runtime and S/M/X cases | Pending; S-01 is prepared but has not executed through the public driver. |
| Results, blueprint, tooling and product adoption | Pending; successful evidence precedes adoption and normative specification changes. |

The starting evidence and observations below retain the sequence of discoveries.
Later reviewed checkpoints supersede earlier pending statements within their
explicit scope. The case ledger changes only after actual source observations.

## Starting evidence

### Completed native checkpoint

N0's copying adapter is implemented in the root workspace's
[foreign-adapter](../../../foreign-adapter/README.md) crate. Its 21 tests,
warnings-denied Clippy and rustdoc checks, formatting and diff checks passed.
Independent review confirmed the pinned header and runtime provenance and the
safe API's consumption, refusal, partial-owner and copying contracts. Recorded
inputs and limits are in [environment.json](environment.json).

Physical arena backing is also implemented in the same crate and independently
reviewed for contract conformance and Rust safety. Its 16 tests cover real
bounded storage, alignment, non-owning keys, immutable publication, rollback and
cleanup. The combined native package passed 37 tests, warnings-denied Clippy and
rustdoc, formatting and diff checks. This supplies host storage primitives only;
checked Ash layouts, encoding, lifetime/dependency checking and the evaluator
bridge remain pending. Native tests do not complete any M case.

Independent review also found P-1 ready for implementation within its selected
synchronous copying profile. Review corrections made source/native error
mapping, callable authority boundaries, lifecycle rows, state lineage, template
validation and body-free public facts explicit. This is an experimental contract
checkpoint, not a claim about implemented Ash behavior.

These checkpoints do not complete an Ash-source case. F0/F1 declaration and
instance parsing/resolution is implemented and independently reviewed. Thirteen
provider tests and one internal imported-origin fixture passed. Independent
review also passed 258 existing integration tests, all-target Clippy with
warnings denied, formatting and diff checks. A 256 KiB probe resolved and
disposed 128 nested instances; the retained regression covers success and late
rejection. Review corrections fixed iterative scheduling, frame size, grammar
diagnostics and exhaustive test walkers.

F0/F1 retains explicit checker, evidence and export-authentication guards.
The imported-origin fixture bypasses checked-summary admission for its isolated
resolver test; it does not establish admitted client use. T0 foreign registration
and admission is implemented and independently reviewed. Its final checks passed
1,306 library tests and 124 affected integration tests, warnings-denied
all-target Clippy, formatting and diff checks. Independent review reran 1,369
unique tests and verified the original malformed-state probes now reject.

T0 retains canonical signatures, operation roles, complete state operand paths,
owned and retained lineage, result constructors and sealed StateAccess identities.
Summary admission and linking independently authenticate its immutable
certificates. Ordinary native calls and source handlers remain unavailable;
passive registered imports and ordinary configuration construction work.
T1a declaration checking and retained typed templates is active. T1b instances,
T1c dependency/control validation and R1 execution follow the agreed descriptor
seam. The source S/M/X ledger remains unimplemented until actual fixtures cross
those boundaries. A-0's bounded arena contract also passed independent design
review; Ash typing, runtime integration and source evidence remain pending.

T1a's structural Core checkpoint passed independent review and 1,318 library
tests. Its private entry compares contextual metadata with independently
reconstructed registrations and authenticates native certificates before
allowing sparse imported identities. Final dense linked validation is unchanged.
The entry returns unvalidated Core: it grants no lifecycle, publication or
execution authority. Independent phase/ownership flow analysis is active;
authenticated external environments, handler templates and retained typed
template publication remain pending.

Structural quality review found an omitted operation annotation origin in the
canonical comparison. The correction uses the existing cumulative, iterative
origin comparison. An annotation-origin-only regression first failed and then
passed for changed and absent source origins. Independent re-review resolved
that finding; phase/ownership flow remains outside this structural approval.

The unpublished Current-state ownership analysis passed eight focused tests and
independent conformance and Rust/API quality review. Evidence covers native
outcome branching, duplicate completion, guard loss, aliases, phase boundaries
and bounded cleanup. The implementation owner passed 1,326 library tests before
StateAccess landed. Review found uncharged global native-fact scans: adding one
canonical state and 64 operations initially left the measured cost unchanged.
The corrected immutable local index charges every module, record and lookup,
reserves fallibly and rejects duplicate defining IDs. The new regression passed
exact and one-short work limits; independent re-review resolved the finding.
This approval establishes ownership classification only. Complete report-role/
error fidelity, independent mapped payloads, Enclosing-state access and
authenticated template-entry capabilities remain required before executable
template admission.

The unary `ProviderStateAccess` Core substrate is implemented in
[effect.rs](../../../src/core/effect.rs) and
[transform.rs](../../../src/core/transform.rs), and passed independent scope
and Rust/API quality review. Six new tests passed; the affected effect and
transform suites passed 25 tests. Evidence covers ordered type metadata,
substitution, one operand, operand-row replay, identity/origin preservation,
exact work boundaries and iterative partial-failure disposal. Clippy passed
with warnings denied and an explicit dead-code allowance for active T1 code;
scoped formatting and diff checks passed. This approval covers representation
and rebuilding only. Descriptor, phase, Enclosing-lineage, capture and runtime
admission remain closed.

Direct source StateAccess now emits unpublished typed draft Core from checked
local header associations. Five tests passed: Statement acquisition selects
Connection's association despite their distinct native effects, targeted
renaming preserves the canonical method identity, and first-class/callable,
wrong-operand and missing-association paths reject. Independent conformance
review approved that source slice. Rust/budget review found two gaps: separately
retained argument carriers lacked distinct precharges, and a cloned/displaced
type could lose iterative ownership across a later failure. Both regressions
first failed, including an isolated small-stack overflow, and then passed after
separate precharges and guarded cloning/duplicate-formal rejection. Independent
re-review approved the correction; exact/one-short work and iterative cleanup
tests passed. Imported raw resource facts, ordinary evidence,
independent Core association/Enclosing validation, capture and runtime still
provide no admission authority.

The unpublished independent Core association check now validates the exact
defining relation, ordered resource arguments, associated state type and operand
row. Its three tests also check enclosing-state coordinates, callable barriers,
coherent wrong-owner mutations and deep untrusted metadata disposal. Independent
contract review approved this slice. Rust/budget review found that shared source
and Core state scans visited nullary effect labels without charging for each
label. Paired regressions observed cost 3 for both empty and 64-label rows; after
precharging the labels, the wide rows cost 67. Exact, one-short, prefix and fresh
retry checks passed. Re-review approved the correction and association slice.
Header associations still provide no descriptor certificate or runtime authority.

Before the next lifecycle-entry review corrections, one combined command passed
1,355 library tests and 37 integration tests: foreign admission (20), SQLite
preparation (4), provider resolution (7) and provider syntax (6). The direct
StateAccess import tests now assert the source diagnostic produced by controlled
phase checking; a separate method-value test retains the closed generic-method
guard. Their correction passed independent review. Lifecycle-entry and report
proofs are under review; template publication, capture and execution remain
pending. This is a batched regression checkpoint, not whole-worktree verification
or an executed S-01 case.

The private [lifecycle-entry proof](../../../src/core/provider/entry.rs) and
composed flow now passed independent contract and Rust/API quality review.
They compare canonical local declaration/template identities, ordered source
and generated formals, separate answer/row binders, exact input and state types,
wrapper types/rows/origins, source report constructor roles and registered error
monotypes. Native consumed-success and consumed-error outcomes remain distinct
through source mapping; independent pure error mapping is permitted. Review
mutations exposed four incomplete metadata relations and an aliased source
answer binder. All reject after correction. Connection and Statement acquisition
and finish, two-formal relations and cumulative failure/retry checks passed.

The corrected entry batch passed 1,358 library tests and the same 37 integration
tests. A later focused batch passed 59 provider tests after the final answer
guard and constructor cleanup repairs. Rust review found that the existing
draft compiler dropped deep input/result/function types recursively if a later
clone failed. Two shared production assembly helpers now retain iterative
guards through sibling type/row and parameter cloning. Isolated 256 KiB tests
reproduced three late stack-overflow paths before repair, then passed with
32,000-level untrusted metadata, prefix/exact/one-short budgets and fresh retries.
The fixtures test assembly and disposal, not accepted source or deep admitted
Core. This approval authenticates unpublished local entry and lifecycle flow;
the caller supplies canonical local provenance. Imported helper authentication,
final dictionary ABI lowering, handlers, atomic publication, instance validation
and execution remain pending.

The subsequent plain imported-helper checkpoint now passes 73 focused
provider/capture tests and one combined run of 1,375 library tests plus 111
integration tests. The latter includes module and provider suites and the five
existing resource/control targets used at baseline. Canonical actual imports
determine full normalized `Forall` types and kinds. Actual helper applications
retain their defining binder and inferred type application through aliases;
flow combines independent operands/results with selected callable results,
control and stored captures. Two regressions reproduced the old query accepting
unknown lexical captures and unmatched metadata. The correction distinguishes
metadata slots and permits only the actual canonical application parameters.
An unrelated noisy helper does not poison the selected call.

Statement acquisition now composes that helper context with an enclosing
Connection state association. A proof tied to the immutable program and exact
StateAccess nodes checks method, definition, arguments, operand/result types and
rows before contextual structural acceptance; existing phase/lineage flow then
runs. The contextual registry compares exact independent canonical metadata
before accepting sparse IDs whose allocation order differs from textual order.
Field/row mutants, changed origins and coherently changed identities reject.
Ordinary final validation remains closed. Cumulative exact/prefix/one-short and
fresh-retry tests measure 3,538 work units for external acquisition and 13 for
the selected-capture fixture. Independent contract and Rust/API reviews approved
the exact private bounded slice. The Rust review checked ownership guards,
iterative failure cleanup, borrowed proof lifetimes, metadata relocation and
normalization equivalence. Scoped formatting passed after mechanical correction.

Contract review requested a concrete transitive generic counterexample:
`prepare<B> : B -> B` calls `identity<A> : A -> A`. Both the dependency and each
lifecycle source compile, but contextual checking refuses configuration and
close-error calls with `ResourceEscape`. The outer metadata allowance does not
substitute the nested callee's formal context. A test-only addition reproduces
both phases; its provider/capture batch passed 74 tests after the combined run,
with no further production change. This is a valid P-1 support obligation, not a
source safety rejection. The constrained-helper owner now continues from this
reviewed checkpoint with staged evidence and actual call-context substitution.

The next helper fixture retains generic `normalize<A> : A -> A` with ordered
`Pass<A>` and `Stamp<A>` requirements. `Pass` declares two equal-typed methods;
`Stamp` declares a third. An initial blanket `impl<A> Pass<A>` fixture failed
ordinary dependency checking because its selection key contains only a bare
variable. That failure is fixture evidence, not the missing lifecycle bridge.
Concrete implementations for registered `OpenConfig` and `CloseError` repair
the fixture without changing current implementation rules. The dependency then
checks normally. The closed lifecycle entry reports `Internal(InvalidState)`,
but installing the real selector exposes another fixture issue: the alias-only
import brings names into scope and selects no implementations. It correctly
reports `Unsatisfied` when closing this call's obligations. The positive trial
adds `import helper (impl Pass, impl Stamp)`; the alias-only form becomes an
authority negative. Neither fixture failure is successful lifecycle admission.
Typed Core rewriting and independent admission remain under implementation.

The repaired positive now retains exact unpublished slots, lowers dictionary
Core and passes the private contextual check. A combined external-helper batch
passes 17 tests, including both lifecycle phases with concrete producers and
generic tuple-head producers for Connection, without enclosing state-access
associations. The former transitive generic frontier is now a
positive: actual nested source-call contexts pass through reconstruction from
canonical imported summaries. Capture correction prunes the obsolete source
method placeholder after its authenticated route replaces it, while retaining
the selected binder and evidence dependencies. Coherent ABI mutations, failure
and budget cases, broader regressions and independent reviews remain pending.
Evidence slots, descriptors and templates remain unpublished; this is an
intermediate B2 result.

The reviewed plain helper bridge accepts primitives, tuples and zero-parameter
native ordinary data, recursively inspecting canonical constructor payloads.
Its constrained and transitive-generic restrictions are the subject of B2's
connected positive tests above. B2 still excludes prerequisite dictionaries,
method-local polymorphism, higher kinds, source nominal and parameterized data,
and selected internally handled/resource control. Resource and provider-state
transport remain prohibited by P-1. Complete lawful helper contexts, handlers
and transactional template publication remain required. No S-01 case or public
provider admission follows from these private checks.

Read-only inspection also found an API-level capture gap: the typed query checked
nested callees' stored dependencies but could omit those of its initial target.
A direct regression exercises ignored unknown values and unresolved metadata.
The general query must check that target. Only the synthetic source wrapper
rebuilt from canonical imported facts needs a separate entry, because its
unapplied helper ports become bound at the nested call. Every actual helper and
producer target still requires capture checking. B2's final independent review
checks this boundary: the query accepts an opaque proof whose fields and
constructor belong to canonical reconstruction, rather than an arbitrary
capture summary. This finding does not show a public provider-admission
counterexample.

Constrained helper composition with Statement acquisition is still pending.
The earlier plain-helper test retains its authenticated enclosing Connection
association. B2's convenience compiler and checker currently supply no such
association, although the independent staged authenticator already accepts it.
The next composition case must carry that same checked relation through the
staged path and combine independent SQL normalization with Connection state
access. Missing and wrong associations must reject. This is an unwired support
seam, not a regression of the reviewed plain-helper path.

Following the user's batching instruction, one implementation owner runs Cargo
for related provider, capture and evidence changes. Focused regressions establish
the relevant failure, then combined library and affected integration suites
verify the shared boundaries. Root reads the receipts and maintains this record;
it does not run competing builds.

The correction batch passes 90 provider tests and 119 capture tests. It includes
direct constrained-path ABI and authority mutations, initial-target stored
capture checks, charged target lookups and cumulative output-builder work.
Compilation and independent checking pass exact, one-short and prefixed work
tests in both Connection phases. The new deep-refusal probe passes shallow
checking, bounded and unlimited rejection, and complete draft/fixture teardown
with 8,192-level metadata at 256 KiB. Its earlier 64 KiB failure occurred even
for shallow input and supplies no deep-disposal evidence. The existing cleanup
regression now also passes at its unchanged 256 KiB bound after extracting the
global-occurrence branch from the large expression dispatcher.

The final frozen B2 batch passes 1,394 library tests and 460 integration tests
across 20 targets. Isolated preparation/rebuild proofs verify width-sensitive
work, prefix/exact/one-short refusal and fresh retry. The shared transform's
existing exact accounting test includes the newly charged fallible carriers;
its one-short refusal, exact success and Arc lifecycle checks remain intact.
Independent contract and Rust/API/budget/ownership reviews both approve the
frozen 15-file slice after reading the actual receipts and checking its hashes.
Their lookup, rebuild-accounting, carrier and evidence-attribution findings are
resolved. Approval covers private Connection acquisition and finish with no
enclosing state-access association, within the data and producer limits above.
Whole-worktree Clippy/`xtask`, constrained Statement composition, complete P-1,
template publication and source execution remain pending.

Constrained Statement composition is now active. Its dependency and both local
headers check normally. The actual SQL operand is registered `Native.Bytes`;
the native manifest defines no `Native.SqlText` family. The first staged source
trial fails at `Provider.state_of db` because the compiler supplies no exact
checked local header association. This is the missing wiring to replace, rather
than an invalid helper or a changed native ABI. The owner now carries the same
canonical association through the staged compiler, independent authenticator
and flow entry. Missing/wrong associations, exact work limits and unpublished
failure/retry remain required evidence.

That composition now passes independent contract and Rust/API/budget/ownership
review. Its unfiltered frozen batch passes 1,397 library tests and 566
integration tests across 26 targets, including all 53 baseline runtime/native
resource cases and 53 scoped-evidence interactions. Scoped Clippy passes with
warnings denied and only the active T1 dead-code allowance. Formatting and
whitespace checks pass. Exact work is 2,229 units for association cloning and
source compilation, and 9,813 for independent checking; exact, prefixed,
one-short and fresh-retry cases pass with source slots empty.

Evidence includes renamed imports and helper-file deletion; missing, duplicate
and changed association state/definition/family/formals; changed Core method,
owner, arguments, operand/result types, rows and enclosing identity; wrong
lifecycle phase; and helper transport of native state or an enclosing owner.
The compiler and checker forward the existing checked relations through thin
entries, with no new certificate or native ABI. This adds private Statement
acquisition to the reviewed constrained helper fragment. Prerequisites,
method-local polymorphism, canonical source data, internally handled control,
handlers, publication and execution remain pending. Full `xtask` verification
is not claimed.

B3's dependency now checks normally with transparent `Box<A>` data, decreasing
`Pass<Box<A>>` and `Stamp<Box<A>>` prerequisites, and `first<B>` called at
`Bool` and `Unit`. Concrete registered configuration, error and byte data
terminate the selections. The first trial had an invalid nested constructor
pattern; correcting it establishes a genuine source-positive fixture. The
retained lifecycle draft then fails with `Internal(Core(InvalidPayload))`.
This is missing bridge evidence, not a rejection of the helper's source types.

The ordinary lowerer emits prerequisite and polymorphic method anchors, but
the draft has no canonical method-evidence catalog installed. B3 factors the
existing catalog's checked fact inputs and authenticates imported owners
without claiming they have local definitions. Independent checking must also
authenticate every prerequisite route and compare the complete canonical
catalog; agreement between emitted anchors and supplied rows is insufficient.

Transparent instantiated data has existing canonical payload facts. Opaque
ordinary data remains unsupported by this private checkpoint because the
imported view does not supply its hidden payload family. Current linking rules
already retain hidden defining facts without granting source access; later
support needs an authenticated storage-fact input, not exposed constructors.
No B3 production admission or verification pass is claimed yet. Complete lawful
helper contexts remain a P-1 obligation.

The next connected batch passes the 94 incumbent provider tests, while B3
remains red. An ordinary linked counterpart now reproduces the same failure;
29 incumbent external-helper tests pass alongside both failing B3 cases.
The mismatch is a polymorphic prerequisite dictionary under a monomorphic
implementation method. Its emitted application targets the parent's requirement,
while the existing root application expectation targets the helper's different
requirement. Correcting this shared lowering/catalog relation precedes any
contextual admission claim. The supplied global row cannot authenticate the
nested application merely because its method and type agree.

Both new positives now pass: ordinary linked synthesis/validation and private
retained acquisition/finish with nested source data, prerequisites and distinct
method-local applications. Shared lowering retains canonical passive parent
rows and checks their actual prerequisite edges without requiring nonexistent
abstraction nodes. Carrier validation follows the independently authenticated
parent relation. Contextual checking reconstructs the imported catalog rather
than trusting its emitted anchors. No slot or public resource is published.

The first completed library batch reports 1,392 passing tests and seven
failures, all at existing exact-cost assertions in the catalog, validator,
transform and driver boundaries. The new checks change accounting; independently
derived cost corrections and exact/one-short/prefix/retry evidence are still
required. Review distinguishes restoration of pre-existing linked scan charges
lost during factoring from additional carrier and field-check work. The imported
lookup width regression confirms an undercharge: zero units versus 192 for
three 64-wide searches. Complete catalog/retry evidence remains pending.
The initial authority pass already authenticates polymorphic producer-node
metadata; a contrary preliminary claim was retracted. The added detailed check
is consistency checking. This is an intermediate positive, not a frozen B3
approval or whole-worktree verification.

The later library batch passes 1,407 tests. The provider/storage batch covers
actual imported catalog width, both lifecycle phases, Statement associations,
exact/prefix/one-short/retry limits and 8,192-level storage refusal/disposal on
a 256 KiB stack. Scoped Clippy passes. The broader integration run stops at an
outdated source-text cost formula; its correction and completed receipt remain
pending. These receipts precede the new authority probe below.

That coherent mutation keeps the original helper invocation and every dictionary
ABI node live, then directly calls an installed method that the helper does not
invoke. The selected method contains control outside the admitted private
profile. The checker accepts the mutation because a dictionary producer becomes
an ordinary callable flow fact, whose fallback checks state-free types without
the selected method's call relation. The correction distinguishes dictionary
carriers and permits their applications only at independently authenticated
prerequisite installation nodes. Global ABI staging and the actual helper call
remain separate. Correction and frozen review are pending; no public admission
or new helper-control support follows from this finding.

The corrected source is now frozen across 18 files. All 1,409 library tests
and 593 outer integration tests across 31 targets pass; child-process summaries
are excluded from that integration count. Scoped Clippy with warnings denied
and the active-code dead-code allowance, formatting and diff checks pass.
Independent contract and quality review follow sequentially.

Dictionary facts now remain distinct through direct reuse, aliases, type
application, tuples, branches, identity calls and captured local callables.
Only exact prerequisite installation nodes obtain the carrier application
permission, after independent canonical catalog/Core checking succeeds.
Ordinary fallback rejects nested carrier arguments. The unused noisy selected
method remains a positive; broader lawful callable/control contexts remain
unfinished.

Measured cumulative fixture work is 68,433 check / 12,891 compile units for
Connection acquisition, 144,266 / 33,484 for Connection finish and
69,561 / 13,907 for Statement acquisition. Exact/prefix/one-short/retry checks
retain the same staged prefix. These are compiler work units, not native cost
or elapsed-time measurements. Opaque ordinary data, generic evidence scopes,
handlers, atomic publication, instances, public execution and full product
verification remain outside this frozen slice.

Fresh contract review reproduced an inherited plain-import entry gap. With
valid line-based source syntax and explicit native config/error arrows, direct
control-bearing helper calls reject, but local functions forwarding to that
helper pass the raw plain entry in both acquisition and finish. Pure direct and
forwarded counterparts also pass that entry. The local function's ordinary
callable classification omits its imported callee relation; fallback application
therefore returns independent data without checking the actual helper call.
This demonstrates inconsistent private admission, not public execution or a
native memory failure.

The canonical staged entry rejects both pure and control-bearing forwarders
with `InvalidEntry`. Its source traversal finds one imported occurrence in
acquisition and two in finish, while retained occurrence counts are zero.
That is a missing lawful local-call correspondence bridge, not control-specific
rejection. Only the test file was reopened for this probe; the other 17 frozen
source hashes matched.

The interim correction retains unproved imported-call dependencies through
local functions, aliases, aggregate captures, recursive groups and argument/
return laundering. Direct authenticated calls and ordinary pure local data
computation remain distinct. This closes the unchecked raw entry without
claiming support for the rejected useful forwarders. The next connected
implementation must retain their source occurrences across callable phase
barriers and establish canonical call/capture correspondence before handler
drafts and publication. Lawful higher-order and internally handled helper
support remains required by the full experiment.

The corrected 18-file snapshot passes 1,413 library tests and 593 outer
integration tests across 31 targets. Scoped Clippy, formatting, diff checks and
all recorded source hashes pass. Seven source dependency/laundering variants
cover both lifecycle phases and exact/prefix/one-short/retry budgets. Direct
authenticated aliases and pure local arithmetic/data remain positive. Both
pure and control-bearing local imported forwarders now reject at the raw entry;
the staged occurrence-ledger mismatch remains. The original paired failing
probe is preserved. Fresh contract and quality review approve this corrected
snapshot with no blocking findings. All 18 source hashes match before and after
review; the coordinator preserved their exact snapshot as the next comparison
baseline. The useful local-forwarding bridge remains pending.

The corrected Connection finish check costs 144,279 work units; its compile
cost remains 33,484. Acquisition and Statement costs are unchanged from the
preceding frozen dictionary checkpoint. These measurements describe the private
checked fixtures only.

After the source and external-global cleanup corrections, the coordinator ran
`cargo test --locked --lib --quiet`: all 1,348 library tests passed. The
remaining library-test warnings concern active T1 handler/template fields.
This is a regression checkpoint for the compiled private components; independent
Core association/Enclosing validation and the complete executable provider path
remain unfinished.

After the new Core operation landed, the coordinator reran the five affected
builtin resource/effect suites used at baseline: all 53 tests passed, including
capture/resume/discard, structural completion and both Core transforms. This
checks existing behavior across the new representation; it does not establish
experimental source admission or whole-worktree verification.

The concrete S-01 library/client bundle and its
[preparation tests](../../../tests/provider_sqlite_source.rs) now exist. Four
tests passed: shallow source parsing/projection, preservation of the original
frontend depth failure, and SQLite resolution against normally checked
registered dependencies, plus the concrete client's public-driver failure at
the pending resource admission guard. The last pins typing's internal invalid
state and `type.internal`; it must become successful runtime evidence after
T1/R1. Independent review confirmed the ordinary modular path and all four
tests. SQLite declaration checking, importing client checking and execution
remain pending. These preparation tests do not complete S-01.

### Baseline and scope

The experiment worktree is `.worktree/provider-experiments`, on
`codex/provider-experiments`, based on
`124e164094a9a338fd5ce6a58f979da463285f28`. The carried design package is not
baseline implementation. All changes use the root workspace; `main` remains
untouched. No second parser, checker, runtime or probe workspace is admitted.
Useful experimental code may be retained. Unsuccessful or unresolved behavior
does not merge.

No commits have been made. Any future commit uses
`git -c commit.gpgsign=false commit`, without `-S`, following the user's explicit
request. Do not change global Git configuration.

Current Ash provides scoped builtin cell/native-buffer authority, fresh rigid
identities, stored dependency analysis and structural capture/completion. It
does not provide source resource declarations or general foreign interpretation.
The implementation derives `ResourceApi` from builtin module IDs, uses fixed
`ResourceMethods` arrays, checks integer initializers and stores builtin runtime
payload alternatives. Those facts identify extension seams; they do not define
the experimental resource contract. The affected current contracts are
[resource typing](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies),
[native-buffer execution](../../../spec/dynamic-semantics.md#scoped-native-buffer-execution),
[source grammar](../../../spec/syntax.md) and
[entry checking](../../../spec/static-semantics.md#globals-and-modules).

The transferable evidence is exact lexical selection and hidden capture
tracking, rather than builtin identity numbers. Arena allocation needs a
relational payload summary to admit safe outer projection. Retention and views
need a shorter access interval than owner liveness. Handler clauses depend on
the client's answer type and continuation row, so declaration templates must
instantiate ordinary Core handlers rather than pretend to be ordinary rank-2
source functions. Existing cleanup/control nodes can carry completion policy;
only the resource carrier owns guarded publication and native state. Global
resources, ownership transport, callbacks, processes, tracing and reference
counting remain excluded.

## Shared descriptor seam

Land the declaration registry before splitting callers. The following is an
implementation interface sketch; the checked relations in `semantics.md` govern
its meaning. IDs use existing module/ordinal conventions, and collections remain
budgeted and iteratively disposable.

```text
ResourceDefinitionId = (ModuleId, declaration ordinal)
ResourceDefinition {
  id, origin, family: NominalTypeId,
  parameters: [ResolvedTypeVariable], identity_position: 0,
  input: TypeTemplate, state: TypeTemplate,
  provider: InterfaceId, forwarding_methods: [MethodId],
  state_access: CheckedStateAccessRelation,
  provided: [EffectInstanceTemplate],
  interpreted: [RegisteredForeignInstanceTemplate],
  acquire: ControlledAcquireTemplate,
  handlers: [HandlerTemplate], finish: ControlledFinishTemplate,
  result: ScopeResultTemplate,
  retained_state: ValueRelation, completion: ControlRelation
}
ResourceInstance {
  definition: ResourceDefinitionId, outer_arguments: [Type],
  identity: TypeVariableId, handle: TypedBinder,
  provider_evidence: LexicalEvidenceId,
  provided_instances: [EffectInstance],
  initializer: expression/node, body: expression/node, origin
}
ForeignRegistration {
  library_id, manifest_origin, type/effect/operation identities,
  operation_schemes, roles: Acquire | Borrow | Finish,
  state/dependency/access/postcondition relations,
  constructor identities, safe adapter dispatch
}
```

The concrete source carrier is `SurfaceResourceDefinition`: visibility/name,
ordered parameters, `input`/`state` surface types, `result` type plus one answer
parameter, `provider` interface application, `effect` and `interpret` instances,
acquire binder/body, finish binder/body, handlers state binder/clauses and spans.
`ResolvedResourceDefinition` preserves these as resolved identities and templates;
checking admits `ResourceDefinition` above. Resolution predeclares the opaque
nominal family, resolves the initializer before the fresh instance binders, and
defers outer parameter inference to initializer type unification in elaboration.
Native signatures use canonical native data and state families; controlled
`Provider.state_of` follows a descriptor's sealed state-access relation without
import cycles or nominal spelling tests.

A registry-backed generic descriptor replaces fixed builtin assumptions for new
definitions. Existing builtin descriptors may retain their current optimized
execution. The native library ID selects a registered safe operation; it never
selects a compiler-defined SQLite resource type. No state token or completion
report constructor is sufficient proof of lifecycle authority by itself.

Current module checking retains checked resolved body wrappers; final synthesis
elaborates those bodies again. Provider templates need a separate retained typed
Core table carried from `CheckedModule` through linking, with checked relocation
of references into the final Core environment. The public descriptor remains
body-free. Reusing an ordinary checked body wrapper would not meet P-1's
compile-once contract.

Existing `CheckedGlobalScheme` and `ImportedGlobalScheme` already retain the
defining binder, full constrained scheme, origin and immutable capture/control
summary. Import retention authenticates those facts across routes, and template
capture checking can consume the completed summaries without checking helper
source again. Canonical Core lowering must retain outer type quantification and
the ordered method-dictionary domains of every requirement; the scheme's value
type alone omits those domains.

The private [external-global catalog](../../../src/elaborate/provider_globals.rs)
now projects completed checked modules and admitted imports into those full
Core schemes. It retains defining binders, checked constrained schemes, origins
and shared capture/control summaries, and rejects conflicting duplicate
identities. Nine tests passed, including parity with existing final lowering,
ordered requirements/methods, aliases/re-exports, coherent-fact conflicts,
cumulative work refusal and iterative deep-metadata cleanup. Review during
implementation found missing independent charges for retained interface indexes;
a pre-copy refusal regression failed before the correction and then passed.
Independent conformance review approved the catalog. Rust/API quality review
found a failure path in its reused parent lowering: a substituted method type
lost iterative ownership before fallible application cloning. A constrained
deep-type regression reproduced the precise late-clone stack overflow in an
isolated small-stack process, then passed after retaining the guard through
application cloning and complete method installation. Independent re-review
approved that correction and the catalog's Rust/API quality. Two existing
lowering-budget tests also passed. These checks make no whole-worktree Clippy
claim while Core association work is active. The catalog creates no
graph nodes, admits no occurrences and authenticates no template entry or
publication.

Module-checking drafts currently emit source-scheme global variables and
provisional method occurrences. Final synthesis selects evidence and lowers
global calls to their dictionary ABI. A retained provider template must bridge
that distinction. The active checkpoint selects rewriting typed Core after
authenticated selections, using the complete final lowering environment.
Merely accepting external binder IDs would retain the wrong ABI. Template
publication stays closed until independent checking establishes that lowering
and relocation preserve P-1's compile-once contract.

The next constrained-helper checkpoint will rewrite retained typed draft
occurrences through the existing final dictionary-lowering chain. It must retain
exact occurrence roots, actual type/row arguments, slot identities and origins;
borrow checked selections from pending evidence publication; and rebuild the
graph without retaining obsolete source-scheme children. The lowering
environment needs both admitted globals and separately authenticated
implementation-method producers. Those producers are not ordinary imported
globals. Independent Core checking must derive dictionary order, producer
authorization and occurrence relations from the completed facts and selections.
Dictionary applications stage the ABI; the actual source argument invokes the
helper's capture/control relation once. No provider source replay or early slot
publication supplies that proof.

The proposed regression dependency has `Pass<A>` methods `first` and `second`,
then `Stamp<A>.stamp : (A, Int) -> A`. Its generic `normalize<A>` helper uses all
three methods and is called with native configuration and close-error data.
The final ABI has those three method domains before `A -> A`, in requirement
and declaration-method order. Swapping the equal-typed `first` and `second`
dictionaries must reject even though ordinary arrow types still agree. Batch
evidence also covers exact producers and slots, missing imports, type relocation,
pending-slot failure, cumulative work refusal and checking without helper source
bodies. This pure fixture does not establish hidden continuation-row relocation.
Handler drafts and broader lawful helper control remain subsequent requirements.

After B2's independent reviews, the next connected helper fixture combines
source `Box<A>` data, decreasing prerequisite selections through two `Box`
levels, and a method with its own type parameter. Concrete native configuration
and close-error implementations terminate the selection tree. The helper calls
the polymorphic method at distinct actual types; lifecycle calls wrap and then
project ordinary payloads before native acquisition or completion. This tests
existing language obligations rather than extending implementation selection.

Use the ordinary method-evidence catalog and independent producer expectations
for this slice. The existing lowerer and capture adapters already represent
prerequisite graphs and method-local parameters. Factor their canonical inputs
for imported contextual references; do not fabricate a validated module or
derive producer expectations from emitted anchors. Source data checking must
substitute canonical payloads and newtype representations, respect opaque
source access, and distinguish differently instantiated recursive relations.
A nominal head alone cannot prove independent data. Budget/failure tests and
coherent prerequisite, adapter and payload mutations precede admission.

The ordinary Core variable and scope checks accept graph binders only. T1's
contextual entry therefore needs authenticated checked-global lookup and the
relevant requirement, method, occurrence and authorization facts for evidence
validation. Local scheme headers precede completed body/capture facts, so they
cannot authenticate a published template on their own. Stage those facts until
whole-module publication succeeds. Regression evidence must reject coherently
changed external annotations or dictionary order against unchanged checked
schemes, and must publish no evidence slots or templates after failure.

T1 has three sequential review checkpoints: declaration and template admission;
initializer inference, exact evidence and Core specialization; then actual value
dependencies, completion/control and complete validation/transform coverage.
One implementation owner keeps the shared catalogs coherent. Replace each
pending guard only after its independent replacement proof exists. Runtime
implementation receives the validated interface after all three checkpoints.

### Local-call correspondence before handler drafts

The initial function checker saved and cleared `provider_context` before the
body, then restored it at function completion. Imported globals still recorded
ordinary obligations and capture uses, but `retain_provider_global_occurrence`
used that same context as its recording condition. The source walker traversed
function bodies and recursive initializers, so independent occurrence comparison
detected the missing records.

Give template occurrence retention a lifetime separate from controlled native
phase authority. Retain exact source slots, kinds, type/row arguments, roots and
origins through the existing selection and lowering path. Callable barriers
must continue to clear native phase and StateAccess permission.

Local invocation needs its actual graph and lexical environment, not an invented
global scheme. Reconstruct capture/control facts from draft nodes, canonical
imported summaries and exact selected-method/adapter routes. Reuse the existing
independent typed-call analysis, which tracks actual code, type and value
contexts. Its generated source-wrapper exception cannot authenticate arbitrary
local functions. Unknown captures remain closed until their actual environment
is established.

First evidence admits ordinary pure local forwarders in both lifecycle phases,
then independent captures, aliases and nested calls. Pair them with the same
typed control-bearing helper and coherent target, capture, source-slot and
metadata changes. Preserve exact/prefix/one-short/retry and iterative failure
cleanup. Broader generic/higher-order and internally handled helper contexts
remain subsequent obligations. This map records an implementation target;
the interim unproved-call guard does not complete it.

The first connected paired source test now passes. Plain and staged checking
admit the pure own-parameter forwarder in acquisition and finish. Their source
and retained occurrence counts agree at one and two respectively. The same-typed
helper with internally handled control compiles normally, but both entries
reject at its actual outer invocation with `ResourceEscape`, after occurrence
correspondence succeeds. The proof uses actual local `NodeId` analysis roots
and canonical imported capture facts with the generic typed-call query, without
the generated source-wrapper capture exception. Native phase authority remains
cleared across callable bodies. This is one source-pair receipt, not a frozen
or independently reviewed completion of local-call support.

The next focused batch passes alias captures, nested tuple captures, a source
data constructor carrying the helper, and a recursive forward-to-relay group,
through both entries and lifecycle phases. Exact, zero/17 prefix, one-short and
fresh retry checks pass. Analysis retains only actual `CoreBind`/`RecursiveBind`
initializers available in the flow-call environment, then uses the existing
value-graph relation; environment membership never turns an unknown capture
into independent data. Higher-order argument/return transport remains refused.
Paired captured/control negatives, coherent mutations, constrained occurrence
overlays and independent review remain pending.

A later connected batch passes 49 tests and retains two genuine source failures.
Captured `(config, 41)` / `(error, 41)` data still lacks its proved outer parameter
or native-result pattern value in analysis context zero. A constrained local
forwarder still lacks source-occurrence correspondence over its lowered
dictionary ABI. Both compile normally with complete source ledgers before
rejecting at the actual call. Paired pure/noisy helper captures and recursive
relay, their budget retries and the small-stack capture probe pass. These two
failures identify the next implementation relations; they are not language
restrictions or passing negative cases.

The captured-flow-data correction passes its three-test source batch. Tuple
and transparent data payload captures of input/error data admit the pure helper
and reject the same-typed control-bearing helper in both lifecycle phases.
An opaque local-flow relation is tied to the checked node slice and target. It
permits scalar seeding only for actual Function parameters or Match data binders
whose flow facts are independent data and whose canonical binder types pass the
closed-storage check. Exact local binding initializers keep their value graph;
native state, callable, unknown and unresolved metadata captures gain no proof.
The native close operation is not replayed. Constrained calls and the remaining
mutation, broader verification and review obligations still follow.

The constrained own-parameter forwarder now passes its focused source test in
both lifecycle phases. A capture-analysis projection replaces only authenticated
final ABI occurrence roots with the canonical source callable, ordered type
arguments and selected method evidence. Original structure and complete catalog
validation precede projection. Actual local functions and binding initializers
remain in the projected graph, with an exact original-to-projected node map.
The graph retains instantiated, evidence-bound imported closure values at those
roots; an unapplied generic header cannot supply their prerequisite slots.
These ports do not change ordinary lexical evidence or native permissions.

The compound source test passes nested/concrete constrained forwarding and its
same-typed control-bearing negatives. Statement composition still rejects before
the typed query: the ambient initializer includes the enclosing Connection and
SQL bytes, so whole-tuple storage checking refuses it even when the local
function captures only the SQL binder. Unsupported ambient candidates must
remain unseeded, while resource-limit failures propagate and actual owner
captures remain unresolved. That correction still needs source evidence.

Preliminary review found a genuine dictionary-invocation gap in the projection.
A concrete prerequisite-free producer remains outside a source cut and is
invoked inside a local function with a legitimate imported source occurrence.
The original structural check accepts its identity, but the capture projection
loses its restricted dictionary role and incorrectly admits the call. Generic
reuse probes rejected for unresolved prerequisite slots and did not establish
that role boundary. Retain exact surviving dictionary-variable occurrences as
unproved, separately from legitimate selected-method evidence paths. Review also
found fallible origin cloning after guarded recursive types had been released
into builder argument temporaries. Clone origins before that handoff. Both
findings are active corrections, not frozen approval.

The first correction batch passes 46 external-helper tests, including the
concrete dictionary-invocation probe and its laundering variants. It keeps exact
surviving raw dictionary-variable nodes unknown in the actual capture graph,
while selected adapters use their separate canonical imports. Origin cloning
now precedes recursive-owner handoff. Statement local forwarding remains the
one failing test, with `ResourceEscape` at node 16. Ambient storage refusal was
only its first missing relation; this result does not complete Statement
composition or frozen review.

The diagnostic identifies the remaining Statement cause: shared capture
compilation rejects the surrounding lifecycle's StateAccess node before querying
the SQL forwarder. The local-call proof retains that outer graph to recover real
lexical initializers, but does not invoke its acquisition computation. The
private query needs an explicit unavailable control/data representation for
ambient StateAccess, with rejection if the actual target reaches it. Ordinary
capture admission keeps its existing unconditional refusal. This representation
does not grant native phase permission, replace complete structural/lifecycle
checking, or turn unknown captures into independent data. Lawful SQL-only
forwarding and coherent reachable-StateAccess mutations must prove the boundary.

The corrected batch now passes all 47 external-helper tests. The private
program-bound query retains ambient StateAccess as `Unavailable` control and
unknown data; ordinary compilation still refuses it. Copying preserves the
marker, sequence simplification removes only returns, and actual typed-call
traversal refuses unavailable control. Statement's SQL-only local forwarder
admits with its canonical enclosing association, while missing/wrong associations
and cumulative exact/short/retry cases preserve the prior boundary. This batch
also passes the dictionary-invocation mutations and the small-stack disposal
probe. Review identified a further stored-capture question: a raw producer
occurrence is unknown, but its free capture may still name the canonical imported
binder. An unused raw-producer capture must establish that dependency relation
before broader verification and frozen review.

The extended stored-capture probe now reproduces that gap: concrete mutation 8
binds an unused selected producer inside the local function while preserving
the legitimate normalization call; acquisition incorrectly admits it. Making
only the raw expression unknown does not change a closure capture that still
names the canonical imported binder. The correction retains exact raw occurrence
values as separate private capture ports, alongside the authenticated source
instantiations, so the actual dependency stays unknown. Canonical selected
adapter imports remain available. The earlier 47-test batch predates this
extended probe and does not establish stored-producer refusal.

The exact capture-port correction passes the next 78-test provider/capture batch
(the small-stack child receipt is separate). Concrete and generic dictionary
cases reject all nine invocation/laundering/stored-reference variants in both
lifecycle phases, after their original drafts admit. The graph keeps source
instantiation and raw dictionary proof inputs distinct, then retains their exact
values as capture roots; raw values remain unknown. Same-typed noisy target
rerouting and changed source-ledger nodes, arguments, identities and origins
reject. A renamed helper still checks after its source file is deleted. Statement
rejects direct and unused privileged callable mutations, and actual unavailable
control refuses with exact/prefixed/one-short/retry budget evidence. Final
positive/budget coverage, broader regression checks and frozen review still
follow this focused batch.

The first broad library run aborts on a stack overflow before its summary; no
library or integration totals follow from that command. A serial rerun of the
already-built binary isolates
`deep_capture_equations_and_retained_types_are_stack_safe_and_retryable`. Its
unchanged 64 KiB thread checks 4,096 bindings and then clones/disposes an
8,192-deep retained function type. The focused provider batch's 256 KiB disposal
case does not cover this invariant. Preserve the existing stack/depth bounds and
trace the actual failing phase before repair. Broader verification and frozen
review remain open.

The debugger isolates overflow during unlimited `check_builder`, in the finite
`Graph::build_expression` → `build_computation` → symbol/reservation call chain
at shallow node 3. The preceding budget-128 check completes; retained deep-type
cloning and disposal have not started. This is an ordinary-path static-frame
regression, not evidence of recursive graph traversal or unsafe type disposal.
The new provider graph fields and shared setup carriers increase frame storage.
Reduce that storage without changing query semantics, test bounds or work
limits, then rerun the isolated invariant and the affected batch before broad
verification.

The unchanged 64 KiB invariant now passes. Provider-only lexical, parameter and
capture-port vectors live in one fallible, precharged private carrier; ordinary
graphs leave it empty. This reduces persistent graph frame storage and factors
provider setup into small methods without changing identities or scan work.
Private use charges the carrier allocation; ordinary analysis retains its prior
work accounting. The crossed capture batch passes 121 tests, including the
existing small-stack registration callback case. The crossed provider batch
passes 78 tests, with its separate small-stack child receipt excluded from that
count. The broad rerun remains pending; these batches do not close that gate.

The broad rerun passes 1,419 library tests and 593 integration tests across 31
integration targets. Child process summaries are excluded. The ordinary 64 KiB
and provider 256 KiB invariants both pass, alongside the existing module,
interface, resource, native-buffer and runtime suites. Scoped Clippy identifies
two complex borrowed-input tuple types and an obsolete lint expectation; their
mechanical cleanup precedes the final freeze. The seven-variant local-helper
frontier still refuses its three higher-order argument/return cases. Those
normally checked useful sources remain support obligations, rather than passing
safety negatives or new language restrictions.

The final local-call snapshot is frozen for independent contract, then quality
review. Its 18-source manifest and archive match the worktree before and after
archiving. Eight files differ from the approved B3 guard snapshot; ten are
unchanged and no file is added to that scope. Actual HEAD is the later design
documentation commit, while the product source baseline remains unchanged.
The final rerun retains 1,419 library and 593 integration passes across 31
integration targets, excluding eight child summaries. Scoped Clippy passes with
warnings denied and the existing active-work dead-code allowance; named borrowed
input aliases replace complex signatures without a lint suppression. Formatting
and whitespace checks pass. Constrained local cases and their mutations also
check after the helper source file is deleted. This snapshot grants no public
provider admission, completed higher-order support or S-01 runtime evidence.

Independent contract review approves that exact snapshot with no new findings.
Quality review confirms the dictionary invocation/stored-capture correction,
source projection, charged import scans, ambient unavailable control, native
phase barriers and 64 KiB frame repair, but withholds approval for one inherited
cleanup gap. Four calls in `source_capture_relation_builder` still evaluate cloned
domain/result types or release `actual` before fallible origin cloning. Origin
budget refusal then drops those raw recursive type temporaries before builder
guards apply. The source-occurrence emitter is repaired; the shared wrapper
handoffs need the same discipline. Preserve the candidate archive as unapproved
quality evidence, establish its failure path, preclone origins under guards and
verify a corrected freeze before handoff. Handler source work has not started.

The pre-repair wrapper probe distinguishes the cleanup finding from a reachable
overflow. An 8,192-deep argument refuses at the emitter's existing payload-depth
admission before reaching wrapper assembly. An admitted 128-level tuple payload
on a 256 KiB stack safely refuses at all four legacy origin-budget positions;
exact, one-short and fresh retry checks pass at prefixes 0 and 17, with measured
caller cost 3,540. These observations do not establish an overflow in admitted
input. The source still releases recursive temporaries before later fallible
arguments; repair that ordering while preserving admission limits, then verify
the admitted refusal paths and corrected snapshot. No deeper accepting claim or
weakened stack bound follows from this probe.

The correction prepares origins before guarded domain/result cloning and
releases types only at builder entry. The corrected snapshot changes three
files from the prior local-call candidate; its 18-source manifest and exact
archive match the worktree. The batched verification passes 1,420 library tests
and 593 integration tests across 31 targets, excluding eight child summaries.
Capture and provider batches pass 63 and 116 outer tests. Scoped Clippy,
formatting and whitespace checks pass. The admitted probe retains caller cost
3,540 with a separate unbounded builder ledger; the deep argument remains an
early admission refusal. Sequential contract and quality re-review are pending.

Both independent re-reviews approve the corrected freeze with no remaining
findings. Each verifies the exact archive and all 18 hashes before and after
review. The quality finding is closed: types remain guarded until builder entry,
binder disposal is iterative, and production callers debit consumed builder work
before propagating success or refusal. Approval retains the bounded local-call
scope and all previously pending obligations. Source and Cargo ownership now
passes to the handler-template implementer; the coordinator continues to own
this record and the authoring log.

### Handler draft boundary after B3

After the local-call correspondence checkpoint, the connected source case
checks the existing Connection read clause,
then the Statement tuple/column clause, as unpublished generic templates.
Allocate distinct hidden rigid answer and continuation-row binders before
checking their bodies. Reuse ordinary operation substitution, irrefutable
pattern checking, resume-use checking and clause suffix-row replay from
`finish_handler`. A declaration has no handled client body, so factor the
clause inputs rather than fabricate a handler expression or body value.

Independent resume validation currently obtains its result and row from an
actual handler node. A private draft entry must reconstruct the corresponding
clause contract from the canonical declaration, operation, operand pattern,
state lineage, hidden binders and owned resume. Specialization later produces
an ordinary exact handler and runs ordinary validation. The lifecycle
tail-free row check does not establish handler validity; direct clause demands
and the continuation row need their actual relationship.

Structural scope checking separately derives clause-pattern binders and resume
capability roots from handler children. The private draft needs that canonical
scope relation as well as the resume type/row contract; supplying one cannot
authenticate the other. Keep builder ranges, actual clause records and direct
demands for suffix-row replay. Late clause refusal must unwind pattern binders
and active resumes and leave retained evidence slots unpublished. Allocate hidden
binders before body checking rather than copying lifecycle assembly's later
allocation order.

Positive evidence starts with those real clauses and checked helper/error
mapping. Nearby source and coherent Core negatives cover operation/result
types, coverage, patterns, resume identity/use, hidden type/row binders,
operand paths, authority laundering and state/owner escape. Late failure and
work-limit refusal must leave source slots, templates and descriptors
unpublished. This is a read-only implementation map, not completed handler
support or a new semantic decision.

Handler reconstruction exposes a governing row question before generic draft
assembly. Current row formation makes `{D | rho}` assert that its tail lacks
every known member of D; substituting a whole continuation row containing D
therefore rejects. P-1 names a hidden continuation-row parameter but does not
define it as a residual. Treating that whole row as the canonical tail would
silently exclude useful overlap. The unpublished source draft retains closed
direct demands and the hidden continuation identity separately while a design
amendment is prepared for review. No guessed exclusions or new closed-row
restriction are added. A normalized residual needs an explicit checked
instantiation/recomposition relation, with native demands preserved until exact
interpretation. Handler Core admission remains pending that governed relation.

Independent design review confirms the proposed ordinary-union/residual
calculation, but requires two further relations before the amendment governs
implementation. Discard demands depend on actual captured owners, completion
obligations and surviving interpretation, not formal substitution and a scalar
continuation row alone. Nested handlers also require their own shared output
and owned-resume equations. For an outer continuation requiring H and J, an
inner H handler can produce only J; its resume cannot reuse the outer row.
Existing range replay keeps nonmatching resumes and does not by itself solve
that dependency. The candidate is being revised to retain and authenticate those
inputs and equations, then independently re-reviewed. An authenticated full row
equal to the derived residual remains valid; overlap is refused only when the
required residual relation fails. No governing or normative text has changed.

The revised [handler row contract](semantics.md#handler-template-answer-and-row-instantiation)
now passes independent design re-review and is recorded in the governing
experimental note. It retains actual capture/context inputs and a separate
output equation for every nested handler and its owned resumes. Residual
normalization uses only the current principal union and exact known-member
removal; no new source exclusions follow. This is a design amendment, not
implementation evidence or a change to the normative specification. Conditional
recipe authentication, open demands, capture-dependent completion, nested
replay and finite-work atomic refusal remain implementation obligations.

The source-only handler draft is frozen for contract then quality review.
Its real Connection and Statement clauses pass 10 source tests, including
imported mapping, irrefutable tuple/newtype patterns, resume/native-role
refusals, nested-handler retention and budget cleanup. The actual missing-entry
test first fails with `Internal(InvalidState)` after header checking. The draft
retains an unfinished builder, actual clause records/ranges, state binder,
distinct hidden identities, direct demands and unpublished occurrences. It
does not fabricate a client body, assemble a generic Core root, realize output
rows, or stage imported code/evidence for source-free specialization.

The 19-source manifest and exact archive match the worktree. Three existing
files change from the approved local-call freeze and one test file is added;
the other 15 source hashes and all eight native hashes remain unchanged. The
broad batch passes 1,430 library and 593 integration tests across 31 targets,
excluding eight child summaries. That batch precedes only two mechanical test
assertion fixes; final focused tests, scoped Clippy and 19-file formatting pass
after those fixes. The failed Clippy log was overwritten; its captured failure
summary is labeled as such, and the coordinator observed the two lint messages
in retained session output. Whitespace checks pass. Compiler-ledger costs 262
and 3,230 exclude the builder's separate admission ledger. Contract review
approves this exact bounded source slice; quality review remains active.

Quality review also approves the exact source-only freeze with no findings.
All 19 hashes match before and after; retained types, patterns and builder
ownership preserve the source draft's cleanup boundaries. The approved slice
does not assemble or authenticate a generic Core template. Source and Cargo
ownership is released to the same handler implementer for independent fragment
admission under the reviewed row contract. Actual clause-root inventory, graph
and type scopes, owned resumes, current-state borrow flow and conditional row
recipes need their independent relations; a fabricated client body cannot
supply those proofs. Public execution and the full P-1 obligations remain open.

The first independent-entry probe finishes the real Connection builder at its
actual clause body. Current contextual structural validation then refuses
`Scope/UnknownVariableBinder` at state occurrence node 1. This is an actual
fragment-entry gap after source checking, not a missing helper API or a
fabricated client body. Coordinated graph, type and scope checks need the
canonical state/pattern/clause-root inventory; ordinary unbound-variable
validation remains unchanged. Conditional owned-resume and row contracts are
subsequent checks, not established by this first refusal.

After canonical multi-root and state/pattern scope reconstruction, the same
actual Connection probe reaches `Resume/ResumeMissingContract` at node 4.
Both refusal receipts remain preserved. The borrowed clause-contract check is
being factored for this conditional fragment entry; it must distinguish owned
resume output from operand demands and independently reconstruct nested owner
relations. The current entry returns structural success or refusal only, with
no descriptor or executable admission witness. Native borrowed flow, external
evidence correspondence and retained conditional equations remain open.

The next focused batch retains all 10 source-handler passes, while the actual
Connection fragment now refuses `ResourceEscape` at node 4. This is a later
boundary than the preserved missing-resume-contract refusal. Diagnosis and
authentication of the real fragment flow remain active; this result is not an
admitted handler template or a completed source case.

Diagnosis identifies the exact source-to-Core pattern-binder relation:
`Source(span)` becomes `Generated(BindingLowering, Source(span))`. The entry
now authenticates that generated reason and full causal origin rather than
comparing the two origins directly. The next batch passes 11 tests, including
the actual Connection structural entry and all 10 source-handler tests.
Source/module inventory scans are precharged and clause-root lookup is indexed.
This has not yet passed independent review. Statement fragment admission,
borrowed flow, selected external evidence and conditional row/capture recipes
remain required before a complete handler template can be admitted.

The shared native flow evaluator now has a borrowed handler entry while
lifecycle construction and terminal role checks retain their existing entry.
The actual Connection check invokes this copying-profile flow after structural
validation; the next 11-test batch passes. It checks exact Borrow roles,
registered state operand lineage and independent copied resume arguments.
This is not a general classifier for arena or view results. Statement, local
nested-handler lineage, StateAccess operand provenance and imported evidence
remain active evidence obligations; no admission witness or public contract is
published by this batch.

The next actual-fragment batch passes 14 tests, including Statement's three
real clause roots, tuple/newtype lowering and provisional nested-owner checks.
It preserves one new refusal: a source-checked Current `StateAccess` variant
rejects at its actual StateAccess node. Canonical header associations and
operation-domain resource paths must authenticate operand provenance before
that path can enter the shared flow. The nested result-row equations are still
provisional, and local nested-state aliases remain a useful control/lineage
frontier rather than an escape rejection result.

The Current StateAccess correction reconstructs associations from the defining
module and seeds resource-input provenance from canonical clause-domain paths.
Pattern binding and local flow preserve those paths; an access operand must
match its actual path before native state lineage is accepted. The next focused
batch passes 15 tests. Coherent wrong-path/owner mutations, wrapped inputs,
selected helper transport, cumulative budgets and independent review remain
required; this positive alone does not authenticate the broader frontier.

The next 17-test batch preserves those 15 passes and exposes two useful
source-checked positives that still refuse: a direct StateAccess alias fails
with `ResourceEscape` at its real clause root, and an imported pure error mapper
fails with `Scope/UnknownVariableBinder` at the helper occurrence. Source-root
lowering correspondence and authenticated imported entry are the next
boundaries under diagnosis. These refusals do not establish prohibited escape;
the alias and helper cases remain support obligations.

Strengthening exact source-root correspondence exposes the retained
`TypeChecking` wrapper as well as block binding lowering. The next extended
batch passes 12 tests and refuses five positives. A focused diagnostic confirms
that the ordinary Connection body has
`Generated(TypeChecking, Related(Source(body.span), [clause.span]))`.
The entry must authenticate this actual checking cause and its precise related
context. The prior 15-test pass is historical evidence, not verification of the
current correction; all new refusal receipts remain preserved.

The corrected 17-test batch passes. Source-root checks authenticate the exact
ordinary `TypeChecking` context and binding/recursive lowering causes, including
source binder identities and initializer/annotation spans. The imported mapper
uses existing plain-import type, origin and capture reconstruction in the
canonical multi-root context, without a synthetic client body. Local non-binder
patterns, lexical evidence and nominal wrappers still need their source-root
correspondence; selected evidence and per-owner conditional row/capture equations
remain open. This result is unreviewed and returns no template witness.

The next mutation and cumulative-work batch passes 21 tests. Mutations cover
canonical owner, clause/root inventory, pattern and body provenance, hidden
binder roles, state types, resume ownership and rows, native direct demands and
StateAccess metadata. Exact, one-short, nonzero-prefix and fresh-retry tests
exercise the independent checker ledger; they do not measure source checking or
builder work. A proposed Enclosing mutation is identical to Current for the
Connection fixture and supplies no distinct wrong-owner evidence.

A separate actual imported-helper mutation then exposes an authority gap:
replacing the real mapper with a different canonical imported binder of the
same type and capture contract is accepted. The retained failing regression
is `/tmp/ash-h1-handler-wrong-helper-gap-actual.log`; the earlier similarly
named receipt failed only in test setup. Matching type and origin roles does
not establish the actual source VALUE occurrence. The correction independently
collects the complete imported-variable inventory from the resolved handler
clauses, including aliases, nested bodies and unused stored values. Exact
canonical binders and full occurrence origins must correspond one-to-one
before imported scope is granted. The corrected 22-test batch passes.

The following batch passes 25 tests. Actual Statement StateAccess succeeds at
all three clause roots through tuple operand paths. Called and unused stored
mapper mutations reject; the corresponding aliases and stored values remain
admitted. A wide fixture checks 64 actual clause roots, 66 source rows and 66
module rows with cumulative independent cost 23,853 and exact, one-short,
prefix and fresh-retry results. These are unreviewed private-entry observations,
not complete conditional row/capture admission or public template authority.
Connected regression checks and selected evidence admission follow.

Connected regression checks then pass 141 provider library tests and six
ordinary effect Core integration tests. Child-process test summaries are not
added to the 141-test count. The eight-file reviewed native manifest remains
unchanged. Markdown lint, changed-document diff checks and relative links pass
for the tracking update. This evidence does not replace broader verification
or independent review of a frozen handler-admission checkpoint.

### Handler selected-evidence boundary

The constrained copied-error mapper first fails source interface selection
because its implementation was not explicitly imported. After the ordinary
`import helper (impl Pass)` supplies that implementation, source checking and
builder completion succeed, but independent plain entry refuses
`ResourceEscape` at the actual root, node 7. The genuine entry-gap receipt is
`/tmp/ash-h1-handler-selected-helper-entry-gap.log`; the preceding receipt
establishes only the fixture's missing import.

Read-only inspection identifies the existing lifecycle staged authenticator as
the reusable mechanism. Source preparation must retain the pending publication
and actual occurrence inventory without installing slots. Independent checking
must authenticate that inventory against the defining module's complete
handler VALUE inventory before granting selected ABI scope. The existing
catalog, selection, dictionary producer, provenance and capture checks remain
required.

Both source ABI rebuilding and external capture reconstruction currently walk
one root. Their handler path must retain the actual clause-root forest and
off-graph state/pattern binders, using the existing builder's binder reservation
before materialization. An invented enclosing handler cannot supply these
roots. This is an inspected integration requirement, not implemented or reviewed
staged handler admission. Existing closed-selection limitations do not replace
P-1's required generic evidence and conditional row/capture support.

The first selected-forest implementation batch passes 27 focused tests. The
actual constrained copied-error mapper now compiles selected ABI and passes
independent private checking. Connection, Statement and newtype clauses retain
their actual roots, while state and pattern binders are rebuilt in the new
arena after reserving their identities. Source preparation is shared without
changing the source-only H0 path. Pending selections remain unpublished, and
the original entry-gap receipt is preserved. Later-clause forwarding and stored
selected VALUE cases, catalog/occurrence mutations, cumulative compile/check
limits, broader verification and frozen independent review remain required.
This result returns no conditional template witness or public authority.

The wider third batch passes 28 tests and fails in two test fixtures: the local
forwarder is not valid surface syntax, and requested catalog variants cannot
mutate this fixture's absent domain/adapter records. The fourth receipt reaches
a genuine useful case: storing the mapper unused passes, but calling the local
forwarder in a later Statement clause refuses `ResourceEscape` at Apply node
90. The separate catalog-fixture failure remains setup evidence.

Diagnosis finds that capture compilation scans the complete projected forest
and requires every resume to have an ordinary Handler node. The body-free
outer provider deliberately has no such node. Its private query path now marks
unmatched resumes as unavailable control; reaching that control still rejects,
and ordinary capture compilation still rejects missing owners. Matched nested
handler owners retain their existing relation. This does not create a handler,
completion capability or conditional row witness.

The corrected selected budget batch passes 32 tests. It covers the two ordered
requirements and methods at all Statement roots, called forwarding and unused
stored values, nine occurrence/producer/argument/publication mutations and the
applicable wrong-method-scheme catalog mutation. The closed fixture has no
domain/adapter entries, so inapplicable variants do not count as refusals.
Private checking also succeeds after the helper file is deleted, using retained
facts. Measured type-work costs are 7,047 for compilation and 28,122 for checking;
builder and interface-constraint ledgers remain separate. Exact, one-short,
nonzero-prefix and fresh-retry paths retain unpublished evidence. Actual-graph
ordinary/query/matched-owner regressions, pattern ownership, stronger refusal
classification, broader verification and frozen review follow. This remains a
staged private checkpoint, not full generic or conditional admission.

An actual-graph query regression passes separately: unmatched outer resumes
remain unavailable to provider queries and invalid in ordinary capture
checking, while matched nested owners retain their exact relation.

The first nested/small-stack batch aborts before a complete summary. A marker
probe establishes that it overflows during fixture parsing/import setup before
private checking. The corrected probe prepares fixtures and compiles drafts on
the normal test stack, then runs actual retained private proof, refusal, retry
and disposal on 256 KiB. That scope passes; it proves neither small-stack
compilation nor setup. The corrected batch passes 33 tests but retains one
useful nested-prerequisite refusal: source and ABI compilation succeed, while
independent checking reports `Registry`.

The nested fixture exposes an order assumption in contextual registry checks.
Canonical imported closure retention visits the later Box declaration before
the earlier Completion declaration; exact mirror comparison succeeds, but the
range check treats that retention order as source declaration order. Contextual
range indexing now derives source order while retaining canonical comparison,
valid source/ranges, disjointness, IDs and names. Ordinary noncontextual order
rules remain. The nested case then passes its focused test. Charged key/index
work, coherent range/provenance mutations, broader verification and frozen
review still require their complete receipts before this correction is
approved.

The coherent staged batch passes all 36 focused tests. Updated type-work costs
are 7,093 for selected compilation and 29,110 for checking; the 64-root fixture
costs 24,637 and the 64-imported-nominal fixture costs 10,267. Caller prefixes,
one-short resource classification and fresh retries pass. Actual nested
prerequisites exercise applicable catalog domains/adapters rather than counting
mutator setup failures. Two separate low-level tests preserve ordinary ordering,
reject mirror-identical overlapping contextual ranges and account for sorting
64 reversed keys with 32-deep primary origins at exact work limits. The actual
query-owner regression passes separately.

Scoped Clippy retains seven initial findings and a subsequent unused-import
finding in separate receipts. All corrections pass the third Clippy run with
warnings denied and the existing active-T1 dead-code allowance; no new lint
suppression is introduced. The 36-test result precedes those mechanical
corrections. One final broad batch checks the resulting source before an exact
20-file freeze and independent contract/quality review. Conditional solver
ownership remains untouched until this staged checkpoint is reviewed.

The first broad run finds three ordinary exact-work regressions. Contextual
sorting now returns a borrowed iterator for ordinary registries, and pattern
origin charging is confined to provider supplemental rebuilding. The corrected
run passes all 1,459 library tests with the original ordinary allowances. A
separate explicit integration batch passes 1,536 tests across 93 targets,
excluding three nested child summaries. Architecture checking separately
passes 29 tests and fails three; it was not part of the earlier 31-target batch.
Those failures and the carrier inventory remain explicit verification gaps.

The exact 20-file staged snapshot is frozen in
`/tmp/ash-h1-handler-staged-frozen-code.sha256`. Its archive SHA-256 is
`3efa57cdeb3d613bd16c669b069c79d28a5e420bdd448366c02b0cd5b87f1448`.
The root independently verifies all file hashes and the archive before assigning
contract review, followed by quality review. Source and Cargo remain stopped
during review. This snapshot returns unpublished structural checking only;
it creates no conditional template witness or public admission authority.

Contract review traces a possible independent-admission gap: a nested ordinary
Handler targeting the canonical registered native instance could remove a real
native request from direct demands. Source checking rejects that handler target,
but neither source provenance nor ordinary signature and least-row agreement
substitutes for independent authority checking. The sole source/Cargo owner is
authorized to add an isolated coherent mutation probe while preserving the
original snapshot. Acceptance or the exact contrary refusal must be recorded
before a correction and revised freeze. Quality review and architecture work
wait for this contract question.

The third probe reaches independent checking. Its ordinary nested-handler
baseline passes, while the coherent registered-native target graph returns
`Ok(())`; the rejection assertion fails with exit 101 in
`/tmp/ash-h1-native-handler-probe-third.log`. Using independent Unit report
payloads in the source fixture avoids the unrelated source setup frontier;
the mutation then substitutes canonical native state arguments and signatures
in retained Core. The original staged snapshot is rejected. The shared
independent Handler validator must reject registered foreign targets while
preserving ordinary nested handlers and native direct demands. The compiled
forest variant, revised verification and contract re-review precede quality
review.

The compiled-forest negative case independently confirms the same original
acceptance in `/tmp/ash-h1-native-handler-probe-compiled-red.log`. The shared
`validate_effect_handler` check now rejects registered foreign targets at the
actual Handler node. Both plain and compiled variants reject with
`ResourceEscape`, while their ordinary nested-handler baselines pass. Exact
refusal work, one-short resource refusal, charged prefixes, fresh retries and
empty pending slots are checked. The corrected library batch passes 1,460
tests, excluding six nested child summaries; the affected integration batch
passes 169 tests across eight targets. The earlier 1,536-test integration run
belongs to the original snapshot, not this correction. Final scoped checks
and a revised freeze remain prerequisites to re-review.

The corrected snapshot is now frozen in
`/tmp/ash-h1-handler-staged-native-target-corrected-frozen-code.sha256`, with
archive SHA-256
`f3e5a28aeef069e92c65225205a2379977da98a3a5ae9f5825a8a085d10e746c`.
Only the shared validator and the two test-containing files differ from the
original 20-file snapshot. The final 37-test receipt includes the budget
assertions; Clippy, formatting, diff and unchanged native hashes pass. The root
verifies all 20 source hashes, the new archive/context and the preserved original
archive before assigning contract re-review. Source and Cargo remain stopped.

Re-review confirms that the target denial closes the original finding, but
identifies new uncharged work: `ResolvedRegistry::foreign_effect` scans every
foreign module's effect vector. The validator invokes it for each ordinary
Handler. Once-paid registry authentication does not cover repeated membership
scans; the fixed refusal ledger also cannot prove wider scans are charged.
The sole implementation owner is assigned a charged canonical membership
check and deterministic empty/wide work cases before the next freeze. Limits
and handler semantics remain unchanged. Quality review remains pending.

The shared accounted membership helper now charges one unit per visited module
and its complete effect-vector length before membership comparison. Both the
ordinary Handler target guard and the canonical provider-entry check use it.
The first corrected batch passes 38 focused cases. Valid loader/import fixtures
measure empty inventory at zero, the narrow SQLite inventory at three, and 64
additional eight-effect manifests at 579 units for a miss or last-member hit.
Exact/one-short limits, a charged prefix and fresh retries pass. The actual wide
handler entry costs 61,249 units; its exact/refusal/retry and empty-slot checks
also pass. Native-target refusal now costs 5,816 units with its existing paired
baselines and refusal cases retained. Broader verification and re-review remain
pending; the source-identified unpaid scan is not presented as a fabricated
pre-correction raw failure receipt.

The accounted 20-file archive is frozen with SHA-256
`18f4b22ba59bd794a431aaf8396cee4071f413a1821f845d2a651ffd76969c2a`.
Final verification passes 38 focused tests, 1,461 library tests excluding six
child summaries, 169 affected integration tests across eight targets, scoped
Clippy, formatting, diff and unchanged native hashes. Contract re-review closes
both findings and approves only the declared unpublished structural component.
A fresh quality reviewer is assigned while source and Cargo remain stopped.

The final selected fixture costs 7,056 compilation and 29,117 checking work
units. Review catches a context receipt that still records the historical
29,113 value; the metadata is corrected atomically and the old context retained.
The source archive and manifest are unchanged. No conditional witness,
publication, runtime, architecture completion or full-plan completion follows
from this contract approval.

Fresh quality review finds one remaining proportional scan in the new handler
entry: `canonical.foreign_state` visits module state inventories without a
charge. The wide canonical import case reaches this path, but its exact total
does not account for the omitted lookup. A charged canonical state lookup or
index, deterministic hit/miss accounting and actual-entry refusal/retry checks
are assigned before revised contract and quality review. No other actionable
findings emerge in the reviewed ownership, iterative disposal, allocation,
forest, source correspondence, capture-query, native lineage or evidence paths.
The quality rejection leaves this checkpoint unapproved for continuation into
architecture work until the correction is reviewed.

### Architecture inventory boundary

The architecture checks enforce complete Type/Kind carrier inventories and
narrow Core/evaluator interface-evidence identifiers. Their checks must remain
intact. An isolated reproduction of the existing scanner stops on an ambiguous
`NominalTypeId` under a provider glob import. Temporary explicit-import
simulation exposes older provider carrier omissions and new handler carrier
obligations. The frozen H0 archive covers 19 files; copied surrounding files
do not independently prove their historical contents.

After staged contract and quality review, complete a coherent inventory/import
checkpoint before conditional solver changes. Classify each real field and
alias by owned, borrowed or shared retention, and verify its existing disposal
gate or correct a missing one. Remove unused comparison machinery if source
references show it is dead; do not enlarge a closed identifier inventory merely
to retain unused code. Run the architecture checks with their existing invariants and affected
regressions against the resulting source. Until then the staged evidence is not
a full architecture or product-verification pass.

The imported-method catalog comparison is live compile-time authentication,
with a call retained in the frozen H0 source. Its inventory correction must
remain specific to that path and identifier; it creates no evaluator dispatch.
The scanner also needs faithful modeling of owned-or-borrowed `Cow<Type>` and
module-path aliases before its discovered field set can be treated as complete.
Add positive and negative scanner fixtures for those relationships while
preserving bidirectional inventory and narrow mutation checks.

### Conditional row and capture retention

The inspection below records the earlier provisional-template checkpoint. Its
uses of “current” refer to that inspected source, rather than the integrated
common implementation. The [current checkpoint](#current-checkpoint) records
later checked recipes and the remaining actual request-input work.

Read-only inspection confirms that the current fragment entry authenticates a
provisional graph. Provider resumes contribute their operand rows, and direct
demands are compared with ordinary least-output reconstruction. Hidden rho is
not permitted in graph annotations. These checks do not establish the
[reviewed conditional relation](semantics.md#handler-template-answer-and-row-instantiation).

The current source preparation retains scalar direct demands and actual clause
Core but no conditional row/capture equation owner. Ordinary discard synthesis
creates a deferred row and a `CleanupRows::Equation::Discard` entry. Consuming
the elaborator without transferring or independently reconstructing that
relation loses the solver's conditional ownership. Unknown capture and close
demands cannot be replaced with a guessed empty context. The retained relation
must authenticate its actual code, handler/resume ownership, child row
operations and capture/completion/interpreter inputs.

Ordinary range replay updates one matching handler/resume pair and preserves
other resumes. Full nested specialization must instead refresh every affected
resume and descendant. Existing whole-graph cleanup replay supplies useful
bottom-started iteration and rollback, but its owner map expects real Handler
nodes; it cannot directly stand in for the body-free outer provider entry.
Neither an invented client body nor widening hidden-rho scope proves the
missing relation.

The inspected next boundary remains the approved contract: authenticate the
actual equation/root correspondence, retain unknown capture inputs, derive the
actual body remainder and capture context at specialization, solve each
handler's distinct output, check the derived residual and recomposition, and
require ordinary independent Core validation. Closed direct demands are an
initial realization, not a replacement for generic admission. Native demands
remain until separately authenticated exact interpretation. This map supplies
implementation guidance only; conditional admission and its evidence remain
pending.

The read-only implementation plan identifies an owned checked recipe as the
next coherent authority checkpoint after architecture review. A further
`Result<()>` structural entry would leave the same retention gap. The names
below are implementation choices; the reviewed semantics remains governing.

1. Retain or reconstruct source row obligations before consuming the
   elaborator. `CleanupRows::Equation::Discard` stores a `usize` builder
   ordinal, so qualify its source arena and relocate it through the existing
   `LoweredProviderForest.correspondence`. Preserve union, removal, equality
   and pending-position relationships; reject missing or unrelated mappings.
2. Build a flat recipe with checked recipe-local equation indices, actual
   clause roots, per-handler output owners, and each resume's handler, owner,
   root and operand relation. The provider entry identifies its real roots
   without inventing a handled body. Independently reconstruct equations from
   actual Core and canonical operations/imported selections. Authenticate
   every deferred node/type position; ranges and draft claims grant no authority.
3. Represent conditional continuation/capture inputs with a typed port tied to
   the actual owner/root relation. Preserve hidden answer and residual-row roles
   separately from full epsilon, per-handler outputs and c. Ordinary provider
   queries keep their missing-owner refusal. Unknown capture/completion and
   surviving-interpreter inputs remain conditional until actual instance facts
   establish them; they are not empty facts.
4. Return an owned `CheckedHandlerTemplate` only after source, structural,
   phase, state/native, evidence, control and reconstructed recipe checks pass.
   Its private constructor retains immutable typed code and recipe without
   self-referential borrowed proof fields. A body-free `HandlerRowContract`
   retains template-scoped contracts; arena-local node identities and executable
   correspondence stay with the checked code. Copies do not create authority.
5. At actual specialization, borrow authenticated kind-preserving substitutions
   and evidence plus the real boundary/capture context. Derive epsilon and c;
   solve every output, resume and descendant equation with ordinary principal
   union/removal. Check the outer candidate against ordinary least output,
   derive r and its recomposition, then substitute rho. Refresh the whole graph
   transactionally and require ordinary independent Core validation. No source
   replay, unresolved equation or guessed capture context crosses that boundary.
6. Retain checked code/contracts through the existing module and linking path,
   then stage them with lifecycle templates, descriptors, summaries and evidence
   before the existing publication commit. Actual instances and public use
   follow this admission; early resolved resource facts are not certificates.

Evidence must cover the reviewed closed/open overlap, principal open D,
authenticated equal residual, nested outer/inner resume and c-dependent cases,
plus coherent equation/owner/relocation mutations and source deletion after
admission. Native demands remain present. Work scans, retention, substitution,
fixed-point passes and final validation charge cumulative caller work, with
builder work separate. Exact/one-short prefixes, fresh retries, late rollback,
empty publication tables and iterative disposal remain required. Every new
owned, borrowed, shared or mixed carrier receives a source-attached architecture
profile before the checkpoint freezes for independent contract and quality
review. Planning completes none of these implementation obligations.

Read-only capture analysis identifies a separate private handler entry at the
existing value graph and capture compiler. The current provider callable query
remains tied to `ProviderLocalFlow`; its missing-owner refusal is unchanged.
A conditional clause port must authenticate template, handler, resume,
operation and root identities plus Q, hidden A and hidden rho roles. Full
epsilon, the owner's Omega and c use distinct internal input/output identities.
Current capture compilation allocates owner tokens from real handler clauses;
completion then needs the actual captured segment, event and contexts. A new
token alone cannot establish those facts, and mapping absent control to return
would invent empty c.

The retained recipe must preserve clause, cleanup, closing, handler and resource
topology, closure dependencies and exact interpreter precedence. Analysis-local
code/context ordinals are not portable identity claims. Local relationships
within the actual forest can be reconstructed now; the missing client capture,
activation, substitutions, full epsilon and surviving outer interpreter remain
conditional. A nested Unit handler with discard supplies the initial typed
case; a real armed cleanup callback adds a nonempty close-demand case. Concrete
specialization must resolve all conditional transitions before ordinary
capture/completion validation. The missing boundary API is an implementation
gap under the reviewed contract, not a new semantic rule.

The first compiled equation fixture exposes a provisional replay distinction.
Its actual discard and nested output retain one inference tail; a separate
pending union includes the exact native demand. The enclosing Bind annotation
still retains the discard tail while its second child carries that demand.
Independent correspondence therefore authenticates the actual child equation
and its pending rewrite, rather than expecting the provisional annotation to
equal a solved output. Merely allowing that tail would lose the native demand.
The fixture still fails ordinary row checking; it establishes this input shape,
not conditional admission. Positive correspondence and coherent demand-erasure
cases belong to the next deterministic verification batch.

### Whole-module publication boundary

The existing module checker stages body evidence and freezes public exports,
then reserves the remaining checked-body storage before publishing slots.
Provider checking must prepare and authenticate every descriptor, executable
template, public hidden closure and retained carrier before that same commit.
A later unrelated body failure or allocation/work refusal returns no checked
module or summary and leaves every source slot empty. Work already consumed
is not reset on refusal.

At the start of this slice, normal module checking and final checked-group
elaboration reject resource declarations, summary authentication rejects
unproved resource facts, and checked modules have no provider template table.
The active implementation replaces those declaration guards with independently
checked groups and body-free certificates. Receipt 48 supplies focused normal
link/Core/evaluation evidence, as recorded above. Complete local-helper and
transaction evidence, a final freeze and independent reviews remain pending;
opening declaration checking does not admit resource instances.

`CheckedModule` retains ordinary checked resolved bodies, which final synthesis
elaborates again. The active provider table separately retains already checked
typed Core through checked module grouping and linking. Final occurrence
relocation and actual instance specialization remain subsequent work.
The defining module supplies code; imports and
re-exports preserve body-free contracts and defining template references.
Required imported facts must survive preparation before `CheckedModule::new`
consumes them. Project completed pending global facts without manufacturing a
checked module or committing evidence early.

The front-end `ResourceTypeFact` carries no lifecycle authority. Public-summary
authentication must require its separately checked certificate, covering
the complete descriptor and hidden closure before opening that guard. Evidence
includes helpers declared after their resource, aliases/re-exports/diamonds,
client checking without dependency source, and separate failure for missing
executable code. Removing or poisoning retained provider resolved bodies after
checking must not trigger source replay. Coherent descriptor/template, hidden
binder, native lineage, capture/control and dictionary mutations must reject.
Private acquisition/finish drafts and local header associations do not prove
this publication boundary.

Read-only lifetime inspection adds a retention/relocation obligation.
`EvidenceSlot::storage_id` is derived from its Arc allocation. Pending handles
and retained source occurrences currently pin it; Core catalogs retain only
the numeric ID. Ordinary linking keeps checked resolved bodies through final
synthesis, and ordinary transforms remap graph nodes without renaming those
occurrence IDs. A body-free owner can preserve distinct original allocations
after provider bodies are removed. It does not give repeated specializations
of one template distinct occurrence identities or substituted facts.
Independent design review supports the explicit relocation direction now
recorded in [semantics](semantics.md#evidence-occurrence-retention-and-specialization):
retain source provenance, create separately owned final identities for copies,
and validate each specialization against the recorded selections and admitted
defining context. Final catalog preparation precedes builder sizing.
Same-argument copies, generic dictionary scopes, complete index relocation and
acyclic retention remain required evidence. This approves the experimental
direction, not its implementation; current pinned B3 drafts are unaffected.

### Runtime boundary after validated T1

This dependency map records the earlier T1 inspection before executable foreign
bindings and provider activations. Its evaluator limitations describe that
checkpoint. The [current checkpoint](#current-checkpoint) records integrated
SQLite/arena execution and later control observations.

R1 receives admitted descriptors and executable templates, exact provided and
interpreted instances, operand paths, native operation registrations, owned and
retained identity coordinates, capabilities, report roles and complete control
contracts. Resolved headers or private drafts cannot supply runtime authority.
The current evaluator has builtin resource owners and structural capture,
resume, discard and disposal, but no registered provider execution or native
state access. Its singleton activation lookup also cannot identify both
Statement parameters. Extend the generic resource path from the validated
coordinates; SQLite-specific operation code belongs in the safe adapter.

Preflight and reserve storage before native acquisition. Move a successful
guard into the owner frame only after publication succeeds; late failure
destroys unpublished state once and never enters the body. Completion preserves
the body value while running the checked finish template. A retained finish
report removes source access and quarantines the owner with its native
dependencies; its storage and host teardown require accounting. Capture and
resume move ownership without reacquisition, and admitted discard uses the
existing structural completion order.

The safe adapter now also supplies the registered Connection diagnostic's
copied status data; independent review and 41 native tests cover that host API.
Its registered operation still needs evaluator dispatch. S-01 must
run the retained source bundle through the public driver, independently validate
generated/transformed Core and observe native statement-before-connection
release. Repeated and simultaneous instances, real acquisition failures,
empty SQL, preflight/late-publication refusal and consumed/retained completion
are required observations. This map records dependencies, not runtime support.

## First source fixture

The [source library](../../../tests/fixtures/provider-experiments/sqlite-copying/sqlite.ash)
declares and exports the resource assemblies and effects in `semantics.md`.
It re-exports native configuration and lifecycle error families,
defines its own operation result and error families, and provides pure functions
`memory : Unit -> OpenConfig` and `select_parameter : Unit -> SqlText`. The
latter constructs actual UTF-8 bytes for `SELECT ?1`. Current equational globals
require a positive pattern count; these are functions called with `()`, rather
than unimplemented global value definitions. The client fixture has no direct
native calls. The [client](../../../tests/fixtures/provider-experiments/sqlite-copying/entry.ash)
uses an ordinary generic helper with explicit argument, row and provider
requirement. The originally planned four nested matches exceed the existing
frontend depth budget; that source is retained in
[entry-deep.ash](../../../tests/fixtures/provider-experiments/sqlite-copying/entry-deep.ash)
as a frontend failure, not a resource-safety rejection. Factoring preserves the
query, call order and nested result:

```text
import provider as Provider
import sqlite as Sqlite

main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>>
main () = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
resource Sqlite.Statement<S> stmt = (db, (Sqlite.select_parameter ())) {
match Sqlite.bind_int (stmt, 1, 42) {
Sqlite.Ok(()) => after_bind stmt
Sqlite.Err(error) => Sqlite.Err error
}
}
}

after_bind<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
after_bind stmt = match Sqlite.step stmt {
Sqlite.Row => match Sqlite.column_int (stmt, 0) {
Sqlite.Ok(value) => match Sqlite.step stmt {
Sqlite.Done => Sqlite.Ok value
Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
Sqlite.StepError(error) => Sqlite.Err error
}
Sqlite.Err(error) => Sqlite.Err error
}
Sqlite.Done => Sqlite.Err Sqlite.MissingRow
Sqlite.StepError(error) => Sqlite.Err error
}
```

Expected normal observation is
`Completed(Completed(Ok(42), Closed), Closed)`, with statement finalize preceding
connection close. Do not assert a display string until actual constructor display
has been checked. S-01 still requires the source to pass through
`driver::run_path` and its generated and transformed linked Core to pass
independent validation. Parser or resolver preparation does not establish those
obligations. The initial execution test must fail because P-1 support is
missing, after native smoke setup passes.

Pair this fixture with wrong initializer type, wrong connection parameter,
escaping statement, hidden capturing closure, forged provider evidence,
duplicated finisher and fabricated state/publication. Repeat with two live
connections and repeated activation at one source site. Native counters observe
actual acquisition/release, not a manually constructed trace pretending to call
SQLite.

## Work ownership and dependency order

Owners are roles assigned by the coordinating task. One writer owns each shared
file at a time. A listed seam transfers only after its current owner reports the
interface and verification. Tests are partitioned by suite to avoid shared edits.

Batch related edits and focused suites at meaningful checkpoints, following the
user's 2026-10-02 instruction and 2026-10-03 goal-completion direction. Prefer
public source-to-runtime scenarios and integration coverage. Add internal tests
when required evidence or an observed bug needs them, rather than for every
small implementation change. Coordinate Cargo runs so agents do not queue
duplicate compilations of the same workspace. Retain observed failing causes
and rerun the affected regression batch after correction. Run broader checks at
completed capability checkpoints, for unresolved shared regression risk, or when
a failure requires them. Batching changes the schedule, not the contract,
independent reviews or required exit evidence. Progress reports lead with
completed source behavior and the next blocking execution boundary.

| Work | File ownership | Depends on | Exit evidence |
| --- | --- | --- | --- |
| P0: candidate contract and registry schema | Design owner: `semantics.md`, this record; coordinating task owns plan updates. | Context and independent seam review. | Typed declaration/instance/report/native authority contract; no compiler spelling with an unstated type. |
| N0: native setup and safe adapter | Native owner: `foreign-adapter/`, root Cargo membership/lockfile, native environment report. | Recorded ABI inputs and native contracts. | Matching headers/library, smoke calls; partial-owner guards, consumed finalize and retained close tests. |
| F0: declaration/registration descriptor | Front-end owner: `surface.rs`, `resolved.rs`, registry/module structures. | P0. | Generic identities, templates and imports; no third SQLite resource kind. |
| F1: parse and resolve declarations/instances | Front-end owner: lexer/parser, `resolve.rs`, `module.rs`; syntax/module suites. | F0 and registration interface agreed with native owner. | New source positions resolve with input-before-binder scope and preserved defining origins. |
| T0: authenticated foreign registration | Registration owner: foreign manifest modules, loader/driver configuration and resolved registration facts; foreign module suite. | P-1 admission contract and F0/F1 schema. | Generic registered imports, canonical signatures/roles/state/result facts and defining identities; no source spelling grants privilege. |
| T1: check and elaborate P-1 | Typed/Core owner: `kind.rs`, `types.rs`, `elaborate.rs`, evidence validation, Core effect/dialect/validation/transform and capture analyses; typing/Core suites. | F0/F1 fixtures and T0 authenticated facts. | Controlled lifecycle roles, exact handler types/rows, independent descriptor/instance validation and mutation rejection. |
| R1: execute P-1 | Runtime owner: evaluator machine/value/disposal, driver and executable adapter registration/dispatch; runtime suites. | N0, validated T1 Core interface and reviewed typed binding/ownership handoff. | Authenticated callable binding with missing/mismatched registration refusals; S-01 source-to-native path, guarded publication, reports, structural completion/capture and safe failure teardown. |
| S2: copying SQLite library | Library/runtime owner: Ash library fixtures and runtime/module suites; checker changes return to current seam owner. | S-01 complete. | S-02..S-05, actual bytes/null/empty distinction, temporary-file persistence, authenticated generic importing helpers. |
| A0: quantified coverage/layout contract | Design/Core owners: selected arena contract and descriptor extensions. | S-01 plus review. | Handler template coverage, sealed layout dictionaries, relational allocate/load summaries and failure policy. |
| A1: arena implementation/library | Native owner: backing storage; typed/Core owner: layout and relations; runtime owner: arena execution; separate arena suites. | A0, stable generic resource path. | M-01..M-05 with real payload storage, sharing, safe projection, deep-copy costs and rejected owner transport. |
| C1: completion/control composition | Typed/Core/runtime owners in their files; `provider_control.rs`. | P-1 completion and arena ownership. | M-06 and compatible SQLite capture/resume/discard, independent validation, required action-before-release order. |
| X0: retained/view contract review | Design owner: `semantics.md` only. | Copying and arena observations. | Release points, invalidation, branch joins and captured access specified before code. |
| X1: retained/view implementation | Existing seam owners; `foreign_memory_interactions.rs`, composed control suite. | X0, A1, C1. | X-01..X-04 positive and rejection cases; no silent copy in the borrowing candidate. |
| E1: compare assembly and authoring tools | Coordinating/library owners: `results.md`, `blueprint.md`, `tooling.md`; one small root-workspace tool if evidence warrants it. | All cases observed or explicit counterexamples retained. | Measured costs, useful API/friction comparison, native-build/contract report compared with manual workflow; blueprint applied to the arena boundary and a contrasting foreign-API walkthrough. |
| D1: adoption artifacts | Coordinating/design owners: adoption report and proposed semantic/architectural artifacts. | Successful evidence or clearly bounded partial result. | Current behavior/delta, trust assumptions, compatibility, target support and coherent proposed product checkpoints. |

Do not parallelize a caller change with an unagreed descriptor rewrite. The
front-end and typed/Core owners coordinate `resolved.rs` schema changes through
the front-end owner. Runtime changes begin against the validated Core interface.
Native safe APIs may proceed independently while their signatures are recorded.

Preparation of A1's physical arena block/table completed independently in
the existing adapter crate against the reviewed A-0 capacity, alignment and
publication contract. This slice stores opaque encoded bytes and checks
allocation keys; it supplies no authenticated Ash layout or lifetime facts.
Layout codecs, registration, family evidence, source checking and execution
retain A1's dependencies on the validated generic resource path. Native backing
tests cannot complete an M case.

## Case and evidence ledger

At creation, all Ash-source cases remain unimplemented. Native helper tests do
not change that status. The coordinating task updates case status only from
actual source fixtures and observations, with commands and outcomes.

| Cases | Required semantic evidence | Required observation |
| --- | --- | --- |
| S-01 | Input inference, two identities, exact operations, non-escape, controlled publication/completion. | 42, statement-before-connection release, distinct/repeated activations. |
| S-02 | No body after failure/empty input; guarded partial state. | Real open/prepare errors separately from injected failures. |
| S-03 | Independent copied bytes versus aliases. | 1/2/3 and empty/null distinctions; bytes copied. |
| S-04 | Body/finish report nesting, consumed versus retained authority, protocol checks. | Native finalization/close refusal separately from report fault injection. |
| S-05 | Public contracts, defining origins and helper relationships. | Temporary-file persistence after close/reopen; owned file cleanup. |
| M-01 | Layout evidence, checked arithmetic, complete publication and rollback. | Exact capacity, prior objects survive failure, payload/metadata measured separately. |
| M-02 | Alias and hidden closure capture relationships. | One node payload, repeated reads, no alias payload copy. |
| M-03 | Relational payload/load summaries, selected outer projection. | A reference usable after B; whole tuple and B reference rejected. |
| M-04 | Deep-copy relation, recipient dependencies. | Independent result after A closes, sharing duplicated or preserved as declared. |
| M-05 | No owner transport; repeated scope identity and completion. | Reusable scratch capacity, peak payload and metadata. |
| M-06 | Completion captures and interpreter/storage requirements. | Actions read live arena data before release on return/resume/discard. |
| X-01 | Retention creation/release and incompatible mutation. | Stable retained input; reset alone preserves retention; copy comparison. |
| X-02 | View interval and invalidating-operation conflict. | Live owner does not authorize stale view; copied output survives. |
| X-03 | Captured access obligation visible to surrounding handlers. | Resuming compatible handler succeeds; conflicting alias access rejects. |
| X-04 | Combined owned completion and consumed/retained reports. | Statement, connection, arena-using actions, arena release in checked order. |

For every case record candidate, fixture, parse/resolution/type/Core/runtime phase,
positive and negative outcome, causal diagnostic, explicit and inferred facts,
Core/native event agreement, completion, assumptions and measured cost. A
rejection due to an unsupported layout is not evidence of correct borrow or
escape checking. An unimplemented case is not a passing negative test.

## Verification and completion gates

Run affected suites per coherent slice and the existing resource/native-buffer,
module, evidence and Core suites for crossed invariants. Run `cargo xtask verify`
at coherent compiler/runtime checkpoints. Adapter unit tests verify only its
safe API/ABI boundary; public modular driver execution verifies the Ash path.
Check documentation links, authority labels and formal notation manually under
the [documentation policy](../../project/documentation.md).

Results, blueprint and tooling are written from observations. If a required
useful case fails, retain its counterexample and revise the design explicitly.
Report supported fragments and unresolved cases without narrowing success to
S-01. Product proposals and tasks precede normative specification changes.
Adoption requires the accepted contract, retained implementation, library APIs,
tests and specification to agree; integration into `main` is a separate gate.
No commit, merge or completion claim follows merely from this record.

## 2026-10-05: bounded watcher membership

The next isolated common delivery replaces repeated scans of each capture
slot's reader list with an analysis-local index of exact source/reader slot
pairs. Slot creation contexts remain part of their identities. The ordered
reader list still determines notifications; no capture, evidence or owner
authority comes from the index. Both retained entries are charged and reserved
before insertion. Duplicate visits retain their original notification position.

Focused regression cases cover distinct creation contexts, notification order,
wide repeated visits, exact work and one-short refusal with prefilled ledgers.
The selected Type work limit remains 327680. This does not add a runtime limit
or complete the pending contextual control and generic codec changes. All 65
pending common paths remain in immutable source copies and a retained stash;
SQLite independently preserves its adapter and library files. Fresh common verification passes all-targets compilation, 1,541 library
cases with one inherited ignore, and 183 connected public/architecture cases.
Unsigned original-branch integration and fresh integrated checks remain the
delivery gate. The unrelated inherited baseline warnings remain visible; the
pending B3 cleanup is not included in this isolated delivery.

## Shared edge membership delivery (2026-10-05)

The next measured SQLite capture frontier after `3f8e03e0` is ordered edge
membership. The common delivery preserves exact slot/context identities and
ordered propagation while indexing membership. Edge, watch, and queue
publication share a fallible admission boundary; watch-only relations remain
independent. Fresh-edge work is seven units, or five with an existing watch;
duplicate work is one. This does not imply every low-fanout input costs less.

The evidence directory
`/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04/shared-edge-membership-39/`
records the all-target build, 1,543 passing library cases with one inherited
ignore, 142 passing public cases, 41 architecture cases, and unchanged work
limits. Integrated verification is the next gate.
Larger copying and persistence execution must be measured again after this
delivery. No default limit increase or source workaround is admitted.

## Common control checkpoint (2026-10-05)

The shared lookup, watcher, and edge deliveries are integrated on the original
branch. The latest unsigned integration is
`642bb6b0d2536849d0c281783af60fec7a79ae3e`; its fresh original checks pass
all-targets compilation, 131 capture cases, and 136 public cases. These deliveries
preserve the selected work limit and are complete separately from B3.

B3 remains uncommitted. A Rust row trace identified stale effect metadata after
committing the last deferred cleanup-row solution. Marking the existing builder
rewrite demand on successful completion restores the ordinary zonk. The finite
same-arguments/same-body-row/different-capture witness and the exact, one-short,
and prefilled completion-budget case pass. A connected run passes 17 of 19
control cases and all ten codec cases, including actual payload admission refusal.
The two control failures retain contrary evidence: a fixture used invalid
single-line function blocks, and lexical owner row qualification lacked its
original context. The fixture is corrected and the independently reviewed
qualification repair is under fresh compilation; neither is yet a passing claim.

SQLite's complete copying and session runs after the edge merge pass four of
seven and seven of eight cases respectively. The reset copying program still
refuses at the unchanged 327680 work limit. A temporary bounded diagnostic
reconciles 141440 initial units plus 186240 admitted units, with zero table
overflow. Repeated capture specializations all observe changed revisions, so
this evidence does not justify skipping them. Root removed the diagnostic and
restored all six compiler files and all 48 pending SQLite file hashes exactly.
Native/library work remains SQLite-owned; root owns shared compiler, Core,
capture, provider checking, generic runtime, and shared merges. Cargo windows
are serial. Native Clippy after the separate finish-dispatch observer passes;
that observer is pending SQLite work, not part of the integrated edge delivery.

Receipts live under the common evidence directory in
`batch-3-committed-cleanup-row-rewrite-44/` and
`batch-3-sqlite-capture-cost-45/`. The next integration gate is complete connected
control/validation verification and relevant realistic SQLite regression evidence,
followed by an unsigned common commit, a real merge into the original branch,
and fresh checks there. Experimental execution does not alter normative Ash.

## Connected common delivery preparation (2026-10-05)

Fresh connected receipt68 passes all 1,577 library cases, with no ignored cases,
and all 44 selected public cases: 21 control, ten codec, three retained-owner,
and ten runtime-diagnostic cases. This includes formal open Delta with its
established exclusions and the separate finite same-substitution,
same-scalar-body-row witness with different captured-control demands. Actual
capture/resume does not reacquire native owners. Owned discard performs source
completion in structural order; outer-resource cleanup precedes its release.
Consumed and retained dispositions remain distinct. Retained owners lose source
access and remain quarantined with dependencies until host teardown.

The final-answer path uses ordinary enclosing typing for both capture-free and
conditional resource bodies. Only admitted actual values and the original
checked occurrence supply specialization inputs. Final Core independently
reconstructs owner kinds, complete tagged arguments, table coverage, identity
scope, evidence and actual control rows. Original whole declarations provide
rigid-row exclusions; a nested annotation must entail them rather than create
new ones. The same constraints remain checked after both transforms.

An unpublished acquired owner is destroyed before a failed publication returns.
Injected publication failures test that boundary separately from real native
failures. Source-only deferred cleanup equations close before executable Core;
successful closure demands the ordinary builder rewrite. The 64-KiB and
256-KiB regressions retain their original bounds. Outlining discard and binding
completion preserves executable order, ownership and charged work while removing
large debug dispatcher frames; it does not raise a depth or work limit.

The current-B3 realistic SQLite probe61 executes every supplied copying/session
case: four of seven copying cases and seven of eight session cases pass. Four
larger cases refuse with `TypeResourceExhausted`. Diagnostic70 measures the reset
program against the actual formatted common source: 146,059 initial units plus
181,621 admitted units reach the unchanged 327,680 limit, with one refusal and
no diagnostic-table overflow. The profile retains exact original function and
evidence identities; changed revisions do not justify memoizing dynamic capture
results. This evidence does not establish complete copying or persistence
support. All twenty temporarily overlaid files, all 91 preserved file hashes,
and both Git diffs were restored exactly. SQLite's uncommitted native/library
work remains separate.

The quality gate found two test-style Clippy diagnostics, repaired without a
lint waiver. A valid ordinary bare-Delta annotation then reproduced loss of an
already established enclosing exclusion; public receipt71 records that failure.
Normalization is being repaired without adding exclusions or weakening row
equality. Connected checks and final quality, architecture, independent review,
unsigned commit, real original-branch merge and fresh integrated verification
remain required before Batch 3 is a completed delivery.

Common owns shared compiler, Core, capture, provider checking, manifests and
generic runtime changes. SQLite owns its library and native adapter. Arena owns
independent arena backing/bindings/private codec and arena-only candidate
paragraphs, transferred as pinned patches. Layout, references, typed allocation
and transactional borrowed-operation publication remain later arena work.
Cargo windows and integration merges are serial. Consumers start from the
verified original integration, then merge its next exact tip before delivering
independent changes; no uncommitted common snapshot is a delivered dependency.

Receipts and reviews remain under
`~/.codex/ash-provider-evidence/common-resource-support-2026-10-04/`, including
`batch-3-current-cost-profile-70/`, `batch-3-owner-row-final-contract-review-68/`
and `batch-3-formatted-binding-delivery-review-69/`. These are tested experimental
properties and explicit foreign assumptions, not a completed correspondence
proof, accepted production architecture or current language semantics.

### Final preparation corrections

Common verification72 passes format, metadata, workspace/all-target build,
workspace/all-features Clippy and all 1,577 library cases. Its architecture run
passes forty of forty-one cases. The strict inventory identifies one missing
shared-map alias and two stale source coordinates for existing borrowed
carriers. Those exact entries are corrected; the inventory remains strict.

The public bare-row regression first rejects during typing in receipt71.
Normalizing its checking type fixes that phase, but receipt76 then passes 21 of
22 control cases: independent Core rejects the local initializer/binder type
comparison. The scheduler retained a second raw annotation for binding
completion. Both owned views now use the same entailed enclosing-row
normalization before task publication. Neither inferred initializer types nor
weaker Core equality replace the declared annotation. Independent reviews find
no changed authority or partial publication. Fresh execution remains the gate.

A focused private boundary regression checks two established contexts, nested
forall shielding, every work cut at zero and prefilled ledgers, and exact fresh
retry. This observes the source preparation publication boundary unavailable
through the public budget API. Its coarse unknown tuple provenance does not
exercise provenance rebuilding failure; no such coverage claim follows.

### Connected correction verification

Receipt77 passes all 1,578 library cases with no ignored cases and all 45
selected public cases: 22 control, ten codec, three retention, and ten runtime
diagnostic cases. The bare local annotation now passes source checking and
independent Core validation. Its arbitrary-exclusion negatives remain rejected.
The private two-context work-cut and forall-shielding regression also passes.
Both annotation preparations retain the complete declared type and authenticate
existing row facts; their added structural work remains charged. The legacy
provenance shape reader stays bounded by the admitted type copy and retains its
existing host scratch-allocation convention. No recoverable global OOM guarantee
or provenance rebuilding-failure test is claimed.

Full common verification78 is the next gate, including the corrected strict
inventory. The original branch remains `642bb6b0`; no Batch 3 commit or merge
has occurred at this checkpoint. The 23 unrelated and planning files in the
original worktree remain pinned separately. Required integrated verification
will run `CARGO_BUILD_JOBS=1 cargo xtask verify` there after the real unsigned
merge. Later arena Layout/Ref/family/publication candidates and SQLite's
14-operation String/TEXT migration remain separate deliveries.

### Final shared SQLite regression probe (2026-10-05, receipt 81)

The latest common source, including the rigid-row annotation and retained binder
normalization corrections, was checked against SQLite's frozen minimal executable
TEXT/copying/persistence inputs. The public copying suite passes 4 of 7 cases and
the session suite passes 7 of 8. The same four larger programs stop with
`TypeResourceExhausted` under the unchanged default Type work limit of 327680.
This is regression evidence for the shared repair, not a completed SQLite library
delivery. The temporary fourteen-operation manifest and twelve SQLite-owned
inputs were restored after the run. All ninety preserved file pins and both
staged and unstaged differences match their pre-probe state.

The command was `CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test
provider_sqlite_copying --test provider_sqlite_sessions --no-fail-fast`. The
external receipt is `batch-3-realistic-final-probe-81/results.json` under the
common evidence directory. No limit, assertion, compiler policy, or native
ownership rule changed for this probe. Common integration still awaits the
strict scanner import-graph correction and the complete verification gate.

### Strict carrier correction (2026-10-05, receipts 82–86)

The architecture gate exposed a scanner defect in inherited `Arc` imports, not
a change in provider ownership. Exact module import routes now reach the
standard shared wrapper, including reexports through modules with no carrier
fields. Lexical local types retain their own ownership, nearer explicit imports
win, and actual borrowed payloads remain mixed. Repeated import routes must make
strict progress; conflicting or cyclic routes refuse. The single earlier
`PreparedLocalProviderCode.code` mixed-retention override is corrected to its
source-derived shared retention. Productive compiler/runtime behavior and work
limits are unchanged by this test-inventory repair.

The focused inherited-wrapper witness first failed in receipt 82. Ten scanner
cases pass after independent review in receipt 85, and the complete strict
bidirectional field/retention inventory passes in receipt 86. No inventory check
was suppressed. Full connected verification and original integration remain
required. The source is held stable for that gate.

## Verified common delivery before integration (2026-10-05)

The required common checks pass against the restored twelve-operation SQLite
contract. Receipts 87, 89, 90 and 91 together cover all 1,578 library cases, all
102 Ash integration binaries, all 43 architecture checks, the remaining native
workspace tests, formatting, all-target builds, strict Clippy and strict rustdoc.
No library case is ignored. Public suites include 22 control cases, basic SQLite
and arena execution, complete owner rows, retention and runtime diagnostics.

The broad gate 87 is not a passing receipt: it stopped at an artifact containing
the temporary TEXT manifest. Exact source restoration had preserved old mtimes,
so Cargo reused the probe's normal library. Fresh mtimes on exactly six restored
inputs rebuilt that library without a source, contract or assertion change; the
passive import check passes in receipt 88. Gate 89 then exposed six stale literal
formula guards. Their owning unit probes already passed: the test helper now
pays a separate measured registry precheck before unchanged catalog work. The
guards now name that precheck and pass all four cases in receipt 90. Limits,
inner formulas and all-cut/retry assertions are unchanged. Receipt 91 passes the
45 remaining Ash integration binaries and native workspace, plus final format
and strict Clippy checks. The two expensive source-only architecture checks
reuse their receipt-87 passes on byte-identical productive source. The final
original-branch `cargo xtask verify` will run every check without those skips.

Independent contract, runtime quality, scanner and documentation reviews accept
this bounded delivery. The finite source witness is separate from the formal
open-Delta callback and supplies executed observation, not a general proof.
Original integration and its fresh whole gate are the next checkpoint.

Larger SQLite copying/persistence programs retain the four default-work-budget
refusals observed in receipt 81. The fourteen-operation TEXT migration and
associated cost work remain separate shared follow-ons. Typed arena allocation,
Layout, references, containment, borrowing, sharing and storage families belong
to the independent arena workstream. No DN-0037 or DN-0038 implementation is
included, and no experimental rule is promoted into `spec/` or `main`.

## Common control integration (2026-10-05)

Unsigned merge `3f9dd7565992169a1d9a77278105c99d6c8b4cdb` preserves original parent
`642bb6b0d2536849d0c281783af60fec7a79ae3e` and verified common parent
`9080b9508be3a8a0b5bea2332826b6301cc4cdea`. The common source passes the connected
checks recorded above. All twenty-three unrelated original files remain byte
identical, the original index contained no unrelated staged changes, and the
merge includes only the reviewed seventy-eight common paths.

This checkpoint integrates complete owner arguments, formal open-Delta callback
execution, the separate finite capture-demand witness, ownership-preserving
resume, structural discard with outer-resource cleanup, consumed and retained
completion handling, dependency quarantine and independent final Core checks.
Existing S-01 and basic arena programs use the same public generic runtime.
The original-branch final gate and its source pins are recorded in the external
`batch-3-integration` receipt. The exact verified original tip is the handoff
point for SQLite and arena; their independent delivery merges follow it.

Common retains shared compiler, Core, capture, provider and generic-runtime
ownership. SQLite retains library/native adapter ownership and supplies
executable evidence. Arena's basic lifecycle is integrated; typed allocation and
storage work remain its later study. Cargo windows stay serial: original whole
verification first, arena's queued codec window next, then the separately queued
proof tooling window after arena returns the lease. No missing process handle
constitutes a lease release.

The four larger SQLite default-budget refusals, deferred fourteen-operation
TEXT migration, trusted foreign contracts and unproved general correspondence
remain explicit limitations. No retry, close_v2 substitution, raised source
limit, production-semantic adoption or main merge is included.


## Shared String/TEXT and cost checkpoint preparation (2026-10-05)

The common row/control delivery is integrated and verified at `3f9dd75`; its
tracking tip is `b04ff1c`. SQLite imported that tip with unsigned merge
`3a60215`, preserving its pending library/adapter work. Common owns shared
compiler, Core, capture, provider checking, generic runtime and shared merges.
SQLite owns its library, native adapter and executable evidence. Cargo windows
are explicit and serial; dependent work imports verified original-branch
commits. No independent library completion is required before a shared repair
can be delivered.

SQLite transferred nineteen pinned native/library/program inputs and a separate
completion-observation assertion patch. Common reconciled the fourteen-operation
String/TEXT manifest with the matching binding, source library and existing
fixtures. The native adapter run passes sixty cases. Connected receipt 97
passes existing public control, retention, codec and Core cases, plus two new
SQLite capture/resume/discard cases. Four larger copying/reuse/persistence
programs still refuse at the unchanged type-work limit; this preparation is
not an integrated String/TEXT delivery.

Receipt 98 corrects a module path in the new malformed-coordinate test and
passes 1,581 library cases, including original-coordinate refusal, unchanged
unpublished slots and fresh retries. One nine-clause nested-helper case still
refuses. Its trace reaches 21,579 units after checked catalog and imported ABI
preparation, then exhausts work during repeated method-evidence anchor scans.
The public copying target passes four cases and refuses three in generic
capture work. The session target did not execute in receipt 98 because that
probe command lacked `--no-fail-fast`; its receipt-97 result remains seven
passes and one refusal.

Receipts 99–103 reconcile the nine-operation handler table with its exact
original operation and resume identities. The nine-clause nested helper and its
malformed-coordinate cases now pass at the default work limit. Receipt 100
passes all 1,585 then-current library cases after the transform ledger was
recomputed from its actual indexed work. Receipts 102 and 103 pass the connected
Core, control, retention, basic SQLite and arena checks. Receipt 103 passes all
94 capture cases, including successful closure/evidence setup, late dictionary
owners, exact creation and reader contexts, and refusal before completion.

The productive repairs preserve original source coordinates, exact evidence and
anchor predicates, lexical watches and append-only value facts. Immutable
capture setup uses successful exact-coordinate completion records; ordered
edges retain only the prefix already propagated to that exact target. These
records do not store owner values or capture demands. Required cold derivation,
lookups, retained records and propagation remain paid and fallible. The
four larger public programs still refuse at the unchanged 327,680-unit type
work limit. Passing internal boundaries do not establish their execution.

Receipt 103 measures repeated metadata headers within the same immutable Core
build. The persistence program reaches a 1,226-node build at 263,051 units;
1,976 completed header visits cover 1,003 distinct nodes. The 973 repeated
visits consume 16,391 units before a later partial refusal. This demonstrates
repeated structural work, not the net saving of a proposed header projection.
The temporary traces were removed using exact owned patches. Shared source is
being prepared for another connected checkpoint; no String/TEXT or cost
follow-on commit has been merged.

Receipt 104 tests the proposed control-call replay explanation. The reset
program completes initial value closure at 266,523 units. Its first ten control
value queries consume 47,806 units, while thirteen known-successor transitions
consume 2,103. No repeated known-successor transition or tail replay occurs
before refusal. A control-successor completion record is therefore not the
measured repair for this failure and has not been implemented.

Receipt 105 applies the independently reviewed build-local metadata header
projection. Production compiles through the public driver and the connected
Core/control/retention/basic SQLite/arena checks pass. The same four larger
programs still refuse. Full-library compilation stops at a new test fixture
missing the required boxed Resource node; only that test wrapper is corrected,
and full-library execution remains pending. The next diagnosis measures value
expression setup and propagation separately. Function closure publication keeps
its existing behavior, including empty captured slots.

Receipt 106 restores the exact productive source before quality execution and
passes all 1,590 library cases without ignores, including the corrected header
fixture and fixed small-stack regressions. The connected Core, control,
retention, basic SQLite and arena cases pass. The same four larger public
programs still refuse. Exact value-graph traces have no identity, storage or
counter overflow: the reset program spends 10,681 units repeating already
successful Function setup, and 29,196 repeating Evidence evaluation. These are
measured predecessor costs; they do not establish a safe shortcut or net saving.
The following shared repair keeps late value facts, existing propagation and
independent validation as required boundaries.

Receipt 107 separates Evidence evaluation costs without changing its equations.
The same four public programs refuse. The Unicode copying program spends 19,711
units in 63 cold closure transfers and 8,933 in dictionary reads; the reset
program spends 16,797 in 81 cold transfers and 12,664 in dictionary reads.
Unknown-value dependency traversal contributes no work in these samples. Exact
analysis and slot records report no omitted identities or counter overflow.
Thus a repeated successful Evidence evaluation does not establish that its new
closure transfer can be skipped. The diagnostic was removed by restoring the
exact productive bytes with a fresh modification time. Static route reuse and
work before value analysis remain separate hypotheses, not tested savings.

Receipt 108 installs the independently reviewed normal queue setup completion
for Alias, Merge and Function. Every ordered edge still propagates unread facts
on every visit, while direct evaluations retain their original behavior.
Completion is paid and recorded only after the entire original setup and current
ordered propagation succeed. Fresh and focused slots start incomplete; terminal
and cut authority remain separate. All 1,593 library cases pass without ignores,
including late actual resource identities, every cold work cut, focused/restore
cases and fixed small-stack regressions. The same four larger public programs
still refuse. Connected control, retention, Core, basic SQLite and arena cases
pass. All 43 architecture cases pass without ignores. This establishes this
repair's tested boundaries, not completion of the larger-program delivery.

Receipt 109 measures the original paid Type-work callsites and cold Evidence
subphases. Each failing parent ledger reconciles its site charges exactly with
its admitted total, without omitted parent calls or sites. The diagnostic omits
many separate finite child ledgers, so these parent reports are not whole-program
work totals. All probes were removed using exact source snapshots with fresh
modification times, and their new diagnostic module was removed.

The Unicode and reset samples contain respectively 63 and 83 cold Evidence
slots, with only one cold transfer at each exact slot/context. Prior successful
empty-source evaluations explain the earlier repeated-success label. Capture
specialization consumes 14,821 and 11,923 units, while dictionary linking consumes
3,537 and 3,003. A reviewed dictionary-link completion candidate has no reuse
opportunity in these prefixes; it is withdrawn and preserved privately rather
than retained as the required repair. The four larger public programs still
refuse. Original immutable structural capture scans and required independent
validation remain separate cost boundaries under investigation.

The next connected checkpoint must retain all required larger programs and
negative cases, remove temporary probes, complete independent review and
architecture checks, commit and merge unsigned, and verify the integrated
original branch. Original identities, full anchor validation, lexical watches,
existing work/depth limits and unrelated drafts remain required invariants.


Receipt 110 retained the same four public refusals and restored the exact
productive receipt-108 source after a temporary capture-index probe. Complete
copying graphs contained one duplicate among 104 capture entries; reset
contained none among 59. Persistence stopped during graph construction, with
five duplicates among 135 entries in its created prefix. Created entries and
completed inventories are separate observations. The affected duplicate
vectors disagree between forward first-occurrence and reverse last-occurrence
order; a single deduplicated vector would change a consumer's discovery order.
These counts do not justify a capture deduplication change. Evidence and the
source-only assessment are retained in `provider-capture-duplicates-110/` and
`/tmp/ash-function-capture-duplicates-analysis-20261005-frozen-01/`. No probe
remains in productive source and no new execution capability is claimed.


## Separate generic cost delivery (2026-10-05)

The common control delivery remains verified at `b04ff1c`. Common and SQLite
agreed to deliver generic compiler cost repairs against its twelve-operation
contract before the pending fourteen-operation String/TEXT package. Common
owns shared compiler, Core, capture, provider checks, runtime and integration
merges. SQLite owns library, adapter and programs. Cargo windows remain serial.

All forty coherent String/TEXT working files, including the four unchanged
larger copying, reset and persistence programs and their tests, are preserved
with exact pins in `provider-cost-isolation-112/preservation.json` and its
`coherent-atomic14-owned-source.tar.gz` archive. They are pending work and will
be restored and reconciled after this delivery. Their observed default-limit
refusals are retained as contrary evidence; this split does not satisfy those
programs' acceptance or establish a completed String/TEXT delivery.

The generic repairs retain original identities and ordered evidence, paid and
fallible work, lexical watches and late value propagation. Original-coordinate
mutation regressions accompany the occurrence index. Independent Core
reconstruction remains required. Verification, unsigned commit, original-branch
merge and integrated verification are pending at this preparation point.


Receipts 112 and 113 verify this isolated twelve-operation snapshot: 1,595
library cases, 139 connected public cases and 43 architecture cases pass with
no ignores. All-targets checking, workspace Clippy with warnings denied and
workspace rustdoc with warnings denied pass. The connected cases include
independent Core validation, method evidence, module admission, owner rows,
control, retention, native SQLite sessions and basic arena lifecycle. Fixed
small-stack regression cases are included in the library run. Independent
contract and quality reviews found no changed-contract blocker.

These checks validate the shared cost repairs on this contract. The preserved
fourteen-operation copying and persistence programs remain pending. Their work
refusals locate an exhausted ledger; they do not prove whole-pipeline
convergence or establish that all measured work is unnecessary. The next
diagnosis records ordered value and control events on the unchanged reset
program, with exact source pins and explicit truncation boundaries. No trace
or speculative shortcut is part of this delivery. Unsigned integration and
verification in the original worktree remain required.


The coherent fourteen-operation preparation is restored after the separate
cost commit `50f4b6b` and unsigned original-branch merge `c97e0f3`. Its generic
compiler files include that verified common snapshot; pending package files
retain their preserved contents. Integrated original-branch verification is
still pending. The next diagnosis is the requested ordered trace on the
unchanged reset program. No uncompiled bound-port or borrowed-projection
candidate has been applied, and no larger-program acceptance is claimed.


## Ordered reset execution trace and propagation review (115–117)

The user requested actual ordered compiler execution before another long gate or
optimization. The initial original-branch gate 114 was interrupted after 22.64 s;
its partial log is preserved and it establishes no passing integrated result.

Receipt 115 executes the unchanged 45-line reset entry through the existing public
`sqlite_session` driver on the coherent fourteen-operation source snapshot. The
entry SHA is 0979f33b5696c6f6cc799e8c5002caad079029eed67c94b4699d4f2e1578ed5b.
Temporary streamed instrumentation preserves original charges and decisions and
records early finite-ledger work, queue causes, contexts, fresh versus existing
facts, container lengths/capacities, ordered continuation-state snapshots and
refusal. Explicit terminal flush receipts record 364343 reset events and 326019
short-TEXT control events, with no omissions, overflow or I/O failures. Independent
Value, Control, integrity and SQLite extractions agree. Unbounded budgets are
excluded and parent/child ledger lineage is absent; neither summed child work
nor total allocated bytes is claimed.

The reset entry still fails with `TypeResourceExhausted` before acquisition. Its
exact compiler ledger 3 admits 327680 units, then refuses two. One Value analysis
reaches an empty queue 13 times; later Control queries extend that same analysis.
The refusal occurs during the fourteenth drain, with slot 2413 still being
processed despite an empty pending queue. Original source 0 bytes 1692–1702 are
`Sqlite.Err` on line 31 in `after_second`. Its context follows main → after_first
→ after_second. The Control prefix has 218 distinct committed and popped states,
25 existing-state suppressions, and no replay. No focused child analysis occurs.
These observations establish finite progress to refusal, not whole-pipeline
convergence or remaining-work sufficiency.

The short TEXT control returns
`Completed(Completed(Ok(TextValue("héllo 世界")), Closed), Closed)`, copies 13 input
and output bytes, finalizes the statement, then closes the connection. Both
processes retain zero native owners. The five existing-source overlays and added
module are removed by exact fresh source restoration; all 37 before-source pins
and all 40 coherent-source pins match. Raw logs, source pins, reproducible commands,
terminal receipts and readable ordered timelines are under
`/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04/provider-ordered-execution-trace-115/`;
independent reconstructions are the sibling `ordered-trace-*115` directories.

The trace supports a narrow implementation candidate: propagation currently
copies an ordered edge vector and each unread scalar Atom suffix before visiting
them. Source review establishes that publishing an Atom does not mutate the
current edge list or a distinct source's atoms; a self-edge sees existing
membership. Fixed original counts and end positions therefore permit indexed
Copy reads, preserving every original check, notification, order and complete
cursor commit. Independent contract review approves this candidate; its source
is applied only to the common worktree and has not yet been compiled. The
historical successful reset prefix contains 18153 units of these physical copies;
this is not a measured new-program saving or budget-fit claim. Existing exact
work-cut/retry/self-edge/late-fact tests retain their obligations with formulas
adjusted only for removed physical work. No work or depth limit is raised.

Original merge c97e0f3 is now undergoing the complete gate 116. The verified
cost-only handoff will be released to SQLite only after that gate passes.
Connected verification 117 of the new propagation candidate remains pending.
This work changes neither `spec/` nor the experimental authority of DN-0036.


## Verified shared cost integration and SQLite handoff (2026-10-05)

Common cost commit `50f4b6b8b33a04f77cc6eeb511fa6f453fff48f2` is merged
with both histories into `codex/provider-experiments` by unsigned merge
`c97e0f3fdb4ec0c1269015864a7ca4efeaa132fd`. Receipt 116 runs
`CARGO_BUILD_JOBS=1 cargo xtask verify` in that original worktree and exits zero
after 1,073.79 seconds. Its 117 reported test blocks contain 3,330 passes, zero
failures and zero ignored cases; 103 integration binaries execute. Formatting,
all-targets build, strict workspace lint, architecture and fixed small-stack
regressions, native adapters and documentation checks pass. These reported
counts include subprocess test receipts and are not a claim of unique test
identities. The complete log SHA is
`ded101cb6a5ee4060e918f529fdfc50614f3581ee6e2d1a580e0ac38428cc70e`.

All ten delivery file pins and twenty-three unrelated working file pins match
the before receipt. The index is empty at engine return; no Cargo, rustc,
rustdoc, Lean or Rust LSP engine remains. Evidence, command, terminal result,
source pins and explicit return are retained under
`/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04/provider-cost-integrated-final-gate-116/`.

This completes the separate shared cost delivery on the twelve-operation
contract. The coherent fourteen-operation String/TEXT package remains
preserved in common and SQLite worktrees. The unchanged larger copying,
reset and persistence programs are required pending acceptance; the ordered
reset trace in receipt 115 still refuses before acquisition. The applied
borrowed propagation candidate is outside this integrated commit and requires
fresh connected verification. No work or depth limit changes, weakened
assertions or trace instrumentation are integrated.

Common owns shared compiler, Core, capture, provider checking, generic runtime
and shared integration merges. SQLite owns independent library, native adapter,
programs and executable evidence. SQLite imports this verified original
checkpoint with an unsigned merge preserving its pending work, then receives
a serial Cargo check window. Common next verifies the propagation repair
against the unchanged realistic programs, reconciles further shared work, and
merges each verified shared delivery through the original branch before
SQLite's complete library delivery. These experimental results do not change
`spec/` or establish production architecture or a mechanized P-1 proof.


## Borrowed propagation connected check (117)

The diagnostic-free propagation candidate compiles and passes the complete
1,595-case library run, including exact refusal cuts and fixed small-stack
regressions. The eight connected common suites pass 139 cases, and SQLite
capture/resume and owned discard pass both cases. The copying suite passes
four cases and refuses three; the session suite passes seven and refuses one.
The four unchanged larger cases still fail with typing work exhaustion before
execution. These failures do not validate their required native observations
and do not establish whole-pipeline convergence or budget fit. No assertions,
fixtures or limits are weakened.

The formatted candidate source SHA is
`83823efc059483c139e91e927a94d98b2aa1fc2844993aa205721fdc582cbdda`.
Formatting changes only two added test assertion layouts; the reviewed
production change is identical. The 168.35-second serial window returns
terminal failure because realistic acceptance remains incomplete, with all
forty source pins unchanged and no active engine. Commands, full logs, exact
source pins and return receipt are retained in
`/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04/provider-borrowed-propagation-117/`.
The candidate remains uncommitted common work. The integrated cost-only
checkpoint stays verified at original tracking tip `7cf295e`. SQLite receives
the next bounded workspace check window; reduced diagnostic variants will
use the exact preceding compiler source to isolate program-shape effects.
Original acceptance programs remain required.


## Ready setup and helper isolation (123–124)

The shared candidate now completes fixed Tuple, Cleanup, Bind, Recursive,
Match and Resource setup only after their original readiness gates, watches,
relations and ordered propagation succeed. Reactive Call, Project and Evidence
inputs remain live. Connected receipt 123 passes 1,596 library cases, 139 common
public cases, 43 architecture cases and both SQLite control cases. The unchanged
copying suite still refuses three cases and the session suite one, all with
typing work exhaustion before acquisition. The candidate remains uncommitted
and unmerged. The separate late-constructor Match regression in receipt 124
passes after completed Match setup; its existing projected arm still carries a
new constructor payload's ownership. Work and depth limits remain unchanged.

The equal-engine diagnostic comparison 124 restores the exact pre-117
compiler and frozen ordered probes used in 115, 119 and 121. The staged reset
program still completes when the exact original `read_cleared` declaration is
restored unused. It reports all three copied answers, four steps, two resets,
clear-bindings, statement finalization before connection close, and zero retained
owners. Keeping every original helper signature and call site while staging
only `read_cleared`'s internal Result forwarding still exhausts source checking
work. These source variants preserve the native sequence but change pure
dataflow; they do not replace original acceptance or establish general control
convergence. The result rules out the restored declaration alone as the complete
cause of the refusal. Detailed context and charged-work attribution remains
required before the next repair.

Receipt 124 returns after 108.69 seconds with all 46 current source pins and nine
frozen input pins preserved, temporary instrumentation removed and no active
engine. Source review, commands, full traces, native observations, source pins
and terminal receipts are under
`/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04/provider-helper-isolation-trace-124/`.
The verified original checkpoint remains tracking commit `7cf295ee` over code
merge `c97e0f3`. Common continues to own shared compiler, Core, capture, provider
checking, generic runtime and integration. SQLite retains library, adapter and
program ownership. The next integration checkpoint requires unchanged larger
program acceptance and connected independent validation, then an unsigned common
commit, an unsigned original-branch merge and integrated verification before
SQLite imports it. This remains DN-0036 evidence, not current Ash semantics or a
mechanized P-1 proof.


## Current preparation cost and typed reuse boundary (125–131)

At receipt 131 the fourteen-operation package still refuses the same four
unchanged larger copying, reset and persistence programs before acquisition.
That public check passes both control cases, four copying cases and
seven session cases. Three copying cases and one persistence case still exhaust
typing work. These failures remain required acceptance cases. No work or depth
limit, source program or assertion changes.

Receipts 127–129, on the ready-setup candidate before the hash and scalar
changes, separate these failures from the older pre-117 helper trace. Copying
refuses during Function value routing; reset refuses
during the final Value drain after Control discovery. Persistence refuses during
static Match construction before that graph's Value activation. Receipt 128
places the persistence graph's 1,226 nodes at 263,425 of 327,680 source-checking
units before construction. Its completed free-value, metadata and abstract
capture walks cost 8,824, 36,880 and 7,905 units respectively; the failed tail is
not included. These are intervals within that existing ledger, not an
addition across independent budgets or proof that all metadata work is redundant.

The proposed bound-variable membership index is parked: receipt 129 predicts
additional work of 72 units for copying, 56 for reset and 158 for persistence.
A proposed zonk follow-up guard cannot reduce the measured intervals for these
four cases because they already have empty row-solution maps. Readiness
notification filtering has no beneficiaries before persistence's static refusal
and no sufficient demonstrated benefit for the other cases. Lawful source
optimizations are not automatically productive optimizations.

Receipt 131 compiles the complete-Type universe hash index and scalar metadata
root simplification. All five focused tests pass: complete hash equivalence,
three type-universe cases and the metadata collector boundary. Hash collisions
still require full equality; original first-occurrence order, complete owner
arguments, kinds and row distinctions remain checked. Scalar metadata roots
avoid unnecessary worklist and intermediate result allocation while compound
roots retain the original complete walk and Forall shielding. This connected
candidate does not complete the four larger programs and has not been committed
or merged. Receipt 130 records the preceding failed test build caused by a
missing test-only import, which receipt 131 corrects.

The investigation following receipt 131 measures large preparation phases and
repeated immutable provider authentication. At that checkpoint, template lookup
re-authenticates original
code, certificates and lifecycle associations. A proposed private prepared-data
boundary would encode which obligations have completed, so specialization cannot
accidentally re-enter preparation. Pending publication and committed publication
must have distinct states: certificates retain publication slots, so the same
allocation does not establish the same facts before and after publication.
Successful committed preparation can retain exact immutable code and certificate
identity; source import association, actual capture demands, copied identities
and independent final Core reconstruction remain separate obligations. At receipt 131, this proposal is not an implemented or verified capability.

Receipt directories `provider-zonk-cost-125`, `provider-ready-notify-cost-126`,
`provider-current-refusal-127`, `provider-construction-cost-128`,
`provider-metadata-filter-cost-129`, `provider-index-scalar-130` and
`provider-index-scalar-131` are under
`/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04/`.
They retain commands, exact source pins, raw logs and explicit engine returns.
Temporary diagnostic changes are restored before subsequent work. Original
integration remains `7cf295ee` over `c97e0f3`; no new completed delivery is claimed.


Receipt 132 verifies the same diagnostic-free hash/scalar candidate with all
1,601 library cases, 139 connected public cases and 43 architecture cases
passing. Deep-input, fixed-stack, owner-argument, publication and independent
Core-validation regressions pass. This gate validates the connected changes;
it does not supersede receipt 131's four required larger-program failures or
establish their current refusal frontier. The source and return receipts are
under `provider-index-scalar-connected-132/` in the same evidence directory.
The candidate remains uncommitted and unmerged pending realistic acceptance.

Receipt 133 compiled the temporary coarse preparation probe and passed its first
capture/resume case. The runner then stopped because its parser required the
terminal marker at the beginning of a line; Rust emitted that marker after the
test name. The raw terminal and trace were complete. This remains a partial
one-case receipt, with the failed runner result preserved.

Receipt 134 corrects that parser and measures all seventeen unchanged copying,
session and control cases in separate processes. Thirteen pass and the same
four larger programs exhaust typing work. Independent readers validate thirty
public-driver terminal receipts, contiguous sequences, zero omitted records,
zero diagnostic failures and the exact aborted-phase counts. All forty-six
production pins are restored and the temporary helper is removed before the
explicit engine return.

At receipt 134, the source ledger repeats complete original-code authentication
four times in copying and its NUL case (7,236 units), six times in reset (10,854), and
twelve times in persistence (21,708). Lifecycle state-association checks cost
438, 621 and 1,360 additional units respectively. These are observed repeated
invocations, not net savings or proof that every invocation can be removed.
Copying now finishes static graph construction and refuses during initial
Control analysis. Reset completes source capture, then refuses in source-plan
preparation. Persistence still refuses during static graph construction. The
earlier 127–129 frontiers do not describe this moving candidate.

A private typed preparation candidate retains an exact original owner through
available, committed and selected-template states. Its source and linked routes
remain distinct; local component promotion does not require complete group code
availability. Pending publication cannot be promoted using pointer identity
alone. Per-instance substitution, fresh identities and capture demands remain
separate, and independent import and final Core checking still reconstruct
their own authority. Receipt 135 applies and builds that patch. Sixty-five of
sixty-six connected provider cases pass; the new preparation test fails while
linking its fixture, before reaching the owner checks. The public SQLite checks
therefore have not run on this candidate. Independent source review finds no
production blocker. Its cold storage, warm lookup and preparation costs require fresh
measurement before any savings or completion claim.

Receipt 136 corrects the fixture by linking its actual checked dependency graph
while retaining the already-checked entry and published slots. It removes two
immediately erased route wrappers; method arguments and certificate checks
continue to distinguish source, pending and linked access. The preparation
regression passes, including partial-stage publication and an exact remaining
budget retry of the same owner. The unchanged reset and clear-bindings program
now executes successfully through the public driver with its existing native,
copy and completion assertions. All previously passing public cases still pass;
the full result is fourteen passes and three typing refusals.
Copying, its NUL variant and persistence still refuse before acquisition. No
limit, program or assertion changed. This candidate remains uncommitted and
unmerged, and the remaining refusal frontiers require fresh attribution.

Receipts `provider-preparation-phases-133`, `provider-preparation-phases-134`,
`preparation-phase-analysis-134`, `provider-typed-preparation-135` and
`provider-typed-preparation-136` are in the same evidence directory. The
integrated original branch remains `7cf295ee` over `c97e0f3`.


Receipt 137 measures the diagnostic-free typed preparation candidate with the
same five representative public programs. Original group authentication occurs
once per source entry, at 1,809 units. Each selected template's state associations
are checked once; later lookups retain the exact prepared owner. The four
lifecycle input preparations cost 2,844 units in total. Sharing their immutable
inputs offers at most 2,121 repeated units before new storage and lookup costs;
this is not enough evidence to claim that a refused program will fit. Argument
context matching has not run before the three remaining refusals, so retaining
its lookup index is parked. All forty-seven production pins are restored.

Receipt 138 separates initial Control universe preparation from Value graph
setup and its first closure. Copying and its NUL variant complete the universe
at 7,823 units and initial setup at 2,330 units. Their first Value closure then
admits 122,905 units before refusing. This is an incomplete dynamic propagation
cost, not removable immutable preparation. Persistence instead refuses inside
Control universe preparation with only 3,828 units remaining; it never reaches
Value graph setup. Its unknown remaining tail cannot be inferred from copying.
Reset completes those phases at 5,141, 1,298 and 61,071 units respectively, and
capture/resume completes them at 4,176, 1,004 and 20,931 units.

The five programs retain their source, acceptance assertions and work limits.
Independent readers validate contiguous trace sequences, exact terminal results,
zero omitted records and diagnostic failures, and the expected aborted phases.
The temporary diagnostic is removed, all forty-seven pins are restored, and the
engine returns explicitly. The next investigation measures actual queue growth,
new graph state and repeated visits within the first Value closure. It keeps
immutable prepared facts separate from context-specific answers and processing
progress. No additional overhead is accepted as necessary without that evidence.

Receipts `provider-preparation-phases-137` and
`provider-preparation-phases-138` are in the same evidence directory. The typed
preparation candidate and passing reset program remain uncommitted and unmerged;
original integration remains `7cf295ee` over `c97e0f3`.


Receipt 138b checks the diagnostic-free typed preparation boundaries. All 66
external-provider cases pass. Architecture enters its 43 cases but the combined
240-second window expires during the checks; that result is incomplete, not a
pass. All forty-seven input pins remain unchanged and no engines remain.

Receipt 139 measures three unchanged public programs with a temporary bounded
Value progression diagnostic. Resume and reset pass; copying still refuses.
Their coarse traces are byte-identical to receipt 138. Independent readers
validate all 501 per-close reports, post-flush status records and exact exclusive
cost partitions, with zero omissions, diagnostic failures or unreconciled work.
The initial copying closure grows from 276 to 4,402 slots and from 38 to 287
contexts. Watch, edge and slot operations account for 74,482 disjoint units of
its 122,905 admitted units; dependencies account for only 84. Evidence-kind
visits cost 54,884 inclusive units, an overlapping view that cannot be added to
those operation totals. Revisit counts do not prove unchanged-state repetition.
Refusal occurs at the next queue-visit charge before evaluation begins. Both
diagnostic helpers are removed, all forty-seven pins are restored and the
engine returns explicitly.

Receipt 140 applies the independently reviewed consumed Control code inventory.
It classifies each original code entry once, deriving both resource presence and
ordered owner rows before creating query state. The remaining type-universe and
Analysis construction suffix stays unchanged. The candidate builds and all 106
existing capture/control cases pass. Its new boundary test fails because the
expected row inventory omits known-prefix members that the canonical open-row
constructor also retains in the tail lacks set. The actual count is sixteen,
not twelve. Public SQLite and architecture checks have not run after that
failure. Correcting the fixture must preserve those rows and their original
order; it does not authorize changing the productive traversal.

The next Evidence-stage proposal carries a unique mutable Analysis borrow from
successful capture transfer into residual dictionary routing. It can prove that
an exact relation has already been installed before filtering repeat setup.
Global ports outside the capture topology remain required by existing tests;
a lazy-port replacement is unproved across focused snapshots and joined
contexts. The proposed phase receipt is not implemented or verified yet.

Receipts `provider-typed-preparation-boundaries-138b`,
`provider-value-progression-139`, `value-progression-analysis-139` and
`provider-control-inventory-140` are in the same evidence directory. These
candidates remain uncommitted and unmerged.

Receipts 141 and 141b validate the corrected canonical row fixture without
changing the productive inventory. All 107 capture/control cases and all 43
architecture cases pass. The architecture suite takes 517.52 seconds; receipt
132 recorded 444.51 seconds with parallel test execution, so the shorter 138b
timeout did not establish a regression. The guard implementation is unchanged.

Cargo stops the initial public command after the copying binary fails. Receipt
141 therefore establishes two control passes and five copying passes with two
typing refusals, but does not execute sessions. Receipt 141b runs all eight
sessions separately: seven pass and persistence still refuses during typing.
Across the three binaries the result remains fourteen passes and three typing
refusals. Copying, its NUL variant and persistence are incomplete; reset and
capture/resume execute their unchanged native assertions. All forty-seven pins
remain unchanged within each command window and both engines return explicitly.

The next temporary observation checks exact current capture-installed dictionary
relations before their original repeated routing. A successful phase receipt
will need the same mutable Analysis loan and exact transfer coordinates;
prepared topology membership alone cannot authorize skipping a relation.
These candidates remain uncommitted and unmerged. Integration remains
`7cf295ee` over `c97e0f3`.

Receipt 142 observes current dictionary routing after successful capture
specialization. Independent readers validate original coordinates, both indexed
and physical ordered relations, successful cost records, setup/output endpoints
and post-flush status. Resume completes 30 observed transfers with 110 routes,
copying 114 with 882 routes, and reset 84 with 378 routes. Every observed route
is covered by the completed capture transfer and physically ready; its repeated
slot/link work costs five units. Zero omitted or partial records are reported.
Copying still refuses later, so these are complete observed transfers rather
than whole-program completion or net savings. All forty-seven pins are restored
and the temporary helper is removed.

Receipt 143 applies the consuming Evidence transfer phases. One exclusive
Analysis borrow flows through reservation, capture installation, required
residual routing and final output publication. Bound-port topology is immutable
structure; only successful contextful installation permits filtering a repeated
relation. Initial input watches, Unknown dependencies and late owner propagation
remain live. The candidate builds and all 108 capture/control cases pass. The
three public binaries run with `--no-fail-fast`: fourteen pass and the same three
typing refusals remain. No larger program is recovered at this checkpoint.

The candidate pays two new source guards per closure attempt, a membership
lookup per route and fallible storage for each cold bound port. The observed old
five-unit routes do not establish its net benefit. The next comparison measures
actual closure costs and considers reusing the checked Evidence match once per
visit. Source reviews establish no demonstrated identity or publication blocker;
fresh architecture, small-stack and full quality checks remain required before
integration. These changes remain uncommitted and unmerged.

Receipt 144 compares the same four unchanged Ash programs across the preceding
inventory baseline, receipt 143 and a candidate that carries the checked
Evidence visit into each consuming transfer. Independent readers validate all
twelve traces and their provenance. The completed first source closure costs
20,931 units for resume at baseline and 20,577 with the checked visit; reset
costs 61,071 and 59,833 respectively. These matched intervals save 354 and 1,238
units. The guard savings include cold and warm attempts. Copying reaches
different partial states at the same limit, which establishes no comparable
whole-program savings or fit. Persistence reaches no Value closure.

At the actual Control type-universe boundary, persistence has used 325,834 of
327,680 units. It completes 300 visits costing 1,841 units and refuses during
the next Application visit. The observed prefix contains 211 repeated Unit
visits costing five units each. A private append-only universe builder could
carry successful Unit admission as a variant and avoid repeating its hash and
equality checks. Other types still require full collision equality and original
traversal. Its proposed prefix saving accounts for new classification work and
does not establish that the unobserved remainder fits. No limit increase or
fixture reduction is authorized by this measurement.

Receipt 145 retains the checked Evidence visit candidate. Only the actual
Evidence expression match creates that visit, with its exact expression,
context and bindings; one exclusive Analysis borrow carries it through closure
transfer and publication. All 108 capture/control cases pass. The three public
SQLite binaries execute all seventeen cases with `--no-fail-fast`: fourteen
pass and copying, its NUL variant and persistence still refuse during typing.
Both windows return explicitly with all forty-seven input pins preserved and
no engine left running. Temporary diagnostics are removed. These improvements
remain uncommitted and unmerged; fresh architecture, stack and quality checks
are still required before integration.

Receipt 146 applies the privately reviewed Unit admission owner. The builder
owns the append-only ordered universe and hash buckets. Its actual Unit match
introduces a private occurrence; successful full cold admission changes Unseen
to Admitted. That state remains inside the same owner and permits later Unit
occurrences to skip repeated hash and equality work. Consuming the builder
returns the original ordered borrowed entries. All other types keep full hash,
collision equality and child/owner-row traversal. New classification and phase
work is charged before the associated operation, and allocation remains fallible.

All 108 capture/control cases pass, including exact seed-first representative,
mixed row/type arguments, collision comparisons and refused cold/warm admissions.
All seventeen public SQLite cases execute: fourteen pass and the same three
typing refusals remain. This receipt establishes no actual 330-unit saving or
complete larger-program execution. It returns explicitly with all forty-seven
pins unchanged and no engines active. The separate discovery that a provider
call starts an ordinary Value analysis before replacing it with provider data
is parked: measured first constructor failures have no actual seed, whereas
that provider bridge supplies one, so it is outside the reached frontier.
These follow-on changes remain uncommitted and unmerged.

Receipt 147 observes the current Unit candidate with bounded temporary probes.
The ordinary universe starts at the same recorded boundaries as receipt 144.
Resume completes preparation in 2,774 units and copying in 5,570, reductions
of 474 and 757 respectively. Resume's first Value closure still completes in
20,577 units with the same reported final state. Copying uses the available
124,360 closure units but remains incomplete at 4,507 slots, 295 contexts and
960 pending slots; this partial state cannot establish whole-program savings.

Persistence still starts its universe at 325,834 units. It now reaches visit
372 and refuses during Unit admission. The completed prefix includes 263
duplicate Unit admissions costing three units each. That longer prefix cannot
be treated as the earlier 330-unit model or proof that the remainder fits.
No Value closure runs for persistence. Independent raw, provenance and negative
reader checks retain the pop/admit schema, finite caps, partial endpoints and
post-flush status. The window returns explicitly with all forty-seven pins
freshly restored, its temporary helper removed and no engines active.

Receipt 148 prepares the complete ordered dictionary projection with each
immutable capture topology. The result is Complete or an ordered Pending list
of original binding and Graph evidence positions. Only a successful contextful
capture installation consumes that result. All uncaptured matching global
ports remain pending, including duplicate bindings and empty-capture cases.
The membership set now belongs only to construction; the published topology
retains the projection. Cold classification, residual retention and publication
are paid and fallible. Dynamic watches, dependencies, output and completion
stamps retain their original behavior.

All 108 capture/control cases pass, including the extended ordered-residual and
empty-capture boundary. All seventeen public cases execute: fourteen pass and
copying, its NUL variant and persistence still refuse during typing. This is
compiled phase processing evidence, not a net-saving or larger-program fit
claim. The window returns explicitly with all forty-seven pins unchanged and
no engines active. A misleading has_graph comment is corrected: logical query
projections also retain graphs, so graph presence alone cannot establish ordinary
capture admission. Imported symbolic roots also receive live actual captures;
skipping them is unproved. Follow-on integration remains pending.

Receipt 149 broadens verification of the current prepared-route candidate.
The all-targets Ash build and all 1,604 Ash library cases pass, with no failures
or ignored cases. This covers broader authority, kind, control and deep-input
regressions than the capture slice. The window returns explicitly with all
forty-seven input pins unchanged and no engines active. It does not change the
three public typing refusals or establish integration; architecture and remaining
connected quality gates are still required for the eventual shared delivery.

Receipt 150 replaces fabricated non-callable records with explicit absent
positions. Callable positions retain the original body, type and result; real
Unit-typed callables remain present. Imports preserve dense coordinates and
checked target access rejects absence. Type preparation retains one borrowed
Unit witness at the original first-admission position instead of copying and
traversing a dummy Unit for each absent callable. Presence processing, root
preparation and allocation remain bounded and paid.

All 108 capture/control cases pass, including imported offsets, genuine Unit
callables, invalid absent targets and budget refusal. All seventeen public
SQLite cases execute: fourteen pass and the same three typing refusals remain.
The window returns explicitly with all forty-seven pins unchanged and no engines
active. This establishes compiled behavior, not net cost reduction or complete
larger-program execution. Fresh architecture, stack and broader quality checks
are required for this representation change before shared integration.

Receipt 151 verifies the current absent-callable representation with the
all-targets Ash build and all 1,604 Ash library cases. Both pass, with no failures
or ignored library cases. The fixed small-stack capture and evaluator gates in
that library suite pass. The window returns explicitly with all forty-seven
pins unchanged and no engines active. Public module/transform paths,
architecture and the source runtime stack gate remain to be checked for the
eventual shared delivery. The three larger public typing refusals remain.

Receipt 152 checks twelve connected public binaries against the same candidate.
Their 171 outer cases pass, with no failures or ignored cases; child stack
subprocess summaries are not counted again. This includes the fresh 256 KiB
source runtime gate, imported polymorphic and selected-evidence paths, identity
and escape rejection, native authority and conversion failures, open callback
and distinct captured-control demands, quarantine and structural completion.
The actual SQLite baseline and arena lifecycle still execute through the public
driver. All forty-seven pins remain unchanged and no engines remain active.
The three larger SQLite typing refusals and final architecture/integration
checks remain outstanding.

Receipt 153's temporary frontier probe fails to compile before any test or
measurement because its presence counter lacks an integer type annotation.
The exact productive source is restored. Receipt 154 corrects only that
diagnostic annotation and executes the unchanged resume, copying and persistence
cases. Independent readers validate the bounded streams and reject five
tampered traces. All forty-seven pins are restored, the helper is removed and
no engines remain active.

The original callable-value solver completes three passes in 3,655 units for
copying's largest scope and 7,163 for persistence's largest scope. These are
separate solver-scope observations, not budget identities. They do not support
a large worklist repair as the main cost reduction. Persistence's immutable
graph has 63 actual callable positions and 1,241 absent positions. Its current
universe starts at 325,548 units, spends 1,369 preparing 112 roots, and refuses
on visit 82 during EffectfulFunction admission at 327,680. No persistence Value
closure executes.

Copying's universe completes from 195,427 to 199,970, including 605 units of
root preparation. Its first Value closure remains incomplete after the available
125,380 units, with 4,590 slots and 924 pending slots. This longer failed prefix
does not establish fit or comparable closure savings. Resume's first closure
completes in 20,241 units with the same reported initial and final state as the
earlier 20,577-unit interval. The conditional matched saving is 336 units; it
does not establish the larger programs' cost. Remaining attribution separates
ValueGraph construction, SummaryGraph compilation and pre-Control root selection.
No work-limit increase is justified by these observations.

Receipt 155 checks the restored productive source with strict workspace and
all-targets Clippy. It passes with warnings denied. All forty-seven pins remain
unchanged and no engines remain active. This quality check leaves the three
typing refusals and final shared integration gates outstanding.

Receipt 156 measures the original ValueGraph construction, control compilation
and root selection without changing productive behavior. Resume passes; copying
and persistence retain their typing refusals. All forty-seven pins and the exact
productive sources are restored, the temporary helper is removed, and no engines
remain active. Independent source readers check the unchanged bodies, paid
operations and finite diagnostic storage; actual readers check provenance and
reject tampered observations.

Copying's final ValueGraph construction uses 30,033 units. Its disjoint detail
costs are 3,966 for free-value collection, 16,122 for function metadata, 3,869 for
abstract captures and 6,076 for remaining construction. The 148 units of bound
filtering are included in metadata. Persistence's coarse construction uses
68,677 units, followed by 11,040 for control compilation and 2,514 for root
selection. Its detail stream omits 136 records after reaching its diagnostic
cap; the observed 26,621 metadata units describe a completed prefix, not the
whole construction. No product limit changes.

All observed function-metadata roots are distinct. An exact-root memo therefore
has no observed reuse. The next candidate studies composition of overlapping
child summaries tied to the exact borrowed nodes and operation projection.
It must preserve discovery order, complete subtree binding exclusion including
prefilled metadata, fallible storage and bounded cold work. Prepared facts do
not authorize reuse of live capture answers or completion authority. This is a
pending simplification study, not a verified saving or integrated delivery.

Receipt 157 starts the outstanding architecture check on the unchanged current
candidate. After session interruption, its orchestration and test processes are
absent and the log has no completion receipt. The recovery check finds all
forty-seven pins unchanged and no engines active. This run remains unverified;
its preserved prefix is not a passing architecture result. The temporary agent
workspace is absent, so the next private candidate is reconstructed from the
preserved source and source-law evidence in durable role-specific directories.

Receipt 158 temporarily applies a reconstructed metadata candidate after exact
forward and reverse pin checks. It uses an owner tied to the original nodes
and operation projection, a consumed preparation loan, bounded complete scope
facts and exact traversal fallback. Independent source-law and bounds reviews
accept those representation boundaries. All 118 capture cases and 31 public
control and owner-row cases pass, including the new scope, cyclic-order,
refusal/retry and fixed-stack witnesses.

The seventeen unchanged SQLite cases yield thirteen passes and four typing
work refusals. Reset/clear regresses from the productive baseline's passing
case; copying, its NUL variant and persistence remain refused. The candidate
is not retained. All forty-seven pins and the three exact productive files are
restored, with no engines active. Two unused operation parameters are also
reported during compilation. The next comparison measures whole graph builds
and their contained metadata intervals on both exact variants, including the
reset regression. Source-law equivalence and phase encoding alone do not
establish lower cost, program admission or a completed delivery.

Receipt 159 compares the exact productive sources with the rejected receipt-158
candidate using diagnostic wrappers that preserve the original bodies, charges
and results. Four unchanged public cases run in fresh processes for each
variant. Resume passes on both; productive reset passes and the rejected
candidate refuses it. Copying and persistence retain typing work refusals.
All eight strict readers accept complete owner and call coverage: neither
diagnostic storage cap is reached. All forty-seven pins and the three exact
productive files are restored, with no engines active.

Copying's matched 556-node ValueGraph build increases from 30,033 to 40,986
units. Its contained metadata increases from 16,122 to 27,075; the remaining
13,911 units are identical. Reset's matched 376-node build increases from
21,090 to 28,832, with metadata increasing from 11,798 to 19,540 and identical
remaining work. Persistence's productive 1,226-node build completes in 68,677
units, including 37,759 metadata units. The rejected candidate instead stops
at the unchanged 327,680-unit ceiling during that build: its 81,399-unit
observed prefix includes 55,069 metadata units and only ninety of the
productive run's ninety-eight completed metadata calls. That prefix does not
establish a complete cost or justify a larger limit.

The source study identifies an overlap despite distinct requested roots:
increasing original-node order checks a function body before an enclosing
type abstraction requests the function node containing that body. The next
private candidate studies summaries of completed requested roots with complete
binding exclusions, reusing the existing original-header lookup where practical.
A conservative decreasing-child-coordinate witness can qualify an independently
acyclic summary; forward edges and cyclic inputs keep the structural reader.
No eager per-descendant preparation protocol, limit increase or new semantic
authority follows from this study. Actual savings and successful larger-program
execution remain unverified.

Receipt 160 temporarily applies the smaller requested-root candidate after
exact forward and reverse pin checks. Its owner borrows the original nodes
and operation projection. A consumed preparation state publishes complete
requested-root facts or a structural recipe; it reuses the existing header
lookup and pays a scalar summary index per retained header. Eight focused
laws cover complete binding exclusion, cyclic and forward fallback, seen
backedges, capacity, refusal/retry and fixed-stack traversal/disposal.

All 116 capture cases and all 31 public control and owner-row cases pass.
The unchanged seventeen SQLite cases give fourteen passes and the three
existing typing work refusals in copying, NUL handling and persistence.
Reset/clear passes, as do the capture/resume and discard cases. Compilation
reports no warnings. All forty-seven pins and the three exact productive
files are restored, with no engines active.

These results establish focused nonregression, not net preparation savings or
a completed delivery. The next matched measurement records complete graph
construction and its contained metadata work, distinguishing direct warm-root
reads from successful reuse of a previously requested descendant. Fresh
architecture, aggregate checks and larger-program execution remain required
before integration. No source or work limit changes.

Receipt 162 measures the exact productive and requested-root variants using
source-preserving wrappers and bounded completed-splice counters. All eight
processes and strict readers complete; all owner and call details are covered.
Every measured metadata call and graph build succeeds. Original node counts,
requested-root order and nonmetadata work match. Resume and reset pass on both
variants; copying and persistence retain typing work refusals elsewhere.

The final copying graph build decreases from 30,033 to 29,463 units; contained
metadata decreases from 16,122 to 15,552, with thirty completed descendant
splices. Persistence decreases from 68,677 to 66,858, with metadata decreasing
from 37,759 to 35,940 and eighty-eight descendant splices. The final resume
and reset owners save 5,711 and 9,931 units with fifty-three and sixty-two
descendant splices. There are no direct warm-root events. These are actual
later-descendant beneficiaries, rather than repeated identical-root requests.

The first three small helper owners instead add thirty-four, seventeen and
392 metadata units. All cold preparation and publication costs are included
in each owner interval. Do not add metadata to enclosing build work, infer
a common budget from owner labels, or treat final-owner savings as a
whole-pipeline quota or complete cost for the refused programs.

Both exact patch directions and all forty-seven restored pins are verified.
Independent raw readers reproduce the results and reject corrupted receipts.
The exact receipt-160 source is then retained as uncommitted work in progress,
supported by its unchanged fourteen-of-seventeen public frontier and measured
local benefit. It is not an integrated delivery. Fresh architecture and
aggregate validation remain required. The next measured seam is repeated
context-path preparation within one value analysis; it must preserve distinct
live capture and owner associations and must not cache source answers.

Receipt 161 observes original context requests on the retained receipt-160
work in progress. The source-preserving diagnostic keeps the original charged
body, arguments and result. Resume passes and copying retains its typing work
refusal. Both strict receipts have complete owner, request and key coverage.
Copying makes 301 successful context requests with 5,033 units of whole-call
work. All 301 keys are distinct: there are no prior-successful exact requests,
existing-context returns or recursive-prefix branches in this observed prefix.
Resume has two owners with 1,841 and 4,189 context units; their previously
successful requests account for 376 and 1,515 units, respectively. These are
separate original-call observations, not a shared quota or subphase attribution.

Persistence retains its typing work refusal and emits no context events. The
strict reader rejects the missing completed-owner checkpoint; this absence is
not evidence of zero analysis or setup cost. The runner stops at that rejection,
so reset is not run in receipt 161. All forty-seven source pins are restored,
with no engines active. Independent readers reproduce the two complete receipts
and reject corrupted logs. Exact-request preparation and borrowed recursive
prefix lookup are parked: neither has a demonstrated beneficiary in the failing
copying prefix, and persistence has no observation at this seam.

Receipt 164 starts fresh architecture verification on the retained sources.
The 360-second wall-time bound expires during the second source-scanner case;
exit status is 124. The suite does not complete, so it supplies no architecture
pass or diagnosed source failure. All forty-seven source pins remain unchanged,
with no engines active. The final architecture gate requires a complete run
with sufficient wall time. The next cost probe separates original value setup
from edge propagation and observes existing budget charges by source location.
No source-work limit or semantic authority changes.

Receipt 167 combines two disposable source-preserving probes over the exact
retained work in progress. All three narrow files pass forward/reverse checks
and return to their original hashes; all forty-seven source pins are restored,
with no engines active. Copying and persistence retain typing work refusals;
resume passes. All applicable strict readers pass. Persistence has no observed
close interval, and resume has no first-refusal histogram; neither absence is a
zero-cost receipt.

Copying's first close is an admitted 125,507-unit failure prefix, partitioned
into 96,082 evaluation units, 19,684 edge-propagation units and 9,741 remaining
queue/classification/publication units. Evidence evaluation contributes 49,044
successful units plus a 136-unit failed prefix; call evaluation contributes
24,468 units and function setup 13,432. Each partition uses the original budget
before/end values and preserves every original operation and ordering. The
unobserved tail cannot establish the full cost or a fitting program.

The first-refusal charge histograms fill all 512 location slots. Omitted admitted
observations are explicit: 145,277 for copying and 45,790 for persistence. The
retained locations cannot rank the omitted locations. Moreover, validator and
builder discharge sites transfer already measured work into enclosing budgets;
whole-process histogram volumes combine local and transfer observations across
independent budgets. They are useful location/frequency evidence, not a compiler
quota, unique physical work total or isolated function cost. Independent readers
reproduce the raw partitions and omission accounting and reject corrupted logs.

The next targeted question is whether evidence specialization repeats the same
immutable original binding/capture preparation. Exact dictionary identities and
ordered binding positions must remain distinct from actual argument expressions,
creation contexts and live dependencies. No cache or skip follows merely from a
large evaluation interval, and the source-work limits remain unchanged.

Receipt 168 measures original Evidence input prologues and capture-topology
preparation on the retained sources. All three fresh public cases and strict
readers complete. Copying and persistence retain typing work refusals; resume
passes. All forty-seven source pins are restored, with no engines active.
Copying has 366 successful prologues whose exact source coordinates and reader
watches already exist, costing 7,320 units; 215 prologues witness an absent
relation before execution and cost 9,663 units. These relation predicates bound
idempotent-work opportunity; they do not certify prior completed preparation.
The 1,024-detail pool omits 260 calls, while complete count/work counters remain
available. Evidence evaluation encloses these prologue intervals.

Copying has 114 exact-pair warm topology reads and eight cold preparations,
with no completed same-function distinct-Evidence ordered-key projection
witness. Resume likewise has no such witness. Projection sharing is parked.
Resume has 206 complete-watch prologues costing 4,120 units and thirty missing
relation prologues costing 1,370; its details are complete. Persistence has no
Evidence checkpoint, which is absence rather than a zero-cost receipt.

The next narrow candidate replaces the existing slot completion bit with
distinct fixed-setup and Evidence-input phases. A consuming visit installs all
original input watches before publishing the input-only phase. Reuse is limited
to the same slot reader; every live atom and Unknown dependency still routes
through the original dynamic operations. Cold guards and publication are paid.
Connected verification and actual savings remain required before retention.

Receipt 169 temporarily applies the exact Evidence-input phase candidate after
verified forward/reverse pin checks. All 119 capture tests and all 31 public
control and owner-row tests pass, including the three new phase laws. The
unchanged seventeen SQLite cases remain fourteen passes and three typing work
refusals in copying, NUL handling and persistence. Reset/clear and public
capture/resume and discard still pass. Compilation reports no warnings.
All forty-seven pins return to the retained receipt-160 sources, with no engines
active. This candidate remains private and unretained. A matched comparison of
original Evidence evaluation calls must include cold guards and publication
before claiming net savings; the refused programs still have unobserved tails.

Receipt 170 stops after the original copying run because the strict reader
misses a metric prefixed by the test harness. The raw program still reports the
same typing work refusal. The observer, source operations and charges are
unchanged. A reader-only correction accepts the harness prefix while preserving
schema and conservation checks; prefixed malformed records still fail. The
interrupted receipt remains preserved, with all forty-seven source pins restored.

Receipt 174 reuses that exact original copying stream after checking its source
provenance, then runs the remaining five fresh comparison processes. All sixteen
applicable reads and three comparisons pass independent review; corrupted raw
streams fail. The original and candidate copying prefixes have 580 matching
successful Evidence evaluations with identical ordered coordinates, readiness
and semantic end states. Their measured work falls from 49,044 to 42,904 units:
a net reduction of 6,140, including every cold guard and publication charge.
Both closes still refuse work. Additional candidate progress has no matching
original tail, so it establishes neither complete execution nor a fitting cost.
Resume passes on both sources, with complete matching closes. Persistence has
no Evidence checkpoint; its absence remains unobserved rather than zero cost.

After source, regression and net-cost review, the receipt-169 Evidence-input
phase is retained as uncommitted common work. The phase certifies installation
of the exact original input coordinates and reader watches. It grants no whole
capture, output, callable or final-Core validation authority. Live atoms and
Unknown dependencies continue through the original operations. Source work and
depth limits remain unchanged. This retention is not a completed delivery or
integration checkpoint.

The branch observations park further Evidence routing and topology sharing:
copying has only 434 units of warm closure routing and no completed same-function
distinct-Evidence projection witness. Persistence enters its final control type
universe constructor after 324,039 admitted units; successful hashes account for
only 797 units there. A hash cache has no demonstrated substantial beneficiary.
The next investigation brackets original earlier module and provider operations.
Earlier ValueGraph builds account for 9,123 of the 241,645 units admitted before
the final build; the remaining prefix needs causal attribution before adding
preparation metadata or reconsidering a work bound.

Receipt 176 verifies the retained receipt-160 and receipt-169 sources together.
`CARGO_BUILD_JOBS=1 cargo check --locked -p ash --all-targets` passes, followed
by all 1,615 Ash library tests with zero failures or ignored cases. Compilation
reports no warnings. All forty-seven source pins remain unchanged, with no
engines active. This fresh baseline includes the deep-input and provider
regressions; public integration, architecture and final merged verification
remain separate gates.

Receipt 175 cannot compile its temporary probe: two scalar counters read a
private CoreBuilder field from elaboration. No Ash case executes and no earlier
cost attribution follows. The guarded runner restores all forty-seven pins and
removes its helper. Rust LSP navigation confirms the existing crate-visible
`node_checkpoint` accessor returns the required node count. A separate corrected
packet replaces only those two counter reads; the failed packet and raw evidence
remain preserved. The retained productive baseline is unchanged.

Receipt 177 executes the accessor-only corrected probe. All three fresh public
cases and strict readers complete, with 72, 77 and 59 observed whole calls for
copying, persistence and resume. Copying and persistence retain their typing
work refusals; resume passes. All forty-seven source pins are restored and the
temporary helper is removed. No active engine remains; the deactivated Rust LSP
process is recorded separately as defunct, with no runnable work.

Persistence's entry module-body interval is 118,823–327,679. Its first Global
declaration completes at 119,371–181,408, costing 62,037 units; final completed-root
capture starts at 229,422 and admits a 98,257-unit failure prefix. The cleanup-row
guard at that final boundary completes with zero work. Copying's final capture
starts at 152,267 and admits 175,413 units before refusal. These are inclusive
original-call intervals; the refusal leaves an unobserved tail. Lexical nesting
does not establish budget identity, and stage volumes must not be added into a
compiler quota. The next selected boundary distinguishes original body checking
from evidence closing and deferred resource completion. No further cache or
limit change follows from this observation.

Receipt 178 extends the same disposable original-call probe. All three fresh
public cases and readers complete, with 116, 133 and 91 uncensored whole calls.
Copying and persistence retain their typing work refusals; resume passes. The
preservation set now includes every temporary patch input: all fifty source
pins are restored and the helper is removed. No active engine remains.

All three programs check the same two original provider definitions at
6,488–97,165, costing 90,677 units. Persistence's first Global declaration has
five complete scope-copy intervals costing 23,679 units within its 62,037-unit
declaration. Its five copy plans cost 7,500 units. These original-call intervals
do not establish which preparation inside copying is repeated. No deferred
instance or actual-provider-capture call is observed in this path; this is
absence at the instrumented seam, not a zero-cost claim for other analyses.
The final module finish starts at 213,167 and enters completed-root capture at
229,422, confirming the 16,255-unit preparation gap on the same source ledger.
Provider admission and copied-template preparation are the next causal targets.
Direct collection of caller identities remains a source-only consolidation
candidate; no saving, cache or additional work allowance is claimed.


### Copied input preparation consolidation (2026-10-06, receipts 180–181)

The retained working source now collects the original Type/row payload identity
union once after all three unique substitutions succeed. It preserves the final
pending-row map, including its winning values. Freshening still avoids free and
forall-bound identities, nested rows and lacks identities. All three owned
substitutions, original occurrence checks and independent final Core admission
remain. A private borrowed Type/Row input ADT supplies the same checked insertion
path directly; it removes three temporary Type clones and three temporary row
clones. It retains each required owned copy and both cross-kind duplicate guards.

Receipt 180 passes six focused laws, including complete identity union, pending
winners, cross-kind duplicates and every insertion work cut. Its complete public
SQLite run observes 14 passes and the same three typing-resource refusals across
17 cases. Native resume and discard assertions remain enabled and pass. Receipt
181 applies the unchanged thirteen-boundary observer to that exact candidate.
Each matched successful scope-plan call decreases: copying calls save 91 units;
persistence calls save 510; resume calls save 202 across separate observed
pipelines. Resume's first enclosing checked body saves 101 units. These are
bounded call comparisons, not a combined compiler quota or full program fit.
Provider-group work remains 90,677 units, and actual template-copy work is
unchanged. The failed final capture prefixes grow by 91 and 511 units because
preparation leaves more budget for them; neither is completed capture evidence.

Both runs restore all 50 pinned inputs and remove temporary diagnostics. Source,
bounds and actual-result reviews support retaining the two-file simplification
as uncommitted work. The two borrowed carrier fields have explicit architecture
inventory entries; their full gate remains pending. No work or depth limit rose.
The next delivery isolates the ten generic source/test files against the original
twelve-operation SQLite contract, preserving all pending SQLite manifest,
adapter, library and program work. Required verification, unsigned integration
and checks in the original worktree remain pending for this shared follow-on.


### Separate shared follow-on verification (2026-10-06, receipts 182–184)

Receipt 182 checks the isolated original twelve-operation contract with the ten
generic source and regression files. Formatting and workspace all-targets
checking pass. All 1,621 Ash library cases and 152 connected public cases pass,
with zero failures or ignores. These include independent Core validation,
method evidence, module admission, owner rows, control, retention, effects,
original SQLite and basic arena native lifecycle assertions.

The architecture run initially passes 41 of 43 cases and exposes two stale
source-inventory assertions. Receipt 183 adds the owned summary carrier and its
two cycle coordinates, and follows the borrowed input delegate into its
canonical charged insertion for the relational check. All 43 architecture cases
then pass. Its strict Clippy gate stops at one cfg-test range-loop lint; rustdoc
does not run. The private correction changes only that test loop to enumeration.
Receipt 184 passes formatting, workspace all-targets checking, the focused
capacity law, strict workspace Clippy and rustdoc with warnings denied. Its
explicit return restores all 54 pinned inputs, preserves status and the empty
index, and leaves no active engine. No compiler behavior or limit changes in
either verification repair.

The raw results and exact source/restoration pins are retained in
`shared-original12-gate-182/`, `shared-original12-gate-183/` and
`shared-original12-gate-184/` under the common evidence directory; the final
source export is pinned in `shared-lint-repair-184/export/`. The earlier
fourteen-operation receipt 180 remains fourteen passes and three
`TypeResourceExhausted` failures: copied Unicode/BLOB/null results, bound NUL
input and transaction/reopen persistence. Isolating the original twelve-operation
contract does not discharge those pending package obligations. Observed failed
capture prefixes are incomplete work, not a cost-to-completion or fitting quota.

To repeat the integrated S-01 and basic arena capabilities, use the root
workspace with the coherent original manifest, adapter and source fixtures:

```bash
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test provider_sqlite_source copying_sqlite_session_executes_through_public_foreign_runtime -- --exact
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test provider_arena_source arena_acquires_queries_actual_usage_and_releases_through_public_driver -- --exact
```

The SQLite case observes nested successful completion with 42 and statement
finalization before connection close. The arena case observes actual usage
`(0, 64, 0, 4)` and release exactly once. The programs and public driver setup
are linked in [the package instructions](README.md#reproducing-common-source-cases).
Typed arena allocation and borrowing remain excluded. Reproduce the connected
shared public gate with:

```bash
CARGO_BUILD_JOBS=1 cargo test --locked --no-fail-fast -p ash --test core_validation --test method_parameter_resources --test foreign_module_admission --test provider_control_source --test provider_retention_source --test provider_owner_rows --test provider_sqlite_source --test provider_arena_source --test effect_modules -- --test-threads=1
```

Root must preserve the pending package, review and commit the shared diff,
perform the unsigned original-branch merge,
and run fresh `CARGO_BUILD_JOBS=1 cargo xtask verify` there before naming a
completed follow-on delivery. These cost repairs change no selected experiment
contract or normative language semantics. They establish no mechanized
whole-P-1 correspondence proof or completed String/TEXT package.


### Integrated preparation-cost delivery (2026-10-06, receipt 186)

Common commit `183e9d506f0e3a41833f29b3e614616345169074` is merged into the
original branch by unsigned merge `5991e3d882b4a161c137fb826e73e79c149d550a`.
The parents are original tracking `7cf295ee266997be22ee54ae8ecb2323372f22c9`
and that common commit. The exact ten-file export is
`shared-lint-repair-184/export/`, pinned by
`2e482c55cf2dd5f0e244b8135cd36c70f4795e4ed84d254376c4cef5ea2bcadc`.
Only the two root-owned tracking documents accompany those files. SQLite's
manifest, adapter, library, examples and expanded fixtures stay outside this
commit and remain preserved working changes.

This delivery reuses immutable preparation through private data phases and
consuming evidence. Capture input reuse requires the exact reader slot and
context; live values, unknown demands, callable routing and actual captured
control still undergo their original analysis. Bounded function metadata retains
complete ordered sources or a certified bounded compact summary, with the
original fallback. Copied Type/row inputs use one checked borrowed insertion
route and the complete original dependency union, retaining all three required
owned substitutions. No quota or depth limit rises. The measured reductions and
incomplete failed prefixes remain distinguished in receipts 162, 174 and 181.

Receipt 186 runs the unfiltered root workspace verification in the original
worktree with one Cargo build job. Format, metadata, all-targets build, strict
all-feature lint, all-targets/all-feature tests and rustdoc pass. The outer Ash
library summary is 1,621 passes; architecture is 43 passes. All 117 reported test
summary blocks have zero failures and zero ignores. That block count includes
fresh-child summaries and is not a count of unique tests. Original SQLite S-01,
arena acquisition/usage/release, owner rows, callback/control, retention,
independent Core, module and deep-input paths run in this integrated gate.

The explicit return is `2026-10-06T08:09:14.122089+00:00`, after 1,110.522
seconds. Log SHA-256 is
`cc4ddc359b11abf9e5036f1559b2b7969fab5971319c03ee6a25825faa5d2565`
in `shared-preparation-integrated-final-gate-186/`. All 1,228 tracked input pins
and 26 unrelated working-file pins match; branch HEAD, status and the empty
index are unchanged, and no verification engine remains active.

Before the merge, a preservation guard noticed concurrent updates to three
untracked design notes, DN-0039, DN-0040 and DN-0041. The shell erroneously
continued to the merge after that assertion. Post-merge checks verified both
expected parents, exact source scope and preservation of the updated drafts;
their author confirmed ownership and no executable overlap. The other 23
unrelated pins matched. All 26 current files subsequently remained unchanged
through receipt 186. This workflow defect is recorded in
`shared-preparation-integration-185/integration.json`; future guarded mutations
use checked orchestration. No draft was staged, restored or overwritten.

Common retains shared compiler, Core, capture, provider checking and generic
runtime ownership. SQLite's next preserved import must pair its fourteen-operation
manifest with its matching native adapter, library and exact fixture adaptations
from `sqlite14-fixture-handoff-187/`; the verified twelve-operation checkpoint
does not complete that package. The three larger typing refusals remain pending.
Typed arena allocation, Layout, references, containment, borrowing, sharing and
storage families remain later arena work. DN-0037 and DN-0038 remain separate.
These are tested implementation properties under DN-0036 and foreign adapter
assumptions, not current Ash semantics or a mechanized whole-P-1 proof.
