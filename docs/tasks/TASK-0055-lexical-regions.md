# TASK-0055: Lexical regions

- ID: `TASK-0055`
- Status: active — partial R3 retention and R4 completion
- Related: [CP-0025](../proposals/CP-0025-lexical-region-construction.md) (accepted for transition),
  [DN-0054](../design/DN-0054-base-lexical-region-memory-contracts.md),
  [DN-0055](../design/DN-0055-algebra-of-regions-lifetimes-and-ownership.md),
  [AD-0012](../decisions/AD-0012-proof-development-feedback-and-build-reuse.md),
  [M2 #53](https://github.com/dikini/ash-lang/issues/53)

> This task organizes authorized work. It defines no current Ash semantics and
> does not authorize product implementation before the R1/R2 gates.

## Dependencies

M1 is integrated into Main at `0d8df03d4db2e70294487fc2e61f3629ff33b246`
through [PR #143](https://github.com/dikini/ash-lang/pull/143). Current
[specification](../../spec/README.md) remains normative. DN-0054 records the
user-approved intended direction. CP-0025 is accepted for transition with a
matching reviewed bounded R1 proof and audited frozen gate, retained by
[PR #146](https://github.com/dikini/ash-lang/pull/146) at `aee02227b69fb6cbbd00c23904ffe2a0c7df6924`. Retained verification and author acceptance closed R1/R2.


R-core's unchanged 8,000-member/256 KiB driver test now passes under normal
selected policy. Closure preparation uses one charged temporary first-variable
index per batch; Source work fell from 519,069,391 to 7,149,428 and Final from
350,952,800 exhausted to 2,296,950 complete. The separate program primary-builder
allowance is `max(327680, 8*S)` from the already-paid canonical source closure;
its largest complete arena used 2,680,644 at S = 438,691. That checkpoint
retained the then-current Source/Final/Core and rewrite coefficients,
standalone/image capacities and original assertions; [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md) records the measurement and ownership. This restores
one required test, not the full gate; remaining fixture and product failures
still require repair before integration.

The reviewed Source driver callback seam now validates and evaluates actual
Effect Core at its real phase boundaries, dropping owned interface input before
independent validation. Focused driver evidence restores six injection/owner
tests, including
registry-owner count and measured/unmeasured failures. Both original Pure
small-stack disposal cases remain passing separately. This is partial repair
evidence, not a full gate.
The unchanged depth-48/width-4 public routes completed resolution at 643,634
cells (S = 11,791) under a finite 2× diagnostic. The selected independent program
resolution allowance is `max(327680, 80*S)` (943,280 here); standalone and explicit
caller budgets and original stack/constraint assertions remain unchanged.
That resolution checkpoint retained its then-current Source/Final/Core coefficients. Temporary diagnostics were removed. The
normal-policy focused refresh passes
12 distinct policy, gas, duplicate-route, Render exact/short and deep-route
tests; the full gate remains pending. AD-0013 records the measured owner and
fitting reserve.

The original 24-owner Cell witness exposed repeated backward-prefix work in
escape checks that consume only owner boundaries. Reusing the unchanged charged
forward walk preserves all owner/payload checks and ordinary capture prefixes;
78 focused control/capture tests pass. Complete Source work fell 37.49%, from
21,142,054 to 13,215,994 at S = 1,791. Finite completion also measured Final
29,736 and full Core 33,035,808, with the original result, acquisition and
reverse-release assertions intact. Source `10000*S` and Core `25000*S` are the
selected rounded fits under the existing 25% rule; Final, resolution, builder,
rewrite, standalone and stack policies are unchanged. All temporary diagnostics
were removed. The normal-policy focused run passes 114 distinct driver, policy, capture,
reporting and observer tests, including the original staged 24-owner 256 KiB
witness and 8,000-member worker. The fresh full-library inventory records
1,489 passes and 106 failures across the same 1,595 names; the complete workspace
gate remains pending and no whole criterion closes here.

## Work

Follow the task-owned [execution plan](plans/lexical-regions.md) through existing
R1–R5 issues. Deliver all six required features: default placement for ordinary
construction, explicit region selection, lexical ownership, bulk reclamation,
region-stored closures and recursive immutable graphs. Usage/lifetime placement
inference remains a later optimization.

The accepted contract and matched proof are retained and verified; R3 is active.
Preserve current Cell, request,
capture, cleanup, kind/row and resource-dependency invariants. Return semantic
gaps to R2 rather than deciding them during implementation.

## Progress

The initial planning delivery consolidated approved allocator, placement, effect,
storage/bootstrap and operational directions in DN-0054 and the execution plan.
It reconciled informative DN-0055 and the trajectory with that scope; that
planning checkpoint claimed no implementation or preservation result.

At R1 preparation, the Main one-shot registry had 763 modules; the existing
frozen 1,035-module integration parent did not match it. R1 therefore used a small
standalone proof root with the same pinned Lean toolchain and an explicitly
empty registration seed. A narrow existing-runner directory option preserves
its checks rather than rebuilding or changing unrelated proofs. This is gate
preparation, not a region theorem or accepted R2 contract.

The standalone runner foundation is retained by
[PR #145](https://github.com/dikini/ash-lang/pull/145) as
`31fcfa5674f7cbd46ee583507f47a5c0cf21170e`. Its independent review and five
focused tests cover only gate preparation, not region preservation.
[CP-0025](../proposals/CP-0025-lexical-region-construction.md) records the
accepted R2 transition contract: prospective activation, canonical owner-targeted callback
and one-shot return, actual backing registration, explicit default/cleanup
operands and fixed paired allocation/release. It is not current Ash.

The reviewed finite model now has eight modules and 195 axiom reports under
`Coherent` step/trace preservation. Its frozen AD-0012 integration passed using
eight independently validated cached artifacts and no fresh module compilations.
The [proof guide](../design/lexical-regions/README.md),
[correspondence and assumptions](../design/lexical-regions/correspondence.md) and
[gate/transfer record](../design/lexical-regions/evidence.md) delimit that result.
Exact source/registration transfer has passed. Independent actual-gate audit
cleared the bounded evidence; root accepted CP-0025's matched semantic content.
Exact-head review, GitHub milestone retention and retained verification completed
through [PR #146](https://github.com/dikini/ash-lang/pull/146) at `aee02227b69fb6cbbd00c23904ffe2a0c7df6924`; R1 #65 and R2 #66 are closed after independent acceptance readback.

The retained partial [R3 PR #147](https://github.com/dikini/ash-lang/pull/147),
at `ac340a31df1d383afce25c7aef3ee08d2e83614d`, connects source tuple construction to explicit context/operand bindings, a typed
request, owner-targeted allocation and initialization into the same supplied host
array. Ordinary owner close retires those arrays; outer selection survives an
inner close. Whole-record residency is separate from projectable field facts.
The private binding facade and pending adapter preserve owner/invocation/layout
and replay guards. This is a partial host tuple result, not R3 acceptance.

The custom tuple path uses one host-level adapter at the existing generated
native boundary. It initializes and reads the supplied address, releases the
Rust-owned fields in the current `Value` representation before calling the
paired provider release, then retires logical records. The provider retains
responsibility for freeing backing. This adds no Ash finalizer or object graph
walk. These Rust representation details do not define Ash memory management or
exempt buffers and captures from region-backed construction.

[PR #148](https://github.com/dikini/ash-lang/pull/148) retained ordinary nominal
storage as `50fb799a469fa7d04f68d506290d2dbae28e35a7`. Its tree equals reviewed
head `233bff0924abd96b1ef7ba7b892acd3627c3a018`; 111 distinct focused cases
transfer by exact equality. The same Value-slot storage and native adapter hold
a private discriminant and optional payload. Constructor functions carry explicit
caller allocation effects, including aliases and higher-order calls. Existing
guarded recursive slots and aliases remain; independent validation rejects
unfinished payload transport and private runtime constructor forgery.

[PR #149](https://github.com/dikini/ash-lang/pull/149), retained at
`a02ae1bb4fa5e27d0bbd95da26eff6997af3348e`, adds actual supplied Bytes/String payloads,
with one borrowed reader and byte-copy/borrow leaves on the same host adapter.
A closed Core operation carries explicit context and original operands; its
existing evaluator control retains preparation, dynamic request and initialization
progress across suspension. Successful append/decode initializes the byte payload
before its nominal envelope; invalid alternatives initialize only the envelope.
`BytesAt`, `StringFromUtf8` and `BytesAppendByte` now use the retained nominal
initializer. Constructive builtin wrappers expose DefaultAlloc; read-only host
leaves keep their actual pure rows. Region-enabled EffectCore rejects raw
constructive intrinsic and literal bypasses; pure/no-region Core remains supported.
Source/native, allocation suspension/discard, independent Core and image checks
passed independent exact-head review and retained verification: 125 distinct
focused cases transfer by exact tree equality. No new build or full gate is claimed.

[PR #150](https://github.com/dikini/ash-lang/pull/150) retained the integer
admission clarification at `5ce3f2943b1efad1f7c0b7a001da43cb06d8d842` before
product work. The retained integer implementation uses private inline `i128` values
and selected supplied byte backing for larger sign/magnitude digits. Literal,
addition and multiplication preparation reuse the existing explicit context,
ordered operands, request and initialization path. Actual Cell values and
summaries preserve digit ownership; unknown Int no longer becomes independent
merely from its type. Mathematical results remain unbounded, while local
arithmetic escape follows the accepted conservative restriction.

Legacy Cell analysis exposed a closure-context join. The implementation distinguishes
invocations and handler dispatches with a finite projection of existing creation
paths, preserving exact capture coordinates, caller/focus parents, oldest-callee
invocation recurrence and class-sensitive dispatch recurrence. The
rejected raw dynamic-ID trial is not product code. The approved dated
[AD-0013 recalibration](../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
uses Source `2600S`, Final `800S`, Core `5300S` and startup `65B`; standalone limits are unchanged.
Normal-driver checks of the two original same-site fixtures and 24 nested Cells
return 42. The original staged 256 KiB stress pipeline also preserves 24 unique
acquisitions and exact reverse release order. A separate whole-public-driver
256 KiB abort was unclassified at that checkpoint; the current bounded
classification below does not add an arbitrary whole-driver stack guarantee.

[PR #151](https://github.com/dikini/ash-lang/pull/151) retained the partial Int
delivery at `df79789134d680f4288b48c0081c6c74c6bf4de9`, with author and
independent retained acceptance complete. Its 216 distinct focused cases transfer
by exact reviewed-tree equality; no fresh build or full gate is claimed. The dispatch repair also restores the original
1,024-level registration stress, including its 256 KiB runtime worker, callback
counts, exact refusal/retry and teardown assertions. Startup fitting uses complete
restore-stage costs; later native admission retains the same cumulative meter.
Focused runtime, image and native checks passed independent exact-head review. The representative bindings helper now checks its actual
entry and passes all ten cases. Other module-fixture setup failures remain
separate; unreached numeric assertions are not verified. No full R-core gate or
R3–R5 product acceptance is claimed.

[PR #152](https://github.com/dikini/ash-lang/pull/152) carries the accepted
[closure timing amendment](../proposals/CP-0025-lexical-region-construction.md#closure-creation-timing-accepted-amendment-2026-10-26)
and the partial closure implementation retained at
`0f2cc97b22b0ee3f14ded9118275cc83c80497ee` on the milestone. Its tree equals
reviewed `f8bee32878764f4beed45b3d7e4d32f4c8fae66c`; independent whole-PR review,
retained verification and author/PM partial acceptance are complete. Ordinary creation now uses the
existing supplied Value slots and common callable reader; initial source lifetime,
outer-selection and polymorphic-view checks pass. Generated evidence wrappers
retain complete allocation rows and exact capture authentication. Record-only
forwarding shares immutable views. Authenticated deferred adapters retain term
captures in the same supplied record and enter their ordered evidence applications
only at type application. Focused checks cover Score capture storage, local and
transitive imported ownership, mixed function/data cycles, source-order creation,
recursive-group resume/discard, and independent capture/layout/row refusals.
Handler-row recomputation and lexical evidence blocks retain actual creation rows.
The retained slice also repairs constructor creation rows, inline function-header
row expansion and full-row evidence validation. Source placement and recursion
suites pass. Callback preflight fixtures now execute in their validated arena;
replay checks recognize exact structured work refusals. Two private disposal
workers preserve all depths/assertions with measured 128 KiB headroom; production
stack settings are unchanged. The original 1,024-level registration fixture
resolved its lexical method capture, then exceeded the previous Source allowance.
One bounded diagnostic completed at Source 4,886,806 and Core 7,763,338 units over
1,582 bytes; the existing fitting rule selects Source `3900S` and Core `6200S`.
Normal-policy deep registration, coefficient and exact capture-quota checks
pass. Machine's remaining four failures and capture's ten failures match the
separately pinned prior fixture debt; their blocked assertions are not verified.
A supported recursive image exceeded `65B`; all nine flows completed under a
bounded `130B` diagnostic, selecting `118B` by the existing fitting rule. Normal nine-flow restoration, fresh native 21-case execution and affected
source/Core checks pass. Existing Pure method-carrier fixtures stop before their
assertions at an Effect lowering boundary; this remains separate from passing
Effect donor guards. Two current Effect Score negatives now preserve the
transformed donor's original evidence anchors, consumers and complete rows while
adding an ordinary same-scope strict Bind use. The full donor validates first;
the Adapter scheme and abstract-domain scheme Variable are then each rejected
with NodeType at the exact unauthorized scheme. The selected final evidence
contains 384 distinct passing test names, including those two negatives, while
preserving the fourteen inherited Machine/capture failures and two obsolete Pure
fixture setup failures as unverified behavior. This is focused evidence, not a
fresh full gate. The feature-gated syntax census now visits existing region
provider/selection operands and bodies; both observer tests reach and pass their
changed coefficient assertions. Its cfg-only repair preserves all 134 default
compiler dependency/configuration pins, allowing the normal 382 passing names to
transfer; the observer adds two fresh names. This retains partial closure
acceptance, not whole construction acceptance. Legacy Pure callback fixtures cover isolated preflight/disposal,
not supplied storage.

A generated-native Score attempt stops in the unchanged image profile: its
registry inventory omits method/head quantifiers, and the method-evidence codec
explicitly excludes concrete implementation owners/adapters. This delivery does
not extend that profile. Host supplied-slot execution and prefix-before-argument
discard cover the deferred behavior; the isolated Adapter carrier wire test is
not a complete source-free Score image or native execution. Native generic and
mixed-cycle checks use the same shared storage adapter. Their final results belong
to the frozen checkpoint receipt. Remaining connected construction/completion
evidence still requires its checkpoint gate. No executable
memory-read-to-Bytes producer exists at the current slim-FFI boundary, whose
native replies are Address or Unit; its borrowed Bytes argument uses the common
reader. The native checks distinguish custom supplied-byte construction/read,
a root-host Bytes argument kept live through a native call, and exact rejection
of an explicit-region payload sent through an unprotected outward request. The
last case preserves the existing lexical payload rule; this delivery adds no
source native-interpretation syntax. This partial delivery does not complete
ordinary-construction acceptance.
That construction checkpoint left observation-before-root-release and the
bounded target-discharge correspondence audit for the following R4 root slice.
Full close/composition, connected R-core and all whole R3–R5 acceptance remain
pending. Existing issues
[#65](https://github.com/dikini/ash-lang/issues/65),
[#66](https://github.com/dikini/ash-lang/issues/66),
[#67](https://github.com/dikini/ash-lang/issues/67),
[#68](https://github.com/dikini/ash-lang/issues/68) and
[#70](https://github.com/dikini/ash-lang/issues/70) retain their review,
verification, integration and author-acceptance obligations.

The partial R4 root slice is retained by [PR #153](https://github.com/dikini/ash-lang/pull/153)
at `dd4137703da03ca404939ecb7b0bf14c0a6e0541`; author and independent live acceptance
confirmed that subset while preserving the whole criteria. It transfers only the
fixed host entry's completion records
to the existing shared observed heap. It authenticates the runtime host pair,
owner, concrete locations and layouts and charges close preparation before
consuming the boundary. Last-owner disposal clears current Rust representation
fields while all root backing remains live, frees backing and then retires the
logical records. An error before observation publication disposes that pending
owner inside the evaluator's existing disposal scope; no new scope hides teardown
failure. Outside that scope, final host disposal retains ordinary host OOM
assumptions. The owner stores no source callback, saved evaluator, heap back-edge
or additional registry; bare RegionFunction clones acquire no heap ownership.
The bounded target-discharge regression keeps a live outer A through a helper
parameter and unrelated inner B. The original source evaluates to Unit; identity
and literal-fold reconstruction both pass full independent Core validation and
execution. Existing private-constructor, escape, request-payload and outer-Cell
backpatch negatives retain the view-origin and dependency boundaries. These
checks follow the existing explicit view/actual-dependency/owner-invocation chain;
no admitted missing-owner example warrants another checker. They do not complete
close-service/removed-backend correspondence by themselves.

For a DefaultAlloc-bearing or open-row invocation, the retained connected R4 composition
implementation binds one Unit allocation-context query after the original cleanup
callback is evaluated once. Closed invocations without DefaultAlloc retain the
original direct callback form; no unused handler or context query is emitted. Cleanup-equation tails
wait until the existing row-completion boundary. A final empty row stays direct;
a final DefaultAlloc row receives a local appended cleanup and query binding at
the original owner ID, with exact outward-row equality checked before retargeting.
The nested allocating-discard regression exercises that latter branch through
ordinary source execution and independent Core validation. Its explicit
saved-view handler surrounds the eventual callback invocation. Independent Core
validation authenticates both forwarding clauses, the query/binder association,
the original callback/Unit/once/origin relationships and the invocation's unique
incoming use. Current admitted Source donors survive identity/fold validation;
well-typed alternative-view, mismatched-clause, extra-use and callback-identity
mutations reach their exact independent refusals.

Control analysis follows explicit view targets through the existing finite
Resource occurrences. Its internal ordinary handler/call/resume equations run
the real saved allocate member at the owner position, and an existing required
cleanup equation runs the real release member before retiring the Resource.
Their existing provider adapters supply the preceding allocation context. Public
backend lookup and removed-handler refusal remain ordinary; no runtime service,
callback package, frame family or registry is added.

Regression checking exposed two value/control correspondence errors in the new
analysis wrapper: its saved body result must remain available independently of
the release's Unit result, and focused lifetime analysis must reuse the provider
initializer completed before Resource entry. The synthetic completion now
forwards the saved service result while ordinary control still executes release;
the existing completed-input cut freezes the initializer without changing fresh
owner identities. This restores progress through provider calls and preserves
large-Int, nominal and Bytes escape checks. A measured outer-placed Score donor
also reaches the same request first with no target facts and then with its actual
owner after existing value-revision replay. Explicit requests check the transported
independent descriptor as payload; their view remains target authority and an
actual dependency. Ordinary request payload checking stays unchanged.

Native fixtures cover allocating cleanup after normal return and discard under a
different surviving default; helper-created cleanup and H/J provider routing;
removed required allocation-only and release-only backends despite a live outer
same-instance handler; corresponding action-local admission; and separate region
handles/block lists sharing a refcounted backend. The isolation case closes A,
reads B's pre-existing tuple, then allocates/reads another B tuple before the
backend's single final close. The action-local backend fixture packages its
outbound Cell write arguments before A entry; cleanup allocates and consumes its
own A tuple, then gates the write on the computed sum. This preserves the existing
conservative payload contract for symbolic generic callables, rather than claiming
new opaque-call precision. PR #154 retained this composition slice as
`0064080b41016679fca26c735b41d2fe119c3867`, with reviewed tree equality and
partial author acceptance. Its 366 selected passes include a native suite of
29 executions and two exact admission refusals; they do not establish the
connected full gate.

Five focused root checks cover structured exact/short/retry, forged pair/record
rejection, shared Evaluation lifetime/weak expiry, repeated close, post-transfer
primary plus teardown failure, and ambient-scope failure visibility. Existing
Observation/value/parts accessors retain the same shared owner. The root subset's
review, retention and partial acceptance are complete, as are those of the
connected composition slice. The root-owned R-core checkpoint is now active.
Its initial canonical gate stopped at test-consumer compilation before later
stages ran. Focused repairs have restored the four inherited Machine and ten
capture tests using complete dependency provenance and actual activation IDs.
They also exposed and repaired stale resume-row finalization without cleanup
equations and lost intermediate arrow rows in curried equation reconstruction.
The latest complete all-feature library inventory executes all 1,595 tests:
1,489 pass and 106 fail, restoring 303 original failures (18 since the prior
draft checkpoint) without a newly failing name. All 8,565 tracked input hashes
match before/after that run; only this task and its plan inventory prose changed
afterward. Full workspace/all-target/all-feature Clippy and the 114 focused
driver/policy/capture/reporting/observer checks pass. Seven integration names
are additional to the library inventory; the overlapping 107 are not added
again. This is partial repair evidence, not the complete workspace gate.
Cell mutation donors now validate through the actual Source/Effect pipeline
before corruption, with physical closure capture/layout metadata kept coherent.
Source Effect transforms preserve region arithmetic and its allocation effects;
the independent seven-node Pure contracts retain actual folding and exact
budgets. Full dependency provenance replaces incomplete manual import setup. The remaining failures require classification across graph fixtures,
selectors, exact ledgers and product behavior; this library run does not replace
the canonical workspace gate.
The final fresh full gate and independent review remain pending.
The historical extra whole-driver nested-Cell diagnostic at 256 KiB does not
establish a guarantee for arbitrary compile_path inputs. Existing whole-driver
small-stack tests on their actual inputs and the staged 24/deep 1024 assertions
remain required; no new stack work is assigned for that historical diagnostic.

R5 still needs actual fixed-capacity refusal preservation evidence: a finite
provider must refuse after an old tuple and cleanup closure occupy its capacity,
then checked discard must consume the old tuple during cleanup while its region
is live, publish completion through an older argument package, and release once.
Existing Pause injections occur before allocation and do not prove that case.
Later R5/specification/final/Main gates and all whole criteria remain open.

Keep implementation tight: reuse existing Ash mechanisms and libraries, prefer
removing duplicate machinery, and seek constructive planner/reviewer scrutiny
before adding a material mechanism. The tuple initializer now retains original
field values in its existing frame before requesting storage; one saved-context
binding replaces the field/storage binding scaffold. Full M2 scope remains required.

## Verification

For the changed task/plan/proof prose, check artifact authority, required coverage,
unchanged future acceptance checkboxes, Markdown structure and affected/incoming
links. The frozen proof gate already covers the transferred sources; do not
repeat it at equal inputs or run product builds for prose alone.

R1 requires frozen mechanized integration and assumption/dependency audits under
AD-0012. R2 requires reviewed model-to-contract correspondence. Product stages
require positive, negative, exact/short/retry, deep/stack and source/Core/runtime
evidence appropriate to their changes. The plan names connected full-gate and
separate Main requirements; this task does not waive them.

## Discoveries

The existing scalar Arena experiments do not prove closure or recursive graph
support. Slim FFI establishes ABI calls, not native memory validity or region
ownership. Ordinary Ash binding contracts carry those assumptions. Required
supplied storage must back actual objects, buffers and closures; quota-only
accounting is insufficient.

A focused default-library Clippy attempt during the R4 root slice reports 16
diagnostics whose enclosing functions or files are byte-equal to retained
`0f2cc97b22b0ee3f14ded9118275cc83c80497ee`. Test linting is not established by
that failed command. These lints join the connected R-core migration inventory;
they are not repaired or waived by the partial root delivery.

The constructor-focused sweep also exposed 22 dependency-setup and four
positional-inventory fixtures that assume implicit builtin modules are absent.
Their migration remains R-core work; the partial nominal delivery does not
establish a clean full suite. The 8,000-member, 256 KiB recursion stress test now
uses the existing driver test seam with one continuous constraint ledger under
the original four-call aggregate allowance. Its evidence stage uses 272,442
units, within the original one-call allowance; the normal driver's separate
327,680 graph-wide limit still refuses that full input. No production allowance
or budget policy changed.

## Deviations

None. No broader permission algebra, backend matrix, FFI type expansion or
omitted-definition-row inference is added. Remove this task and its owned plan
when the completed product checkpoint satisfies the artifact lifecycle.
