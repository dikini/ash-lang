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


## Current R-core progress

Focused interface and scoped-evidence migrations now pass all 44 and 53 original
tests respectively. The module-newtype and local-newtype targets now pass 23
and 20 tests. Runtime, hooks and primitive targets now pass 27, 15 and 12 original
tests. Functions passes all 19 original tests. Polymorphism and interface-module
controls pass all 43 and 25 original tests. Module loading now passes all 24
original tests; library imports now passes all 17. Core validation now passes
all 67 original tests and resource modules all 16. Effect Core, typing and
module targets pass all 6, 30 and 15 original tests. Module resolution and
provenance now pass all 11 and 4 original tests. Semantics now passes all 13
original tests. Architecture retains all 47 original passes. Interface resources
now passes all six original tests; its three new restorations are disjoint from
the prior 458, giving 461 original integration restorations. New constructor
negatives, the private Core census, opaque identity unit and explicit constraint
owner unit remain additional coverage, not restored names.

Fresh Library13 passes all 1,599 tests, with zero failures or ignored tests.
It retains all Library12 names and adds only the explicit constraint-owner unit.
All 35 Library10 unit failures remain restored separately, with no lost names or
new failures. Repeated passes are counted once.

Integration244 is the latest complete integration inventory: all 103 targets
ran, with 83 passing and 20 failing. Its 1,782 unique names record 1,739 passes
and 43 failures, with no ignored, incomplete or unexecuted cases. All 1,780
Integration69 names remain, plus the same two passing constructor negatives.
The 43 failures are exactly the original 504 minus 461 restorations; no old
passes or prior restorations regressed. All 8,565 tracked inputs stayed equal
in each complete inventory. Integration227 remains historical evidence at the
preceding policy, not the latest result. The scoped controls retain exact
resolver/checker reasons and labels, full dependency/source authority, defining
factory privacy, result 42 and fresh independent validation after both Effect
transforms. User-effect counts identify the complete instance and handler; whole
transformed effect traces still equal the original trace.




The graph-wide constraint default is now 1,376,256 work units, retaining its
single cumulative owner and Structural calibration route. The finite constraint-
only diagnostic completed the unchanged 5,000-interface polymorphic graph at
1,096,476 units; its 25% reserve target is 1,370,595, rounded to a 65,536-unit
step (25.5163% reserve). The 2,800 and 4,500 monomorphic graphs completed at
368,276 and 590,976; the genuine cycle reached its semantic failure at 352,321.
Temporary source bytes were restored exactly before normal verification. A
bounded inspection found no small optimization plausibly saving 25% of total
work; independent canonical/source/token authentication remains required.

The unchanged public 4,500/5,000-interface programs now exercise normal admission.
One new actual-driver unit retains two finite 400,000-unit continuous-owner
refusals in evidence validation after the 365,559-unit linked prefix; a fresh
independent validation owner completes its 225,417 units. Two explicit original
327,680-unit polymorphic typing refusals and fresh 1,024-interface recovery remain.
These are whole-boundary observations, not derived local tariffs. The unrelated
standalone resolution-Type refusal was measured separately (327,680 refused,
423,346 completed) and its policy was not changed. Original 4,032-width reference
and 1,310,720-unit recursive stress envelopes, exact/short/retry budgets, stacks
and Source programs stay fixed. Type/Source/Core and all other defaults stay
independent. Normal focused evidence passes 14 distinct checks; fresh Library13
and Integration244 cover the stable candidate. Only TASK/plan result prose
changes afterward; canonical format/Clippy are recorded separately.

Architecture240 audits the complete carrier inventory: 65 new sites and nine
exact coordinate renames retain existing ownership profiles and iterative
owners. Region binders and transient values remain owned; runtime values share
immutable facts, while captured frame segments retain mixed ownership. No new
ownership mechanism or observed runtime disposal defect is claimed.
The evaluator's existing transition handoff now checks its empty control slot
before frame mutation; all 53 previously direct production refills use that handoff. Direct-step
unit fixtures consume and check their expected pending control only at the
simulated step, retaining original refusal-state, budget, trace and heap checks.
Core row replacement uses the existing family disposal contract. Vacant map
insertion avoids replacing prepared quantifiers; displaced nominal-kind facts
use their existing disposer. Tight transfer checks cover the existing heap,
captured-continuation and fallible quantifier handoffs, with adversarial cases.
The scanner retains the source backing field at unmatched closing delimiters;
its synthetic fixtures now include the canonical recursive Kind declaration.
Existing glob/shadowing guards remain fail-closed. Two compile-time identifiers
are permitted only at their defining Core paths. The closed Pure mock keeps one
authenticated conversion; its unchanged Source independently uses Effect Core.

The preceding Architecture240 normal evidence passes architecture 47/0, Library12 1,598/0/0, semantics
13/0, effect runtime 27/0 and existing native storage 31/0, at identical executable
inputs. The native target executes actual C-backed generated programs and retains
exact values and traces. This is connected native evidence, not R5 finite-provider
or canonical full-gate acceptance. Only subsequent TASK/plan result prose changes
after those runs; current Library13 and Integration244 supersede those inventories.

Semantics Source execution uses complete independently validated Effect Core for
self-reference and all five original newtype representations. Exact public nominal
types, values, conversion counts and child adjacency, and whole repeated traces
remain. Five intentional Pure contracts now use one explicit scalar-main donor
with the original Unit-call shape and optional local recursive group. Unchanged
Source companions still check and execute through Effect Core. Exact Pure 7/9
and 9-to-7 traces, strict recursive fold reduction, mathematical integer payloads,
primitive equality, full metadata and the original-span ConstantFolding cause
remain separate from allocation-bearing Source execution.
The final identity fixture keeps all four original Sources. Its public check
compares complete exposed metadata, typed binders, ordered children, bidirectional
sharing and every raw Enter event under the exact remap. One new crate-local
complement checks opaque region, allocation, request, buffer, tuple and stored
closure metadata against the same Sources, including actual Add/Multiply and
region/allocation/request/closure coverage. Fresh arena membership is independently
validated while resolver identities, full types and origins remain equal. No
public inspector, decoder or product change is introduced. Semantics225 passes
all 13 original names plus the new private unit and existing row-registry caller;
Final226 formatting and canonical Clippy use identical executed bytes. Library11
remains the prior complete library result with the added focused unit reported
separately. No fresh complete integration or native inventory is claimed.

The resolution/provenance fixtures authenticate each actual dependency target
before resolving the intended entry or named module. Resolved-only controls do
not check their target; diagnostic controls retain two independent resolutions
and fail only at entry checking. Hidden nominal selection uses its defining
entry identity. Source provenance uses complete linked Effect Core and every
source/module pair. Public source-binder ownership, exact function/body spans
and the sole typed closure parameter retain RecursiveBindingLowering,
FunctionLowering, TypeChecking and occurrence causes. Successful arithmetic
checking records its cause on the returned context binding around RegionBuffer;
the unchanged exact primary/related-span assertion checks that binding.
The repeated-summary witness retains its original program, width and import
count. Its obsolete fixed-limit refusal becomes normal-policy success plus the
existing calibration observer's cumulative resolution owner check: one completed
phase per canonical module, unchanged actual allowance, increasing work and one
matching final endpoint above the old fixed limit. No product policy changes.
Module216 passes 11 original names; Provenance215 passes four at unchanged final
bytes. Final217 format and canonical Clippy pass without executable changes.
Library11 remains carried complete library evidence; this is no fresh full
integration or native gate.

The latest admission repairs preserve exact defining/export identities and
resolver-owned privacy errors across every actual dependency edge. Module-loading
controls retain the complete compiler-service prefix, original user import order,
1,024-depth/256 KiB chain and full pending-edge width. Core newtype and evidence
controls use all-source Effect validation: exact nominal conversion owners,
source-owned full-typed evidence closures, ordered complete arguments and fresh
validation after both transforms remain. Manual Pure corruption, owner, depth,
resource and poison controls are unchanged.

The remaining seven Core evidence/linked controls retain source-owned complete
callable schemes, exact adapter/method identities, ordered arguments and actual
prerequisite application edges. Nested selections require two distinct adapters
of the same implementation with different full heads, value 82 and both fresh
transform validations. Their known Forall1 prerequisite comparison covers the
whole effectful arrow, pair domain, each own bound variable and complete result
computation, without a new equality API. The two linked fixtures retain their
original sources, summary/route/kind/binder facts, registry sharing and public
execution. Their exact source 40 + 2 operation remains an allocating RegionBuffer
with full row and both direct operands after identity and folding. One small
three-node Pure control, using each original arithmetic span, separately retains
Add-before-fold, generated ConstantFolding cause and result 42. This split makes
no claim that allocating Source arithmetic is optimized away. The extensive
manual Pure corruption/depth/resource/ledger suffix is byte-identical.
Resource-module fixtures retain the complete service/source inventory and exact
checked module identities. Negative entry resolution authenticates each actual
preceding dependency but never checks the malformed entry early; sealed-provider,
constructor/privacy and direct-builtin acquisition obligations are unchanged.
The final frozen targets pass 67 + 16 original names, with no added or missing
names and no product, policy, API or program change.


The original 128-method and 192-function public standalone publication witnesses
first refused in the Source type-work owner. Separate temporary tracing recorded
atomic prefixes of 323,970/327,680/request 4,125 and
324,970/327,680/request 9,986. A finite Source-only completion probe then measured
complete defining-module costs of 366,561 and 534,701, with independent entry
costs of 71,000 and 201,323; all four modules completed before the unchanged
stale census failed. Exact original meter/checker bytes were restored afterward.
The earlier reviewed public `check_module` Source-only normal default was 720,896
structural-work units (next 65,536-unit step above the 668,377 reserve target),
with Structural calibration preserved. All explicit caller/driver budgets,
other defaults and original programs/widths remain unchanged. Normal verification
passes all 17 library-import cases and the existing cumulative-owner, policy,
observer and reporting checks (30 distinct cases); it is separate from the
temporary probes and restores the two original default-checking witnesses.

Three focused library tests now pass after exact expectation repairs: canonical
DefaultAlloc after Cell discharge, the complete five-group authorization graph,
and the derived six structural cells plus one provenance handle for a resolved
type copy. These are three unit restorations, separate from integration keys.
An unchanged resource-typing run records 97 passes and five Source-work
refusals over 102 original names, restoring three more Integration69 names
(an intermediate 404 staged integration restorations). The five original
residuals were measured without changing programs, depth 24 or the 256 KiB stack.
Four complete entry owners used 799,093, 828,475, 852,554 and 4,220,960 units;
the nested witness completed at 12,517,818. Temporary probes were restored
exactly. The selected public Source-only default is now 15,663,104 work units,
the next 65,536-unit step above the ceiling 25% reserve target of 15,647,273
(25.1265% reserve). Structural calibration and all explicit/driver/other owner
policies remain unchanged. Normal166 passes all 102 original resource-typing cases, all 17 library-import
cases, the three repaired units and 13 existing owner/policy/calibration/reporting
controls: 135 distinct names. All eight old resource failures now pass without
program, stack or depth changes; no original resource name is missing or newly
failing. The eighteen evidence/summary controls below complete the 35 Library10 unit
restorations. Library11 freshly verifies the complete library at zero failures;
these unit names add no integration credit. Diagnostics remain separate from normal
verification, and integration-only inventory/full-gate clearance remain pending.
The connected unchanged resource-runtime target also passes all 32 original
names, restoring its one old Source-work failure. These fresh target observations
remain separate from the complete Integration69 baseline.

Six additional elaborate ledger controls now pass with production bytes unchanged.
Module construction's actual paid setup stays in the owner before each local
allowance. Tuple retention derives two effect-catalog scans, wrapper 1, real
DefaultAlloc qualification/union 8 and tuple-copy 3 (14 for the canonical
single-effect fixture). Match retains its original 17 arm/matrix/copy units plus
two integer catalog scans (19); inferred-function work retains its original
48 local units plus constructed-row lookup 1 and empty-row clone 1 (50).
The early inference-record refusal remains atomic, with prefix 0/17 and two
fresh exact retries. The relational declaration guard derives 15 units from
preflight/retention and the complete First/absent-Second occurrence walks;
its exact MethodParameter diagnostic and two fresh retries remain. Cumulative
constraint and implementation-substitution controls measure complete successful
check/freeze boundaries, retain one-short/exact/fresh-owner admission and
second-module no-refill, and make no local-tariff or atomic-saturation claim.
These six unit restorations add no integration credit, API, policy or semantic
change; a fresh whole library/integration inventory and canonical gate remain
pending.


Eight Core unit controls also pass at canonical-formatted frozen inputs. Linked
scalar and Arrow matching retain the derived local formula 2R + K + S + L,
including canonical service parameters and the sole entry-region identity;
the exact fixture fees are 16 and 14. Four method-authority controls measure
complete successful authority phases for exact/one-short/fresh admission.
Parameterized newtype checking retains its independent 4P + 1 = 9 parameter
counter, complete three-source prelude and canonical Box parameter/representation
premises, separately from the complete consuming-validation boundary.

The linked transform retains four anchors, one embedded producer remap, exact
coordinate candidate visits, carrier/key/replay fees, fresh validation and shared
Arc/Weak lifecycle. Restored temporary probes completed identity and folding at
2,025 work units each; static carrier/candidate inventories leave a fixed
1,946-unit reconstruction/structural-copy subtotal after the explicit terms.
Normal retries use that fixed subtotal rather than measuring their own allowance.
Core197 passes all eight original names after formatting; Final198 format and
canonical Clippy pass without subsequent executable edits. Production prefixes
remain byte-identical. These eight unit restorations add no integration credit,
policy, API or semantic change; the complete library inventory is not refreshed.


Eighteen evidence/summary ledger controls retain local derivations separately
from complete admission boundaries. Linked kinds retain the five canonical
service nominals, original user kinds and independent owner records. Full
DefaultAlloc rows add their real structure, synthesis, substitution and comparison
work; original lookup-width deltas and local relationship/key fees remain.
Block scheduling preserves unscoped 8-constraint/0-type atomic admission and
checks scoped 18/10 work with exact annotation ownership and fresh retries.
Registry rows retain local 8, prefix 45 and complete 54; combined linking derives
83 constraint/94 type units. Its 74-type cut leaves the paid 13-unit prefix before
the atomic 62-unit retention charge; final one-short and two fresh retries remain.
Complete catalog/header/public/detached-summary donors measure only their own
whole boundaries, retaining exact source identities, kinds, rows and dual errors.

The deep constructor fixture now mutates only its actual Deep/Make defining
owner and compares that same checked summary with the imported physical scheme.
Its unchanged pure payload of depth 16,384 pays original 13D, the required export
effect-inventory scan 2D + 1, admission 2 and fixed metadata 211: 245,974 units.
The public deep fixture retains depth 32,768, generated-origin depth 16,384 and
its 9D + origin + fixed 456 boundary (311,752 constraint/17 type units). Both
256 KiB workers, exact/short/default admission and iterative disposal pass.
The temporary complete-cost probe was restored exactly before normal controls.
Canonical formatting preceded Final208 and Library11, which freshly covers all
eighteen controls at committed executable bytes; no production/API/policy change
or new unit name accompanies these repairs. Integration/native/full-gate and R5
specification/Main acceptance remain separate and open.


The effects fixtures use complete checked dependency summaries and the actual
entry's defining effect/operation. Source row controls compare complete canonical
DefaultAlloc instances with every original user instance; open rows retain the
exact rigid binder and lacks facts. Cell discharge leaves only DefaultAlloc,
while forwarding and delegation retain precisely their original State instances.
Inline explicit and omitted rows retain State<Int> plus DefaultAlloc and
DefaultAlloc alone. No row is projected or selected by spelling alone.
The discard/resume fixture still synthesizes Unit with an empty expression row
before capture proof, then independently validates and identity-revalidates with
all actual source/module pairs. Manual Core mutation/reason/identity/transform
checks and 32,768-node/64 KiB disposal remain unchanged. Effects210 freshly
passes all 51 original names, retaining 22 prior restorations and adding thirteen;
Final211 format and canonical Clippy pass at identical executable bytes. Library11
is carried without a repeat; these integration-test edits change no product/API,
Source program, policy or library-test input.

Runtime trace controls retain all 13 original Source programs, exact user event
vectors/counts/handler identities and whole raw transformed-trace equality. A
local test classifier identifies canonical compiler-service operations and full
validated handlers, rejects unknown events and attributes contiguous restoration
blocks to the immediately preceding resume. Raw observations remain available.
The manual 4,096-addition/256 KiB continuation and 24-hook/256 KiB fresh-process
witnesses retain their original controls after actual-entry/provenance repair.
Primitive admission now checks only preceding dependencies; its deliberate Pure
scalar pipeline, exact trace, huge integers, poisoning and manual closure remain.
Those runtime/primitive fixture migrations changed no Source rule, API or
runtime limit. The public Source-default policy exception is recorded above.

Function Source Core controls retain exact original binders, owned callable
subtrees, parameter identities, source spans and causal origins, with complete
own-graph canonical allocation rows. Returned capture checks identify the exact
offset binder through public child edges and execute the same function body;
public rendering/debug remains opaque. The application trace retains all twelve
original semantic role IDs and adds two actual Source closure-creation IDs. Its
exact fifteen-event sequence includes main's once-created increment capture
before entry and the later ordinary lookup, preserving function/argument/body
order. Raw trace evidence remains; no creation is treated as administration.
The deliberate Pure diagnostics and structural arrow rendering are unchanged.

Polymorphism controls retain exact source binders, canonical partial Pair identity,
ordered type arguments and fixed kinds, complete scheme/row/lacks traversal and
fresh independent validation after both transforms. The paired higher-kind run
keeps the complete non-erasure event vector, lookup count and frame high-water
mark equal; generic record creation adds one abstraction entry and its call one
application entry. Evidence retains all nine semantic IDs, including its
metadata-only type application, in an exact ten-event capture/view sequence.
Only that authenticated adapter forwards its known variable rather than entering
its type-application body. A whole Effect depth sanity bound of 32 replaces the
obsolete Pure depth 3; this does not assert absence of temporary ordinary evaluator frames.
Interface-specific frame inventory remains excluded.
All other retained-child checks and exhaustive runtime inventories remain.
Interface-module admission preserves resolver-owned privacy errors and defining
identities while authenticating every actual dependency edge's own summary.

First-class constructor positives use existing inferred local functions because
CP-0025 default-expands explicit callable annotations while erased constructor
invocation stays pure under exact row equality. Both original annotated programs
remain verbatim negative controls (argument/result ownership); no coercion or
product rule changed. The returned closure checks its exact lexical offset binder
among public capture edges, complete callable type and usable result after scope
return, rather than the historical whole-environment size. The original deep
integration name retains 4,096 scopes/256 KiB and public Unit/escape checks. A
separately added private driver test retains the exact Core scope census and
execution under existing paid program owners. Its standalone Source type-work
refusal was diagnosed at 327,680 cells; no default capacity was raised.

The fixed generic-prerequisite program completes with 93 Enter events and 12
frames; its whole Source sanity ceilings are 120/16, retaining exact method IDs,
five-event application prefix and prerequisite ordering. These are test ceilings,
not runtime budgets. Current dynamic semantics explicitly records the historical
32/6 profile; R5 must reconcile that statement under CP-0025's accepted timing
transition before Main or whole acceptance. The canonical gate, remaining
regressions and R5 finite-provider/operational specification work remain open.

The following measurements and staged checkpoint counts are historical evidence.

R-core's unchanged 8,000-member/256 KiB driver test now passes under normal
selected policy. Closure preparation uses one charged temporary first-variable
index per batch; Source work fell from 519,069,391 to 7,149,428 and Final from
350,952,800 exhausted to 2,296,950 complete. The separate program primary-builder
allowance at that checkpoint was `max(327680, 8*S)` from the already-paid canonical source closure;
its largest complete arena used 2,680,644 at S = 438,691. That checkpoint
retained the then-current Source/Final/Core and rewrite coefficients,
standalone/image capacities and original assertions; [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md) records the measurement and ownership. This restores
one required test, not the full gate; remaining fixture and product failures
still require repair before integration.

The unchanged 10,000-member cyclic-data witness at 320 KiB later identified a
primary-owner refusal during cleanup row replay: 3,189,424 of 3,189,424 cells,
requesting one. Aggregate Source was not the refusing owner. A finite primary
16*S diagnostic completed the original render/count/drop assertions; the largest
independent primary arena used 3,430,528 at S = 398,678. Its 25% target is
4,288,160, so the selected rounded policy is now `max(327680, 12*S)` (4,784,136
here). Source, Final and Core completed at 8,654,930 / 2,320,736 / 15,063,023.
No small replay optimization justified changing its propagation/strict-removal
and rollback obligations. All temporary diagnostics were restored; standalone,
rewrite and other owner policies remain unchanged. Normal verification of the
selected policy is recorded separately from the finite diagnostic: the original
10,000-member/320 KiB witness passes uninstrumented with complete Source/Final/Core
reports at the same costs, alongside all 25 driver, four policy, 57 builder and
one exact/short/retry replay tests. The kind fixture now resolves only its actual
entry after authenticating preceding dependencies, preserving original phase,
count and span assertions; all 27 tests pass, restoring 25 baseline failures.
Their names are disjoint from the prior 203 staged restores. Including the newly
passing original cycle witness gives 229 staged integration restorations, not a
refreshed full-suite result. Library9 and Integration69 remain the latest
complete baselines; all whole-gate requirements remain pending.

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
witness and 8,000-member worker. The latest full-library inventory records
1,560 passes and 35 failures across 1,595 executed names. It restores 17 existing
failed names since the prior draft without a new failure. The earlier private
Source capture test has one justified rename and passes under its Effect lifetime
obligation; its old name's disappearance is not counted as restoration. The
complete workspace gate remains pending and no whole criterion closes here. These
35 failures are the latest full-library backlog. The subsequent integration-only
baseline executed all 103 workspace test targets: 1,276 passes and 504 failures
across 1,780 package/target/test keys, without ignored, aborted or unexecuted
cases. These are separate inventories, not a refreshed combined total.

Checkpoint 10 removed the concrete Effect operation sum from the
family-neutral Core interface through borrowed closure, tuple and request views.
Contextual anonymous functions now infer only the residual beyond the expected
row's known prefix, using existing charged row operations and transactional
unification. Fixed/rigid rows, exclusions and named-value equality are unchanged.
The two original empty-residual callback programs pass; a four-case Source/Core
control checks empty and parameterized residuals, complete callback rows and
execution. Ten focused product checks, 78 capture checks and the native suite's
31 cases pass (29 native executions and two exact admission refusals).

Dependency-ordered diagnostic/resolution helpers retain every builtin dependency
and return the original unresolved entry or checking result. Checkpoint 10 selected reruns
restored 135 baseline integration failures, with no newly failed names in those
selected groups; this is staged evidence, not a new full inventory. Remaining
failures include seven known Core ledger cases, six effect-row expectations and
one direct setup path, fourteen runtime trace/setup cases, one resolution type
shape and three diagnostic/profile expectations. Two architecture probes now
reach a separate visible-glob carrier ambiguity in evaluator region metadata;
no manifest entries were guessed. The complete normal gate remains pending.

Checkpoint 11 reused dependency-ordered checking for original
positive and negative entry endpoints. Exact callable checks retain their kinds,
arguments and requirements and now include the closed singleton DefaultAlloc row
from the actual defining checked compiler module. Import-route checks preserve
the two source edges' target identities and distinct spans alongside the complete
service graph. Both complete targets were rerun: interfaces 38 pass / 6 fail,
interface selection 40 pass / 0 fail. All 68 original setup-blocked names now
pass, with no new or missing failed names. Their exact name set is disjoint from
the prior 135 restores, yielding 203 staged integration restorations without a
refreshed whole-suite total. At that checkpoint six interface failures reached existing
Source-to-Pure Core producers; no stored-closure decoder, trace projection,
capacity change or production code is included in this fixture batch.

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
An earlier all-feature library inventory executed 1,595 test names:
1,560 pass and 35 fail, restoring 17 existing failed names since the prior draft
checkpoint without a newly failing name. The earlier private-Pure Source
expectation was renamed to assert required local Effect lifetime summaries; the adjacent Pure
capture-demand exact/short/retry contract remains unchanged and passes. That
rename is recorded separately, not counted as a restored old name. All 8,565
tracked input hashes match before/after the run; only this task and its plan
inventory prose changed afterward. Full workspace/all-target/all-feature Clippy
and the 114 focused driver/policy/capture/reporting/observer checks pass. Seven
integration names retain prior reviewed evidence because this checkpoint changes
only test fixtures and progress prose; they were not rerun here. The fresh library
inventory includes the overlapping 107, which are not added again. This is partial repair evidence, not the complete workspace gate.
Core validation fixtures now retain complete provenance and actual defining
user owners. The manual seven-node Pure donor keeps its original canonical
relay/F facts through existing registry construction, with separate reserved-source,
authority, final-carrier and identity-discovery debits. Its exact/short/retry and
original deep 256 KiB assertions pass. Closure mutations inspect actual stored
code, retain full rows/capture layouts, preserve the authenticated entry root,
and reach their original rejection reasons and anchors. Extra-use tests check
incoming authority at the original source before full refusal; the distinct
Return mutant is not claimed otherwise ordinarily profile-typed. Whole-validation
one-short cases preserve paid prefixes under atomic refusal rather than assume a
rejected bulk debit consumes its remaining credit. Per-charge accounting tests
retain their specific exact debits. These are test-fixture repairs, with no
production behavior, capacity or meter change. The 35 remaining failures are only
the library backlog at checkpoint 9; the integration-only baseline above was
subsequently executed before further ledger migration. The final canonical gate
remains pending.

Cell mutation donors now validate through the actual Source/Effect pipeline
before corruption, with physical closure capture/layout metadata kept coherent.
Source Effect transforms preserve region arithmetic and its allocation effects;
the independent seven-node Pure contracts retain actual folding and exact
budgets. Full dependency provenance replaces incomplete manual import setup. Source
newtype/pattern fixtures now lower and independently validate the complete Effect
component, inspecting actual user closure code and RegionTuple constructors.
Import mutations select defining modules while retaining supplied corrupt
summaries. Global-row mutations use named user owners and their actual registry
positions, preserving all unrelated service rows and exact rejection spans;
the same donor validates before corruption. Hidden summary mutations and linked
nominal mirrors now select the defining user owners, with EffectfulFunction rows
preserved. Direct-resolution fixtures pass caller budgets through the existing
full dependency seam; the malformed-order cut includes the real reserved-source
prefix before the original source-summary boundary. Source lexical finalization
uses Effect lowering while preserving poisoning and fresh-retry checks.
Registration rebuilds retain actual module/source provenance. A mechanical
extraction reuses the original paid effect-selection body walker: actual Source
headers select Effect Core, while 96 nested empty blocks retain the exact 97-unit,
one-short and retry proof on a 64 KiB stack. Standalone native donors now retain
all original effect declarations, symbol Arcs and the defining Address kind
through existing registry APIs. Type-only GenericCell donors retain the complete
zero-dependency builtin registry and the same graph's original method catalog.
Image fixtures use the existing Effect encoding/restoration path and complete
source relations, preserving exact wire/preparation/refusal cuts and execution
after source removal. The unsupported Pure registry case first publicly validates
its original unused generic nominal. These are fixture repairs without codec or
allowance changes. The remaining failures require classification across graph fixtures,
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
