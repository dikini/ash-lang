# TASK-0055: Lexical regions

- ID: `TASK-0055`
- Status: active — partial R3 implementation
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
256 KiB abort remains unclassified; the staged result does not clear it.

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
and the active partial closure implementation. Ordinary creation now uses the
existing supplied Value slots and common callable reader; initial source lifetime,
outer-selection and polymorphic-view checks pass. Generated evidence wrappers
retain complete allocation rows and exact capture authentication. Record-only
forwarding shares immutable views. Authenticated deferred adapters retain term
captures in the same supplied record and enter their ordered evidence applications
only at type application. Focused checks cover Score capture storage, local and
transitive imported ownership, mixed function/data cycles, source-order creation,
recursive-group resume/discard, and independent capture/layout/row refusals.
Handler-row recomputation and lexical evidence blocks retain actual creation rows.
The current WIP also repairs constructor creation rows, inline function-header
row expansion and full-row evidence validation. Source placement and recursion
suites pass, but affected Machine checks remain open: callback replay/discard
fixtures, two small-stack aborts and exact capture quotas. The original 1,024-level
registration case now resolves its lexical method capture and exhausts the normal
Source allowance of 4,113,200 work units; attribution is pending, with limits
unchanged. Isolated legacy callback preflight/disposal fixtures use independently
validated Pure closures and are not supplied-storage evidence. Final affected
regressions and independent completed-slice review remain pending.

A generated-native Score attempt stops in the unchanged image profile: its
registry inventory omits method/head quantifiers, and the method-evidence codec
explicitly excludes concrete implementation owners/adapters. This delivery does
not extend that profile. Host supplied-slot execution and prefix-before-argument
discard cover the deferred behavior; the isolated Adapter carrier wire test is
not a complete source-free Score image or native execution. Native generic and
mixed-cycle checks use the same shared storage adapter. Their final results belong
to the frozen checkpoint receipt. Closure acceptance and remaining recursive
initialization/capture/abandonment evidence still require independent review. No executable
memory-read-to-Bytes producer exists at the current slim-FFI boundary, whose
native replies are Address or Unit; its borrowed Bytes argument uses the common
reader. The native checks distinguish custom supplied-byte construction/read,
a root-host Bytes argument kept live through a native call, and exact rejection
of an explicit-region payload sent through an unprotected outward request. The
last case preserves the existing lexical payload rule; this delivery adds no
source native-interpretation syntax. This retained partial delivery does not complete
ordinary-construction acceptance.
The host root retains backing through the existing observed heap, but
observation-before-root-release ordering remains pending. Target-specific discharge correspondence/regression audit, full close/composition,
connected R-core and all R3–R5 acceptance remain pending. Existing issues
[#65](https://github.com/dikini/ash-lang/issues/65),
[#66](https://github.com/dikini/ash-lang/issues/66),
[#67](https://github.com/dikini/ash-lang/issues/67),
[#68](https://github.com/dikini/ash-lang/issues/68) and
[#70](https://github.com/dikini/ash-lang/issues/70) retain their review,
verification, integration and author-acceptance obligations.

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
