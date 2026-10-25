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

The first R3 work checkpoint adds region/selection syntax, shared default-effect
expansion, explicit owner/handler lowering, generated root setup and runtime
owner/close control. The binding facade exposes only Request, Storage and three binding functions;
its pending backing adapter checks owner, invocation, layout and replay. Focused
tests cover this control plumbing, not actual supplied storage.
Persistent records, buffers, closure captures and recursive slots still use the
previous representations. Target-specific discharge, typed initialization, full
close/composition, R-core and all R3–R5 acceptance remain pending. Existing issues
[#65](https://github.com/dikini/ash-lang/issues/65),
[#66](https://github.com/dikini/ash-lang/issues/66),
[#67](https://github.com/dikini/ash-lang/issues/67),
[#68](https://github.com/dikini/ash-lang/issues/68) and
[#70](https://github.com/dikini/ash-lang/issues/70) retain their review,
verification, integration and author-acceptance obligations.

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

## Deviations

None. No broader permission algebra, backend matrix, FFI type expansion or
omitted-definition-row inference is added. Remove this task and its owned plan
when the completed product checkpoint satisfies the artifact lifecycle.
