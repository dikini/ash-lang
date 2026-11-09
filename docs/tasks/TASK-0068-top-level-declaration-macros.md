# TASK-0068: Top-Level Declaration and Derive Macros

- ID: `TASK-0068`
- Status: active; partial delivery retained; refreshed plan awaiting re-review
- Related: [GitHub parent issue #206](https://github.com/dikini/ash-lang/issues/206),
  [CP-0034](../proposals/CP-0034-top-level-declaration-macros.md),
  [DN-0062](../design/DN-0062-hygienic-surface-macros.md),
  [slice 2 delivery plan](../design/macros/slice2-delivery-plan.md),
  [reviewed work structure](../design/macros/slice2-work-structure.md),
  [integration corpus](../design/macros/fixtures/README.md).

> This task tracks delivery of the accepted transition. CP-0034 is partially
> implemented on the retaining branch; this task does not define current Ash
> semantics or extend the authorized scope.

## Dependencies

The retained [expression-syntax specification](../../spec/syntax-expansion.md)
is the slice 1 baseline. CP-0034 is accepted, and the C1–C4 contract and corpus
checks are recorded in the delivery plan. On 2026-11-09, local and live remote
`codex/task-0068-integration` identify
`476b5ca9e4b4c7fdfacf7baa27e43094d8551d9b`, tree
`7087eb1cbdd4e8a9ffd331011b3560c136cd9395`. Recheck refs and worker ownership
before dispatch. The plan records the 13 retained squash commits, their partial
criteria and the remaining producer/consumer interfaces.

The reviewed work structure is filed under [issue #206](https://github.com/dikini/ash-lang/issues/206)
as seven workstreams and 45 child issues. All 112 native blocking links still
match the reviewed graph. D1 #214 and S1 #215 are closed; 43 child issues remain
open, and no repository PR was open at inspection. The user has authorized
delivery and squash merges into the retaining branch; Main remains separate.

The active `/root` orchestrator inherits its launching model/effort and owns
integration. Planning uses GPT 6.1 Sol Max; development uses GPT 6.1 Terra Max;
independent QA uses Terra 6.1 Medium; independent review and acceptance checking
use Sol 6.1 Max, including replacements. Sol independently checks the developer's
acceptance record; the developer applies the checked record and performs
readback; the orchestrator confirms. Keep these roles independent,
assign shared-file ownership before parallel edits, and use one assigned
heavy-build operator with one Cargo job and the compatible cache.

## Work

Deliver imported top-level declaration macros and type/newtype derives,
including declarative templates, checked procedural transformers, quotation,
executable escapes, repetitions and state-threaded generators. Preserve syntax
contexts, protected fragments and source origins through the existing parser,
host and downstream compiler. Establish the early connected declaration path
at D8, the early quote/escape path at E4, and the complete public-driver path
at V3. The linked work structure records each unit's deliverables, acceptance
cases, prerequisites and hard boundaries.

### Do not do

- Do not add or change downstream type checking, inference, semantic checking,
  name resolution, elaboration, publication rules or Core validation. Ordinary
  compiler stages check generated code and report its errors. Preserve spans,
  contexts and origins; if a downstream consumer is deficient, record its
  concrete gap separately and stop the affected path.
- Do not add a macro-specific semantic checker, second resolver, per-reference
  grants, automatic conflict repair, new host or new error protocol. Do not
  change slice 1 behavior except for CP-0034's accepted `syntax` reservation
  and syntax-service sum extensions.
- Do not implement local declaration macros, generated imports or generated
  syntax definitions, typed reflection, a generic conversion interface,
  implicit primitive conversion, an ambient compiler input for generator
  helpers, effects redesign, Wasm support or unrelated refactoring.
- Do not cross an individual work item's explicit prohibition because it
  appears convenient. Record the reason, return a contract change to its owner,
  and continue independent work within scope.

## Progress

The reviewed original 45-unit delivery prediction is **142 points**. C1–C4's
recorded planning scope is **8 predicted points**, giving **150 points** for
the full scope. Preserve these fixed predictions and all original DAG edges.
D1/S1 account for seven fully closed predicted points; the 43 open units total
135 original points and include retained partial work. These figures do not
measure remaining effort or grant partial acceptance credit.

**Delivered:** Thirteen reviewed squash deliveries are retained at the base
above. They establish D1/S1, partial declaration selection/matching/admission,
type/pattern capture producers and identifier-only declaration collection and
H2/H3 tests. Every retained squash tree matches its reviewed candidate. The
[plan's retention inventory](../design/macros/slice2-delivery-plan.md#retained-deliveries)
links each PR and exact retained commit; issue records retain focused receipts.

**Remaining:** Complete protected-fragment accounting/consumption, declaration
captures, repetition, host transfer and procedural declarations, quotes/escapes,
derives, generators, publication handoffs, full corpus/diagnostics,
specification/tool documentation and integrated acceptance. D3's full I19
criterion awaits D5/G1; D6's procedural-output import refusal awaits S3/S4.
Prior partial H1/H2/H3 tests do not close their original criteria. No TASK-0068
fresh full-workspace receipt or completed D8/E4/V3/final gate is established.

**Awaiting:** Independent re-review of the refreshed full chain and interfaces
before substantial implementation, followed by each delivery's independent QA,
Sol PR review, retained-result verification and acceptance readback. Keep every
incomplete original criterion unchecked with Delivered/Remaining/Awaiting/Owner
and its PR, commit and evidence. The next fresh full checkpoint is D8, after the
first declaration path, integrated H2/H3 and protected-copy/composed-depth gates
are ready; E4 is the second checkpoint, V3 joins the complete public path and
V7 supplies the final fresh full gate before V8 retaining acceptance.

**Owner:** The orchestrator assigns the next eligible delivery and integration;
the developer owns product changes, builds, repairs and acceptance updates;
independent QA and Sol own their respective checks. The orchestrator tracks
these separate downstream issues:
[#263](https://github.com/dikini/ash-lang/issues/263),
[#265](https://github.com/dikini/ash-lang/issues/265),
[#272](https://github.com/dikini/ash-lang/issues/272) and
[#274](https://github.com/dikini/ash-lang/issues/274). All were open and unassigned
at inspection; active repair owners and timing are unverified. Verify live
owner/status before reporting further progress. Dependent criteria remain
blocked, and repairs stay outside this task; continue independent authorized
work without patching those consumers.

The plan preserves the fixed inputs, supplemental early cases and original full
graphs. Component or handwritten-control results do not replace their connected
assertions. Its forecast includes the full remaining chain and separately names
the unresolved downstream wait; a bounded completion ETA is not established.

## Verification

- [ ] Exercise I01–I22, including their fixed positive, negative, mutation,
      hygiene, origin and diagnostic cases, through the specified component
      and connected paths. Preserve the supplemental early cases and the full
      original integration graphs.
- [ ] Run the retained slice 1 regression cases; exercise the real macro
      library, caller and importer through the public driver, interpreter and
      supported build/image path. Verify existing host bounds, transfer and
      teardown, and I16's specified independent validator and handle controls.
- [ ] Update implementation, tests, specification and tool documentation
      together. Check that accepted but unimplemented behavior is not reported
      as current Ash before it is retained.
- [ ] Obtain independent QA and review on the pinned integrated candidate;
      repair and re-review findings. Run the agreed fresh full gate and retain
      its receipts for the exact inputs.
- [ ] Integrate to the authorized retaining branch, verify retained evidence
      and complete independent acceptance readback. Main integration remains a
      separate gate under the project workflow.

## Discoveries

The reviewed draft includes isolated early host, quotation and hygiene cases so
those focused checks do not depend on unrelated definitions in the full corpus.
The original full-module graphs remain required integration evidence.

The preserved `/home/dikini/Projects/ash-lang-task-0068` worktree remains at the
verified base on `codex/task-0068-protected`, with the inspected untracked
`tests/declaration_type_capture.rs` preserved. Its hash and existing type-first
working evidence are recorded in the plan. Resume using the existing syntax
budget/shared accounting; keep expression/pattern/procedural activation guarded
until their required accounting and consumers are independently verified.

The plan names the
[protected type-to-expression accounting and release gate](../design/macros/slice2-delivery-plan.md#protected-type-to-expression-accounting-and-release-gate).
It requires separate independent review. The retained base has broader
protected-capture guards; v3's narrower refusal is proposed, not implemented.
The type-only delivery must first establish and verify that narrow refusal on
protected types in generated expression-macro invocation arguments while
retaining the broader guards, then relax the broader type guard only after its
accounting evidence passes. Keep the narrow refusal until all subsequent
copying, traversal and composed depth are charged by the same existing
`SyntaxBudget` and shared accounting. Required real imported
consumer, repeated-copy, exact/short allowance, depth, late-failure,
small-stack/drop/cleanup and slice 1 regression evidence cannot be replaced by
an isolated projector check. If that connection cannot preserve language and
slice 1 behavior, stop it and return the concrete finding for a decision.

## Deviations

No semantic or scope change is authorized by this refresh. The resource and
diagnostic findings above preserve the reviewed boundaries and original
criteria. Return semantic gaps to CP-0034 or design work; retain separately
owned downstream repairs outside macro machinery. Preserve main's unrelated
effects work. Main integration remains outside this task's current permission.
