# TASK-0068: Top-Level Declaration and Derive Macros

- ID: `TASK-0068`
- Status: planned; delivery base and role assignments pending
- Related: [CP-0034](../proposals/CP-0034-top-level-declaration-macros.md),
  [DN-0062](../design/DN-0062-hygienic-surface-macros.md),
  [slice 2 delivery plan](../design/macros/slice2-delivery-plan.md),
  [local work structure](../design/macros/slice2-work-structure.md),
  [integration corpus](../design/macros/fixtures/README.md).

> This task organizes the accepted transition. It does not define current Ash
> semantics or start implementation. CP-0034 is accepted but unimplemented.

## Dependencies

The retained [expression-syntax specification](../../spec/syntax-expansion.md)
is the slice 1 baseline. CP-0034 is accepted, and the C1–C4 contract and
corpus checks are recorded in the delivery plan. Before dispatch, verify the
actual implementation base, agree the retaining branch and delivery
permissions, and assign the developer, independent QA and reviewer, integration
owner and acceptance owner. Agree the producer/consumer boundaries in the plan
before parallel work touches shared representations or files.

The local work structure contains candidate work items, not GitHub issues.
Create GitHub issues and sub-issues only when explicitly requested. Do not
start product work as a side effect of creating this task.

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

CP-0034 is accepted. The 45 remaining work units have been independently
reviewed and have a **142-point** difficulty prediction. C1–C4's recorded
planning scope is **8 predicted points**, giving **150 points** for the full
scope. These are fixed predictions, not measured effort. No slice 2 product
implementation or connected acceptance gate has been completed.

The delivery plan retains the dependency graph and earlier predictions. The
work structure records the first connected paths, separate QA/review gates,
parallel-work conditions and per-unit prohibitions. The initial fixtures are
acceptance inputs; handwritten controls and isolated checks do not establish
that the proposed macro paths run.

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

## Deviations

None recorded. Return semantic gaps to CP-0034 or design work; record any
separately owned downstream repair rather than adding it to macro machinery.
