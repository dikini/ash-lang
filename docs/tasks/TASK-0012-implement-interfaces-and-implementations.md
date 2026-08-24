# TASK-0012: Implement Interfaces and Implementations

- ID: `TASK-0012`
- Status: active
- Related: [CP-0006: Interfaces and Implementations](../proposals/CP-0006-interfaces-and-implementations.md), [DN-0023: Interfaces and Implementations](../design/DN-0023-interfaces-and-implementations.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), and the [execution plan](../plans/2026-08-24-implement-interfaces-and-implementations.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0006 is accepted transition authority. Current `spec/` remains normative
  until implementation, tests, and specification changes are committed together
  on this feature branch.
- Work runs on `feature/modular-ash` in `.worktrees/modular-ash` and remains
  unmerged unless the user later requests integration.
- The implemented passive-module boundary remains intact: canonical module
  identity, direct imports, body-free checked summaries, opacity, hidden
  nominal identity, dependency-ordered Core groups, and entry `main` are inputs
  to this work rather than interface semantics to redesign locally.
- Behavioral changes use witnessed red-green-refactor cycles. Production Rust
  follows the project lint configuration and the selected Rust ownership,
  error, API, type-safety, testing, and documentation guidance.
- Interface selection must remain structurally attached through checking and
  linking. A span-keyed side table or repeated selection during final lowering
  does not satisfy CP-0006.
- Intermediate commits may contain a deliberately incomplete transition but
  must state their bounded checkpoint and keep their focused tests green.

## Work

Execute the linked plan to:

- parse and project method-only interfaces, trailing `where` requirements, and
  implementation declarations;
- allocate stable qualified interface, method, impl, impl-method, requirement,
  and hidden binder identities;
- extend checked schemes and body-free summaries without changing ordinary
  type equality or turning summaries into source module signatures;
- check interface and impl headers, visibility, orphan ownership, structural
  termination, exact method membership, and implementation overlap;
- select abstract, exact-rigid self, concrete, and generic prerequisite evidence
  once and retain it on the checked occurrence;
- validate linked evidence identities, availability, substitutions, method
  order, scope, type, and provenance before Core synthesis;
- lower evidence to existing type abstractions, ordinary function binders,
  applications, and module recursive groups without a new Core or evaluator
  feature;
- close diagnostics, graph-wide interface-and-constraint accounting,
  deterministic failures, deep worklists, and small-stack destruction;
- update the corpus, normative specification, tool docs, retained evidence,
  proposal/task indexes, and trajectory; and
- leave associated types, specialization, first-class dictionaries, runtime
  lookup, module signatures, effects, and the later core-versus-library audit
  outside this implementation task.

## Progress

- CP-0006 converged through independent syntax, semantics, and implementation-
  boundary reviews and is accepted.
- Unsigned checkpoints through `f4d89e6` implement parsing, stable identity and
  constraint resolution, interface checking, implementation-header admission,
  and checked-summary publication on `feature/modular-ash`.
- Task 4 now retains checked interface and implementation facts, publishes
  direct-only summaries, preserves import-route provenance, deduplicates stable
  identities, and rejects overlapping admitted heads after pair-freshening.
- Focused tests cover exact resource limits, deep payloads on a 64-KiB stack,
  public and private module boundaries, targeted imports, direct-only
  availability, and alternate-route deduplication.
- Task 4's implementation and evidence passed independent high-reasoning
  reviews of ownership, budgets, stable-identity deduplication, overlap,
  summary transport, orphan precedence, opacity, and dependency diamonds.
- `cargo xtask verify` passes after the completed Task 4 test matrix, including
  format, build, Clippy, all test targets, and documentation.
- Task 5 selects abstract, exact-current-impl, and concrete evidence during
  checking and retains each result on its owning occurrence. Checked definitions
  carry the bodies and selections through `CheckedModule::into_group`; the
  checked-body structural-completeness audit rejects missing or extra slots
  before that transition. This audit is not Task 6's linked evidence-validation
  judgment.
- Task 5's 11 focused integration tests and 252 library tests pass. Independent
  high-reasoning reviews found no remaining logic, authority-boundary, or
  resource-accounting defects after the review fixes. The implementation plan
  records the commands and the remaining validation, lowering, resource,
  documentation, and corpus checkpoints.
- Task 6's first bounded checkpoint retains the checker-certified interface and
  zonked argument with each immutable evidence plan. Direct implementation
  routes now retain both the authenticated dependency identity and the source
  import occurrence. These facts are the minimum input needed for independent
  linked validation; they do not yet admit final Core synthesis.
- The checkpoint's 12 focused integration tests and 252 library tests pass,
  together with format, all-target checking, and Clippy. An independent
  high-reasoning review found no remaining goal-retention, budget, iterative-
  destruction, error-precedence, or route-provenance defect.
- Task 6's second bounded checkpoint introduces a distinct pre-Core interface-
  evidence validation result. Location-only indexes authenticate stable
  interface, method, implementation, implementation-method, global, and hidden
  binder identities without cloning fact graphs. Resolver-authenticated direct
  dependency identity and import span survive into linked groups, so imported
  implementation availability is checked independently of its claimed route.
- One graph-wide constraint budget now continues through linking and evidence
  validation. All width-dependent registry, availability, direct-edge,
  declaration, expression, and evidence-plan visits charge before inspection;
  validation traverses declarations and children in retained source order.
  Fourteen focused validation unit tests, one public validation integration
  test, and the 12 selection integrations pass with format, all-target checking,
  and Clippy.
- Task 6 now authenticates complete linked schemes, provenance, availability,
  substitutions, prerequisite structure, termination, scope, types, and method
  order before Core synthesis. Final synthesis accepts only that validated
  capability and lowers abstract and concrete evidence through ordinary type
  abstraction, functions, applications, and defining-module recursive groups.
- The seven planned end-to-end observations and an additional same-typed
  multi-method regression are GREEN. The 84-test focused Task 6 matrix, 282
  library tests, the complete test suite, format, all-target checking, strict
  Clippy, and diff hygiene pass. The closed Core and evaluator inventories
  contain no interface or evidence runtime mechanism.
- Two independent review cycles covered validation, lowering, the driver
  barrier, Core consumers, budgets, and test strength. Fixes added public-import
  authentication, shared strict-subterm revalidation, exact block accounting,
  same-typed slot corruption coverage, and root-method filtering; the repeated
  reviews found no remaining Task 6 defect.
- Task 7 retains generic prerequisite construction, exact rigid self evidence,
  abstract prerequisite use, ordered evidence flattening, cycle and termination
  failures, and direct, mutual, global-to-method, and method-to-global recursion.
  Hidden and opaque generic carriers complete through their defining modules.
- Generic implementation methods now keep source parameter identities for
  checked selection while receiving distinct Core quantifier identities. Each
  completed method zonks its emitted Core slice before bounded alpha-renaming,
  so solved inference cannot reintroduce an unbound source parameter. The Core
  and evaluator feature inventories remain unchanged.
- Task 7's 94-test focused matrix and complete all-target suite pass, together
  with format, all-target checking, strict Clippy, and diff hygiene. Repeated
  high-reasoning semantic and Core reviews plus an independent coverage review
  found no remaining Task 7 defect.

## Verification

Focused commands and witnessed RED/GREEN outcomes are recorded in the execution
plan. Completion requires:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo xtask verify
```

Manual review covers every CP-0006 evidence requirement, Markdown, relative
links, artifact authority, formal notation, reason codes, source occurrence
ownership, summary isolation, direct-only impl availability, graph-wide budget
lifetime, all changed Core consumers, and the absence of associated types,
runtime lookup, interface Core nodes, span-keyed selection, or a new evaluator
dispatch rule.

## Discoveries

- CP-0006's orphan rule and the existing acyclic module graph prevent distinct
  modules from publishing unifying implementation heads. The planned legal
  sibling and co-import conflict cases were therefore not source-expressible.
  CP-0006 and DN-0023 now state that consequence while retaining overlap checks
  over admitted effective-environment facts.
- Empty evidence-slot clones own independent one-shot cells, while clones of a
  filled slot share the same immutable flat evidence plan. This preserves
  occurrence-local selection before checking and stable checked evidence across
  the checked-module and linked-group ownership transitions.
- Resolution charges and reserves the exact requirement-count-by-occurrence
  evidence-slot product before constructing its heap-backed one-shot cells.

## Deviations

- Task 4 exercises cross-route effective-environment overlap with authenticated
  synthetic facts instead of orphan-invalid sibling source fixtures. Source
  tests retain local overlap, orphan precedence, direct fact availability,
  route deduplication, and no re-export.
- Task 5 uses `tests/interface_selection.rs` for checked-occurrence inspection
  rather than extending `tests/interfaces.rs` and `tests/polymorphism.rs`.
  It also adds `src/evidence.rs` and `src/evidence_audit.rs`; the latter audits
  checked-body structural completeness only. The changed implementation files
  are `src/interface.rs`, `src/resolved.rs`, `src/elaborate.rs`,
  `src/driver.rs`, `src/lib.rs`, `src/resolve.rs`, and `src/types.rs`, with
  compatibility regressions in `tests/bindings.rs`, `tests/data_and_adts.rs`,
  `tests/functions.rs`, `tests/module_elaboration.rs`,
  `tests/polymorphism.rs`, `tests/provenance.rs`, `tests/recursion.rs`,
  `tests/resolution.rs`, and `tests/semantics.rs`. `tests/interfaces.rs`
  remains an unchanged regression.
- Task 5 replaces the public arbitrary-result linker input with an authenticated
  entry `main ()` expression derived from the checked entry module. A separate
  resolved-expression constructor retains standalone elaboration probes without
  letting callers present an unchecked expression as a checked linked result.
- Task 6 begins with a bounded representation checkpoint because the pre-Core
  validator cannot authenticate a selection from its root node alone, and an
  import span cannot identify the dependency whose direct export admitted an
  implementation. Validation, evidence lowering, and the end-to-end corpus
  remain deliberately outside this checkpoint.
- Task 6 uses `src/evidence_validation.rs` for the independent pre-Core stage
  and `tests/interface_validation.rs` for its public capability witness. The
  end-to-end observations live in the dedicated `tests/interface_corpus.rs`
  target, while `tests/interfaces.rs` retains the exact resulting-Core shape
  witness. These targets separate validation corruption evidence from ordinary
  Core validation.
- Task 7's three planned end-to-end additions were already GREEN because Task 6
  had implemented iterative substitution, prerequisite application, and one
  recursive group per module. The Task 7 RED audit instead exposed generic
  multi-method Core quantifier reuse. Review additions then exposed inference
  zonking that could reintroduce a source parameter after alpha-renaming; both
  failures were fixed before the Task 7 checkpoint.
