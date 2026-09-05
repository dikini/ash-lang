# Scoped Exact Evidence Implementation Plan

> Use subagent-driven development in this task, with one product writer and
> independent semantic and code-quality review of each coherent checkpoint.

**Goal:** Implement and locally integrate CP-0015, beginning with a pure
relation through the complete existing pipeline.

**Architecture:** Add one distinct canonical lexical evidence source, retain
occurrence scope through deferred inference, and reuse existing flat plans,
method checking, authentication, ordinary Core bindings, and erasure. Do not
introduce a second evidence solver, runtime registry, or generic scope system.

**Tech stack:** Rust, the existing Ash parser/checker/Core/evaluator, Cargo
tests, and executable Markdown specification examples.

The accepted [CP-0015](../proposals/CP-0015-scoped-exact-evidence.md) owns all
semantics; [TASK-0025](../tasks/TASK-0025-implement-scoped-exact-evidence.md)
owns execution. Start from `90f517d` plus the accepted proposal record.

## Task 1: First pure-relation pair

Primary files: `tests/scoped_evidence.rs`, `src/surface.rs`,
`src/parser/grammar.rs`, `src/parser/project.rs`, `src/resolve.rs`,
`src/resolved.rs`, `src/interface.rs`, `src/evidence.rs`,
`src/evidence_validation.rs`, `src/elaborate.rs`, and existing Core
method-authentication owners. Modify exhaustive traversal sites only where the
new source carrier actually reaches them.

1. Add `pure_lexical_method_executes` and
   `pure_lexical_method_forwards_through_a_constraint`, using CP-0015's exact
   complete example and direct-call variant. Reuse the established temporary
   module fixture pattern; do not add a generic test framework. Check the
   distinct retained lexical selection, validate linked evidence and Core,
   execute, and require integer `42`.
2. Run `cargo test --locked --test scoped_evidence pure_lexical_method` and
   retain the expected missing-syntax failure before any product edit.
3. Parse and project the sequential declaration using existing `with` and
   equation grammar. Resolve a stable source identity, complete application,
   contextual method parameters, and ordered method binders under preceding
   scope. Add exact syntax/admission tests before each new owner path.
4. Add a lexical source arm to existing evidence plans. Preserve one optional
   source head per pending occurrence and one parent link per source. Thread
   that head through improvement and recursive selection; do not alter closure
   timing. Admit sources only after all checked methods succeed.
5. Authenticate the source and selection independently from the ordered
   resolved tree. Lower supplied functions to ordinary local bindings and
   extend existing Core producer authentication. No new runtime node or frame.
6. Make both tests pass, run directly affected unit tests, `cargo fmt --check`,
   `cargo check --locked --all-targets`, and `git diff --check`. Obtain semantic
   compliance review followed by code/resource quality review, fix findings,
   and commit the coherent first vertical path unsigned.

This checkpoint is not completion of CP-0015. Keep every unimplemented
interaction visible in Task 2; do not narrow the accepted contract to the pair.

## Task 2: Expand the interaction matrix

Primary files: the first task's owners and `tests/scoped_evidence.rs`,
`tests/interface_selection.rs`, `tests/effect_diagnostics.rs`, and
`tests/local_newtypes.rs` where existing regression owners are preferable.

Write and observe a failing behavioral test before each missing behavior, then
make the smallest production correction. Cases may share fixtures, not
semantic shortcuts. Preserve the complete CP-0015 evidence matrix:

- admission and deterministic diagnostic precedence, all method membership and
  contextual type failures, higher kinds and polymorphic method schemes;
- direct/constrained calls, abstract and exact-current priority, lexical
  priority over concrete selection, distinct identities and disjoint scopes;
- active-key duplicate/conflict, dependent-only branding rejection, and no
  implicit self or sibling evidence;
- known-key improvement, mandatory conflict, unknown-key ambiguity, fixed
  snapshot ineligibility, delayed selection, recursive prerequisites, and the
  specified root/prerequisite asymmetry;
- selected function leaving an inner evidence block without exporting its
  evidence, identity-free closure after nominal-scope return, and no new
  nominal escape;
- effectful methods preserve declared rows and handlers; supplied method bodies
  enforce the existing resume barrier; ordinary recursive functions remain
  usable captures.

Run `cargo test --locked --test scoped_evidence --test interface_selection
--test local_newtypes --test effect_diagnostics --test kinds`, affected unit
tests, formatting, and diff checks. Review semantic compliance then code quality,
correct findings, and commit the complete interaction boundary unsigned.

## Task 3: Authenticate and bound the complete path

Use existing linked/Core unit-test owners for mutations; add only focused
resource tests to `tests/interface_resources.rs` or the owning module.

1. Write failing mutations for wrong source/goal/method/parameter/capture/scope
   and verify rejection at the independent linked or Core boundary. Cover
   unused sources and stale or forged parent links, not only executed calls.
2. Run both existing Core transforms on accepted programs, revalidate, and
   require preserved observations. Keep Pure and Effect Core inventories closed
   except the necessary static producer facts.
3. Measure and record actual additive work by owner. Test exact success,
   one-short atomic failure, retry, and deep iterative success/error disposal.
   Scope retention must be proportional to sources plus occurrences, not a
   copied source vector per occurrence. Keep all production limits unchanged.
4. Run the existing source, CLI, resource, and architecture predecessors and
   independently review the complete diff from `90f517d`. Correct all Critical
   and Important findings with their own failing regression witnesses.

Commit reviewed hardening unsigned. Do not add resource-lifetime or proof
machinery to satisfy hypothetical downstream tests.

## Task 4: Specify, close, and locally integrate

Update the CP-named specification sections and `tests/spec_examples.rs` with a
complete executable example, stable failure example, and normative rule
manifest. Retain a concise `docs/design/effect-ash/scoped-evidence-evidence.md`
report containing exact formulas, cases, reviews, hashes, and exclusions.
Update DN-0026/27/28, design index, and trajectory to record the actual boundary.

Run `CARGO_INCREMENTAL=0 cargo xtask verify`, Markdown lint, diff checks, and
the task's manual obligations. Record verified outcomes before deleting the
proposal, task, and this plan; update their indexes. Commit specification and
transition closure separately. Recreate the milestone integration checkout,
merge explicitly, verify the combined result, and reconcile its documentation.
Only remove the clean feature checkout/branch after proving its exact tip is
retained by integration. Preserve unrelated main changes and historical
worktrees. Do not merge into `main`, push, or tag.
