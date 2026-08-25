# Top-Level Interface Method Functions Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Make every admitted interface method a top-level function and reconcile the feature branch with current `main` without invalidating retained checkpoint identities.

**Architecture:** Static interface admission checks the outer `Type` constructor after parameter validation. Existing substitution, evidence selection, Core lowering, validation, and evaluation preserve the admitted function type. Current `main` is merged into the feature branch so historical product commits named by retained evidence remain reachable.

**Tech Stack:** Rust 1.97.1, Ash's parser/resolver/checker/Core pipeline, Cargo integration tests, Markdown specification and project artifacts.

---

## Task 1: Integrate current `main`

### Task 1 files

- Modify: `docs/design/README.md`
- Modify: `docs/trajectory.md`
- Modify: `docs/design/DN-0024-executable-learning-and-evidence-stream.md`

### Step 1: Merge without signing

Run: `git -c commit.gpgSign=false merge --no-ff main`

Expected: content conflicts only in `docs/design/README.md` and
`docs/trajectory.md`; no source, specification, or test conflict.

### Step 2: Resolve both conflicts

Keep the feature branch's completed Modular Ash status and evidence links. Add
DN-0024 after DN-0023 in the design index and after Mini-Ash in the trajectory
table.

### Step 3: Correct DN-0024

Replace the deleted CP-0005 references with DN-0022 and DN-0023. State that the
`mini-ash` tag is historical and the current specification defines Modular Ash
modules, `main`, interfaces, and implementations.

### Step 4: Verify the integration

Run: `git diff --check && markdownlint --disable MD013 -- README.md spec docs`

Expected: both commands exit 0 and all changed links resolve on manual review.

## Task 2: Specify negative and positive method shapes

### Task 2 files

- Modify: `tests/interfaces.rs:134`
- Modify: `tests/implementations.rs`

### Step 1: Write the failing negative test

Replace the nested-arrow acceptance with:

```rust
#[test]
fn rejects_interface_method_with_only_nested_function_arrow() {
    let error =
        check_error("interface Callable<A> {\ncallable : (A, Int -> Int)\n}\n");

    assert_eq!(reason(&error), "interface.method-not-function");
}
```

Add a declaration-plus-implementation case with the same method type and assert
that `interface.method-not-function` precedes `equation.arity`. Add a
`(B, Int -> Int)` case and assert `interface.method-parameter` precedence.

### Step 2: Verify RED

Run: `cargo test --test interfaces rejects_interface_method_with_only_nested_function_arrow -- --exact`

Expected: FAIL because the checker currently accepts the declaration.

### Step 3: Add positive guards

Retain `(A, Int -> Int) -> Int` and `A -> Int -> Int` as valid interface method
types. Add an end-to-end `Transform<Int>` program whose tuple domain contains an
`Int -> Int` value and whose observation is `42 : Int`.

### Step 4: Run the focused tests

Run: `cargo test --test interfaces --test implementations`

Expected before the checker change: only the new negative shape cases fail.

## Task 3: Enforce the admitted shape

### Task 3 files

- Modify: `src/elaborate.rs:5794`
- Modify: `src/interface.rs:817`

### Step 1: Implement the minimal checker change

After parameter validation, replace recursive arrow search with:

```rust
if !matches!(&method.annotation.ty, Type::Function(_, _)) {
    // Preserve InterfaceReason::MethodNotFunction and existing source spans.
}
```

Use the existing per-method constraint charge for this constant-time match.
Delete `type_contains_function` and update the diagnostic to say that the method
type must have a top-level function arrow. Update the public reason
documentation without changing its stable reason code.

### Step 2: Verify GREEN

Run: `cargo test --test interfaces --test implementations`

Expected: all focused interface and implementation tests pass.

## Task 4: Rebaseline resource evidence

### Task 4 files

- Modify: `src/elaborate.rs:8909`
- Modify if required after measurement: `tests/interface_resources.rs`

### Step 1: Replace obsolete traversal evidence

Remove `nested_method_arrow_traversal_has_an_exact_constraint_boundary`. Add a
small-stack checker test with a deeply nested function inside a tuple method
type and assert `interface.method-not-function` at the exact boundary and
constraint exhaustion one unit earlier.

### Step 2: Verify the old exact limits fail

Run: `cargo test --lib one_constraint_budget_spans_all_checked_modules impl_method_substitution_uses_the_exact_constraint_budget`

Expected: FAIL at the obsolete exact limits because removing recursive search
saves two constraint units per method.

### Step 3: Remeasure and update exact limits

Set the one-interface boundary from 39 to 37 and the implementation-method
boundary from 79 to 77, then confirm one unit less fails and the exact limit
passes. Re-run `tests/interface_resources.rs`; adjust its width only if the
expected failing stage changes.

### Step 4: Verify resource tests

Run: `cargo test --lib constraint_budget && cargo test --test interface_resources`

Expected: all focused resource and small-stack tests pass.

## Task 5: Update normative and retained documentation

### Task 5 files

- Modify: `spec/README.md`
- Modify: `spec/static-semantics.md:478`
- Modify: `spec/elaboration.md:128`
- Modify: `docs/design/DN-0023-interfaces-and-implementations.md:192`
- Modify: `docs/design/modular-ash/interfaces-evidence.md`

### Step 1: Update normative truth

Replace `function_arrow_count(method_type) >= 1` with:

```sequent
method_type = domain -> codomain
```

Define the diagnostic by the outer constructor, preserve parameter-check
precedence, and state that substitution preserves the outer function used by
implementation equations and evidence slots.

### Step 2: Update informative evidence

Replace nested-arrow acceptance and recursive traversal claims with the new
negative, positive, end-to-end, exact-budget, and stack-safety witnesses. Record
the corrective product checkpoint after implementation review without erasing
historical provenance.

### Step 3: Verify documentation

Run: `markdownlint --disable MD013 -- README.md spec docs && cargo test --test spec_examples`

Expected: lint and executable specification examples pass.

## Task 6: Review, verify, and close temporary artifacts

### Task 6 files

- Remove after the verified product checkpoint: `docs/proposals/CP-0007-top-level-interface-method-functions.md`
- Remove after the verified product checkpoint: `docs/tasks/TASK-0013-require-top-level-interface-method-functions.md`
- Remove after the verified product checkpoint: `docs/plans/2026-08-25-top-level-interface-method-functions.md`
- Modify: `docs/proposals/README.md`
- Modify: `docs/tasks/README.md`

### Step 1: Run independent spec and code-quality review

Review the complete current-main-to-HEAD diff. Fix and re-review every actionable
finding.

### Step 2: Run the root verification boundary

Run: `cargo xtask verify`

Expected: exit 0 with formatting, build, lint, all tests, and rustdoc checks
passing.

Also run:

```text
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Expected: both exit 0; manual relative-link and authority review is clear.

### Step 3: Close temporary artifacts

After one commit retains the implementation, tests, specification, review, and
verification, remove CP-0007, TASK-0013, this plan, and their index entries.
Commit the retained evidence report separately so it can name the product
checkpoint without moving that boundary.
