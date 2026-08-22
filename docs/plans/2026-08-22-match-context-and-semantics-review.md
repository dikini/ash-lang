# Match Context and Semantics Review Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Correct contextual match checking and align the normative pattern and recursive-initialization rules with the retained implementation.

**Architecture:** Preserve match synthesis and add one expected-type path through the existing elaborator. Update the static and dynamic specification to state the already-authorized bidirectional pattern typing and explicit evaluator transitions without introducing new runtime behavior.

**Tech Stack:** Rust 2024, retained Ash compiler pipeline, CommonMark with `sequent` formal notation, Cargo verification.

---

## Task 1: Check function-valued match arms contextually

### Files

- Modify: `src/elaborate.rs`
- Test: `tests/data_and_adts.rs`

### Step 1: Write the failing test

Add `contextually_typed_matches_check_every_anonymous_function_arm`. Run the
program below through `run_source` and require value `42` with type `Int`:

```ash
fn choose(flag : Bool) -> Int -> Int {
    match flag {
        true => fn(value) { value + 1 }
        false => fn(value) { value * 2 }
    }
}

choose true 41
```

### Step 2: Verify the test fails for the reviewed reason

Run:

```text
cargo test --locked --test data_and_adts contextually_typed_matches_check_every_anonymous_function_arm
```

Expected: failure because the first arm reports
`type.function-needs-context`.

### Step 3: Implement the minimal elaborator correction

Make `ElaborationTask::Check` dispatch a resolved match to
`elaborate_match` with its expected `ProvenancedType`. Let synthesis pass no
expected type. Initialize the arm result constraint from the optional expected
type so every checked arm receives it; preserve the existing first-arm
synthesis behavior when no expected type exists. Retain the empty-arm rejection.

### Step 4: Verify focused behavior and regressions

Run:

```text
cargo test --locked --test data_and_adts contextually_typed_matches_check_every_anonymous_function_arm
cargo test --locked --test data_and_adts
cargo test --locked --test diagnostics
```

Expected: all pass.

### Step 5: Commit

Commit the Rust change and regression without GPG signing.

## Task 2: Correct normative static pattern rules

### Files

- Modify: `spec/static-semantics.md`
- Test: `tests/spec_examples.rs`

### Step 1: Split match synthesis and checking rules

State that synthesis obtains the result type from the first arm and checks the
remaining arms, while checking passes the expected type to every arm. Keep the
shared pattern, usefulness, and exhaustiveness premises in both rules.

### Step 2: Add pattern premises to function and block rules

Replace single-binder premises with `pattern ⇐ type => bindings`, singleton
exhaustiveness, and `GAMMA, bindings`. Use `pattern` in source conclusions for
anonymous functions and local bindings.

### Step 3: Verify executable examples

Run:

```text
cargo test --locked --test spec_examples
```

Expected: all examples pass.

## Task 3: Correct normative recursive and scalar transitions

### Files

- Modify: `spec/dynamic-semantics.md`
- Test: `tests/spec_examples.rs`

### Step 1: Replace the big-step initializer premise

Add one rule that enters the next initializer with an explicit continuation and
one rule that stores its returned location before resuming `initialize(rest,
...)`. Explain source order through the head/rest control state.

### Step 2: Correct representative derivations

Describe scalar binders and function binders as direct environment values.
Remove function-slot and template-storage claims from function-only recursive
groups. Update the rule-sequence table accordingly.

### Step 3: Review formal notation

Confirm every changed `sequent` fence has premises, one conclusion, and matching
prose. Confirm no big-step evaluation premise remains in the normative
recursive-binding family.

## Task 4: Retain evidence and verify

### Files

- Modify: `docs/design/mini-ash/data-and-patterns/evidence.md`
- Modify: `docs/tasks/TASK-0009-implement-monomorphic-data-and-patterns.md`

### Step 1: Record the correction

Map contextual match checking and the corrected formal accounts to their test
and specification owners. Keep proposal, task, and evidence authority labels.

### Step 2: Run complete verification

Run:

```text
cargo fmt --all --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo xtask verify
```

Expected: all commands exit successfully.

Run Markdown lint on changed Markdown and accept only the project's existing
line-length and repeated-heading exceptions. Check changed relative links,
formal notation, and authority boundaries manually.

### Step 3: Commit and request review

Commit documentation and evidence without GPG signing. Confirm a clean
worktree, request an independent review of the complete correction range, and
stop before integration.
