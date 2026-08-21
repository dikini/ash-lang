# TASK-0008: Implement Recursive Function Definitions

- ID: `TASK-0008`
- Status: active
- Related: [CP-0002: Recursive Function Definitions](../proposals/CP-0002-recursive-function-definitions.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0019: Primitive Feature Composition](../design/DN-0019-primitive-feature-composition.md), [execution plan](../plans/2026-08-22-recursive-function-definitions.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0002 is the accepted semantic authority for this change until the
  implementation and specification merge together.
- AD-0005 through AD-0008 govern parser recovery, resolved identities and
  elaboration, typed Core validation, and the explicit evaluator machine.
- Current `spec/` remains normative until this task lands implementation,
  tests, and specification changes together.
- The work runs on branch `feature/recursive-definitions` in the isolated
  `.worktrees/recursive-definitions` worktree. Intermediate commits are
  unsigned.
- No merge is authorized before review and explicit user confirmation. The
  eventual merge commit must be GPG-signed.
- Each behavior slice follows a witnessed red–green–refactor cycle. Mechanical
  representation migrations use the existing suite as characterization
  evidence and remain behavior-preserving.

## Work

Execute the linked plan to:

1. represent ordered local declarations without treating every declaration as
   a sequential binding;
2. add recursive binding groups to the closed typed Core dialect, validator,
   transforms, and explicit evaluator;
3. add `rec` and `and` tokens, grammar, recovery, concrete-tree validation, and
   surface projection;
4. resolve globals and explicit local groups with simultaneous scope;
5. check recursive members against required declared monotypes and reject
   unsafe non-function initialization;
6. lower globals and local groups through one recursive Core form with causal
   provenance;
7. cover self recursion, mutual recursion, forward references, lexical scope,
   rejection paths, malformed Core, transforms, deep execution, and exact CLI
   observations;
8. update the normative specification and executable language and tool
   documentation;
9. measure changed sites and maintenance discovery against the transferable
   DN-0019 findings;
10. complete requirement-by-requirement verification and prepare the branch for
    review without merging it.

## Progress

- The user accepted file-wide global scope, explicit local
  `let rec ... and ...` groups, required member annotations, direct-function
  initialization, one recursive Core group, and template-based recursive
  environment frames.
- CP-0002 records the accepted semantic transition and required evidence.
- The isolated worktree starts from signed merge `079b8eb`. Fresh `cargo build`
  and `cargo test` passed before implementation; the test command ran 272
  tests.
- Product implementation has not started.

## Verification

Focused red–green commands are listed in the execution plan. The completed
branch must pass:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo xtask verify
```

Evidence must cover every item in CP-0002's required-evidence section,
including exact structured diagnostics, independent Core rejection, transform
preservation, deep execution on a small Rust stack, executable specification
examples, and exact CLI output. Documentation review must check authority,
links, formal-notation syntax, and the prose explanation accompanying every
`ebnf` and `sequent` fence.

The final review must also inspect the diff against `main`, confirm that
ordinary `let` remains nonrecursive, confirm that recursive environment frames
cannot own closures back to themselves, and audit all closed Core consumers.

## Discoveries

None yet. Record implementation evidence here while the task is active and
distill transferable findings into DN-0019 before removing this task at
completion.

## Deviations

None.
