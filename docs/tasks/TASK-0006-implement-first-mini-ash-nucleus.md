# TASK-0006: Implement the First Mini-Ash Nucleus

- ID: `TASK-0006`
- Status: active
- Related: [CP-0001: First Mini-Ash Nucleus](../proposals/CP-0001-first-mini-ash-nucleus.md), [AD-0004: Small-Step Semantic Method](../decisions/AD-0004-small-step-semantic-method.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0016: First Mini-Ash Corpus Stratum](../design/DN-0016-first-mini-ash-corpus.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0001 is accepted and exclusively owns the language behavior implemented by
  this task.
- AD-0004 through AD-0008 govern the specification method, parser, front-end,
  Core, and evaluator boundaries.
- The [execution plan](../plans/2026-08-21-first-mini-ash-nucleus.md) sequences
  implementation and verification. It is temporary and leaves the tree when
  this task completes.
- The pinned stable Rust toolchain and
  [dependency policy](../project/dependencies.md) govern implementation.
- Implementation runs in an isolated worktree. Integration into `main`
  requires independent review, fresh verification, user confirmation, and the
  required signed merge.

The accepted arbitrary-precision `Int` requires a numeric representation.
Rust's standard library provides only fixed-width integer types. Implementing
and maintaining Ash-owned arbitrary-precision arithmetic would add substantial
correctness, performance, unsafe-code, and review cost without advancing the
language experiment, so a focused existing package is preferable.
The preliminary dependency choice is exactly `num-bigint` 0.5.1 with default
features disabled and only its `std` feature enabled:

- purpose: represent and calculate arbitrary-precision Ash integers;
- role: runtime dependency included in the distributed interpreter;
- source: [crates.io](https://crates.io/crates/num-bigint/0.5.1) and the
  [rust-num repository](https://github.com/rust-num/num-bigint);
- license expression: `MIT OR Apache-2.0`; this supplies clear license
  metadata but does not claim compatibility with Ash's still-unselected license;
- toolchain and targets: upstream declares Rust 1.60 and a pure-Rust
  implementation, below Ash's Rust 1.97.1 pin and without a native-library
  dependency;
- maintenance: version 0.5.1 was current during task planning, and the upstream
  repository showed recent 2026 activity;
- unsafe-code review: upstream uses contained unsafe operations for validated
  UTF-8 conversion, arithmetic CPU intrinsics, and division; optional random
  support also contains unsafe code but is not enabled.

The first implementation step must resolve the transitive graph, rerun advisory
and source checks, inspect every resolved package's machine-readable license
expression or license files, inspect enabled features and target support,
record the exact distributed dependency set, and stop if that evidence
contradicts this preflight. Because Ash has no selected license, this review
collects exact license evidence rather than inventing a `cargo-deny` allowlist.
It must also record `cargo audit`'s expected `RUSTSEC-2021-0090` name-collision
warning for this private workspace package named `ash`; the advisory concerns
an unrelated crates.io package and must not conceal any dependency advisory.

## Work

Implement CP-0001 as one retained Rust pipeline:

```text
UTF-8 source
  -> spanned tokens and logical line boundaries
  -> token-complete error-bearing concrete syntax
  -> recovery-free spanned surface syntax
  -> resolved binders
  -> bidirectional typed elaboration
  -> independently validated pure Core
  -> explicit first-order evaluator machine
  -> rendered value and type
```

The implementation includes:

- the `ash <source-file>` executable;
- the complete CP-0001 positive, negative, diagnostic, invariant, provenance,
  architectural-locality, and deep-machine evidence;
- separate normative specification documents for lexical structure, syntax,
  resolution, static semantics, elaboration, and dynamics;
- user-facing executable documentation;
- dependency evidence required by policy.

No implementation step may add behavior excluded by CP-0001. A semantic gap
returns to the proposal before work continues.

## Progress

- CP-0001 received explicit semantic acceptance.
- The task and execution plan are active.
- Dependency preflight selected `num-bigint` 0.5.1 subject to the
  required resolved-graph review.
- No product implementation or specification change has started.

## Verification

Completion requires every item in CP-0001's Required evidence section and the
execution plan's final evidence matrix. At minimum:

- `cargo xtask verify`;
- direct unit and integration tests for every accepted semantic stage;
- end-to-end corpus, diagnostic, CLI, large-integer, provenance, validator,
  transformation, locality, and deep-frame tests;
- independent review of implementation, tests, normative specification, tool
  documentation, dependency evidence, and authority boundaries;
- Markdown lint plus relative-link, anchor, formal-notation, and verbal-
  explanation review;
- a clean worktree and confirmation that no disposable probe or temporary
  execution plan remains in the completed merge.

## Discoveries

The accepted semantics require arbitrary precision. Current upstream metadata
supports using `num-bigint` 0.5.1 as the initial implementation candidate,
but the resolved dependency review remains part of implementation.

## Deviations

None.
