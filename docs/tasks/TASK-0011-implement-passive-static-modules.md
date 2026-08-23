# TASK-0011: Implement Passive Static Modules

- ID: `TASK-0011`
- Status: active
- Related: [CP-0005: Passive Static Modules](../proposals/CP-0005-passive-static-modules.md), [DN-0022: Passive Static Modules](../design/DN-0022-passive-static-modules.md), [DN-0020: Ash Dialect Milestones](../design/DN-0020-ash-dialect-milestones.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), and the [execution plan](../plans/2026-08-23-implement-passive-static-modules.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0005 is accepted transition authority. Current `spec/` remains normative
  until implementation, tests, and specification changes merge together.
- Work runs on `feature/modular-ash` in `.worktrees/modular-ash`.
- The `mini-ash` tag retains the historical compiler and corpus. Current source
  receives no Mini-Ash dialect selector or compatibility grammar.
- Behavioral changes use witnessed red-green-refactor cycles. Production Rust
  follows the project lint configuration and the Rust ownership, error, API,
  type-safety, testing, and documentation guidance selected for this task.
- Intermediate commits may contain a deliberately incomplete transition but
  must state their bounded checkpoint and keep their focused tests green.

## Work

Execute the linked plan to:

- replace the file-result root with declarations-only module syntax;
- add qualified and targeted imports, named roots, canonical loading, graph
  identity, deterministic cycles, and graph-wide resource accounting;
- add private, public opaque, and public transparent declarations;
- resolve each module from immutable dependency export summaries;
- preserve hidden nominal identity across public schemes without exporting its
  source name or constructors;
- link dependency-ordered module groups and generated `main ()` into one pure
  Core program without a module Core node;
- update the CLI, diagnostics, corpus, normative specification, tool docs, and
  retained evidence; and
- compare representative unchanged behavior against a separately built
  `mini-ash` tag.

## Progress

- The user accepted CP-0005 and its required evidence.
- The isolated worktree starts from `main` at `f1cf6a1`.
- `cargo build --locked` and `cargo test --locked --all-targets` pass before
  implementation. The baseline contains 565 passing tests and no failure.
- The implementation plan records the intended red-green checkpoints.
- Declarations-only module syntax and import spellings are implemented and
  committed with focused syntax evidence.
- Canonical graph loading is implemented and committed with focused loader
  evidence.

## Verification

Focused commands are recorded in the execution plan. Completion requires:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo xtask verify
```

Manual review covers CP-0005 required evidence, Markdown, relative links,
artifact authority, formal notation, reason codes, all changed Core consumers,
module-summary isolation, graph and type resource accounting, multi-source
provenance, historical-tag comparison, and the absence of interfaces, module
signatures, parent traversal, runtime modules, or a current-tree Mini-Ash
compatibility path.

## Discoveries

- One canonical source may be reached through several configured roots. It has
  one compilation-local module identity, retains every owning root, and checks
  relative descendants against every owner. This removes discovery-order
  dependence without creating route-specific module identities.
- Linking registries also requires module-qualified resolved type variables and
  a separate namespace for generated term and type binders. Qualifying only
  source term binders and nominal declarations would leave cross-module or
  generated-identity collisions.

## Deviations

- Task 4's identity migration crosses Core construction, transformation,
  validation, evaluation, and their tests in addition to the files named by the
  initial plan. Those consumers must change together to preserve exact
  identities. This expands the implementation boundary without changing
  CP-0005 semantics.
