# TASK-0016: Implement Explicit Kinds and Higher-Kinded Parameters

- ID: `TASK-0016`
- Status: active
- Related: [CP-0009: Explicit Kinds and Higher-Kinded Parameters](../proposals/CP-0009-explicit-kinds-and-higher-kinded-parameters.md), [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), the [approved design record](../plans/2026-08-26-explicit-kinds-design.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), and the [execution plan](../plans/2026-08-26-explicit-kinds-and-higher-kinded-parameters.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0009 is the accepted transition authority. The current specification owns
  implemented Ash until this product branch lands implementation, tests, and
  normative updates together.
- This branch is stacked on explicit-import checkpoint `a1647ff`, which is not
  integrated into `main@4f0541d`. It cannot integrate independently; the
  predecessor must integrate first, or the stacked product branches must
  integrate in predecessor order.
- The predecessor supplies explicit implementation selection and re-export,
  stable declaration and evidence identities, body-free summaries, linked
  authentication, independent Core validation, graph-wide resource budgets,
  and the retained [explicit-import evidence](../design/lib-ash/imports-evidence.md).
- A fresh `cargo xtask verify` passes in the dedicated `lib-ash-kinds` worktree
  before production changes. The branch remains separate and unmerged.
- Every behavior change uses a witnessed red-green-refactor cycle. Production
  Rust follows `rust-skills`; unexpected failures use
  `superpowers:systematic-debugging`. Intermediate commits are unsigned.

## Work

Execute the linked plan to:

- retain kind and explicit type-binder syntax with contextual `Type`, exact
  interface arity, recovery, spans, and legacy headers;
- replace saturated nominal applications with one canonical unary semantic
  application while preserving n-ary source syntax and simultaneous n-ary
  Core scheme instantiation;
- make kind operations, application operations, and their disposal stack-safe
  and exactly charged;
- assign canonical fixed kinds to declaration and inference binders and derive
  local nominal kinds before checking any type-bearing declaration fact;
- kind-check every monotype and interface argument, preserve exact explicit and
  implicit binder policies, and retain deterministic structured failures;
- extend first-order inference, eligible local generalization, interface and
  implementation matching, termination, overlap, orphan ownership, and
  inference-free evidence selection to fixed higher kinds;
- retain and authenticate kinded body-free summaries, hidden closure, imported
  facts, linked evidence, Core binders, transformations, and independent Core
  validation before evaluation;
- preserve erasure and evaluator state-machine behavior while mechanically
  migrating nominal-shape inspection;
- establish a closed type-bearing site inventory, exact resource formulas,
  one-short and atomic failure witnesses, 256 KiB-stack deep and wide coverage,
  complete summary, linked, and Core tampering, and library and CLI diagnostics;
- migrate every predecessor-valid omitted annotation and implicit global or
  implementation binder without edits while recording deliberate stage and
  reason changes; and
- reconcile the specification and explanatory documentation from implemented
  behavior, retain `docs/design/lib-ash/kinds-evidence.md`, complete independent
  reviews and the full gate, then remove transition artifacts without creating
  a `lib-ash` tag.

This task excludes method-local type parameters, multi-parameter interfaces,
associated outputs, functional dependencies, defaults, packages, kind
inference, kind polymorphism, type lambdas, higher-order unification, source
`forall`, explicit term type application, higher-rank source values, runtime
kind values, a compatibility grammar, a second semantic type representation,
and evaluator semantic or state-machine changes. The absence of kind inference
is the accepted phase-dependent semantic boundary of this increment, not a
permanent language principle.

## Progress

- The approved design record narrows the second prepared `lib-ash` increment.
- Three independent proposal reviews covered semantics, representation and
  pipeline ownership, evidence, resources, migration, and lifecycle. Review
  corrected exact binder policies, interface-argument kind checking, transient
  inference-kind ownership, Core-instantiation distinctions, and the complete
  evidence gate before CP-0009 was accepted.
- The dedicated worktree starts from `a1647ff`; baseline build and full
  repository verification pass. CP-0009 is accepted, the task and execution
  plan are authorized, and the branch remains stacked and unmerged.
- The execution plan orders the closed type-site inventory and resource
  formulas early so omissions fail during implementation rather than closure.
- Task 2 retains contextual kind syntax and exact explicit binder lists across
  nominal, interface, equational, operational, and implementation headers.
  Parser evidence covers right-associated kinds, exact spans, omission versus
  explicit `Type`, token-complete recovery, every header-owner boundary,
  line-end and end-of-file termination, and contextual `Type` as either a kind
  atom or an ordinary implementation-head name. Mechanical resolver changes
  preserve predecessor semantics until kind resolution begins in Task 4.
- Task 2 passed independent semantic and parser-quality review after recovery
  ownership, synchronization context, exact `>` diagnostics, owner-token
  preservation, and contextual-name ambiguity were corrected. Focused tests,
  the full all-feature workspace suite, Clippy with warnings denied,
  formatting, all-target checking, and diff hygiene pass on the final change.

## Verification

Each plan checkpoint records focused RED and GREEN commands. Completion
requires reading the complete output of:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --workspace --all-targets --all-features
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
cargo test --locked --workspace --all-targets --all-features -- --list
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Manual and independent review covers every CP-0009 evidence requirement,
including authority labels and links, contextual syntax, exact binder sets and
order, total `DELTA`/`OMEGA`/`XI`/`IOTA` kinding, canonical application,
scheme-versus-monotype separation, summary and Core authentication, failure
ownership, resource formulas and teardown, migration, exclusions, and the
unchanged evaluator state machine.

## Discoveries

Proposal review established that interface applications cannot use the
ordinary kind-`Type` value rule: their arguments must synthesize the selected
interface parameter's declared kind. It also established that total kind
synthesis needs a transient fixed `OMEGA` entry for every inference variable,
even though zonking removes those variables before summaries and Core.

The canonical unary semantic application and the existing n-ary Core
`TypeApplicationNode` are different operations. The former is structural type
syntax; the latter simultaneously instantiates one complete outer rank-1
scheme. Tests and validation must keep that distinction explicit.

The type-bearing site map and additive resource formulas are implementation
inputs, not retrospective documentation. The architecture guard and exact
budget probes therefore precede summary and Core expansion.

## Deviations

No deviation from CP-0009 is currently known. Any product evidence that exposes
missing or incorrect semantics returns to proposal or design work instead of
being decided in this task.
