# TASK-0016: Implement Explicit Kinds and Higher-Kinded Parameters

- ID: `TASK-0016`
- Status: active
- Related: [CP-0009: Explicit Kinds and Higher-Kinded Parameters](../proposals/CP-0009-explicit-kinds-and-higher-kinded-parameters.md), [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), the [approved design record](../plans/2026-08-26-explicit-kinds-design.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), and the [execution plan](../plans/2026-08-26-explicit-kinds-and-higher-kinded-parameters.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0009 is the accepted transition authority. The current specification owns
  implemented Ash until this product branch lands implementation, tests, and
  normative updates together.
- This branch starts from explicit-import checkpoint `a1647ff`, which is now
  integrated as `main@a1647ff`. The predecessor-order restriction is therefore
  satisfied; this branch remains separate and unmerged while the increment is
  active.
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
  plan are authorized, and the branch remains based on the integrated
  predecessor and unmerged.
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
- Task 3 replaces the saturated `AppliedNominal` representation with one unary
  `Application` tree throughout production code. Resolution folds source
  arguments left while preserving the predecessor's saturation and failure
  boundary until Task 4. Type operations, paired application provenance, both
  retained Core transforms, independent Core validation, and evaluator nominal
  inspection use that tree. Core `TypeApplicationNode` remains the distinct
  simultaneous n-ary outer-scheme instantiation operation.
- Task 3 also closes the source-derived type-carrier and kind-site inventories.
  The production-wide recursive-owner guard rejects raw destructive mutation;
  exact resource and 32,768-level, 256 KiB-stack witnesses cover canonical
  operations, retained payloads, replacements, and normal error exits. Two
  independent reviews approve the final semantics and ownership boundary. The
  focused suites, full all-target and all-feature workspace suite, Clippy with
  warnings denied, formatting, all-target checking, test enumeration,
  `cargo xtask verify`, Rust documentation, Markdown lint, and diff hygiene pass
  on the final change.
- Task 4 assigns every declaration binder one canonical fixed `Kind` and makes
  present explicit binder lists complete and ordered. Omitted annotations and
  absent global or implementation lists receive `Type` in this phase; this is
  the accepted no-inference boundary, not a permanent language principle.
  Checked schemes and body-free summaries retain the ordered identity-kind
  pairs.
- Task 4 also adds iterative, budgeted Kind operations and one total resolved
  kind stage. The stage freezes local nominal and interface environments before
  declaration checking, uses owner-specific declaration environments, leaves
  the resolved-stage inference environment empty, authenticates direct
  body-free kind facts, and admits partial constructors where the enclosing
  rule accepts their residual kind. The public resolution pipeline has one
  fail-closed kind gate before it constructs a `ResolvedModule`.
- The new stage takes ownership of predecessor saturation and type-parameter
  application failures. Value-boundary failures now use
  `kind.expected-type`, non-function applications use `kind.not-applicable`,
  and application-domain or interface-argument mismatches use
  `kind.argument`. Structured diagnostics retain expected and found kinds,
  causal occurrence spans, and relevant declaration spans. Exact budgets,
  one-short atomic failures, and 32,768-level or 32,768-wide tests on 256 KiB
  threads cover Kind operations, synthesis, environments, provenance, body
  traversal, diagnostics, and teardown. The architecture inventory closes the
  new carriers and enforces the sole public gate.
- Task 4 closure authenticates declaration order as a complete, duplicate-free
  partition and authenticates constructor-provenance cardinality before any
  consumer uses the frozen environments. The kind stage stops at the first
  candidate owned by the later method-local, determination, or
  prerequisite-only check, so a later declaration cannot preempt that owner.
  Rendering and surface-kind conversion now publish and test their
  one-state-per-node resource formulas. The unused predecessor arity reason is
  removed; `resolve.type-kind` remains only for using an interface identity as
  an ordinary value type.

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

Canonical application also makes a retained result type deep enough that
`Observation` needs iterative teardown. Implementing `Drop` prevents Rust
callers from moving its public fields directly. CP-0009 now records the
consuming `ObservationValue` and `ObservationParts` API that preserves captured
evaluation heaps and transfers or dismantles result types without recursive
drop. It also records that `TypeContext::insert` dismantles a displaced binding
fact instead of returning a raw recursive type that callers can ignore, and
that automatically dropped checked facts expose their structural types through
borrowing accessors rather than mutable raw fields. Public carriers without
automatic `Drop` remain caller-managed and use `discard_type_iteratively` when
disposing a potentially deep extracted type.

The type-bearing site map and additive resource formulas are implementation
inputs, not retrospective documentation. The architecture guard and exact
budget probes therefore precede summary and Core expansion.

## Deviations

Task 3 refines the predecessor Rust API so `Observation` can dismantle a
canonical result type on drop without recursion or unsafe code. Borrowing moves
to `value()` and `ty()`; direct field moves, overwrites, and by-value
destructuring are replaced by borrowing and consuming accessors. CP-0009
records this source-compatibility exception and its heap-owning return types.
Checked requirements, constrained schemes, interface method facts, and
implementation facts likewise expose their automatically dropped structural
fields through borrowing accessors. `TypeContext::insert` now disposes
a displaced binding fact iteratively and returns nothing; repository callers
already ignored its previous raw `Option<Type>` result. Ash semantics, library
and CLI rendering, and evaluator behavior do not change.

No semantic deviation from CP-0009 is currently known. Any product evidence
that exposes missing or incorrect semantics returns to proposal or design work
instead of being decided in this task.
