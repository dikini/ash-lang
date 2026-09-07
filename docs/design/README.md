# Design notes

Design notes record exploration, research, alternatives, experiments, tradeoffs, uncertainty, and future architectural pressure. They are informative and do not define Ash semantics or accept architecture. A note may govern a disposable prototype limited to its stated question, comparison cases, and retention conditions when code is necessary to compare candidates; the prototype remains evidence rather than product implementation.

Use [the template](template.md), allocate the next `DN-NNNN` ID, and link related artifacts. When a non-language choice converges, record it in an architectural decision. When a language-semantic change becomes concrete, write a change proposal.

## Current notes

### Foundations

- [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md)

### Immediate architecture

- [DN-0002: Core Representation](DN-0002-core-representation.md)
- [DN-0003: Parser Architecture](DN-0003-parser-architecture.md)
- [DN-0019: Primitive Feature Composition](DN-0019-primitive-feature-composition.md)
  — transferable findings from the retained Float composition experiment.
- [DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md) — growing evaluation
  corpus, component experiments, and retained product increments.
- [DN-0016: First Mini-Ash Corpus Stratum](DN-0016-first-mini-ash-corpus.md) —
  shared evidence for the initial monomorphic functional nucleus.
- [DN-0020: Ash Dialect Milestones](DN-0020-ash-dialect-milestones.md) — retained
  Mini-Ash history, the completed passive-module and method-only interface
  increments, and the completed Modular Ash audit and closure checkpoint.
- [DN-0022: Passive Static Modules](DN-0022-passive-static-modules.md) —
  retained design exploration for the implemented declarations-only modules,
  rooted imports, visibility, opacity, generated export summaries, and
  single-program Core assembly.
- [DN-0023: Interfaces and Implementations](DN-0023-interfaces-and-implementations.md)
  — retained exploration for the completed method-only type-class-like
  interfaces, scoped implementations, constrained rank-1 schemes, and explicit
  Core evidence.
- [DN-0024: Executable Learning and Evidence Stream](DN-0024-executable-learning-and-evidence-stream.md)
  — a version-pinned external learning corpus, forward migration, and
  cooperative design-evidence flow.
- [DN-0025: Library and Package Milestones](DN-0025-library-and-package-milestones.md)
  — the completed `modular-ash` closure boundary, four completed bounded
  `lib-ash` increments retained by the import, kind, method-parameter, and
  relational-interface evidence reports, and later exploratory package-
  artifact work.
- [Explicit implementation import and re-export evidence](lib-ash/imports-evidence.md)
  — selector and facade behavior, identities, summaries, diagnostics,
  resources, linked authentication, Core locality, migration, and exclusions
  for the first `lib-ash` increment.
- [Explicit kinds and higher-kinded parameter evidence](lib-ash/kinds-evidence.md)
  — fixed kinds, canonical application, inference and evidence preservation,
  body-free and linked authentication, Core authority, resources, migration,
  and exclusions for the second bounded `lib-ash` increment.
- [Method-local type-parameter evidence](lib-ash/method-parameters-evidence.md)
  — canonical method schemes, occurrence instantiation, rigid implementation
  checking, body-free and linked authentication, generated Core adapters,
  resources, migration, runtime erasure, and exclusions for the third bounded
  `lib-ash` increment.
- [Multi-parameter relational-interface evidence](lib-ash/relational-interfaces-evidence.md)
  — complete ordered applications, one total forward edge, method and
  requirement determinacy, implementation coherence, one-pass improvement,
  linked and Core authentication, exact resources, migration, runtime erasure,
  and downstream exclusions for the fourth bounded `lib-ash` increment.
- [Passive-module evidence](modular-ash/evidence.md) — implementation,
  resource, locality, historical-comparison, and verification evidence for the
  first Modular Ash increment.
- [Interface implementation evidence](modular-ash/interfaces-evidence.md) —
  implementation, diagnostic, resource, Core locality, runtime, and
  unspecialized trace evidence for the method-only interface increment.
- [Core and library equality evidence](modular-ash/core-library-evidence.md) —
  paired admission, typing, diagnostic, Core, evaluation, maintenance, and
  lifetime evidence for the final Modular Ash audit.
- [Modular Ash closure report](modular-ash/closure.md) — retained dialect,
  stage boundaries, simplification conclusions, resources, ownership,
  verification, and exclusions at the final checkpoint.
- [Mini-Ash closure report](mini-ash/closure.md) — retained dialect inventory,
  simplification audit, budgets, ownership boundaries, and exclusions.
- [Rank-1 integration evidence](mini-ash/rank-1-polymorphism/evidence.md) —
  cross-stage evidence for Mini-Ash's final semantic increment.

### Compiler transformations and backends

- [DN-0030: Typed Compiler Macros and Declarative Hooks](DN-0030-typed-compiler-macros-and-hooks.md)
  — work-in-progress exploration of typed compiler transformations,
  declarative phase hooks, registration scopes, unresolved selection policy,
  staged handlers and providers, and library-defined specialized kernels.

### Surface language, typing, and elaboration

- [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md) — equational and operational function presentations and their elaboration.
- [DN-0006: Initial Type System](DN-0006-initial-type-system.md) — candidate first-nucleus kinds, types, polymorphism, inference, and unification.
- [DN-0007: Data and Pattern Typing](DN-0007-data-and-pattern-typing.md) — products, ADTs, visibility, patterns, irrefutability, and coverage.
- [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md) — explicit typed Core, representation contracts, execution, and semantic policy seams.

### Effects and dynamic composition

- [Synchronous hook evidence](effect-ash/synchronous-hooks-evidence.md) —
  verified root checkpoint and explicit outstanding registration, runtime and
  full-contract evidence.
- [Safe resource scope evidence](effect-ash/resource-scope-evidence.md) —
  cell ownership, dependency, activation, runtime and full verification
  evidence; the product checkpoint is complete and locally integrated with
  merged-checkout verification.
- [Scoped exact evidence](effect-ash/scoped-evidence-evidence.md) — in-progress
  pure relation, method/selection interactions, and retained review corrections.
- [Local `newtype` evidence](effect-ash/local-newtype-evidence.md) — lexical
  identity, escape, scope authentication, erasure, and exact resources for the
  local nominal checkpoint.
- [Resume-required effect kernel evidence](effect-ash/resume-required-effect-kernel-evidence.md)
  — retained source, Core, runtime, diagnostic, resource, and predecessor
  observations for the first effect kernel.
- [DN-0026: Effect Ash Resource-First Milestones](DN-0026-effect-ash-resource-first-milestones.md)
  — a partial-order decomposition through shared generative identity, scoped
  evidence, resources, synchronous hooks, foreign providers, suspension, and
  concurrency.
- [DN-0029: Human Diagnostic Presentation](DN-0029-human-diagnostic-presentation.md)
  — human-first source rendering, machine output, structured internal causes,
  and localized message catalogues.
- [DN-0027: Effect Ash Program Design](DN-0027-effect-ash-program-design.md) —
  the current informative closure boundary, causal checkpoint program,
  authority gates, implementation seams, and downstream extension pressures.
- [DN-0028: Effect Ash Milestone Plan](DN-0028-effect-ash-milestone-plan.md) —
  proposal-gated execution protocol, relative budget forecast, exact first
  proposal work, post-acceptance TDD skeleton, and later checkpoint gates.
- [Module `newtype` evidence](effect-ash/module-newtype-evidence.md) — retained
  cross-stage product evidence for the first bounded `effect-ash` input.
- [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md) — effect APIs and rows, handler composition, and continuation contracts.
- [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md) — static/runtime identity, ownership, withdrawal, and captured resources.
- [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md) — passive modules and typed composition at static-link and runtime-load stages.
- [DN-0012: Coeffects and Hooks](DN-0012-coeffects-and-hooks.md) — typed handler hook points, subscription, composition, effects, and lifetime.

### Downstream type-system and resource exploration

- [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md) — tests for protocol, multiplicity, continuation, and handler composition machinery.
- [DN-0014: Finite Kinds and Promotion](DN-0014-finite-kinds-and-promotion.md) — finite nominal static domains and restricted datatype promotion.
- [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md) — deterministic cleanup, plural storage policies, transfer, sharing, and cost visibility.
- [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md) — generative evidence for checked values and relationships, with possible place decomposition.

`DN-0005` through `DN-0014` adapt user-supplied explorations preserved in Git history at commit `abd793c`. Their placement here records useful design context; it does not add them to the development trajectory.
