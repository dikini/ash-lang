# Design notes

Design notes record exploration, research, alternatives, experiments, tradeoffs, uncertainty, and future architectural pressure. They are informative and do not define Ash semantics or accept architecture. A note may govern a disposable prototype limited to its stated question, comparison cases, and retention conditions when code is necessary to compare candidates; the prototype remains evidence rather than product implementation.

Use [the template](template.md), allocate the next `DN-NNNN` ID, and link related artifacts. When a non-language choice converges, record it in an architectural decision. When a language-semantic change becomes concrete, write a change proposal.

The userspace scheduling exploration is retained in
[DN-0051](DN-0051-userspace-concurrency-and-scheduling.md).
The checked FFI, region and local-control exploration is retained in
[DN-0057](DN-0057-checked-ffi-module-boundaries.md),
[DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md) and
[DN-0056](DN-0056-scoped-continuation-retention-and-library-scheduling.md).
[TASK-0050](../tasks/TASK-0050-checked-ffi-regions-control-program.md) owns delivery
coordination; these notes remain informative.

## Implementation and evidence boundaries

A note's `exploring` or `evaluating` status describes its design work, not the
completion of every feature it discusses. Read each claim within its scope:

- **Implemented** means a specified product slice, or an accepted architectural
  choice present in the implementation. It does not accept the rest of a note.
- **Experimental** means a bounded prototype, formal model, or comparison with
  stated assumptions. Retention on `main` does not make it product semantics.
- **Open** means a candidate, unresolved question, or incomplete delivery.
  A delivery sketch or worked fragment does not establish the full capability.

The [specification](../../spec/README.md) owns language truth; accepted
[decisions](../decisions/README.md) own non-language architecture. The
[feature inventory](../project/implemented-features.md) links product and
experimental implementation evidence, while the [trajectory](../trajectory.md)
records milestone maturity. The following summary identifies scope rather
than assigning new artifact statuses or authorizing work. Detailed evidence
and exclusions remain at their linked owners.

| Notes | Implemented or retained evidence | Open scope and limits |
| --- | --- | --- |
| DN-0001–0003: foundations, Core, parser | Accepted implementation, parser, front-end, Core, and evaluator choices are recorded in the [decisions](../decisions/README.md). | Broader foundation goals and unselected representation alternatives remain informative. |
| DN-0005–0008: functions, typing, data, elaboration | Functions, rank-1 typing, tuples, nominal ADTs, patterns, and typed Core are specified. [Mini-Ash closure](mini-ash/closure.md) retains the bounded result. | Record forms and other unselected candidates are not current Ash. |
| DN-0009–0013: effects, identities, composition, hooks, protocols | Exact effects, one-shot handlers/discard, scoped ownership, and synchronous hooks are implemented within the [Effect Ash boundary](effect-ash/milestone-closure-evidence.md). | General protocols, dynamic composition, multi-shot/escaping continuations, suspension, and concurrency remain open. |
| DN-0014: finite kinds and promotion | Current fixed higher kinds are distinct from this proposal. | Nominal finite kinds and datatype promotion are not implemented. |
| DN-0015–0016, DN-0020: corpus and milestones | Mini-Ash and Modular Ash are complete; their [closure reports](modular-ash/closure.md) and tags retain evidence. | Historical milestone grammar is not a selectable current dialect. |
| DN-0017–0018: storage and runtime-established evidence | Current resources supply scoped dependency and completion checks. | General storage policies, ownership transfer, and runtime-established proof evidence remain exploratory. |
| DN-0019: primitive feature composition | A separate [Float prototype and comparison](DN-0019-primitive-feature-composition.md#retained-experiment) retain maintenance findings. | No Float semantics or feature-composition architecture was adopted. |
| DN-0022–0023: modules and interfaces | Passive modules and method-only interfaces are implemented; [Modular Ash closure](modular-ash/closure.md) retains evidence. | Runtime module loading and interface lookup are not supplied by these increments. |
| DN-0024: executable learning | [Migration evidence](migration-repair-evidence.md) records concrete compiler repairs and source outcomes. | The external learning programme is outlined; its adoption belongs to the external project. |
| DN-0025: libraries and packages | Four bounded library increments are complete, with the final [relational-interface evidence](lib-ash/relational-interfaces-evidence.md). | Package resolution, persistent compiled modules, and separate object linking remain exploratory. |
| DN-0026–0028: Effect Ash programme | The selected milestone is [complete and integrated](effect-ash/milestone-closure-evidence.md). | General foreign acquisition, suspension, and concurrency were excluded; planning forecasts are not active tasks. |
| DN-0029: diagnostics | [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md) and the [tool guide](../tools/ash.md) record implemented human/localized and JSON output. | Editor protocols and interactive correction remain excluded from that checkpoint. |
| DN-0030: compiler macros and hooks | Typed Core validation and runtime effect/resource contracts provide the foundation. | Macros, compiler-phase hooks, staged handlers, registration/selection, and specialized kernels are not implemented. |
| DN-0031–0032: resource composition | Concept maps and [bounded algebraic derivations](DN-0032-algebra-of-scoped-resource-composition.md) relate candidates to current sequencing and scopes. | General contextual provision, composition laws, and combined soundness remain open. |
| DN-0033–0034: direct effects and verification | The [one-shot formalization](direct-effects/one-shot/README.md#current-proof-status) establishes stated annotated-model admission, preservation, progress, and bounded execution results. | It is not a complete Ash compiler-correctness proof. Core alignment evidence remains branch-local and incomplete. |
| DN-0035: regions and verified providers | Current dependency rules and scalar Arena experiments supply limited evidence. | General region interfaces, borrowing, ordinary storage policy, and provider verification remain open. |
| DN-0036: foreign/provider experiments | [Main delivery](provider-experiments/main-delivery-2026-10-08/README.md) retains verified Rust-authored SQLite and scalar Arena experiments. | Product adoption, general borrowing, and wider Arena payload/graph work remain incomplete. |
| DN-0037: Ash-authored foreign interfaces | The [specified foreign-interface profile](../../spec/static-semantics.md#source-foreign-declarations), [Ash-authored libraries](../../libraries/README.md) and [generated-host builds](../tools/ash.md#generated-host-linkage-checks) implement the selected source contracts and native lifecycle. The [readiness brief](foreign-authoring/dn-0036-readiness.md) preserves the bounded comparison. | The specification defines the exact profile and exclusions; source `given` providers and privileged lifecycle wrappers remain unsupported. This note does not authorize wider FFI or borrowing. |
| DN-0038: resource properties and mutation | Scoped cells already distinguish reusable access from scope-owned release. | General linear/unique usage, borrowing, disposal permissions, and mutable syntax remain candidates. |
| DN-0039–0041: files, Float, serialization | Existing effects/interfaces and retained native experiments provide foundations and comparison cases. | Filesystem contracts, Float semantics, and serialization APIs are delivery sketches, not implemented capabilities. |
| DN-0042–0043: native/data direction and shorter syntax | Synthesis and syntax comparisons reuse existing checked forms. | The summaries add no implementation; shorter forms need parsing, elaboration, and equivalence evidence. |
| DN-0044–0046: runtime services, native execution, agent tooling | Existing Core, evaluator, and diagnostics provide foundations; native execution and agent tooling are outlined in the trajectory. | Selectable runtime services, a native backend, interactive native execution, LSP, and the agent semantic interface remain design work. |
| DN-0047: ECS and heterogeneous stores | [Checked source fragments](DN-0047-ecs-and-open-heterogeneous-stores.md#evidence-and-experiments) validate limited current-language encodings. | No ECS implementation or measured performance follows; open stores and existential packaging remain candidates. |
| DN-0048: parallel kernels | Current Pure Core and strict evaluation supply reference obligations. | Kernel extraction, a kernel IR, interaction-net translation, and SIMD/GPU lowering are not implemented by this note. |

## Current notes

### Foundations

- [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md)

### Immediate architecture

- [DN-0002: Core Representation](DN-0002-core-representation.md)
- [DN-0003: Parser Architecture](DN-0003-parser-architecture.md)
- [DN-0019: Primitive Feature Composition](DN-0019-primitive-feature-composition.md)
  — transferable findings from the retained Float composition experiment.
- [DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md) — completed evaluation
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
- [Migration repair evidence](migration-repair-evidence.md) — current-main
  reproduction, verified main integration and original-source outcomes.
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

- [DN-0050: Native program gas estimates](DN-0050-native-program-gas-estimates.md)
  — calibration and prediction errors for the input-derived gas policies adopted
  in AD-0013; predecessor diagnostics remain scoped evidence, not full-port verification.
- [DN-0048: Pure Core Kernels and Parallel Lowering](DN-0048-pure-core-kernels-and-parallel-lowering.md)
  — Pure Core first, a typed Ash-owned kernel IR with strict completion,
  optional interaction-net dependencies and sharing, and SIMD/GPU lowering;
  exploratory contracts, law obligations and bounded comparison criteria.
- [DN-0045: Native Compilation and Interactive Execution](DN-0045-native-compilation-and-interactive-execution.md)
  — AOT and interactive paths, human and AI feedback needs, shared lowering,
  LLVM/MLIR/Cranelift alternatives, continuation representations and CPS;
  no accepted native architecture.
- [DN-0044: No Default Runtime](DN-0044-no-default-runtime.md)
  — working exploration of library-supplied services, compiler defaults,
  ordinary construction and storage lowering, constrained targets, and foreign
  callers; no ready design or accepted backend.
- [DN-0030: Typed Compiler Macros and Declarative Hooks](DN-0030-typed-compiler-macros-and-hooks.md)
  — work-in-progress exploration of typed compiler transformations,
  declarative phase hooks, registration scopes, unresolved selection policy,
  staged handlers and providers, and library-defined specialized kernels.

### Tooling and feedback

- [DN-0046: Agent Semantic Exploration and Feedback](DN-0046-agent-semantic-exploration-and-feedback.md)
  — an agent interface combining semantic navigation, search and executable
  probes alongside intended LSP support; depends on DN-0045's shared compiler
  and execution boundaries, without requiring completed optimizing AOT or JIT.

### Surface language, typing, and elaboration

- [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md) — equational and operational function presentations and their elaboration.
- [DN-0006: Initial Type System](DN-0006-initial-type-system.md) — candidate first-nucleus kinds, types, polymorphism, inference, and unification.
- [DN-0007: Data and Pattern Typing](DN-0007-data-and-pattern-typing.md) — products, ADTs, visibility, patterns, irrefutability, and coverage.
- [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md) — explicit typed Core, representation contracts, execution, and semantic policy seams.

### Effects and dynamic composition

- [DN-0043: Shorter Surface Alternatives](DN-0043-shorter-surface-alternatives.md)
  — requests and mutable-resource access; a catalogue of scope, handler,
  function, evidence and type-notation alternatives with checked authority.
- [DN-0033: Direct Effects and Continuation Capabilities](DN-0033-direct-effects-and-continuation-capabilities.md)
  — direct operational calculus, ordered interpretation frames, ownership and
  continuation checks, mixed-handler derivations, and scoped async exploration.
- [DN-0032: Algebra of Scoped Resource Composition](DN-0032-algebra-of-scoped-resource-composition.md)
  — literature-based derivation of binding, resource/body composition,
  provider interpretation and conditional lifetime laws.
- [DN-0031: Resource Composition Concept Map](DN-0031-resource-composition-concept-map.md)
  — maintained concept, identity, implementation-coverage and overlap maps for
  the exploratory algebra of resources, effects, providers and handlers.
- [Milestone closure evidence](effect-ash/milestone-closure-evidence.md) —
  combined conformance, downstream-pressure and simplification audit; final
  merged-main verification passed after signed integration.
- [Narrow checked foreign-provider evidence](effect-ash/narrow-foreign-provider-evidence.md)
  — native allocation, checked access, scoped ownership, fail-stop resource
  reports, independent validation and verified local integration.
- [Reliable cleanup evidence](effect-ash/reliable-cleanup-evidence.md) —
  verified normal completion, owned abandonment, typed reporting and local
  integration of the complete cleanup contract.
- [Synchronous hook evidence](effect-ash/synchronous-hooks-evidence.md) —
  verified hook roots, registration, runtime composition and local integration
  of the complete hook contract.
- [Safe resource scope evidence](effect-ash/resource-scope-evidence.md) —
  cell ownership, dependency, activation, runtime and full verification
  evidence; the product checkpoint is complete and locally integrated with
  merged-checkout verification.
- [Scoped exact evidence](effect-ash/scoped-evidence-evidence.md) — verified
  pure relation, method/selection interactions, authentication and local merge.
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

- [DN-0034: Verification Foundation for Ash Semantics and Implementation](DN-0034-one-shot-kernel-soundness-and-practicality.md)
  — one-shot and Core correspondence as a base for soundness and correctness,
  parallel development, tooling, and lightweight verification artifacts.

### Downstream type-system and resource exploration

- [DN-0047: ECS and Open Heterogeneous Stores](DN-0047-ecs-and-open-heterogeneous-stores.md)
  — ECS as a stress case for typed immutable worlds, generic queries, static
  heterogeneous schemas, authenticated type-key composition, checked lookup
  and future existential packaging; theoretical costs without measurements.
- [DN-0042: Native Interaction and Efficient Data](DN-0042-native-interaction-and-efficient-data.md)
  — a summary connecting FFI, resources, regions, native use cases, numeric
  representations and data processing, with missing collection and SIMD
  concerns for planning and tracking.
- [DN-0041: Typed Serialization and Data Pipelines](DN-0041-typed-serialization-and-data-pipelines.md)
  — an Ash adaptation of Serde's architecture, first-class JSON/YAML/CSV/TOML/BSON
  contracts, owned and incremental processing, scoped storage and attributable
  type/runtime costs.
- [DN-0040: Floating-Point Semantics and Representation](DN-0040-floating-point-semantics-and-representation.md)
  — a minimal binary64 language direction, source/Core/operational obligations,
  numerical conversions and format contracts, with proposed representation-cost
  comparisons.
- [DN-0039: Files and Filesystem Resources](DN-0039-files-and-filesystem-resources.md)
  — scoped file access and filesystem authority, copying I/O, partial progress,
  fallible completion, host profiles and later arena/buffer integration.
- [DN-0038: Resource Properties and Mutable Variable Usage](DN-0038-resource-properties-and-mutable-variable-usage.md)
  — separate usage, uniqueness, access, lifetime, payload and completion
  properties; compare Rust-like regimes, semantics, Core, proofs, surface forms
  and memory/performance opportunities before choosing a design.
- [DN-0037: Ash-Authored Foreign-Library Interfaces](DN-0037-ash-authored-foreign-library-interfaces.md)
  — a separate program for typed foreign contracts, generic host ABI calls,
  memory and linking, with Ash binding code and declarative native build inputs.
- [DN-0036: Foreign Library and Memory Provider Experiments](DN-0036-foreign-library-and-memory-provider-experiments.md)
  — coordinated SQLite and scoped-arena experiments, type-checking contracts,
  surface syntax and Core semantics, a foreign-library authoring blueprint,
  tooling, and an adoption path into Ash and its standard library.
- [DN-0035: Region Memory Management and Verified Providers](DN-0035-region-memory-management-and-verified-providers.md)
  — nested lexical regions, statically selected library policies, immutable
  sharing, provider verification, and a memory-management reference corpus.
- [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md) — tests for protocol, multiplicity, continuation, and handler composition machinery.
- [DN-0014: Finite Kinds and Promotion](DN-0014-finite-kinds-and-promotion.md) — finite nominal static domains and restricted datatype promotion.
- [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md) — deterministic cleanup, plural storage policies, transfer, sharing, and cost visibility.
- [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md) — generative evidence for checked values and relationships, with possible place decomposition.

`DN-0005` through `DN-0014` adapt user-supplied explorations preserved in Git history at commit `abd793c`. Their placement here records useful design context; it does not add them to the development trajectory.

## Generic Cell follow-up

- [DN-0053: Scoped Generic Cells Without Native Owners](DN-0053-scoped-generic-cells-without-native-owners.md)
  records the rationale and remaining questions behind the
  [generic cell checkpoint integrated into local Main](generic-cell/evidence.md).
- [DN-0054: Base Lexical Region Memory Contracts](DN-0054-base-lexical-region-memory-contracts.md)
  remains separate design work and is outside the generic Cell implementation.
