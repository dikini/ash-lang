# Development trajectory

This is a dependency and maturity view, not a sequential roadmap. Maturity
uses: `idea → speculative → outlined → designed → specified →
implementation`. A completed row records `complete / implementation` to
distinguish its result from its maturity.

The Mini-Ash milestone is retained historically at the `mini-ash` tag, whose
peeled commit is `d62d3ba`. Its
[closure report](design/mini-ash/closure.md) records the complete dialect
inventory, simplification audit, retained budgets, ownership boundaries, and
intentional exclusions. Historical comparisons build that tag separately;
current source contains no Mini-Ash dialect selector or compatibility grammar.

The [current specification](../spec/README.md) defines four implemented bounded
`lib-ash` increments on the completed Modular Ash base. It retains
passive source modules and method-only type-class-like interfaces; adds explicit
implementation selection and targeted name and implementation re-exports; and
adds explicit kinds, higher-kinded declaration parameters, explicit fixed-
kinded method-local parameters with authenticated generated evidence, and
complete relational interface applications with one optional total forward
determination edge. The
[`ash` tool guide](tools/ash.md) documents entry-module execution, named module
roots, and interface-related source failures. The
[passive-module evidence](design/modular-ash/evidence.md) and
[interface implementation evidence](design/modular-ash/interfaces-evidence.md)
retain the completed passive-module and method-only interface increments across
implementation, resources, locality, Core assembly, runtime observations, and
historical or future comparison baselines. The
[core-and-library audit](design/modular-ash/core-library-evidence.md) and
[Modular Ash closure report](design/modular-ash/closure.md) retain the completed
audit, simplification analysis, and closure evidence.

The first Mini-Ash corpus consistency, component-comparison, and convergence
gates are complete. Their retained results remain in the
[DN-0016 experiment program](design/DN-0016-first-mini-ash-corpus.md#tracked-experiment-program)
and its [convergence record](design/mini-ash/first-stratum/comparisons/component-convergence.md).

[DN-0020](design/DN-0020-ash-dialect-milestones.md) outlines two retained
milestones. Mini-Ash, passive static modules, method-only interfaces and
`impl`, the bounded core-versus-library audit, simplification, and Modular Ash
closure are complete. Interfaces are type-class-like relationships, not module
signatures. The final annotated unsigned `modular-ash` tag retains the completed
current milestone checkpoint. [DN-0025](design/DN-0025-library-and-package-milestones.md)
now gives `lib-ash` a dependency spine with decreasing planning detail. Its
first bounded increment is complete; its reviewed implementation and evidence
corpus are retained by the
[explicit-import evidence report](design/lib-ash/imports-evidence.md). The
second bounded increment is also complete; its reviewed explicit kinds and
higher-kinded declaration parameters are retained by the
[explicit-kind evidence report](design/lib-ash/kinds-evidence.md). The third
bounded increment is complete; its reviewed method schemes, generated evidence
adapters, resource bounds, migration, and runtime erasure are retained by the
[method-parameter evidence report](design/lib-ash/method-parameters-evidence.md).
The fourth bounded increment is complete; its reviewed
product evidence is retained by the
[relational-interface evidence report](design/lib-ash/relational-interfaces-evidence.md).
Together, the four integrated increments close the revised `lib-ash` milestone.
The retained product boundary omits associated projections, general
determination graphs, defaults, effects, proofs, and existentials. `effect-ash`,
`proof-ash`, and `pack-ash` are named future milestones. `effect-ash` and
`pack-ash` have no ordering between them. `effect-ash` and `proof-ash` remain
separate, but their work may interleave through explicitly named synchronization
checkpoints.
[DN-0026](design/DN-0026-effect-ash-resource-first-milestones.md) outlines a
resource-first partial order for `effect-ash`: common pure and resource
generativity and the effect kernel meet at resource scope, synchronous hooks
follow early, and suspension and concurrency remain later work.
On this product branch, the first bounded input, module `newtype`, is complete
with retained [cross-stage evidence](design/effect-ash/module-newtype-evidence.md)
and remains pending separately authorized integration. Local `newtype` is the
next programme input only after that integration boundary; neither statement
makes the wider Effects Ash milestone current on `main`.

| Work | Maturity | Dependencies | Next evidence |
| --- | --- | --- | --- |
| [Mini-Ash phase](design/DN-0015-mini-ash-phase.md) | complete / implementation | historical `mini-ash` tag, reviewed [first corpus stratum](design/DN-0016-first-mini-ash-corpus.md), accepted component decisions, retained [data-and-pattern evidence](design/mini-ash/data-and-patterns/evidence.md), and retained [rank-1 evidence](design/mini-ash/rank-1-polymorphism/evidence.md) | Use the separately built tag only for bounded historical comparisons. |
| [Executable learning and evidence stream](design/DN-0024-executable-learning-and-evidence-stream.md) | outlined | historical `mini-ash` tag, current [specification](../spec/README.md), [documentation policy](project/documentation.md), and retained [first corpus stratum](design/DN-0016-first-mini-ash-corpus.md) | Run an external-repository pilot that tests executable teaching, forward-only migration, source adaptation, and cooperative evidence exchange. |
| [Passive static modules](design/DN-0022-passive-static-modules.md) | complete / implementation | completed Mini-Ash tag and closure evidence, current [specification](../spec/README.md), and retained [passive-module evidence](design/modular-ash/evidence.md) | Preserve the implemented export-summary and module-identity boundaries during later audits. |
| [Interfaces and `impl`](design/DN-0023-interfaces-and-implementations.md) | complete / implementation | implemented passive static modules, current [specification](../spec/README.md), retained interface design, and [implementation evidence](design/modular-ash/interfaces-evidence.md) | Preserve the method-only, authenticated-evidence, and unspecialized-trace boundaries during separately authorized later interface work. |
| [Modular core-versus-library audit](design/modular-ash/core-library-evidence.md) | complete / implementation | implemented passive modules and method-only interfaces, their retained evidence, and the [Modular Ash closure report](design/modular-ash/closure.md) | Treat exploratory `lib-ash` pressure as separate work that requires its own authorization, not as the next authorized step in a sequential roadmap. |
| [Explicit implementation imports and re-exports](design/lib-ash/imports-evidence.md) | complete / implementation | completed `modular-ash` checkpoint, current [specification](../spec/README.md), stable module and interface identities, body-free summaries, scoped implementation evidence, and the prepared [library milestone sequence](design/DN-0025-library-and-package-milestones.md#prepared-lib-ash-sequence) | Preserve the explicit selection, identity, summary, authorization, validation, Core, runtime, and resource boundaries during separately authorized later `lib-ash` work. |
| [Explicit kinds and higher-kinded parameters](design/lib-ash/kinds-evidence.md) | complete / implementation | integrated [explicit-import increment](design/lib-ash/imports-evidence.md), current [specification](../spec/README.md), accepted [ordered resolved-global authority](decisions/AD-0009-ordered-resolved-global-binder-authority.md), stable identities, body-free summaries, and independent Core validation | Preserve the phase-dependent inference boundary, authenticated ordered ownership, exact resource formulas, and runtime erasure during separately authorized later work. |
| [Method-local type parameters](design/lib-ash/method-parameters-evidence.md) | complete / implementation | integrated [explicit-kind increment](design/lib-ash/kinds-evidence.md), current [specification](../spec/README.md), stable method identities, body-free summaries, linked evidence validation, authenticated generated adapters, and independent typed Core validation | Preserve exact method-scheme authority, occurrence-local instantiation, bounded adapter authentication, ordinary rank-1 source values, resource limits, and runtime erasure during separately authorized later work. |
| [Multi-parameter relational interfaces](design/lib-ash/relational-interfaces-evidence.md) | complete / implementation | integrated [method-parameter increment](design/lib-ash/method-parameters-evidence.md), current relational [specification](../spec/README.md), stable identities, body-free summaries, occurrence-owned evidence, linked validation, typed Core erasure, and completed transition cleanup | Preserve forward-only improvement, full-application selection, and the effects, proofs, and existentials exclusions during separately authorized future work. |
| [`effect-ash`: resource-first effects, handlers, and providers](design/DN-0026-effect-ash-resource-first-milestones.md) | module `newtype` complete / product branch; programme outlined | retained module-`newtype` [evidence](design/effect-ash/module-newtype-evidence.md), current product-branch [specification](../spec/README.md), accepted [typed Core](decisions/AD-0007-typed-core-dialects.md) and [evaluator](decisions/AD-0008-explicit-evaluator-machine.md) boundaries, the exploratory [effect](design/DN-0009-effects-handlers-and-continuations.md), [identity and lifetime](design/DN-0010-identities-and-resource-lifetimes.md), [provider resolution](design/DN-0011-modules-providers-and-resolution.md), [hook](design/DN-0012-coeffects-and-hooks.md), and [protocol stress](design/DN-0013-session-and-resource-protocol-stress-tests.md) models, and the checked [interface evidence flow](../spec/elaboration.md#interface-evidence-lowering); no ordering dependency on `pack-ash` | After separately authorized integration, compare local `newtype`, pure scoped exact evidence, and a minimal one-shot effect kernel as independently bounded inputs to the first resource-scope proposal. Keep dynamic loading, existentials, async execution, and concurrency outside that first proposal. |
| [`proof-ash`: propositions, laws, program proofs, and law-derived testing](design/DN-0001-reboot-foundations.md#14-propositions-laws-and-proofs) | idea | current pure [specification](../spec/README.md), accepted [small-step semantic method](decisions/AD-0004-small-step-semantic-method.md) and [front-end](decisions/AD-0006-front-end-semantic-boundaries.md) and [typed Core](decisions/AD-0007-typed-core-dialects.md) boundaries, implemented [checked interface-evidence flow](../spec/elaboration.md#interface-evidence-lowering), and exploratory [runtime-established static evidence](design/DN-0018-runtime-established-static-evidence.md) | Define a bounded pure proposition-and-law corpus and compare proof-evidence and program-logic models before selecting a calculus. Any work that requires effect semantics must name a synchronization checkpoint with `effect-ash` and state its required inputs and retained outputs. |
| [Core representation](decisions/AD-0007-typed-core-dialects.md) | implementation | accepted typed-dialect and pure-computation boundaries | Exercise the retained closed pure dialect and operation-family seam against the next proposed feature pressure. |
| [Parser architecture](decisions/AD-0005-parser-architecture.md) | implementation | accepted event-producing recursive-descent boundary and current grammar | Measure locality, recovery, and source coverage when a later proposal adds syntax. |
| [Front-end semantic boundaries](decisions/AD-0006-front-end-semantic-boundaries.md) | implementation | accepted resolved-surface and bidirectional typed-elaboration boundaries | Extend stage interfaces and structured diagnostics only with an authorized semantic increment. |
| [Evaluator architecture](decisions/AD-0008-explicit-evaluator-machine.md) | implementation | accepted first-order machine boundary and current dynamics | Test future effect and continuation pressure without changing current pure semantics implicitly. |
| [Specification methodology](decisions/AD-0004-small-step-semantic-method.md) | implementation | accepted small-step primary method and current dynamics | Keep future operational behavior derived from one normative small-step account. |

Planning detail must decrease with distance. `effect-ash` names effects,
handlers, and providers as a future milestone toward typed interaction with
external systems. It is unordered with respect to `pack-ash`, so exploration
and later separately authorized increments may proceed concurrently.
`proof-ash` names propositions, laws, statically checked proof evidence,
program logic, and law-derived test generation as a separate future milestone.
`effect-ash` and `proof-ash` have no total ordering: work may interleave, but
any increment that needs a semantic fact from the other milestone must declare
an explicitly named synchronization checkpoint with required inputs, retained
outputs, and authority on each side. Exploratory choices do not become
cross-milestone dependencies before such a checkpoint. The current
[`pack-ash` boundary](design/DN-0025-library-and-package-milestones.md#intentional-exclusions)
excludes dynamic module loading and runtime interface lookup. Existential
packaging and runtime-established identities are possible convergence pressure
if later work admits dynamic composition; they do not create a current ordering
dependency. Processes and optimizer search remain future design pressure, not
planned language inventory. Immediate work should preserve relevant options
without implementing those features.
