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

The [current specification](../spec/README.md) defines Modular Ash with passive
source modules and method-only type-class-like interfaces and implementations.
The [`ash` tool guide](tools/ash.md) documents entry-module execution, named
module roots, and interface-related source failures. The
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
current milestone checkpoint; no closure task is active.

| Work | Maturity | Dependencies | Next evidence |
| --- | --- | --- | --- |
| [Mini-Ash phase](design/DN-0015-mini-ash-phase.md) | complete / implementation | historical `mini-ash` tag, reviewed [first corpus stratum](design/DN-0016-first-mini-ash-corpus.md), accepted component decisions, retained [data-and-pattern evidence](design/mini-ash/data-and-patterns/evidence.md), and retained [rank-1 evidence](design/mini-ash/rank-1-polymorphism/evidence.md) | Use the separately built tag only for bounded historical comparisons. |
| [Executable learning and evidence stream](design/DN-0024-executable-learning-and-evidence-stream.md) | outlined | historical `mini-ash` tag, current [Modular Ash specification](../spec/README.md), [documentation policy](project/documentation.md), and retained [first corpus stratum](design/DN-0016-first-mini-ash-corpus.md) | Run an external-repository pilot that tests executable teaching, forward-only migration, source adaptation, and cooperative evidence exchange. |
| [Passive static modules](design/DN-0022-passive-static-modules.md) | complete / implementation | completed Mini-Ash tag and closure evidence, current [Modular Ash specification](../spec/README.md), and retained [passive-module evidence](design/modular-ash/evidence.md) | Preserve the implemented export-summary and module-identity boundaries during later audits. |
| [Interfaces and `impl`](design/DN-0023-interfaces-and-implementations.md) | complete / implementation | implemented passive static modules, current [specification](../spec/README.md), retained interface design, and [implementation evidence](design/modular-ash/interfaces-evidence.md) | Preserve the method-only, authenticated-evidence, and unspecialized-trace boundaries during separately authorized later interface work. |
| [Modular core-versus-library audit](design/modular-ash/core-library-evidence.md) | complete / implementation | implemented passive modules and method-only interfaces, their retained evidence, and the [Modular Ash closure report](design/modular-ash/closure.md) | Treat exploratory `lib-ash` pressure as separate work that requires its own authorization, not as the next authorized step in a sequential roadmap. |
| [Core representation](decisions/AD-0007-typed-core-dialects.md) | implementation | accepted typed-dialect and pure-computation boundaries | Exercise the retained closed pure dialect and operation-family seam against the next proposed feature pressure. |
| [Parser architecture](decisions/AD-0005-parser-architecture.md) | implementation | accepted event-producing recursive-descent boundary and current grammar | Measure locality, recovery, and source coverage when a later proposal adds syntax. |
| [Front-end semantic boundaries](decisions/AD-0006-front-end-semantic-boundaries.md) | implementation | accepted resolved-surface and bidirectional typed-elaboration boundaries | Extend stage interfaces and structured diagnostics only with an authorized semantic increment. |
| [Evaluator architecture](decisions/AD-0008-explicit-evaluator-machine.md) | implementation | accepted first-order machine boundary and current dynamics | Test future effect and continuation pressure without changing current pure semantics implicitly. |
| [Specification methodology](decisions/AD-0004-small-step-semantic-method.md) | implementation | accepted small-step primary method and current dynamics | Keep future operational behavior derived from one normative small-step account. |

Planning detail must decrease with distance. Effects, providers, processes, propositions, laws, proofs, and optimizer search are future design pressure, not planned language inventory. Immediate work should preserve relevant options without implementing those features.
