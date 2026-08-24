# Development trajectory

This is a dependency and maturity view, not a sequential roadmap. Maturity uses: `idea → speculative → outlined → designed → specified → implementation`.

The Mini-Ash milestone is retained historically at the `mini-ash` tag, whose
peeled commit is `d62d3ba`. Its
[closure report](design/mini-ash/closure.md) records the complete dialect
inventory, simplification audit, retained budgets, ownership boundaries, and
intentional exclusions. Historical comparisons build that tag separately;
current source contains no Mini-Ash dialect selector or compatibility grammar.

The [current specification](../spec/README.md) defines Modular Ash with passive
source modules, and the [`ash` tool guide](tools/ash.md) documents entry-module
execution and named module roots. The
[passive-module evidence](design/modular-ash/evidence.md) records the first
Modular Ash increment across implementation, resources, locality, Core
assembly, and historical comparison.

The first Mini-Ash corpus consistency, component-comparison, and convergence
gates are complete. Their retained results remain in the
[DN-0016 experiment program](design/DN-0016-first-mini-ash-corpus.md#tracked-experiment-program)
and its [convergence record](design/mini-ash/first-stratum/comparisons/component-convergence.md).

[DN-0020](design/DN-0020-ash-dialect-milestones.md) outlines two retained
milestones. Mini-Ash and the passive-static-module increment are complete.
Interfaces and `impl` are the next type-class-like increment; they are not
module signatures. A core-versus-library audit follows implemented interfaces.

| Work | Maturity | Dependencies | Next evidence |
| --- | --- | --- | --- |
| [Mini-Ash phase](design/DN-0015-mini-ash-phase.md) | implementation | historical `mini-ash` tag, reviewed [first corpus stratum](design/DN-0016-first-mini-ash-corpus.md), accepted component decisions, retained [data-and-pattern evidence](design/mini-ash/data-and-patterns/evidence.md), and retained [rank-1 evidence](design/mini-ash/rank-1-polymorphism/evidence.md) | Use the separately built tag only for bounded historical comparisons. |
| [Passive static modules](design/DN-0022-passive-static-modules.md) | implementation | completed Mini-Ash tag and closure evidence, current [Modular Ash specification](../spec/README.md), and retained [passive-module evidence](design/modular-ash/evidence.md) | Use the implemented export-summary and module-identity boundaries as evidence for the interface increment. |
| [Interfaces and `impl`](design/DN-0020-ash-dialect-milestones.md#add-modular-ash-in-bounded-increments) | outlined | implemented passive static modules | Compare type-class-like interface and implementation semantics against real module boundaries without treating modules as signatures. |
| [Modular core-versus-library audit](design/DN-0020-ash-dialect-milestones.md#candidate-trajectory) | outlined | implemented modules and interfaces | Compare representative retained Core behavior with an operation expressed through a library interface, then run the Modular Ash simplification analysis. |
| [Core representation](decisions/AD-0007-typed-core-dialects.md) | implementation | accepted typed-dialect and pure-computation boundaries | Exercise the retained closed pure dialect and operation-family seam against the next proposed feature pressure. |
| [Parser architecture](decisions/AD-0005-parser-architecture.md) | implementation | accepted event-producing recursive-descent boundary and current grammar | Measure locality, recovery, and source coverage when a later proposal adds syntax. |
| [Front-end semantic boundaries](decisions/AD-0006-front-end-semantic-boundaries.md) | implementation | accepted resolved-surface and bidirectional typed-elaboration boundaries | Extend stage interfaces and structured diagnostics only with an authorized semantic increment. |
| [Evaluator architecture](decisions/AD-0008-explicit-evaluator-machine.md) | implementation | accepted first-order machine boundary and current dynamics | Test future effect and continuation pressure without changing current pure semantics implicitly. |
| [Specification methodology](decisions/AD-0004-small-step-semantic-method.md) | implementation | accepted small-step primary method and current dynamics | Keep future operational behavior derived from one normative small-step account. |

Planning detail must decrease with distance. Effects, providers, processes, propositions, laws, proofs, and optimizer search are future design pressure, not planned language inventory. Immediate work should preserve relevant options without implementing those features.
