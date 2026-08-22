# Development trajectory

This is a dependency and maturity view, not a sequential roadmap. Maturity uses: `idea → speculative → outlined → designed → specified → implementation`.

The first retained Mini-Ash increment is implemented. The
[current specification](../spec/README.md) defines its monomorphic,
pure-functional language behavior, and the
[`ash` tool guide](tools/ash.md) documents the single-file executable.

The first Mini-Ash corpus consistency, component-comparison, and convergence
gates are complete. Current decision readiness is tracked in the
[DN-0016 experiment program](design/DN-0016-first-mini-ash-corpus.md#tracked-experiment-program)
and its [convergence record](design/mini-ash/first-stratum/comparisons/component-convergence.md).

[DN-0020](design/DN-0020-ash-dialect-milestones.md) outlines two retained
implementation milestones. Mini-Ash closes with rank-1 polymorphism and a
simplification analysis. Modular Ash then adds passive static modules and
interfaces, uses that boundary to compare core language forms with library
definitions, and closes with its own simplification analysis. The two remain
independently selectable and testable dialects.

| Work | Maturity | Dependencies | Next evidence |
| --- | --- | --- | --- |
| [Mini-Ash phase](design/DN-0015-mini-ash-phase.md) | implementation | current [Mini-Ash specification](../spec/README.md), reviewed [first corpus stratum](design/DN-0016-first-mini-ash-corpus.md), accepted component decisions, and retained [data-and-pattern integration evidence](design/mini-ash/data-and-patterns/evidence.md) | Design and propose rank-1 polymorphism as Mini-Ash's final semantic increment. |
| [Modular Ash milestone](design/DN-0020-ash-dialect-milestones.md#start-modular-ash-at-the-static-boundary) | outlined | completed Mini-Ash dialect and its simplification analysis | Design passive static modules and interfaces, then use them to test core-versus-library boundaries. |
| [Core representation](decisions/AD-0007-typed-core-dialects.md) | implementation | accepted typed-dialect and pure-computation boundaries | Exercise the retained closed pure dialect and operation-family seam against the next proposed feature pressure. |
| [Parser architecture](decisions/AD-0005-parser-architecture.md) | implementation | accepted event-producing recursive-descent boundary and current grammar | Measure locality, recovery, and source coverage when a later proposal adds syntax. |
| [Front-end semantic boundaries](decisions/AD-0006-front-end-semantic-boundaries.md) | implementation | accepted resolved-surface and bidirectional typed-elaboration boundaries | Extend stage interfaces and structured diagnostics only with an authorized semantic increment. |
| [Evaluator architecture](decisions/AD-0008-explicit-evaluator-machine.md) | implementation | accepted first-order machine boundary and current dynamics | Test future effect and continuation pressure without changing current pure semantics implicitly. |
| [Specification methodology](decisions/AD-0004-small-step-semantic-method.md) | implementation | accepted small-step primary method and current dynamics | Keep future operational behavior derived from one normative small-step account. |

Planning detail must decrease with distance. Effects, providers, processes, propositions, laws, proofs, and optimizer search are future design pressure, not planned language inventory. Immediate work should preserve relevant options without implementing those features.
