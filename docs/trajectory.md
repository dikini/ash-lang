# Development trajectory

This is a dependency and maturity view, not a sequential roadmap. Maturity uses: `idea → speculative → outlined → designed → specified → implementation`.

[TASK-0006](tasks/TASK-0006-implement-first-mini-ash-nucleus.md) is the active
implementation task. CP-0001 authorizes only its first monomorphic,
pure-functional increment.

The first Mini-Ash corpus consistency, component-comparison, and convergence
gates are complete. Current decision readiness is tracked in the
[DN-0016 experiment program](design/DN-0016-first-mini-ash-corpus.md#tracked-experiment-program)
and its [convergence record](design/mini-ash/first-stratum/comparisons/component-convergence.md).

| Work | Maturity | Dependencies | Next evidence |
| --- | --- | --- | --- |
| [Mini-Ash phase](design/DN-0015-mini-ash-phase.md) | specified | accepted [CP-0001](proposals/CP-0001-first-mini-ash-nucleus.md), reviewed [first corpus stratum](design/DN-0016-first-mini-ash-corpus.md), and accepted component decisions | Execute [TASK-0006](tasks/TASK-0006-implement-first-mini-ash-nucleus.md) and retain implementation, tests, specification, and executable documentation together. |
| [Core representation](decisions/AD-0007-typed-core-dialects.md) | implementation | accepted typed-dialect and pure-computation boundaries plus CP-0001 | TASK-0006 selects and verifies the smallest Rust composition and storage mechanisms that satisfy the decision. |
| [Parser architecture](decisions/AD-0005-parser-architecture.md) | implementation | accepted event-producing recursive-descent boundary and CP-0001 grammar | TASK-0006 implements event and tree types with the accepted newline and source-coverage behavior. |
| [Front-end semantic boundaries](decisions/AD-0006-front-end-semantic-boundaries.md) | implementation | accepted resolved-surface and bidirectional typed-elaboration boundaries plus CP-0001 rules | TASK-0006 implements the stage interfaces and structured diagnostic outcomes. |
| [Evaluator architecture](decisions/AD-0008-explicit-evaluator-machine.md) | implementation | accepted first-order machine boundary and CP-0001 dynamics | TASK-0006 selects reviewable frame-transition composition without adding effect continuations. |
| [Specification methodology](decisions/AD-0004-small-step-semantic-method.md) | implementation | accepted small-step primary method and CP-0001 dynamics | TASK-0006 writes the normative rules and checks the retained evaluator against them. |

Planning detail must decrease with distance. Effects, providers, processes, propositions, laws, proofs, and optimizer search are future design pressure, not planned language inventory. Immediate work should preserve relevant options without implementing those features.
