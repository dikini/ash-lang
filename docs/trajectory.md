# Development trajectory

This is a dependency and maturity view, not a sequential roadmap. Maturity uses: `idea → speculative → outlined → designed → specified → implementation`.

No implementation task is active. Other work still needs enough evidence to
authorize implementation.

The first Mini-Ash corpus consistency, component-comparison, and convergence
gates are complete. Current decision readiness is tracked in the
[DN-0016 experiment program](design/DN-0016-first-mini-ash-corpus.md#tracked-experiment-program)
and its [convergence record](design/mini-ash/first-stratum/comparisons/component-convergence.md).

| Work | Maturity | Dependencies | Next evidence |
| --- | --- | --- | --- |
| [Mini-Ash phase](design/DN-0015-mini-ash-phase.md) | designed | implementation environment, reviewed [first corpus stratum](design/DN-0016-first-mini-ash-corpus.md), [accepted specification method](decisions/AD-0004-small-step-semantic-method.md), and accepted component decisions | Draft the first semantic proposal from a deliberately bounded subset of the provisional corpus. |
| [Core representation](decisions/AD-0007-typed-core-dialects.md) | specified | accepted typed-dialect and pure-computation boundaries plus downstream representation pressure | Use the first implementation task to select the smallest Rust composition and storage mechanisms that satisfy the decision's verification. |
| [Parser architecture](decisions/AD-0005-parser-architecture.md) | specified | accepted event-producing recursive-descent boundary, kept separate from language authority | Use proposed syntax to select event and tree types without deciding unresolved layout or trivia policy incidentally. |
| [Front-end semantic boundaries](decisions/AD-0006-front-end-semantic-boundaries.md) | specified | accepted resolved-surface and bidirectional typed-elaboration boundaries | Define implementation interfaces only after the first semantic proposal fixes the required rules and diagnostics. |
| [Evaluator architecture](decisions/AD-0008-explicit-evaluator-machine.md) | specified | accepted first-order machine boundary and completed host-stack probe | Determine reviewable frame-transition composition during the first implementation task without adding effect continuations. |
| [Specification methodology](decisions/AD-0004-small-step-semantic-method.md) | specified | accepted small-step primary method | Apply the decision when the first semantic proposal authorizes normative dynamic semantics. |

Planning detail must decrease with distance. Effects, providers, processes, propositions, laws, proofs, and optimizer search are future design pressure, not planned language inventory. Immediate work should preserve relevant options without implementing those features.
