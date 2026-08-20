# Development trajectory

This is a dependency and maturity view, not a sequential roadmap. Maturity uses: `idea → speculative → outlined → designed → specified → implementation`.

TASK-0005 is aligning current planning with the Mini-Ash phase. Other work still
needs enough evidence to authorize implementation.

| Work | Maturity | Dependencies | Next evidence |
| --- | --- | --- | --- |
| [Mini-Ash phase](design/DN-0015-mini-ash-phase.md) | outlined | implementation environment, growing evaluation corpus, accepted specification method, and sufficient component decisions | Develop the first corpus stratum and use it to compare component boundaries without accepting syntax or semantics. |
| [Core representation](design/DN-0002-core-representation.md) | outlined | growing Mini-Ash corpus and downstream representation pressure | Compare typed representations against progressively richer corpus cases; accept an architecture only after invariants, diagnostics, and extension behavior converge. |
| [Parser architecture](design/DN-0003-parser-architecture.md) | outlined | provisional Mini-Ash grammar and diagnostic cases, kept separate from language authority | Compare composable parser organizations on grammar growth, precedence, recovery, spans, and user-facing diagnostics. |
| [Specification methodology](project/specification.md) | outlined | Mini-Ash operational cases and downstream runtime-state pressure | Accept small-step operational semantics as the primary method before substantial normative semantics. |

Planning detail must decrease with distance. Effects, providers, processes, propositions, laws, proofs, and optimizer search are future design pressure, not planned language inventory. Immediate work should preserve relevant options without implementing those features.
