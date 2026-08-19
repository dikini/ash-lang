# Development trajectory

This is a dependency and maturity view, not a sequential roadmap. Maturity uses: `idea → speculative → outlined → designed → specified → implementation`.

No implementation task is active yet. The next work is to gather enough evidence for the decisions that can authorize implementation.

| Work | Maturity | Dependencies | Next evidence |
|---|---|---|---|
| [Core representation](design/DN-0002-core-representation.md) | outlined | none | Compare concrete representations with representative compiler operations. |
| [Parser architecture](design/DN-0003-parser-architecture.md) | outlined | initial syntax needs, kept separate from architecture | Research candidates and test grammar growth, diagnostics, spans, and recovery. |
| [Implementation environment](design/DN-0004-implementation-environment.md) | outlined | constraints from Core and parser experiments | Compare bounded probes, then record an architectural decision. |
| Specification methodology | outlined | needs of the first language nucleus and expected future runtime state | Compare semantic notations and accept one method before substantial semantic specification. |
| Small pure functional nucleus | speculative | implementation environment, sufficient Core and parser decisions | Propose complete increments; each requires implementation, tests, and a specification update. |

Planning detail must decrease with distance. Effects, providers, processes, propositions, laws, proofs, and optimizer search are future design pressure, not planned language inventory. Immediate work should preserve relevant options without implementing those features.
