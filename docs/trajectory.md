# Development trajectory

This is a dependency and maturity view, not a sequential roadmap. Maturity uses: `idea → speculative → outlined → designed → specified → implementation`.

No implementation task is active. Other work still needs enough evidence to
authorize implementation.

| Work | Maturity | Dependencies | Next evidence |
| --- | --- | --- | --- |
| [Core representation](design/DN-0002-core-representation.md) | outlined | none | Compare concrete representations with representative compiler operations. |
| [Parser architecture](design/DN-0003-parser-architecture.md) | outlined | initial syntax needs, kept separate from architecture | Research candidates and test grammar growth, diagnostics, spans, and recovery. |
| [Specification methodology](project/specification.md) | outlined | needs of the first language nucleus and expected future runtime state | Compare semantic notations and accept one method before substantial semantic specification. |
| [Small pure functional nucleus](design/DN-0001-reboot-foundations.md#7-initial-language-trajectory) | speculative | implementation environment, sufficient Core and parser decisions | Propose complete increments; each requires implementation, tests, and a specification update. |

Planning detail must decrease with distance. Effects, providers, processes, propositions, laws, proofs, and optimizer search are future design pressure, not planned language inventory. Immediate work should preserve relevant options without implementing those features.
