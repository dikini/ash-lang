# Lexical region proof boundary

This standalone root belongs to [TASK-0055](../../tasks/TASK-0055-lexical-regions.md)
and its [execution plan](../../tasks/plans/lexical-regions.md). The intended
contract remains [DN-0054](../DN-0054-base-lexical-region-memory-contracts.md)
and the forthcoming R2 proposal. It defines no current Ash semantics.

The registration is initially empty: there are no integrated region proofs or
reusable region artifacts. An explicitly labelled empty seed pins this baseline
and the existing Lean 4.33.1 compiler/libraries. Reviewed model sources enter via
the [existing integration runner](../../project/proof-tooling.md), including
source, review, dependency, report, axiom, resource and final-coherence checks.
Neither an empty seed nor local diagnostic success establishes preservation.

Keep the model finite and sequential with minimal imports. Model ordinary
allocator contracts abstractly; no native-memory theorem, general permission
algebra or rewrite of the separate one-shot proof corpus is required. Product
R3 waits for the accepted R2 contract and matching bounded proof.
