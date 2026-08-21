# DN-0002: Core Representation

- ID: `DN-0002`
- Status: exploring
- Related: [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md), [DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md)

> This design note is informative. It does not accept a Core representation or define Ash semantics.

## Intent

Find a typed Core representation that fits a small pure functional Ash now and can support later effects and representation-changing compiler work without forcing those features into the first language.

The current semantic direction is Freer-like: pure results and effect operations with continuations. This direction does not commit the implementation to a literal textbook Freer Monad encoding.

## Accepted Mini-Ash boundary

[AD-0007](../decisions/AD-0007-typed-core-dialects.md) accepts named closed
typed Core dialects assembled from feature-local families, independent
validation, a pure value/computation boundary with no inhabitable effect
operations, and an explicit future operation-family seam. It leaves the exact
Rust composition mechanism, ownership, storage, provenance tables, effects,
continuations, and CPS questions open. This note continues to explore those
broader representation questions without overriding the accepted boundary.

## Constraints

- Core is typed and remains checkable after transformations.
- Pure Ash fits without depending on effects.
- Adding an effect family should not require extending one monolithic recursive expression type for every family.
- Continuations are explicit compiler data, not host-language closures.
- Traversal and rewriting remain reliable.
- Core has a clear relationship with a separate CPS IR.
- Current work must not assume Core-to-CPS lowering is permanently irreversible.

Current work need not implement effects, handlers, CPS reconstruction, opaque CPS regions, or optimizer search. It must avoid closing off their relevant representation requirements without evidence.

## Candidate directions

- a direct first-order encoding of the accepted Freer-like operation seam;
- different concrete encodings of the accepted value/computation split;
- an explicit bind or step representation within a future computation dialect;
- an explicit continuation graph when accepted effects or CPS require one.

These are candidates for concrete representation experiments, not a complete
set. They do not reopen AD-0007's accepted dialect, typing, validation, or
value/computation boundaries.

## Experiments

Use progressively richer slices of the
[Mini-Ash evaluation corpus](DN-0015-mini-ash-phase.md#corpus-strata). Begin with
the [first monomorphic stratum](DN-0016-first-mini-ash-corpus.md) and its
definition, capture, application, validation, and source-provenance pressure.
Treat effects, continuations, and CPS as downstream pressure; use a theoretical
account or a disposable probe only when the pure corpus cannot distinguish a
candidate.

Compare small concrete representations by implementing or sketching the operations that will stress them:

- pure evaluation and beta reduction;
- algebraic data and pattern matching;
- an effect operation and handler as architectural probes, not current Ash features;
- Core to CPS and CPS to Core;
- an opaque typed CPS fragment;
- typed traversal and rewriting followed by validation.

Record for each Core candidate:

- representation size, invariants, traversal mechanics, failure modes, and which
  facts each transformation must establish;
- source-provenance and diagnostic information preserved by each representation;

## Open questions

- Which concrete encoding keeps continuations inspectable without making ordinary pure terms awkward?
- Where should typing evidence live, and what must transformations revalidate?
- What interface would let Core contain an opaque CPS region without pretending Core can inspect it?
- Which operations become simpler in Core, and which in CPS?
