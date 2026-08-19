# DN-0002: Core Representation

- ID: `DN-0002`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md)

> This design note is informative. It does not accept a Core representation or define Ash semantics.

## Intent

Find a typed Core representation that fits a small pure functional Ash now and can support later effects and representation-changing compiler work without forcing those features into the first language.

The current semantic direction is Freer-like: pure results and effect operations with continuations. This direction does not commit the implementation to a literal textbook Freer Monad encoding.

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

- a direct first-order Freer-like representation;
- a value/computation split;
- an explicit bind or step representation;
- an explicit continuation graph.

These are candidates for experiments, not a complete set and not accepted choices.

## Experiments

Compare small concrete representations by implementing or sketching the operations that will stress them:

- pure evaluation and beta reduction;
- algebraic data and pattern matching;
- an effect operation and handler as architectural probes, not current Ash features;
- Core to CPS and CPS to Core;
- an opaque typed CPS fragment;
- typed traversal and rewriting followed by validation.

Record representation size, invariants, traversal mechanics, failure modes, and which facts each transformation must establish.

## Open questions

- Which concrete encoding keeps continuations inspectable without making ordinary pure terms awkward?
- Where should typing evidence live, and what must transformations revalidate?
- What interface would let Core contain an opaque CPS region without pretending Core can inspect it?
- Which operations become simpler in Core, and which in CPS?
