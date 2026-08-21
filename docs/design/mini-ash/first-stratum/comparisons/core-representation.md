# First-stratum Core-representation comparison

> This comparison is informative evidence governed by
> [DN-0016](../../../DN-0016-first-mini-ash-corpus.md). It does not accept a
> Core architecture or define current Ash semantics.

## Question

Which representation shape keeps the first pure Core typed, inspectable,
validatable, and transformable while leaving a concrete seam for later effect
operations and explicit continuations?

## Scope and method

The comparison combines a disposable Rust probe with written pressure from the
whole first-stratum corpus. The probe represented the lexical capture in
`V-004`, evaluated before and after a typed simplification, preserved causal
origins for generated nodes, and rejected `I-001` through `I-004`. A separate
operation-family probe checked that a future request could carry explicit
first-order continuation data without putting an effect operation in the pure
instance.

The written comparison covers the remaining cases where the consequence is
already visible from the type shape: primitive fragments in `V-001`, `V-006`,
and `V-007`; presentation-independent functions in `V-002` and `V-008`;
higher-order application in `V-005`; structured match in `X-001`; and the
curried-versus-product distinction in `X-003`. It does not prototype effects,
handlers, CPS, or a product runtime.

The probe compared:

1. feature-local node structures joined by a typed sum and recursive term;
2. arena-owned nodes with stable node identities and feature-local payloads;
3. a value/computation boundary parameterized by an operation family, with an
   empty operation family for pure Core.

## Representation shapes

All candidates attached the same binder identity, monotype, and origin data to
semantic nodes. The reduced probe used `Int`, `Bool`, and an undifferentiated
function type because its purpose was representation mechanics, not the
first-stratum typechecker. A retained Core must use the full structural types
required by [typing.md](../typing.md).

### Recursive typed sum

The probe gave each feature its own payload type and joined those payloads at a
dialect boundary:

```rust
enum Sum<L, R> {
    Left(L),
    Right(R),
}

struct Term {
    ty: Type,
    origin: Origin,
    layer: Box<Layer>,
}

type Layer = Sum<
    Literal,
    Sum<Variable, Sum<Add, Sum<Let, Sum<Lambda, Apply>>>>,
>;

struct Literal(i64);
struct Variable(BinderId);
struct Add(Term, Term);
struct Let {
    binder: BinderId,
    initializer: Term,
    body: Term,
}
struct Lambda {
    binder: BinderId,
    body: Term,
}
struct Apply(Term, Term);
```

This shape gives each feature a local payload and keeps the selected dialect
closed enough for exhaustive validation. The concrete nested sum made
construction and matching noisy. A generic fold or generated injection layer
could move that plumbing out of consumers, but the probe did not establish
that such machinery is worth its cost for the first dialect.

### Arena storage

The arena probe replaced recursive ownership with stable identities:

```rust
struct NodeId(u32);

struct ArenaTerm {
    nodes: Vec<Node>,
    root: NodeId,
}

struct Node {
    ty: Type,
    origin: Origin,
    kind: NodeKind,
}

enum NodeKind {
    Int(i64),
    Variable(BinderId),
    Add(NodeId, NodeId),
    Let {
        binder: BinderId,
        initializer: NodeId,
        body: NodeId,
    },
    Lambda {
        binder: BinderId,
        body: NodeId,
    },
    Apply(NodeId, NodeId),
}
```

The arena made identity, shared storage, and iterative ownership direct. It did
not by itself compose features. Static dispatch still required one closed
`NodeKind`; replacing that tag with a registry and erased payloads would weaken
exhaustive matching and complicate validation, transformation, and
serialization. Arena ownership is therefore a storage decision that can sit
beneath either semantic organization, not a competing answer to semantic
composition.

### Operation-parameterized computation

The Freer-like probe separated pure structure from future requests and made a
pure dialect uninhabited on the operation side:

```rust
use std::marker::PhantomData;

enum Computation<O> {
    Pure(Annotated<O>),
    Impure(Request<O>),
}

struct Annotated<O> {
    ty: Type,
    origin: Origin,
    form: PureForm<O>,
}

enum PureForm<O> {
    Int(i64),
    Variable(BinderId),
    Add(Box<Computation<O>>, Box<Computation<O>>),
    Let {
        binder: BinderId,
        initializer: Box<Computation<O>>,
        body: Box<Computation<O>>,
    },
    Lambda {
        binder: BinderId,
        body: Box<Computation<O>>,
    },
    Apply(Box<Computation<O>>, Box<Computation<O>>),
}

struct Request<O> {
    operation: O,
    continuation: Continuation<O>,
}

enum Continuation<O> {
    Return(PhantomData<O>),
    Bind {
        binder: BinderId,
        next: Box<Computation<O>>,
    },
}

enum NoOperation {}
```

`Computation<NoOperation>` cannot contain a request through safe construction.
A future operation family can instantiate the same boundary, and the probe's
request contained a binder and next computation rather than a Rust closure.
This result supports an operation seam. It does not make `PureForm` itself
feature-composable: adding a pure language construct to that enum still changes
every exhaustive consumer.

## Probe evidence

All three candidates used inspectable closure values containing a binder, code
identity or body, and an Ash environment. None represented lexical capture or
continuation state with a Rust closure.

The probe produced these host-specific measurements for the same ten-node
`V-004`-shaped term:

| Candidate | Root bytes | Recorded nodes | Recursive or arena allocations |
| --- | ---: | ---: | ---: |
| Recursive typed sum | 24 | 10 | 10 |
| Arena storage | 32 | 10 | 1 backing vector |
| Operation-parameterized computation | 40 | 10 | 9 child boxes |

These measurements expose ownership shape; they are not performance results.
Rust layout, full structural types, provenance tables, match nodes, and
allocation strategy can change them.

The typed simplification removed `0 + expression`, assigned the replacement a
generated origin causally linked to the removed node, revalidated the result,
and preserved evaluation. Recursive candidates rebuilt the path to a changed
node. The arena appended changed nodes and reused stable identities for
unchanged subtrees. All candidates needed an explicit validator even where
constructors prevented common mistakes, because transformations and future
deserialization can still produce malformed structure.

## Corpus and change-locality comparison

| Pressure | Recursive typed sum | Arena storage | Operation-parameterized computation |
| --- | --- | --- | --- |
| Add a primitive feature from `V-001`, `V-006`, or `V-007` | Add one payload and include it in the dialect sum; generic consumers need a new feature case | Add payload storage and a dispatch case, unless using type erasure | Add a `PureForm` case; unrelated exhaustive consumers change |
| Preserve the two `V-002` presentations | Common semantic function payload can retain distinct origins | Common function node can retain distinct origins | Common pure function form can retain distinct origins |
| Capture in `V-004` | Inspectable closure environment worked | Inspectable closure environment worked; IDs keep code references small | Inspectable closure environment worked without using the operation seam |
| Higher-order and nested application in `V-005` and `V-008` | Recursive application and function payloads compose directly | Stable IDs avoid recursive ownership but require arena access | Pure applications remain direct rather than encoded as operations |
| Add structured match for `X-001` | Add a match fragment and extend the selected dialect | Add match payload and dispatch | Add a pure form unless combined with feature fragments |
| Preserve the types in `X-003` | Structural function and product types belong in common annotations | Same; arena identity does not decide grouping | Same; the operation family does not decide grouping |
| Add a future effect family | Requires an operation fragment or a separate computation layer | Storage can hold it, but does not define its typed interface | Change the operation-family parameter; pure feature consumers need not change |
| Introduce future CPS regions | Needs an explicit fragment and validation contract | Stable IDs can reference regions but do not define their contract | The computation boundary gives a natural seam, but no Core/CPS relation was tested |

No candidate makes every extension invisible. Exhaustive reasoning requires a
closed selected dialect somewhere. The useful property is that adding one
effect family does not require changing the representation of ordinary pure
features, while a dialect boundary still states exactly which features a Core
dialect permits.

## Conclusion

The evidence favors a layered hypothesis rather than one winning candidate:

- compose typed semantic features at an explicit dialect boundary;
- distinguish values and computations, with an empty operation family for the
  first pure Core and a parameterized request seam for later effects;
- keep future continuation data first-order and inspectable;
- choose recursive or arena ownership separately, based on transformation,
  sharing, stable-identity, and diagnostic evidence.

The first retained implementation should not add `Impure`, handlers, effect
operations, or CPS nodes merely to demonstrate the seam. It may use a smaller
dialect-local encoding if that encoding preserves the boundary and can be
lowered or replaced without changing language semantics.

This conclusion does not yet select a concrete Rust library pattern. In
particular, it does not establish that handwritten nested sums, generated
injections, trait objects, or arena IDs should appear in product Core.

## Accepted outcome

[AD-0007](../../../../decisions/AD-0007-typed-core-dialects.md) accepts these
properties:

- every retained Core dialect declares a closed set of permitted typed feature
  families;
- pure Mini-Ash does not depend on an inhabited effect-operation family;
- a future operation-family boundary does not require effect variants in every
  pure feature;
- closures and future continuations are inspectable Ash compiler data rather
  than host closures;
- Core validation checks types, binder scope, dialect membership, and
  provenance after construction and transformation;
- ownership and storage remain replaceable implementation choices unless
  evidence makes stable node identity part of a stage contract.

The decision does not choose effect semantics, continuation multiplicity,
handler behavior, CPS reconstruction, concrete arena allocation, or the first
user-visible semantic increment.

## Remaining questions

- Does the resolver, typechecker, and elaborator benefit enough from stable node
  identities to justify arena storage before transformation work begins?
- What is the smallest Rust mechanism that composes feature-local rules while
  retaining exhaustive validation for one selected dialect?
- Should source provenance live on every semantic node or in a side table keyed
  by stable identity?
- Which typed evidence remains on nodes, and which facts should a validator
  recompute after transformations?
- Where should a later opaque CPS region meet the computation boundary?

The next component comparisons can answer the first four questions without
adding future effects. The last remains downstream pressure.

## Retention boundary

The Rust probe lived under ignored build output and is disposable. Its tests,
format check, and Clippy check passed. This document retains the representation
shapes, measurements, observed change locality, and unresolved questions; the
probe is not product Core or language authority.
