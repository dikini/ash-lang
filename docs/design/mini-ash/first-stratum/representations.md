# First-stratum representation pressure

> These representation sketches are informative evidence governed by
> [DN-0016](../../DN-0016-first-mini-ash-corpus.md). They define comparison
> obligations and do not accept a compiler pipeline, Core encoding, or runtime
> representation.

The corpus needs enough representation detail to expose scope, typing,
elaboration, transformation, evaluation, and diagnostic costs. It does not
assume that every candidate retains every stage.

## Candidate boundaries

The comparison begins with these conceptual contracts:

```text
source
  → spanned surface form
  → resolved form
  → typed structured form
  → validated evaluator input
  → value and trace
```

Each conversion states its input assumptions, output invariants, structured
failures, and provenance mapping. A boundary is justified only if the facts it
establishes simplify a consumer enough to warrant another representation.

### Spanned surface form

The surface form preserves tokens or equivalent source coverage, block and
definition grouping, equational external interfaces, inline operational
interfaces, clause and explicit-match structure, and parser recovery nodes. It
does not claim that names resolve or types agree. Grouping parentheses may
disappear as semantic nodes after parsing, but their delimiter spans remain in
source provenance.

### Resolved form

Every binder has a stable identity distinct from its spelling, every occurrence
names that identity, each global interface is paired with exactly one body, and
duplicate or unknown names have already failed. V-003 must distinguish its two
`value` binders without changing their source spelling.

### Typed structured form

Every expression and binder exposes its monotype. Equational and operational
functions use the same semantic function form after elaboration, while separate
provenance records the original presentation and source locations. Expected
types inserted during checking remain explainable without becoming surface
syntax.

X-003 requires one semantic function type to preserve two different shapes:
successive `Function` nodes for a curried equation and one `Function` whose
domain is a product for grouped operational parameters. A representation that
stores an independent arity alongside the type risks making those facts
disagree.

X-001 requires equation clauses and an explicit match to enter one typed pattern
and coverage subsystem. The equational form synthesizes the scrutinee and match
body during elaboration; the inline operational form already contains them.
After that boundary, both may use the same structured match Core and the same
later decision lowering while retaining different source origins.

### Evaluator input and values

The evaluator consumes a successfully validated typed form. A lexical function
value contains inspectable Ash data equivalent to a code identity plus an
environment of captured Ash values. A retained design must not use a Rust
closure as the only representation of its code, environment, or continuation.

## Typed validation obligations

A validator must independently check at least:

- binder identities are unique and every occurrence is in scope;
- expression annotations agree with primitive, binding, function, and
  application structure;
- global bodies agree with their one explicit interface;
- an application argument agrees with its function domain, and the node result
  agrees with the codomain;
- both V-002 definitions elaborate to valid callable semantic structure without
  losing their presentation provenance;
- sequential global elaboration binds every checked definition over the
  remaining program without placing the name in its own initializer's scope;
- X-003's generated product destructuring agrees with the single product domain
  and its two component binder types;
- every source and generated node has a valid provenance record;
- nodes forbidden by a named representation contract cannot appear.

Validation returns structured failures for the `I-NNN` cases in
[diagnostics.md](diagnostics.md). Construction APIs may prevent some malformed
states, but deserialization and transformations still require a complete
validation boundary.

## Core encoding candidates

Concrete Rust probes should compare at least three ways to avoid one closed
recursive enum controlling every future feature:

1. Feature fragments composed through a recursive fixed point and typed sum.
2. Arena-owned nodes with stable identities and feature-local node families.
3. A value/computation separation with a Freer-like operation-family seam.

The third candidate does not add `Impure`, handlers, or effect operations to the
first stratum. It must show how pure functions, bindings, and applications
remain direct while a future operation family could be added without extending
every unrelated consumer. The other candidates must answer the same extension
question rather than lose because their type names differ from a textbook Freer
encoding.

For each encoding, record:

- complete Rust type sketches and representation size for the corpus;
- which invariants the host types express and which need validation;
- ownership, allocation, traversal, and rewriting mechanics;
- how a feature-specific visitor or transform composes;
- whether exhaustive reasoning survives feature composition;
- how source provenance reaches typed nodes and diagnostics;
- which changes V-001, V-004, and V-005 require in unrelated components;
- the seam, invariant, or redesign risk for future operations and CPS.

Final-tagless or host-function encodings may serve as baselines, but they must
account for inspection, serialization, validation, transformation, and source
provenance. Concise evaluation alone is not enough.

## Typechecker rule organization

The representation must let one reviewable rule boundary own each decision in
[typing.md](typing.md). Storage mechanisms such as arenas, substitutions, or a
future union-find do not decide equality, function exposure, annotation policy,
or diagnostic wording incidentally.

Rule outcomes preserve facts and failures, for example:

```text
FunctionExposure =
    Function { domain, codomain }
    | NotFunction { found }

TypeComparison =
    Equal
    | Mismatch { expected, found, reason }
```

These shapes are illustrative. A candidate should demonstrate that changing a
later generalization or function-grouping policy affects its owning rule rather
than every caller.

## Evaluator candidates

Compare a direct evaluator over typed structured data with an explicit
first-order machine. Both use inspectable lexical function values and must agree
with [dynamics.md](dynamics.md).

The direct evaluator is the smaller baseline. The machine candidate must justify
its control, environment, and frame data through current evaluation-order,
validation, tracing, or host-stack evidence. Later continuations and effects are
pressure, not permission to add unreachable machinery now.

## Transformation probe

Each Core candidate implements one typed identity traversal and one local
reduction or simplification. It validates the result and evaluates before and
after the transform. V-002 tests presentation-independent Core, V-004 tests
scope and capture, and V-008 tests nested applications and evaluation
preservation.

The probe is disposable. Its evidence records changed modules, validation work,
provenance behavior, and failure modes; its code does not become product Core
by remaining in the repository.
