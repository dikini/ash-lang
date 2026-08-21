# DN-0019: Primitive Feature Composition

- ID: `DN-0019`
- Status: exploring
- Related: [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md), [DN-0016: First Mini-Ash Corpus Stratum](DN-0016-first-mini-ash-corpus.md)

> This design note is informative. It does not define current Ash, accept Float
> semantics, or accept a feature-composition architecture.

## Question

Which integration pressure arises when one primitive scalar crosses the real
Ash pipeline, and which candidate mechanisms reduce that pressure without
hiding typing, provenance, validation, or evaluation behavior?

## Retained experiment

The runnable prototype remains on branch
`experiment/primitive-feature-composition` at unsigned commit
`cb4c1dc2fafa413a2492752ab3a6fdfeb5f27e74`. Its detailed report is
`docs/design/primitive-feature-composition/evidence.md` on that branch. The
prototype adds provisional Float syntax and behavior only as experimental
evidence; no `spec/` file changes.

The prototype compared a direct extension with feature-owned implementations
and central subsystem assemblies. It also exercised compile-time availability
and run-time admission to expose integration boundaries. Separately distributed
extensions were not a requirement, and feature gating is not a current
Mini-Ash objective.

## Distilled findings

### Behavior localized more readily than representation

Float typing, constant folding, and evaluation behavior fit in seven
feature-owned files containing 216 lines. Six subsystem assemblies contained
another 256 lines. Even after that packaging, the closed cross-stage
representations still required 35 conditional sites in 15 files outside the
feature package and composition directory.

This finding applies when a proposed form survives across several compiler
stages. It does not show that those stages should collapse, that representations
should become dynamically erased, or that every feature has scalar shape.

### Mechanical maintenance was mostly discoverable

Five contract-mutation probes found their required updates through Rust compiler
errors or one stable text search. Trait contract failures produced the clearest
errors. Macro-schema failures located every invocation but gave weaker messages.
Changing evaluator context remained semantically difficult even when its
mechanical call sites were easy to find.

Compiler-or-one-search discovery is therefore a useful maintenance criterion.
It does not make a wide change local or turn a changed semantic invariant into
registration work.

### Admission and implementation composition are separate questions

One tool-boundary selection constructed an immutable dialect. Source admission
used one general gate, Core independently validated membership, and evaluation
repeated no admission check. This separation worked, but it primarily supplied
experimental pressure. It does not justify user-facing feature flags or a
compiler feature product line at the current stage.

### Simplification precedes composition machinery

Before adding a representation or registry, later work should ask whether the
surface form can elaborate through existing semantics or eventually reside in a
module. Operators may become notation for ordinary typed functions; equality,
ordering, and other capabilities may become library interfaces even when a
compiler intrinsic implements selected operations.

The experiment did not test notation, modules, interfaces, higher-kinded types,
universals, effects, handlers, resources, or continuations. Those features must
not inherit Float mechanisms without separate evidence.

## Use in later work

When a Mini-Ash increment adds a form across compiler stages, reconstruct its
semantic context and consider this evidence if the representation pressure
transfers. Distinguish:

- intrinsic feature behavior;
- cross-feature interactions;
- mechanical stage joins;
- provenance and diagnostic obligations;
- opportunities to lower into existing forms or future libraries.

A later candidate should compare its changed production files, feature-specific
dispatch outside feature ownership, conditional compilation, compiler feedback,
one-search discovery, unrelated test changes, build cost, and representation
cost against the retained Float evidence.

### Recursive-definition transfer

The retained recursive-function implementation provides the first
structurally different comparison. Its
[evidence report](mini-ash/recursive-definitions/evidence.md) finds that the
new Core group payload and runtime template contract are mechanically
discoverable, while simultaneous scope necessarily crosses syntax, resolution,
typing, Core, and evaluation boundaries. Reusing ordinary function nodes and
one recursive group avoided thunks, recursive types, and continuation
machinery. The result strengthens the rule that later work should simplify and
lower first, then preserve explicit exhaustive joins where they enforce a
semantic invariant.

The recursion evidence also identifies transferable preparation for the data
and ADT cluster: ordered declaration forms, allocate-all-then-check scope, and
variable-arity Core traversal. It does not claim that function templates solve
cyclic constructor allocation or pattern typing.

## Open questions

- Can generated closed stage assemblies remove most representation joins while
  preserving useful Rust errors and inspectable code?
- Which current primitive operations can later elaborate to ordinary library
  functions?
- How much of the finding transfers to recursive definitions, ADTs and
  patterns, polymorphism, or effect operations?
- Which prototype mechanisms, if any, merit an architectural decision after a
  second structurally different experiment?
