# AD-0006: Front-End Semantic Boundaries

- ID: `AD-0006`
- Status: accepted
- Related: [AD-0005: Parser Architecture](AD-0005-parser-architecture.md), [AD-0007: Typed Core Dialects](AD-0007-typed-core-dialects.md), [DN-0008: Typed Core and Elaboration](../design/DN-0008-typed-core-and-elaboration.md), [DN-0016: First Mini-Ash Corpus Stratum](../design/DN-0016-first-mini-ash-corpus.md), [first-stratum static-semantics comparison](../design/mini-ash/first-stratum/comparisons/static-semantics-organization.md)

## Decision

Ash resolves names before typechecking and typed elaboration. Resolution emits
a spanned surface form in which every definition and occurrence has a stable
binder identity distinct from its spelling.

One bidirectional typed elaborator consumes the resolved form and emits typed
structured Core. Separate synthesis and checking entry points propagate
expected types where the language requires them. Presentation-specific paths
for equations, operational functions, and explicit matches call shared
function, pattern, coverage, type, and Core-construction rules.

Each semantic question has one reviewable rule interface with structured
outcomes. Type equality, function exposure, pattern typing, coverage, and later
constraint resolution remain separate rule responsibilities even when an early
implementation uses small functions in one module.

Resolution, checking, and elaboration failures are structured data containing
their semantic reason and causal source relationships. Diagnostic rendering
does not parse error strings or own static policy.

The first front end does not retain a separate fully typed surface tree or a
general constraint store unless a later corpus shows a consumer or inference
problem that justifies that boundary.

## Context

The first corpus compared one fused recursive operation, a resolved surface
followed by typed elaboration, a fully typed surface followed by Core lowering,
and a constraint-generation pipeline.

Fusing all work could process valid monomorphic cases, but scope, expected
typing, presentation lowering, and diagnostic classification reconstructed
separate helper boundaries inside one traversal. A typed surface tree duplicated
typed structure and provenance conversion without a current consumer. A
constraint solver deferred direct monomorphic failures and required additional
origin attribution while the corpus used no inference variables or
generalization.

A resolved surface form established binder identity and scope once for tooling,
typing, diagnostics, and Core validation. Bidirectional elaboration matched the
anonymous-function and application rules directly and distinguished
not-applicable from argument-mismatch failures without string inspection.

## Consequences

- Each scope policy accepted by the applicable language specification is
  implemented through explicit resolver operations rather than typechecker
  lookup accidents.
- Stable binder identities, spellings, and source origins remain available to
  typed Core and diagnostics.
- Expected types flow through explicit checking entry points instead of global
  mode flags or reconstructed annotations.
- Equational and operational definitions may converge to the same semantic
  function structure while retaining presentation-specific provenance.
- Shared pattern and coverage rules serve equation clauses and explicit matches.
- Equality, normalization, unification, constraint resolution, and other future
  type mechanisms do not silently collapse into host-language equality.
- This decision does not accept provisional scope or typing semantics, a
  concrete inference algorithm, polymorphism, generalization, a typed surface
  tree, a constraint solver, or one Rust module layout.

## Verification

Front-end implementation and later rule changes must provide:

- isolated resolution tests for the name and scope behavior defined by the
  applicable accepted language specification, including binder-use
  relationships;
- bidirectional typing tests for synthesis, checking, expected-typed functions,
  function exposure, argument checking, and structural type equality;
- paired equational and operational cases that share semantic rules and retain
  different source origins;
- shared pattern and coverage outcomes for equivalent clause and explicit-match
  inputs when those features are implemented;
- structural diagnostic tests for semantic reason, primary span, related spans,
  expected and found types, and justified help independently from rendering;
- evidence that changing one semantic policy affects its owning rule boundary
  rather than unrelated callers;
- no recovery-bearing parser node reaching resolution or typed elaboration;
- typed elaboration output accepted by the independent Core validator before
  evaluation.
