# CP-0004: Rank-1 Polymorphism

- ID: `CP-0004`
- Status: accepted
- Related: [AD-0004: Small-Step Semantic Method](../decisions/AD-0004-small-step-semantic-method.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0006: Initial Type System](../design/DN-0006-initial-type-system.md), [DN-0007: Data and Pattern Typing](../design/DN-0007-data-and-pattern-typing.md), [DN-0020: Ash Dialect Milestones](../design/DN-0020-ash-dialect-milestones.md), [TASK-0010: Finish Mini-Ash](../tasks/TASK-0010-finish-mini-ash.md)

> This proposal is not current Ash. Its accepted status authorizes TASK-0010;
> the specification remains authoritative until the complete change merges.

## Current behavior

Mini-Ash is monomorphic. Nominal declarations have no parameters, type
occurrences cannot apply constructors, and every resolved and Core type is a
closed monotype. Anonymous functions require an expected function type, and
local bindings never generalize. The parser rejects polymorphic punctuation.

## Proposed behavior

Nominal declarations bind zero or more ordered parameters of kind `Type`.
Nominal constructors have internal arrow kinds and source value types must be
fully applied to kind `Type`. Parameterized constructors are ordinary
polymorphic values whose schemes quantify their owner's parameters.

Free uppercase variables in a global value annotation are implicitly
quantified at its outer boundary in first-occurrence order. They are rigid
while checking that definition and instantiate freshly at ordinary value use
sites. Source expressions have no explicit type abstraction or application.

An unannotated local binding generalizes only when its initializer is an
anonymous function. It quantifies solved inference variables not free in the
incoming environment. Other unannotated initializers remain monomorphic, and a
local annotation may use enclosing rigid variables but introduces none.

Recursive members and recursive self-uses remain monomorphic. Inference uses
kind-preserving first-order structural unification with an occurs check. Type
equality, kinding, instantiation, generalization, and unification remain
separate judgments.

Elaboration makes inferred type abstraction and application explicit in typed
Core. Independent validation rechecks binder scope, kinds, substitution,
rank-1 placement, constructor schemes, provenance, and the absence of unsolved
inference variables. Evaluation erases these operations without runtime type
objects or changed value, heap, or order semantics.

## Semantic delta

The change adds type-parameterized nominal ADTs, implicit outer polymorphism for
global interfaces, and conservative function-only local polymorphism. It does
not add higher-rank or higher-kinded polymorphism, broad Hindley–Milner
generalization, explicit value-level type application, or polymorphic
recursion.

## Affected specification areas

- [Lexical structure](../../spec/lexical-structure.md) adds type-application punctuation.
- [Syntax](../../spec/syntax.md) adds declaration parameters and type application.
- [Name resolution](../../spec/name-resolution.md) adds type-parameter identities and scope.
- [Static semantics](../../spec/static-semantics.md) adds kinds, schemes, instantiation, generalization, unification, and monomorphic recursion.
- [Elaboration](../../spec/elaboration.md) adds explicit Core type operations and their erasure boundary.
- [Dynamic semantics](../../spec/dynamic-semantics.md) states the type-erasure transitions.

## Resulting specification truth

After the implementation, tests, documentation, and specification merge,
Mini-Ash is a pure, single-file, rank-1 language. Parameterized nominal
identities remain declaration-based; their arguments compare structurally.
Every admitted source type has kind `Type`, and runtime observations contain no
type arguments or new identities.

## Interactions

- AD-0006 keeps type-variable resolution before elaboration and keeps the five
  static judgments independently reviewable.
- AD-0007 requires explicit typed Core operations, transform preservation, and
  independent malformed-Core rejection.
- AD-0008 requires erasure through explicit machine transitions rather than
  host closures or runtime type reflection.
- Parameter substitution feeds the existing constructor-pattern and coverage
  rules without changing their usefulness relation.
- Future resources may add inputs to the single local-generalization
  eligibility rule without changing ordinary binding semantics.
- Future modules consume retained schemes at a static boundary but are not
  introduced by this proposal.

## Non-goals

This proposal does not add explicit value type arguments, kind annotations,
higher-kinded variables, nested universal types, polymorphic recursion,
application-shaped local generalization, records, aliases, modules, interfaces,
effects, resources, type classes, overloading, type-level computation, or
runtime type representation. Integer equality remains unchanged.

## Required evidence

TASK-0010 must provide:

- source and Core tests for parameterized ADTs, constructor schemes, global
  instantiation, local function generalization, monomorphic recursion, kinds,
  unification, occurs checks, ambiguity, provenance, and erasure;
- exact diagnostics for duplicate and unknown parameters, kind and application
  errors, rigid mismatches, infinite types, unresolved inference, and rejected
  polymorphic recursion;
- transform and differential-evaluation evidence for explicit Core type
  abstractions and applications;
- cumulative, pre-allocation accounting for type construction,
  instantiation, substitution, unification, occurs checks, zonking, and Core
  validation, plus deep and wide small-stack tests;
- unchanged execution and diagnostics for the complete monomorphic corpus;
- updated normative semantics, executable tool documentation, retained
  integration evidence, and a Mini-Ash closure and simplification report;
- `cargo xtask verify` plus Markdown, link, authority, notation, and
  requirement review.

If implementation exposes an omitted semantic choice, work returns to this
proposal rather than deciding through implementation accident.
