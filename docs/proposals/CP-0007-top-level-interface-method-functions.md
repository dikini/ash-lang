# CP-0007: Top-Level Interface Method Functions

- ID: `CP-0007`
- Status: accepted
- Related:
  [DN-0023: Interfaces and Implementations](../design/DN-0023-interfaces-and-implementations.md),
  [TASK-0013: Require Top-Level Interface Method Functions](../tasks/TASK-0013-require-top-level-interface-method-functions.md)

> This proposal is not current Ash until the complete change is integrated into
> `main`.

## Current behavior

An interface method is well formed when its type contains the interface
parameter, contains no other free type variable, and contains a function arrow
anywhere in the type. A tuple such as `(A, Int -> Int)` therefore passes
interface admission.

Every implementation method uses one or more equation patterns. Checking those
patterns consumes top-level function arrows from the substituted method type.
Consequently, a method admitted only because of a nested arrow cannot have an
implementation.

## Proposed behavior

Every interface method type must have `Function` as its outermost type
constructor. Its domain and codomain may contain additional function types, and
its codomain may itself be a function.

The stable `interface.method-not-function` reason rejects a method whose
outermost type constructor is not `Function`. The existing
`interface.method-parameter` check retains precedence.

## Semantic delta

Declarations such as `(A, Int -> Int)` cease to be valid interface method
types. Declarations such as `(A, Int -> Int) -> Int` and `A -> Int -> Int`
remain valid.

## Affected specification areas

- [Interfaces and constrained schemes](../../spec/static-semantics.md#interfaces-and-constrained-schemes)
- [Implementations](../../spec/static-semantics.md#implementations)
- [Interface-evidence lowering](../../spec/elaboration.md#interface-evidence-lowering)
- [Specification overview](../../spec/README.md)

## Resulting specification truth

Every admitted interface method has a top-level function type. Substitution of
an implementation or requirement argument preserves that outer constructor, so
implementation equations and evidence slots always receive function types.

## Interactions

Parsing and resolution continue to admit every type syntax and leave this rule
to static interface checking. Evidence selection, substitution, Core lowering,
Core validation, and evaluation transport the admitted method type unchanged
and need no new representation or runtime behavior.

The checker replaces a recursive search for any nested arrow with a
constant-time outer-constructor inspection. Constraint-work boundaries decrease
by the removed traversal cost.

## Non-goals

This proposal does not add zero-pattern implementation values, first-class
dictionaries, runtime interface values, associated types, specialization,
default methods, or a new Core form. It does not require exactly one arrow or
restrict function types inside a method domain or codomain.

## Required evidence

- A negative test rejects a method with only a nested function arrow.
- Positive tests retain nested functions inside a top-level function domain and
  a function-valued codomain.
- Parameter validation continues to precede method-shape validation.
- An end-to-end program implements, selects, lowers, validates, and evaluates a
  method whose top-level function domain contains a function value.
- Exact checker constraint budgets and stack-safety evidence are remeasured
  after removal of recursive arrow search.
- The implementation, stable diagnostic documentation, normative
  specification, retained design evidence, and current project documentation
  agree on the outer-function requirement.
