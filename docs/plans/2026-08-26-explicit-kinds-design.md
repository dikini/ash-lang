# Explicit Kinds and Higher-Kinded Parameters Design

- Status: approved design
- Date: 2026-08-26
- Related: [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md)

> This document records the approved prospective design. It does not describe
> current Ash or authorize implementation. The accepted change proposal owns
> the semantic transition, and the active task owns its execution plan.

## Goal and boundary

Add explicit `Type` and function kinds, higher-kinded declaration parameters,
kind-aware type application, and independent Core kind validation. This is the
second prepared `lib-ash` increment. It builds on explicit implementation
selection and re-export without changing runtime evaluation.

Current Ash gives every source type parameter kind `Type`, requires every
nominal occurrence to be saturated during resolution, and permits only
kind-`Type` inference variables. The new boundary makes constructor kinds
source-visible where a declaration binds a parameter and moves application
well-formedness from name resolution into a kind-aware static rule.

This increment keeps interfaces single-parameter and source terms rank-1. It
does not add method-local type parameters, kind polymorphism, type lambdas,
source `forall`, explicit term type application, multi-parameter interfaces,
associated outputs, defaults, packages, or runtime kind values.

## Source model

All declaration-level type binders use one grammar. `Type` is contextual in a
kind annotation, `->` associates to the right, and parentheses group kinds.

```ebnf
type_parameters ::=
  "<" type_parameter { "," type_parameter } ">" ;
type_parameter ::= upper_identifier [ ":" kind ] ;
kind ::= kind_atom [ "->" kind ] ;
kind_atom ::= "Type" | "(" kind ")" ;
```

Nominal and interface declarations reuse `type_parameters`; an interface still
requires exactly one parameter. Globals may place a complete binder list after
their name in either presentation. Implementations may place a complete binder
list after `impl`:

```ash
type Compose<F : Type -> Type, G : Type -> Type, A> =
    Compose(F<G<A>>)

type Wrapped<F : Type -> Type, A> = Wrapped(F<A>)

interface IntFunctor<F : Type -> Type> {
    map_int : (Int -> Int, F<Int>) -> F<Int>
}

map_twice<F : Type -> Type> :
    (Int -> Int, F<Int>) -> F<Int>
    where IntFunctor<F>
map_twice (function, value) = map_int((function, map_int((function, value))))

impl<F : Type -> Type> IntFunctor<Wrapped<F>> where IntFunctor<F> {
    map_int (function, Wrapped(value)) =
        Wrapped(map_int((function, value)))
}
```

An omitted annotation on an explicit binder means `Type`. An explicit binder
list is complete: every free type variable in the declaration header must be
listed, duplicate binders are rejected, and no implicit binder is added. A
global or implementation with no binder list preserves current implicit
first-occurrence binding, but every such binder has kind `Type`. This
compatibility rule cannot introduce a higher-kinded parameter silently.

The absence of kind inference is a phase-dependent implementation constraint,
not a permanent language principle. A later proposal may add bounded
declaration-local inference while preserving the same checked kind language.
This increment does not allocate kind metavariables, infer arrows from use, or
default unsolved kind variables. Kind polymorphism remains a separate design
question.

## Kind checking and type representation

Primitive types have kind `Type`. A nominal constructor has the right-folded
kind formed from its declared parameter kinds and result `Type`. A type
variable has its binder's declared kind. Type application has the ordinary
rule: the function must have kind `argument_kind -> result_kind`, and the
argument must have `argument_kind`; the application then has `result_kind`.
Every value annotation, global result, constructor payload, pattern type, and
term binder type must finish at kind `Type`.

The internal type algebra uses one unary application form. A nominal identity
denotes its constructor at any kind, and repeated unary applications represent
both saturated and partial uses. This removes the current split between bare
nominals and saturated nominal applications. Rendering may print conventional
`Name<A, B>` syntax, but equality, substitution, unification, matching, and
validation operate on the canonical unary structure.

Unsaturated constructors are accepted only where the surrounding rule expects
their residual kind. For example, `IntFunctor<Option>` can satisfy an interface
parameter of kind `Type -> Type`, while a value annotation cannot end at
`Option`. Partial application follows the same rule, so `Result<Int>` can be
used where `Type -> Type` is expected if `Result` has kind
`Type -> Type -> Type`.

Type inference remains first-order over the canonical application tree, with
every inference variable carrying one fixed kind. Unification may solve a
higher-kinded inference variable with a constructor or partial application of
the same kind. It does not synthesize a type lambda, abstract over mismatched
arguments, or change an inference variable's kind. Implementation-head
matching uses the same kind-preserving first-order structure and may bind only
the implementation's declared head variables. Evidence selection never solves
an unrelated inference variable merely to make a candidate applicable.

## Pipeline ownership

Parsing retains kind syntax and binder annotations. Resolution assigns binder
and declaration identities, resolves type and interface names, and preserves
kind annotations; it no longer decides nominal saturation or rejects applying
a type parameter merely because the parameter is not a nominal. Sort errors,
such as using an interface as an ordinary type constructor, remain resolution
errors.

Resolution also owns duplicate explicit binders and an unbound uppercase name
under a complete binder list. A distinct kind-checking responsibility derives
declaration constructor kinds, checks binder annotations, synthesizes or checks
every resolved type kind, and freezes kinded facts before ordinary type
checking. It reports structured reasons for a non-constructor application, an
argument-kind mismatch, and a constructor-kinded type in a value-type context.
Diagnostics retain the application or value-type site, the declared binder or
constructor site when useful, and structured expected and found kinds.
Rendering does not own this policy.

Checked schemes bind `(TypeVariableId, Kind)` pairs. Nominal registries,
interface registries, implementation headers, requirements, inference
variables, substitutions, export summaries, hidden summary closure, selected
evidence, and linked checked groups retain the kinds needed by their consumers.
Import admission authenticates the defining identity and checked kind; aliases,
facades, opacity, and diamonds do not recompute or erase the fact.

Core type abstractions and applications retain kinded binders and canonical
type applications. Core construction checks kinds before storing a type
operation. Independent Core validation receives only linked Core and its
registries, synthesizes kinds again, and rejects forged binder kinds, nominal
kinds, application metadata, substitutions, and kind-incorrect value types.
The evaluator still erases all type and kind operations and needs no new value,
frame, or transition.

## Resources and failure behavior

Kind operations are iterative or use explicit bounded work stacks. Clone,
equality, hashing, rendering, substitution, unification, summary admission,
Core admission, validation, and disposal must not recurse on host stack depth.
Lexing, concrete-tree construction, and projection charge the existing syntax
budget. After projection, every retained or visited kind node and every
kind-aware application operation charges the existing type-work resource
family at the stage that owns the work. Core construction and independent Core
validation keep their independent budgets. Exact-limit and one-short tests
establish each new charge rather than relying only on large stress cases.

Kind failures precede ordinary type unification, implementation selection, or
Core synthesis for the same source fact. Dependency, import, declaration,
binder, and type traversal order remains deterministic. A kind error is a
source rejection; a forged kind fact discovered only by linked evidence or
Core validation remains an internal compiler failure at that boundary.

## Evidence

The product checkpoint must retain:

- parser and projection cases for annotations, associativity, grouping,
  complete explicit binder lists, recovery, and legacy headers;
- positive and negative kind matrices for primitives, nominals, variables,
  partial constructors, nested applications, globals, interfaces,
  implementations, constraints, and value-type contexts;
- first-order higher-kinded unification, substitution, occurs-check, overlap,
  termination, orphan, and evidence-selection cases without type-lambda
  synthesis;
- opaque, hidden-carrier, facade, diamond, and implementation-only import cases
  that preserve defining kinds and identities through summaries;
- linked-evidence and Core tampering cases that forge every retained kind
  relationship and stop before evaluation;
- structured diagnostics with stable reasons, primary and related spans, and
  expected and found kinds independently from rendering;
- exact and one-short resource boundaries plus deep and wide 256 KiB-stack
  construction, checking, rendering, validation, and disposal cases;
- all predecessor tests, specification examples, CLI observations, and the
  full repository verification gate without a compatibility grammar or second
  pipeline.

After implementation converges, update the normative syntax, resolution,
static-semantics, and elaboration chapters in the same checkpoint. Retain one
`lib-ash` kind evidence report, then remove the temporary proposal, task,
design record, and execution plan from the closing branch. Git preserves their
transition history.
