# Explicit Kinds and Higher-Kinded Parameters Design

- Status: approved design
- Date: 2026-08-26
- Related: [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), and [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md)

> This document records the approved prospective design. It does not describe
> current Ash or authorize implementation. The accepted change proposal owns
> the semantic transition, and the active task owns its execution plan.

## Goal and boundary

Add explicit `Type` and function kinds, higher-kinded declaration parameters,
kind-aware type application, and independent Core kind validation. This is the
second prepared `lib-ash` increment. It builds on explicit implementation
selection and re-export without changing runtime evaluation.

The implementation branch is stacked on the completed predecessor commit
`a1647ff` and cannot integrate independently. The explicit-import branch must
integrate first. This design therefore compares against that authorized base,
which is not yet current `main`.

The stacked base gives every source type parameter kind `Type`, requires every
nominal occurrence to be saturated during resolution, and permits only
kind-`Type` inference variables. The new boundary makes constructor kinds
source-visible where a declaration binds a parameter and moves application
well-formedness from name resolution into a kind-aware static rule.

This increment keeps interfaces single-parameter and source terms rank-1. It
does not add method-local type parameters, kind polymorphism, type lambdas,
source `forall`, explicit term type application, multi-parameter interfaces,
associated outputs, defaults, packages, or runtime kind values.

## Source model

All declaration-level type binders use one parameter grammar. `Type` is
contextual in a kind annotation and remains an ordinary uppercase identifier
elsewhere. `->` associates to the right, and parentheses group kinds.

```ebnf
type_parameters ::=
  "<" type_parameter { "," type_parameter } ">" ;
type_parameter ::= upper_identifier [ ":" kind ] ;
kind ::= kind_atom [ "->" kind ] ;
kind_atom ::= "Type" | "(" kind ")" ;
interface_parameter ::= "<" type_parameter ">" ;
```

Nominal declarations use `type_parameters`; an interface retains the exact
single `interface_parameter` production. Globals may place a complete binder
list after their name in either presentation. Implementations may place a
complete binder list after `impl`:

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

An omitted annotation on an explicit binder means `Type`. A global list is an
ordered bijection with all free variables of its value type and requirements;
its order becomes scheme order, while the existing requirement-determination
rule still applies. An implementation list is an ordered bijection with the
free variables of its head argument; its order becomes head-parameter order,
and prerequisite variables remain a subset. No explicit list admits an extra
or unlisted binder. Nominal declarations retain declaration order and may
retain phantom parameters.

A global or implementation with no binder list preserves current implicit
first-occurrence binding, but every such binder has kind `Type`. This
compatibility rule cannot introduce a higher-kinded parameter silently. The
absence of kind inference is a semantic boundary of this increment, not a
permanent language principle. A later proposal may add bounded
declaration-local inference while preserving the same checked kind language.
This increment does not allocate kind metavariables, infer arrows from use, or
default unsolved kind variables. Kind polymorphism and higher-order
unification remain separate design questions.

## Kind checking and type representation

`DELTA` maps type-variable identities to fixed declared kinds, transient
`OMEGA` maps live inference-variable identities to fixed kinds, `XI` maps
nominal identities to constructor kinds derived from their ordered parameter
records, and `IOTA` maps interface identities to their canonical single
parameter records. Kind synthesis is total for monotypes. Primitives synthesize
`Type`; declared variables, inference variables, and nominals use `DELTA`,
`OMEGA`, and `XI`; application requires a function kind with a matching
argument; every tuple element and both sides of a term function must synthesize
`Type`, producing `Type`. Every value annotation, constructor payload, pattern
type, and term binder type must synthesize `Type`. A source or inferred
requirement, method obligation, implementation head or prerequisite, or
evidence goal instead checks its argument against the declared kind in its
selected interface parameter record. The interface application is a constraint
and has no monotype kind of its own. A legacy interface parameter defaults to
kind `Type`.

The CST and surface tree preserve a named application and its argument vector
for source spans. Resolution folds that vector left into one unary semantic
application form with one provenance step per argument. A nominal identity
denotes its constructor at any kind, and repeated unary applications represent
both saturated and partial uses. This removes the current split between bare
nominals and saturated nominal applications. Rendering may print conventional
`Name<A, B>` syntax, but equality, substitution, unification, matching, and
validation operate structurally and injectively on the canonical unary tree.

An unsaturated constructor always synthesizes its derived kind; a partial
application always synthesizes its residual kind. It is accepted when that kind
satisfies the owning rule. For example, `IntFunctor<Option>` can satisfy an
interface parameter of kind `Type -> Type`, while a value annotation cannot end
at `Option`. `Result<Int>` can be used where `Type -> Type` is expected if
`Result` has kind `Type -> Type -> Type`.

Type inference remains first-order over the canonical application tree.
Resolved checking uses empty `OMEGA`; elaboration registers every fresh
inference variable at one fixed kind before use. Unification and occurs checking
consult that entry. Unification may solve a higher-kinded inference variable
with a constructor or partial application of the same kind. It does not
synthesize a type lambda, abstract over mismatched arguments, change an
inference variable's kind, or recover a missing or conflicting registry entry.
Zonking removes every inference variable before summaries or Core. Eligible
local bindings may generalize eligible variables of any fixed monomorphic kind,
but only into outer rank-1 schemes whose monotype body has kind `Type`. A scheme
has no ordinary kind and cannot occur in a monotype position.

Implementation-head matching uses the same kind-preserving first-order
structure and may bind only an independently freshened candidate's declared
head variables. Evidence selection begins only after the complete goal has no
inference variable and never solves or refines a goal variable. Both children
of a unary application are strict subterms for termination. Orphan and runtime
nominal-shape inspection follow the application function spine to one stable
outer nominal identity.

## Pipeline ownership

Parsing retains kind syntax and binder annotations. Resolution assigns binder
and declaration identities, resolves type and interface names, and preserves
kind annotations; it no longer decides nominal saturation or rejects applying
a type parameter merely because the parameter is not a nominal. Sort errors,
such as using an interface as an ordinary type constructor, remain resolution
errors.

Resolution owns duplicate, unused, and unbound explicit binders, while existing
interface and implementation rules retain their method-local and
prerequisite-only failures. Imported nominal kinds come from authenticated
summaries. After all local nominal and parameter identities exist, a distinct
kind-checking responsibility derives and freezes every local nominal kind
before checking any payload or other declaration type. It reports
`kind.not-applicable`, `kind.argument`, and `kind.expected-type`. Diagnostics
retain the causal site, the defining binder or nominal site when useful, and
structured expected and found kinds. Rendering does not own this policy.

The defining resolved binder record owns each `TypeVariableId` kind. Nominal
kinds derive from ordered parameter records; any cache must equal that
derivation. Data constructors retain checked term schemes, not independent
kinds. Inference kinds are transient and never enter summaries or validated
Core. Checked schemes, nominal and interface registries, implementation
headers, requirements, zonked substitutions, export summaries, hidden closure,
selected evidence, and linked groups retain the identities and binder kinds
needed by their consumers. Import admission authenticates immutable body-free
facts; aliases, facades, opacity, and diamonds do not recompute or erase them.

Core monotypes use canonical unary semantic application. The existing Core
`TypeApplicationNode` remains a distinct simultaneous instantiation of one
ordered outer scheme; it supplies one same-kinded monotype argument per binder.
Type abstractions and outer schemes retain the same ordered kinded binder list.
Independent Core validation receives only linked Core and its registries,
rederives nominal kinds, checks resolved and generated binder ownership,
distinguishes structural application from simultaneous instantiation, and
rejects forged kinds, scopes, substitutions, inference escape, and ordinary
non-`Type` value annotations. Both retained transforms preserve these facts.
The evaluator still erases all type and kind operations and needs no new value,
frame, or transition; only its nominal-shape inspection migrates mechanically.

## Resources and failure behavior

Kind operations are iterative or use explicit bounded work stacks. Clone,
equality, hashing, rendering, substitution, unification, matching, summary
admission, Core admission, transform rebuilding, validation, and disposal must
not recurse on host stack depth. Lexer token, diagnostic, and parser-event
retention charge syntax work; projection remains bounded by the admitted CST
and structural-depth check without a new ledger. Resolution and ordinary
checking charge their stage type-work budgets. Interface, evidence, and linked
comparisons charge graph constraint work, with structural retention additionally
charging type work. Core construction, transforms, and validation keep their
independent ledgers.

Each kind node, canonical application node, and binder-kind record is charged
before its owning visit or retention. Record retention additionally charges all
copied type and kind nodes. Every operation publishes its additive formula and
proves exact and one-short boundaries, stable precedence, atomic failure, and
accepted and rejected teardown rather than relying only on stress cases.

Kind failures precede ordinary type unification, implementation selection, or
Core synthesis for the same source fact. Dependency, import, declaration,
binder, and type traversal order remains deterministic. A kind error is a
source rejection; a forged dependency summary, linked evidence fact, or Core
relationship remains an internal compiler failure at its validating boundary.

## Evidence

The product checkpoint must retain:

- parser and projection cases for annotations, associativity, grouping,
  complete explicit binder lists, recovery, and legacy headers;
- positive and negative kind matrices for primitives, nominals, variables,
  partial constructors, nested applications, globals, interfaces,
  implementations, constraints, and value-type contexts;
- first-order higher-kinded unification, substitution, occurs-check, overlap,
  termination, orphan, and evidence-selection cases without type-lambda
  synthesis, including missing or conflicting transient inference-kind entries
  and complete zonking;
- immutable body-free opaque, hidden-carrier, facade, transitive, diamond, and
  implementation-only import cases that preserve defining kinds and identities;
- dependency-summary, linked-evidence, and Core tampering cases that forge
  every independently checkable kind relationship and stop at its owning
  boundary before evaluation;
- separate coverage of unary structural type application and simultaneous Core
  scheme instantiation, including both retained transforms and revalidation;
- structured diagnostics with stable reasons, primary and related spans, and
  expected and found kinds independently from rendering;
- exact and one-short resource boundaries plus deep and wide 256 KiB-stack
  construction, clone, equality, hashing, rendering, kind checking,
  substitution, occurs checking, unification, matching, summary/import/link
  admission, Core construction, transforms, validation, and disposal cases;
- all predecessor tests, specification examples, CLI observations, and the
  full repository verification gate without a compatibility grammar or second
  pipeline.

The retained evidence maps every type-bearing source, resolved, checked,
summary, evidence, registry, Core binder, pattern, and node site to its kind
environment, owning rule, required result, failure, budget, and disposal path.
An architectural guard keeps that inventory closed. Migration records every
deliberate stage and reason change while preserving predecessor-valid omitted
kinds and implicit binders unchanged.

After implementation converges, update the normative syntax, resolution,
static-semantics, and elaboration chapters in the same checkpoint. Retain one
`lib-ash` kind evidence report, then remove the temporary proposal, task,
design record, and execution plan from the closing branch. Git preserves their
transition history. This increment creates no `lib-ash` tag and remains stacked
and unmerged until its predecessor can integrate first.
