# Elaboration

Elaboration converts resolved surface syntax into typed semantic terms used by
the [dynamic semantics](dynamic-semantics.md). Each term has its structural type
and a causal source origin. Elaboration does not change the result prescribed
by the typing rules.

## Surface erasure

Parentheses group expressions and types but do not survive as semantic terms.
Resolved spellings become their stable binder identities. Literal, application,
and primitive-operation structure otherwise remains direct. Tuples,
constructor occurrences, typed patterns, and matches remain structured semantic
terms. Their nominal and constructor references use registry identities rather
than source spellings.

Resolution has already replaced source type spellings with stable nominal and
type-parameter identities. Elaboration may introduce inference variables while
checking, but it solves and removes every inference variable before constructing
the final Core program. Only resolved monotypes and outer rank-1 schemes cross
the Core boundary.

An ordinary local binding becomes a nonrecursive Core binding around the
remainder of its block. Its initializer remains outside its new binder's
scope.

All file globals elaborate together through one recursive binding around
the file result. One explicit local recursive group elaborates through the
same form around the remainder of its block. The recursive binding owns a
nonempty ordered sequence of annotated member initializers followed by one body
term. Every group binder is in scope in every initializer and in that body.

A local binder pattern uses the ordinary nonrecursive Core binding. Any other
local pattern becomes a one-arm structured match whose static coverage proves
the arm irrefutable. An equational clause group becomes one structured match
over its curried arguments. An operational multi-parameter header and a
multi-parameter anonymous function each receive one tuple-domain value and
match it with the source pattern in the function body.

## Explicit rank-1 operations

Source type abstraction and application are implicit. Elaboration records both
operations explicitly in Core. A generalized definition becomes
`TypeAbstraction(parameters, body)` with type
`forall parameters. body_type`. Each polymorphic occurrence becomes
`TypeApplication(function, arguments)` with the monotype obtained by
simultaneously substituting those arguments for the quantified parameters.
Parameterized constructors use the same application form as polymorphic value
names.

Global interface variables are abstracted in their first-occurrence order. An
eligible unannotated local anonymous-function binding abstracts only inference
variables that are not free in the incoming environment. Other local bindings
remain monomorphic. A recursive global body checks its self-occurrences against
the same rigid parameters; elaboration does not instantiate recursion at a
different type.

Core transformations preserve type abstractions, type applications, their
ordered identities and arguments, types, and origins. The dynamic semantics
erase the operations. They produce no runtime type value and change neither
evaluation order nor heap contents.

## Function presentations

Both global presentations elaborate to callable unary function values bound to
the global name. Equational patterns consume nested arrows one at a time. An
operational definition with multiple parameters consumes one tuple domain.
Their source origins remain distinct so a later diagnostic can identify the
interface, header, pattern, and body that caused a fact.

Function application is unary and follows the type. Because arrows associate
to the right, an equational definition can return another function. The one
equation binder consumes the outer domain. An anonymous function in its body
checks against the function-valued codomain. Juxtaposition then applies the
result one argument at a time.

The executable test `syntax_curried_equational_example_is_executable` checks
this curried definition and application:

```ash
add : Int -> Int -> Int
add left = fn(right) {
    left + right
}

add 20 22
```

The inline operational header also defines one unary function. A
comma-separated header constructs one tuple-domain pattern; it does not create
nested arrows. Thus `fn add(left : Int, right : Int) -> Int` has type
`(Int, Int) -> Int`, while a two-pattern equation consumes `Int -> Int -> Int`.

Recursive lowering does not introduce a second function representation.
Equational and inline operational globals become the same ordinary function
nodes used by local recursive members, then join at the recursive binding.
Presentation-specific origins remain available even though the callable Core
shape converges.

The executable test `elaboration_tree_presentations_are_equivalent` checks an
equational and operational traversal over the same nominal data:

```ash
type Tree =
    Tip(Int)
    | Fork(Tree, Tree)

size : Tree -> Int
size (Tip value) = 1
size (Fork(left, right)) = size left + size right

fn size_match(tree : Tree) -> Int {
    match tree {
        Tip(value) => 1
        Fork(left, right) => size_match left + size_match right
    }
}

size (Fork(Tip(0), Tip(0))) + size_match (Fork(Tip(0), Tip(0)))
```

The executable test `elaboration_payload_constructor_is_higher_order` checks
that a payload constructor crosses the ordinary function boundary:

```ash
type Wrapped =
    Wrap(Int)

fn build(make : Int -> Wrapped) -> Wrapped {
    make 42
}

match build Wrap {
    Wrap(value) => value
}
```

## Recursive binding structure

A recursive binder occurrence is an ordinary stable binder reference. It is
not an ownership edge to another Core node, so mutual calls do not form cycles
in the Core arena. The recursive binding owns each function once and exposes
their binder identities simultaneously. This keeps the representation acyclic
while making recursive scope explicit to validation, transforms, and
evaluation.

The recursive binding validator requires a nonempty group, distinct binders,
equal annotations and initializer types, admitted guarded roots, valid scope
and child handles, and complete causal provenance. Traversals visit each member
in order and then the body. A transform must preserve or rebuild the complete
group; it cannot silently treat the members as sequential bindings.

## Validation boundary

Every semantic binder, pattern, and expression carries its type and causal
source origin. The resolved and checked programs carry immutable nominal and
constructor registries. Before evaluation, validation independently checks
registry closure and identities, binder scope, node and branch types,
constructor ownership and payloads, pattern bindings, coverage, recursive
groups, type-variable scope, rank-1 scheme shape, type-operation substitution,
origins, child handles, reachability, and cumulative resource limits. A type
application must supply exactly one kind-`Type` monotype per quantified
parameter, and its annotated result must equal simultaneous substitution into
the scheme body. Failure of this boundary is an internal compiler failure, not
a source-language typing result.

This requirement does not prescribe a Rust representation, storage strategy,
or evaluator mechanism.
