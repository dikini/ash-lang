# Elaboration

Elaboration converts resolved surface syntax into typed semantic terms used by
the [dynamic semantics](dynamic-semantics.md). Each term has its structural type
and a causal source origin. Elaboration does not change the result prescribed
by the typing rules.

## Surface erasure

Parentheses group expressions and types but do not survive as semantic terms.
Resolved spellings become their stable binder identities. Literal, application,
and primitive-operation structure otherwise remains direct.

An ordinary local binding becomes a nonrecursive Core binding around the
remainder of its block. Its initializer remains outside its new binder's
scope.

All file globals elaborate together through one recursive Core binding around
the file result. One explicit local recursive group elaborates through the
same Core form around the remainder of its block. The recursive binding owns a
nonempty ordered sequence of typed binders and ordinary typed function nodes,
followed by one body node. Every group binder is in scope in every member
function and in that body.

## Function presentations

Both global presentations elaborate to a typed unary function value bound to
the global name. An equational definition
`name : domain -> codomain` followed by `name parameter = body` and an inline
operational definition `fn name(parameter : domain) -> codomain { body }`
therefore converge on the same callable term shape. Their source origins remain
distinct so a later diagnostic can identify the interface, header, parameter,
and body that caused a fact.

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

The inline operational header also defines one unary function. Its familiar
tuple-like punctuation delimits one typed parameter but does not create a tuple
or accept a comma-separated parameter list. Product types and tuples are not
available, so Mini-Ash cannot express a product-domain operational function.

Recursive lowering does not introduce a second function representation.
Equational and inline operational globals become the same ordinary function
nodes used by local recursive members, then join at the recursive binding.
Presentation-specific origins remain available even though the callable Core
shape converges.

## Recursive binding structure

A recursive binder occurrence is an ordinary stable binder reference. It is
not an ownership edge to another Core node, so mutual calls do not form cycles
in the Core arena. The recursive binding owns each function once and exposes
their binder identities simultaneously. This keeps the representation acyclic
while making recursive scope explicit to validation, transforms, and
evaluation.

The recursive binding validator requires a nonempty group, distinct binders,
one admitted function node per binder, equal binder and function types, valid
scope and child handles, and complete causal provenance. Traversals visit each
member function in order and then the body. A transform must preserve or
rebuild the complete group; it cannot silently treat the members as sequential
bindings.

## Validation boundary

Every semantic binder and expression carries its structural type and causal
source origin. The result of elaboration must have consistent binder scope,
binder-use identity, node types, application domains, primitive types,
recursive groups, and origins before evaluation begins. Failure of this
validation boundary is an internal compiler failure, not a source-language
typing result.

This requirement does not prescribe a Rust representation, storage strategy,
or evaluator mechanism.
