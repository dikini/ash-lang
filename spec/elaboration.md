# Elaboration

Elaboration converts resolved surface syntax into typed semantic terms used by
the [dynamic semantics](dynamic-semantics.md). Each term has its structural type
and a causal source origin. Elaboration does not change the result prescribed
by the typing rules. Checked definitions retain any selected interface evidence
through linking. Linked interface-evidence validation authenticates that
evidence, and Core synthesis consumes it.

## Surface erasure

Parentheses group expressions and types but do not survive as semantic terms.
Resolved spellings become their stable binder identities. Literal, application,
and primitive-operation structure otherwise remains direct. Tuples,
constructor occurrences, typed patterns, and matches remain structured semantic
terms. Their nominal and constructor references use registry identities rather
than source spellings.

Module paths, imports, aliases, targeted bindings, declaration visibility, and
opacity are source-only forms and do not become Core terms. Resolution has
already authenticated each cross-module occurrence against the defining
module's export summary. The resolved semantic terms and registries still
retain the module-qualified term, nominal, constructor, type-parameter, source,
and origin identities that later stages require.

Interface and implementation declarations likewise produce no Core declaration
node. The interface-specific identities and registries established during
resolution and checking remain linked metadata until linked interface-evidence
validation authenticates them. They erase during Core synthesis as described
below.

Resolution has already replaced source type spellings with stable nominal and
type-parameter identities. Elaboration may introduce inference variables while
checking, but it solves and removes every inference variable before constructing
the final Core program. Only resolved monotypes and outer rank-1 schemes cross
the Core boundary.

An ordinary local binding becomes a nonrecursive Core binding around the
remainder of its block. Its initializer remains outside its new binder's
scope.

All globals in one module elaborate together through one recursive binding.
One explicit local recursive group elaborates through the same form around the
remainder of its block. The recursive binding owns a nonempty ordered sequence
of annotated member initializers followed by one body term. Every group binder
is in scope in every initializer and in that body.

A local binder pattern uses the ordinary nonrecursive Core binding. Any other
local pattern becomes a one-arm structured match whose static coverage proves
the arm irrefutable. An equational clause group becomes one structured match
over its curried arguments. An operational multi-parameter header and a
multi-parameter anonymous function each receive one tuple-domain value and
match it with the source pattern in the function body.

## Module linking and entry generation

After every module checks, linking combines the complete defining nominal,
constructor, interface, and implementation registries of all admitted modules.
Each checked module contributes a definition group containing its source
definitions, global schemes, implementation-method bodies, and filled
structural evidence slots. Linking preserves that ownership rather than
extracting selections into a span-keyed side table. Each declaration retains
its module-qualified identity. Distinct identities remain distinct even when
their source spellings or representations match. Access-compatible import
routes have already converged on the same identities. Public summaries can
carry a private nominal identity without giving it a source name. The combined
registries retain that identity so all compatible imported schemes continue to
refer to the same type. Opaque constructor access has already been enforced and
does not restrict the defining constructor facts needed by the linked program.

Every resolved method or constrained-global occurrence has an occurrence-local
structural evidence field. Resolution creates each slot empty. Checking
atomically fills each slot with the zonked checked obligation argument and the
selected evidence at the owning obligation-closure boundary defined by the
[static semantics](static-semantics.md#constraint-satisfaction-and-checked-evidence).
A method occurrence retains one selection for its interface requirement. A
constrained-global occurrence retains one selection for each requirement in
the global signature's order. The checked definition owns those selections
through module checking and linking. Core synthesis consumes the slots on those
exact occurrences; it neither joins evidence by source location nor performs
implementation selection again.

Before Core synthesis, linked interface-evidence validation receives the
checked definition groups and their combined registries. It authenticates:

- interface, method, implementation, nominal, requirement,
  implementation-method, and binder identities;
- each selected implementation's availability in the occurrence module's
  direct effective implementation environment;
- implementation-head matching, recorded substitutions, prerequisite trees,
  and prerequisite termination;
- complete method slots in interface declaration order, including slots with
  equal Core types;
- abstract requirement ownership, declaration order, lexical scope, and
  provenance;
- checked global and implementation-method schemes, selected method types, and
  binder mappings;
- equality between every checker-retained occurrence argument and its selected
  evidence goal; and
- source and module provenance, complete linked definitions, and the absence of
  unresolved inference variables.

This validation checks the recorded selections and does not choose candidates
again. A malformed linked selection is an internal
`evidence.validation.*` failure. The graph-wide interface-and-constraint work
budget continues through this judgment, and exhaustion remains
`internal.resource.constraint-work`. Core construction begins only after the
judgment succeeds.

Each nonempty module definition group becomes one ordinary Core recursive
binding. Groups appear in dependency order: a dependency's group surrounds the
groups that depend on it. An imported binder occurrence therefore refers to an
outer binder with the identity supplied by the dependency summary. Modules do
not form one mutually recursive group, and an import cycle cannot reach this
phase.

Elaboration generates an occurrence of the entry module's local `main` and
applies it to unit. This application is the innermost body of the linked module
groups. It has the closed result type established by the entry contract.
Module linking introduces no initialization, lookup, or runtime module value;
the result is one pure Core expression.

## Interface-evidence lowering

Requirements in a global signature, or prerequisites on an implementation,
flatten in declaration order. Within each requirement or prerequisite, methods
flatten in interface declaration order. Let `s_1` through `s_k` be that
flattened sequence. A constrained global has this derived Core scheme:

```text
forall parameters.
    type(s_1) ->
    ... ->
    type(s_k) ->
    source value type
```

Each `type(s_j)` is the corresponding declared method type after substituting
its requirement argument for the interface parameter. The initializer contains
one outer type abstraction when `parameters` is nonempty, then one ordinary
unary function binder for every flattened evidence method, then the source
function. An unconstrained global retains its existing Core shape.

A constrained-global occurrence starts from its ordinary Core binder. Core
type application, when needed, precedes the ordered evidence applications.
Those evidence applications in turn occur inside any surrounding applications
of source value arguments. Generic implementation-method evidence follows the
same order: type application precedes prerequisite-evidence applications, and
all of them precede the method's source argument.

An abstract selection lowers each selected method to the evidence binder keyed
by its requirement and method identities. A concrete selection maps every
ordered `ImplMethodId` through the defining module's checked
`ImplMethodId`-to-`BinderId` mapping. A generic implementation method is first
type-applied with its recorded head substitution. Its prerequisite selections
then lower recursively, in prerequisite and method order, and become ordinary
term arguments. Exact current-implementation evidence uses the same lowering;
its prerequisite selections refer to the implementation method's abstract
evidence binders rather than triggering another selection.

Each implementation-method binder has the Core scheme obtained from its rigid
head parameters, flattened prerequisite methods, and substituted source method
type. Its initializer therefore uses an outer type abstraction when generic,
then ordinary evidence functions, then the source method function. Every such
binder joins the defining module's existing recursive group alongside ordinary
globals. Global-to-method, method-to-global, direct method recursion, and mutual
method recursion consequently use the existing recursive binding rather than a
cross-module group.

After linked interface-evidence validation, interface, implementation, method,
implementation-method, and requirement identities erase. Their authenticated
relationships have become ordinary Core type abstractions, function binders,
binder occurrences, type applications, and term applications. Stable Core
binder, nominal, constructor, type-parameter, source, and origin identities
remain for ordinary Core validation.

## Explicit rank-1 operations

Source type abstraction and application are implicit. Elaboration records both
operations explicitly in Core. A generalized definition becomes
`TypeAbstraction(parameters, body)` with type
`forall parameters. body_type`. Each polymorphic occurrence becomes
`TypeApplication(function, arguments)` with the monotype obtained by
simultaneously substituting those arguments for the quantified parameters.
Parameterized constructors use the same application form as polymorphic value
names.

Outer type variables from a global signature are abstracted in their
first-occurrence order. An eligible unannotated local anonymous-function binding
abstracts only inference variables that are not free in the incoming
environment. Other local bindings remain monomorphic. A recursive global body
checks its self-occurrences against the same rigid parameters; elaboration does
not instantiate recursion at a different type.

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

main : Unit -> Int
main () = add 20 22
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

main : Unit -> Int
main () = size (Fork(Tip(0), Tip(0))) + size_match (Fork(Tip(0), Tip(0)))
```

The executable test `elaboration_payload_constructor_is_higher_order` checks
that a payload constructor crosses the ordinary function boundary:

```ash
type Wrapped =
    Wrap(Int)

fn build(make : Int -> Wrapped) -> Wrapped {
    make 42
}

main : Unit -> Int
main () = match build Wrap {
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
source origin. After linked interface-evidence validation and erasure, the
existing Core validator receives the produced program, its combined immutable
nominal and constructor registry, the admitted source set, and each module's
source identity. It independently checks registry closure and identities,
module and source provenance, binder scope, node and branch types, constructor
ownership and payloads, pattern bindings, coverage, recursive groups,
type-variable scope, rank-1 scheme shape, type-operation substitution, origins,
child handles, reachability, and cumulative resource limits. A type application
must supply exactly one kind-`Type` monotype per quantified parameter, and its
annotated result must equal simultaneous substitution into the scheme body.
Core validation applies once to the whole linked Core program, including every
module group and the generated entry application. Failure of this boundary is
an internal compiler failure, not a source-language typing result.

This requirement does not prescribe a Rust representation, storage strategy,
or evaluator mechanism.
