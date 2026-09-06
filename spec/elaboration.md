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

An accessible `newtype` constructor occurrence becomes an ordinary unary
function whose body contains an explicit typed representation conversion.
Applying that function wraps the substituted representation as the applied
nominal; matching introduces the reverse conversion before lowering the
representation subpattern. The conversion records the nominal identity,
direction, one child, and causal source origin. It is neither an ordinary
allocating constructor nor an unchecked cast, and it authenticates no
interface, proof, provider, handler, or hook authority.

Module paths, imports, aliases, targeted bindings, public re-export spellings,
declaration visibility, and opacity are source-only forms and do not become
Core terms. Resolution has already authenticated each cross-module name
occurrence against its dependency summary. Implementation authorization routes
remain linked metadata until validation authenticates their complete summary
path. The resolved semantic terms and registries still retain the
module-qualified term, nominal, constructor, type-parameter, source, and origin
identities that later stages require.

Interface and implementation declarations likewise produce no Core declaration
node. The interface-specific identities and registries established during
resolution and checking remain linked metadata until linked interface-evidence
validation authenticates their ordered parameter records, optional determinant
positions, and complete applications. Determination metadata erases during Core
synthesis as described below.

Effect declarations also produce no runtime declaration node. A checked module
summary retains each body-free effect identity, ordered fixed-kinded
parameters, visibility, and ordered operation identities and types. `perform`,
`handle`, handler clauses, `resume`, and `discard` remain typed semantic
operations with their exact effect, operation, handler, and resume-owner
identities. A row tail
or effect argument is zonked before a checked summary or Core node is retained.

Resolution has already replaced source type spellings with stable nominal and
type-parameter identities. Elaboration may introduce inference variables while
checking, but it solves and removes every inference variable before constructing
the final Core program. Ordinary source positions cross the Core boundary as
resolved monotypes or outer rank-1 schemes. A validated generated method-
evidence domain may additionally carry its nested method scheme together with
the minimal immutable authentication facts required by independent Core
validation. Those facts are compiler authority, not source types.

An ordinary local binding becomes a nonrecursive Core binding around the
remainder of its block. Its initializer remains outside its new binder's
scope.

A local `newtype` lowers to `LocalNominalScope(owner, remainder)` around the
following declarations and result of its block. It uses the shared pure Core
family in both Pure and Effect dialects. The unary carrier records its lexical
owner and child; its value type and effect row equal the child's. It has no
initializer or runtime value. Local construction and matching reuse the same
representation conversions as module `newtype`.

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
constructor, interface, effect, operation, and implementation registries of all
admitted modules.
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

A physical data-constructor scheme exists in a checked dependency summary and
then in the authenticated imported constructor fact used to check its
dependent. Linking consumes those body-free summary and import carriers before
Core synthesis. The linked constructor registry retains the defining identity,
owner, payload, and origin needed by Core, but it does not retain another copy
of the physical constructor scheme. The scheme therefore has the lifecycle
summary to imported fact to disposal before linked Core, rather than a
redundant linked carrier.

For a `newtype`, the combined nominal registry instead retains one canonical
hidden fact containing the declaration kind and identity, owner, ordered
parameter records, sole same-spelled constructor, representation template,
access, origin, and representation provenance. Linking authenticates these
facts across direct, aliased, opaque, re-exported, and diamond routes. Hidden
facts authorize later Core validation but create no source name, constructor
access, coercion, or interface evidence.

Local canonical facts never enter dependency summaries, imports, or exports.
Each checked module retains its lexical nominals and constructors separately
from module declaration arrays. Linking preserves their module-qualified
lexical owners and canonical representation facts for independent Core checking;
it creates no source access or implementation-search entry. Shared nominal
lookup and conversion validation serve both ownership classes.

Each checked module also contributes its local implementation inventory, its
effective imported implementation inventory, and a lightweight public
authorization entry for every implementation fact in its public closure. An
entry contains the original `ImplId` and its flat authorization route. Linking
moves these entries out of the frozen summary; it does not retain the complete
dependency summary, duplicate an imported implementation body or method fact,
or synthesize a facade definition.

Every resolved method or constrained-global occurrence has an occurrence-local
structural evidence field. Resolution creates each slot empty. Checking
fixes each selection at the owning obligation-closure boundary defined by the
[static semantics](static-semantics.md#constraint-satisfaction-and-checked-evidence).
The field remains private pending state until whole-module inference closure
atomically freezes its zonked complete obligation application, ordered method-local
arguments, checked occurrence type, and selected evidence. A method occurrence
retains one selection for its interface requirement. A constrained-global
occurrence retains one selection for each requirement in the global signature's
order. The checked definition owns those selections through module checking
and linking. Core synthesis consumes the slots on those exact occurrences; it
neither joins evidence by source location nor performs implementation selection
again.

Before Core synthesis, linked interface-evidence validation receives the
checked definition groups, their combined registries, effective implementation
inventories, and public authorization entries. It first authenticates every
group's local implementation inventory. In dependency order, it then
authenticates every complete public authorization table and every effective
inventory before inspecting occurrence evidence.

An empty public authorization is valid only for a public implementation defined
by the publishing group. A nonempty route must begin at the publishing group,
match one exact direct dependency edge and import span, and continue as the
exact suffix published by that dependency for the same `ImplId`. Repeating the
check reaches the group that owns the public implementation fact, source body,
and original method binders. A disconnected, malformed, repeated, truncated,
or otherwise inconsistent route fails authentication. Validation then uses the
same authenticated relation for occurrence availability; it never substitutes
another route or candidate.

The complete validation authenticates:

- interface, method, implementation, nominal, requirement,
  implementation-method, and binder identities;
- every interface's ordered parameter identities, kinds, origins, and optional
  determinant positions;
- every local implementation inventory, public authorization table, and
  selected implementation's availability in the occurrence module's effective
  environment through its complete local, import, or re-export route;
- complete implementation-head matching, recorded substitutions, prerequisite
  trees, and full-application prerequisite termination;
- complete method slots in interface declaration order, including slots with
  equal Core types;
- each method's exact ordered binder identities, owner, kinds, body scope,
  spelling, identity, and provenance;
- abstract requirement ownership, declaration order, lexical scope, and
  provenance;
- each lexical evidence source's canonical identity, complete application,
  ordered method identities and binders, independent contextual parameters,
  captured binders, and actual preceding lexical scope, including unused
  sources;
- checked global and implementation-method schemes, their ordered kinded
  head-versus-method binder partitions, selected method types, and binder
  mappings;
- equality between every checker-retained complete occurrence interface
  application and its selected evidence goal, plus every ordered method argument, checked
  occurrence type, `MethodId`, selected `ImplMethodId`, and adapter relation;
  and
- source and module provenance, complete linked definitions, and the absence of
  unresolved inference variables.

This validation checks the recorded selections and does not choose candidates
again. A malformed linked selection is an internal
`evidence.validation.*` failure. The graph-wide interface-and-constraint work
budget charges linked public-entry retention and every route hop, then continues
through inventory and occurrence validation. Exhaustion remains
`internal.resource.constraint-work`. Core construction begins only after the
complete judgment succeeds.

Successful linked validation produces the only capability that authorizes
polymorphic Core evidence. A copied scheme, node annotation, or unchecked Core
shape cannot establish that authority, and Core synthesis never reselects an
implementation.

Each nonempty module definition group becomes one ordinary Core recursive
binding. Groups appear in dependency order: a dependency's group surrounds the
groups that depend on it. An imported binder occurrence therefore refers to an
outer binder with the identity supplied by the dependency summary. Modules do
not form one mutually recursive group, and an import cycle cannot reach this
phase.

Elaboration generates an occurrence of the entry module's local `main` and
applies it to unit. This application is the innermost body of the linked module
groups. It has the closed result type and empty effect row established by the
entry contract. Module linking introduces no initialization, lookup, runtime
module value, handler registry, or provider selection.

## Effect Core lowering

Ash has two production Core dialects over one arena, program, validation, and
transform substrate. Pure Core retains the uninhabited operation family and an
empty row at every node. A linked program lowers to Effect Core when any
retained scheme, nominal representation, constructor payload, or expression
requires an effectful function type, an `EffectRow` binder or argument, or an
effect operation. Importing or declaring an effect whose identity does not
occur in any such retained fact or expression does not by itself select Effect
Core.

Every Effect Core node retains its structural value type, exact computation
row, and causal origin. Ordinary value and computation nodes reuse the shared
Pure Core families. Effect Core adds only these operation-family nodes:

- `Request(effect_instance, operation, operand)` evaluates the operand and has
  the operand row union the requested exact instance;
- `Handler(handler, body, effect_instance, clauses)` removes that instance from
  the body row and retains the shared output row;
- each clause retains its operation identity, checked irrefutable pattern,
  body, handler identity, and one resume-owner identity;
- `Resume(handler, owner, value)` remains a clause-scoped Core operation rather
  than a value or function; and
- `Discard(handler, owner)` is a clause-scoped, childless operation with value
  type `Unit` and empty immediate row.

Effect and operation declarations remain authenticated registry facts. Core
contains no provider choice or runtime effect registration. Lowering does not
encode continuations as Rust closures or expose evaluator frames as Core data.
The generated entry application is retained only with an empty row.

Module checking infers private control summaries from typed semantic control
and publishes them only after capture checking succeeds. A function summary
retains possible calls, requests, handlers and completion control, rather than
only a preselected outward-request list. Imported calls specialize retained
type and effect identities before selecting handlers. Summary admission
authenticates the defining function and those hidden identities. No source
capture annotation, dependency source body, or runtime capture registry is
introduced.

When a polymorphic occurrence instantiates an `EffectRow` binder, the shared
`TypeApplication` node retains one complete row argument alongside the ordinary
type arguments. Their two ordered slices follow the abstraction's one ordered
parameter vector by kind. Pure Core type applications retain no row arguments.
Effect Core validation checks argument cardinality, kind, scope, and complete
result substitution; transforms preserve or rebuild the same arguments before
revalidation, and evaluation erases the type application directly.

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

Authenticated nested schemes are valid only in generated method-evidence
positions, including the ordinary local binding of a supplied polymorphic
method. If `s_j` has method parameters, its `type(s_j)` is the corresponding
declared method scheme after substituting the requirement's complete argument
vector for the interface parameter vector:

```text
forall method_parameters. substituted_method_value_type
```

A monomorphic method keeps its substituted ordinary function type. Thus a
constrained definition with a polymorphic method evidence position has this
shape:

```text
forall definition_parameters.
    (forall method_parameters. substituted_method_value_type) ->
    ... ->
    source_value_type
```

Core admits a nested scheme only in an authenticated compiler-generated method-evidence position. Substitution preserves the method value type's
top-level `Function` constructor. The initializer contains one outer type
abstraction when definition parameters are nonempty, then one ordinary unary
function binder for every flattened evidence method, then the source function.
An unconstrained global retains its existing Core shape.

Interface substitution is simultaneous and follows declaration order. It
substitutes the complete interface vector before method-local type arguments
or evidence applications are introduced. This order is structural
authentication authority even when two positions contain equal types.

A constrained-global occurrence starts from its ordinary Core binder. Core
type application, when needed, precedes the ordered evidence applications.
Those evidence applications in turn occur inside any surrounding applications
of source value arguments. Generic implementation-method evidence follows the
same order: type application precedes prerequisite-evidence applications, and
all of them precede the method's source argument.

An abstract selection lowers each selected method to the evidence binder keyed
by its requirement and method identities. At a polymorphic method occurrence,
Core type application supplies the retained ordered method arguments before
source term arguments apply. An authenticated evidence variable may remain
uninstantiated only when it is forwarded to the exact matching generated
evidence domain of another constrained definition.

A lexical selection lowers to the ordinary local binder of the supplied
method. The declaration lowers its checked methods to nonrecursive function
bindings around the following block remainder. Each initializer sees only the
preceding scope and captures ordinary values there. A polymorphic method adds
the existing ordered type abstraction; a direct occurrence applies its retained
method arguments, and constrained forwarding uses the matching method scheme.
Distinct declarations have distinct source and method-binder identities even
when their complete applications or method types coincide in disjoint scopes.

The source method's contextual parameters map positionally to generated Core
parameters without capturing an enclosing method's parameters. Ordinary closed
effect-row substitution canonicalizes the result, including reordering and
coalescing instances made equal by substitution. These operations add no
first-class source polymorphism or new solver pass.

A concrete selection maps every ordered `ImplMethodId` through the defining
module's checked `ImplMethodId`-to-`BinderId` mapping. A monomorphic method uses
the existing binder occurrence and applications. A polymorphic concrete or
exact-current method instead uses one generated adapter:

```text
type-abstract method_parameters.
    type-apply implementation_method
      <implementation_head_arguments, method_parameters>
      prerequisite_evidence...
```

Head arguments precede method arguments. Prerequisite evidence follows
prerequisite and interface-method declaration order. The adapter exposes
exactly the selected method scheme; it neither copies nor specializes the
implementation body and performs no selection. Repeated selections of the same
implementation at different evidence nodes or substitutions retain distinct
authenticated adapters. Exact current evidence uses the same lowering, but its
prerequisite selections refer to the implementation method's abstract evidence
binders rather than triggering another selection.

Direct and facade selections therefore lower through the same original method
binder. A facade authorization contributes no Core binder or forwarding call.

Each implementation-method binder has the Core scheme obtained from its rigid
head parameters followed by its rigid method parameters, flattened prerequisite
methods, and substituted source method value type. Its initializer therefore
uses one ordered type abstraction when generic, then ordinary evidence
functions, then the source method function. Every such binder joins the
defining module's existing recursive group alongside ordinary globals.
Global-to-method, method-to-global, direct method recursion, and mutual method
recursion consequently use the existing recursive binding rather than a cross-
module group.

After linked interface-evidence validation, source-only interface,
implementation, lexical selection scope, requirement, determination, and authorization-route carriers
can erase.
Minimal immutable method-evidence authentication facts survive Core synthesis
so independent validation can derive and check every generated evidence
domain, occurrence, forwarding use, adapter, and supplied local method. Their term structure uses only
ordinary Core type abstractions, function binders, binder occurrences, type
applications, local bindings, and term applications. Method authentication facts and schemes
may remain as inert validation and transformation authority in the validated
program; the evaluator does not inspect them. Core type operations erase
through the existing dynamic rules.
Determination adds no Core node, type binder, evidence method, evaluator value,
or interface-specific operation. Complete substituted types and the existing
method-evidence relationships are sufficient after the determinant-position
metadata erases.

## Explicit rank-1 operations

Source type application is structural type formation. The semantic monotype
form is unary: `F<A>` is one application of `F` to `A`, and a source application
with several arguments folds left into nested unary applications. Each step
checks that the function has an arrow kind and that the argument has its domain
kind. This structural operation is distinct from Core expression-level scheme
instantiation.

Source type abstraction and expression-level type application are implicit.
Elaboration records both operations explicitly in Core. A generalized
definition becomes `TypeAbstraction(parameters, body)` with type
`forall parameters. body_type`; both lists retain the same ordered
identity-kind pairs. Each polymorphic occurrence becomes
`TypeApplication(function, arguments)`. It supplies one argument of the
corresponding binder kind in abstraction order. Ordinary monotypes and complete
`EffectRow` arguments remain in the two ordered slices defined above. It checks
each argument against its binder's kind and obtains the result by simultaneous
substitution into the scheme body. The Core operation is not a curried sequence
of unary expression operations.
Parameterized constructors use the same Core instantiation form as
polymorphic value names.

A newtype constructor occurrence lowers to an ordinary unary function whose body is a wrap conversion.
For a parameterized declaration, the function uses fresh generated type
binders in declared order, applies the nominal to those binders, and derives
the function domain by substituting them into the canonical representation.
Validation matches generated binders with canonical parameters by position and
kind; it does not bind or replace the canonical parameter identities. A
newtype pattern lowers through an unwrap conversion before ordinary pattern
structure. Neither path emits an ordinary constructor Core node for the
`newtype`.

For a local representation, enclosing type parameters remain free relative to
its own constructor scheme. Generated Core binder renaming must preserve their
authenticated enclosing scope. Neither constructor instantiation nor local
generalization replaces the lexical nominal identity with a type variable.

An explicit global binder list establishes abstraction order. A global that
omits the list preserves the shared first-occurrence order of ordinary type and
effect-row-tail variables. A name occurring only in ordinary type positions
has kind `Type`; one occurring only as an effect-row tail has kind `EffectRow`;
using the same name in both roles is invalid. An eligible unannotated local
anonymous-function binding abstracts only fixed-kinded inference variables that
are not free in the incoming environment. Other local bindings remain
monomorphic. A recursive global body checks its self-occurrences against the
same rigid parameters; elaboration does not instantiate recursion at a
different type.

Resolved global abstraction parameters retain their resolved identities.
Implementation-method abstractions and eligible local generalization instead
use generated Core type-binder identities owned by their local abstraction and
matching outer scheme. A complete capture-free renaming of one generated
identity throughout that scope is equivalent Core. The original generated
identity, binder span, and allocation ordinal are not external authority for
later validation.

Canonical resolved method binders remain exact through checking, summaries,
imports, and linked authentication. Only a locally generated adapter may use a
bounded, capture-free, order- and kind-preserving alpha-renaming when compared
with its authenticated canonical method scheme. This comparison does not make
ordinary monotype equality, unification, or canonical method facts alpha-
equivalent.

The executable test
`elaboration_distinguishes_structural_application_from_simultaneous_instantiation`
checks both operations in one program:

```ash
type Option<A> =
    None
    | Some(A)

keep<F : Type -> Type, A> : F<A> -> F<A>
keep value = value

main : Unit -> Option<Int>
main () = keep(Some(42))
```

Within `keep`'s monotype, each `F<A>` is one unary structural application. At
the occurrence in `main`, one Core type application simultaneously instantiates
`F` with the bare `Option` constructor and `A` with `Int`, producing
`Option<Int> -> Option<Int>`.

Core transformations preserve or rebuild type abstractions, type applications,
binder kinds, ordered identities and arguments, structural types, origins, and
every method-evidence authentication relationship. The transformed program
passes fresh independent validation before use. The dynamic semantics erase
the type operations. They produce no runtime kind or type value and change
neither evaluation order nor heap contents.

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
source origin. After linked interface-evidence validation, the validator for
the selected Core dialect receives the produced program, its combined immutable
nominal, constructor, effect, operation, canonical type-binder, and method-
evidence authentication facts, the admitted source set, and each module's
source identity. Both dialects independently synthesize monotype kinds, check
schemes, and check registry closure and identities, module and source
provenance, binder scope, node and branch types, constructor ownership and
payloads, pattern bindings, coverage, recursive groups, type-variable scope,
type-operation substitution, origins, child handles, and reachability.

Pure Core validation additionally requires an empty row at every node and
rejects every effect operation. Effect Core validation independently checks:

- every node's value type and exact row equation;
- effect and operation ownership, type arguments, positional kinds, and
  substituted operation types;
- exhaustive handler clauses, exact-instance removal, pattern scope and type,
  and one shared handler result and output row;
- each resume's handler and owner, input and result types, and output row;
- each discard's handler and owner, `Unit` type, empty row and inferred safety;
- exactly-once structural completion through resume or discard, and barriers
  against escape into functions, recursive members, supplied methods, or nested
  clauses;
- handler nesting, dialect membership, provenance, child handles, and
  reachability; and
- an empty row at the linked entry application.

A construction API does not authenticate these relations. Identity and folding
transforms traverse the effect operation family, preserve or rebuild its
authentication data, and return the result to the same independent validator.
Effect nodes presented to Pure Core, or forged rows, identities, owners, or
scope relations presented to Effect Core, fail before evaluation.
Capture validation independently derives request obligations from the actual
linked Core control after ordinary validation. It does not trust an elaborator
permission or imported summary in place of that derivation. A transformed
program must re-establish the same safety property.

For every resolved global with a nonempty outer binder list, validation
requires its `TypeAbstraction` to be the immediate initializer of exactly one
matching `RecursiveBind` member. The abstraction parameters must match that
global's canonical identities, kinds, and declaration order and must match the
outer scheme in the same order. Every such resolved-global binder-list fact is
authenticated exactly once. A sequential `Bind` is local Core and cannot claim
this resolved-global ownership, and a shared initializer cannot authenticate a
second owner.

Generated type binders remain local structural facts. Validation checks their
agreement with the matching outer scheme, fixed kinds, uniqueness, and lexical
scope without capture, shadowing, or escape, while accepting a coherent
capture-free alpha-renaming. It does not authenticate the elaborator's original
generated identity, binder span, or allocation ordinal.

For every polymorphic method-evidence position, validation derives the expected
scheme from canonical method-binder records and the authenticated complete
interface application. It checks the exact constrained-definition owner, requirement and
method position, occurrence `MethodId` and arguments, adapter
`ImplMethodId`, head-before-method type arguments, prerequisite producers, and
exclusive incoming uses.
Independent Core validation consumes every method-evidence authentication fact exactly once.

For supplied local methods, validation authenticates the source identity,
complete application, declaration-ordered method slot and binder, contextual
parameter mapping, recorded capture binders, and actual binding and nominal
scope. It checks unused owners as well as selected uses. An occurrence must
refer to its recorded source and cannot replace higher-priority evidence with
an otherwise well-typed producer. Validation checks these retained relationships
without selecting another candidate. Both Core transforms preserve them.

A nested scheme is valid only at an authenticated generated evidence domain,
a matching occurrence type application or exact forwarding use, a matching
generated adapter, or an authenticated supplied-method binding and its permitted
uses. It is invalid in ordinary parameters or results, globals, other local
bindings, patterns, tuples, constructors, structural type applications, storage,
and returns. A
missing, duplicate, unconsumed, wrong-owner, wrong-position, wrong-order,
wrong-kind, wrong-method, type-variable-capturing, or mismatched authentication
relation fails Core validation before evaluation.

For every newtype conversion, independent validation derives the expected
relation from the linked canonical fact and the child and enclosing expression
types. It checks a newtype owner, complete nominal application, positional
argument kinds, declared-order representation substitution, direction,
child/result agreement, and declaration and source provenance. It rejects an
ordinary constructor used as a conversion and a newtype constructor or pattern
lowered through ordinary allocating Core. Resolution and linked-summary
validation remain the exclusive authorities for source access and import
routes.

Every retained local nominal fact has exactly one matching scope introduction.
The introduction must have its canonical lexical owner and declaration origin.
Every use of a local identity in a type, row, effect argument, constructor,
pattern, conversion, or operation metadata must lie beneath its introduction.
The scope node's own result type and row must not contain its owner. Dependencies
of the canonical representation must already be in scope at that declaration,
including preceding local nominals and enclosing type parameters, even when
the constructor is unused. Its own declared parameters remain bound only by
the representation template.

Validation rejects missing, duplicate, unmatched, wrong-owner, out-of-scope,
and escaping scope relations before evaluation. Identity traversal and folding
preserve or rebuild the unary scope, conversions, and their metadata and return
the program to independent validation. A scope node contributes no effect-row
member and does not change effect-row algebra.

Validation distinguishes unary structural monotype applications from Core
type applications. A Core type application supplies one argument per quantified
binder in order, each argument synthesizes that binder's kind, and the annotated
result equals simultaneous substitution into the kind-`Type` scheme body.
Inference variables and constructor-kinded ordinary value annotations cannot
cross this boundary.

One cumulative validator resource ledger covers the registry, envelope, graph,
binder, node, term-scope, and type-scope passes. It is neither reset between
passes nor supplemented by a separate kind allowance. Core validation applies
once to the whole linked Core program, including every module group and the
generated entry application. Effect instances, rows, operations, clauses,
resume owners, handler scopes, capture metadata and capture queries charge
that same ledger before retention or
traversal. Failure of this boundary is an internal compiler failure, not a
source-language typing result.

This requirement does not prescribe a Rust representation, storage strategy,
or evaluator mechanism.

Identity traversal and primitive folding preserve or rebuild conversions,
their types, identities, direction, child, and origin. A transformed program
returns to this independent validation boundary before evaluation.
