# CP-0014: Local `newtype`

- ID: `CP-0014`
- Status: accepted
- Related:
  - [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md)
  - [DN-0027](../design/DN-0027-effect-ash-program-design.md)
  - [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md)
  - [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md)
  - [AD-0007](../decisions/AD-0007-typed-core-dialects.md)
  - [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This proposal is not current Ash.

## Current behavior

Ash admits `newtype` only as a module declaration. Each declaration introduces
one stable module-owned nominal identity and one same-spelled constructor over
one representation field. Explicit construction and matching cross an
independently validated Core conversion and erase without allocation.

A block contains sequential `let` declarations and explicit `let rec` groups.
Term bindings use lexical scope, but types and constructors come from the
module and its imports. Eligible local function bindings may generalize
inference variables; no local declaration introduces a rigid nominal identity.

Consequently, a function cannot create a nominal distinction whose name and
constructor are confined to one lexical remainder. Module `newtype` adds no
local type declaration, runtime-fresh identity, local implementation search,
or existential package.

## Proposed behavior

### Declaration and sequential scope

A block may contain the module `newtype` shape without visibility syntax:

```ebnf
local_declaration ::=
    local_binding
  | recursive_binding_group
  | local_newtype_declaration ;
local_newtype_declaration ::=
  "newtype" upper_identifier [ type_parameters ] "="
  upper_identifier "(" type ")" ;
```

`pub` and `opaque` remain module-only. A local declaration has exactly one
same-spelled constructor and one representation field. Existing parameter,
constructor-name, and representation-kind rules apply.

The declaration is sequential. Its nominal name and constructor enter scope
only for the following declarations and result of the containing block. Its
representation resolves in the preceding lexical type scope extended with its
own parameters. The declaration therefore cannot refer to itself or to a later
local `newtype`. If its spelling shadows an earlier nominal, that earlier
identity remains the meaning of the spelling inside the new representation.

A later local `newtype` may shadow an earlier local or module nominal and its
constructor. The two namespaces change together at the declaration boundary.
Equal spelling, parameters, or representation does not equate the identities.
Leaving the block restores both preceding name bindings atomically.

A local `newtype` is not a member of `let rec`, and local nominal declarations
do not form mutually recursive groups. A declaration may precede a recursive
term group, and that group may use the local nominal and constructor.

### Identity and representation

Resolution allocates one stable, module-qualified lexical nominal identity per
source declaration. Allocation happens once while compiling the declaration,
not each time its block, function, generalized binding, or recursive member
executes. A constructor retains its existing owner-and-ordinal relationship to
that nominal identity.

Lexical ownership is distinct from module-declaration ownership. The shared
nominal identity carrier distinguishes those owners while type equality,
application, kinding, substitution, unification, constructor typing, pattern
typing, and representation conversion continue to use the existing nominal
machinery.

The existing ordered fixed-kinded parameters scope over the representation.
The fully applied representation must have kind `Type`. It may mention
preceding lexical nominals, module or imported nominals, structural types, and
effectful function codomains under the existing rules. Sequential scope makes
a local-only representation cycle impossible, so this change adds no second
cycle analysis.

Local canonical facts remain compiler authority for their checked module and
linked Core. They do not enter public summaries, imports, re-exports, module
visibility, implementation ownership, or source name lookup outside their
lexical scope.

### Typing, generalization, and escape

An accessible local constructor has the same rank-1 scheme, explicit wrap,
irrefutable pattern, nominal distinction, and representation erasure as a
module `newtype`. Representation interface evidence does not transfer to the
local nominal.

The local nominal identity is a rigid constant. Generalization never quantifies
it or replaces it with a type variable. Existing eligible-local generalization
may still quantify unrelated inference variables, and polymorphic functions
may consume a local nominal while returning a type that does not mention it.

When a local nominal scope closes, the compiler zonks the outward computation
and rejects it with `type.local-nominal-escape` if the identity occurs anywhere
in its value type, effect row, generalized scheme, or requirements. The primary
label identifies the expression or binding whose outward type escapes; a
related label identifies the local declaration. Traversal includes function
domains and codomains, tuple members, nominal applications, effect arguments,
and row structure.

This rule rejects:

- returning a value of the local nominal type;
- returning its constructor or any function whose exposed domain, codomain, or
  effect row mentions the identity;
- placing the identity inside another outward type or requirement; and
- inferring a hidden local nominal outside the block, including a pair of a
  hidden value and an eliminator.

The last case would be an implicit existential package, which this proposal
does not add. Using the constructor name or nominal name after the block
instead fails under existing name-resolution ownership.

An escaping closure is valid when its exposed type, effect row, and
requirements do not contain the identity, even if its code captures a local
value and unwraps it. For example:

```ash
make : Unit -> (Unit -> Int)
make () = {
    newtype Offset = Offset(Int)
    let offset = Offset(41)
    fn(ignored) {
        match offset {
            Offset(value) => value + 1
        }
    }
}
```

Callers see only `Unit -> Int`; they cannot name, construct, inspect, or mix the
captured identity. Unwrapping and returning the representation, or consuming a
local value through an ordinary polymorphic function and returning an
identity-free result, is likewise valid.

### Core scope and erasure

Elaboration retains each local canonical nominal fact and lowers construction
and matching through the existing `NewtypeConversionNode`. It adds one unary
pure Core scope carrier around the lexical remainder. The carrier records the
local owner and its child; it has no initializer, value, effect row contribution,
or runtime state.

Independent Core validation requires exactly one matching scope introduction
for every retained local nominal fact. Every occurrence of the identity in
types, effect arguments, constructors, patterns, conversions, and operation
metadata must occur beneath that introduction. A scope carrier's own result
type and row must not contain its identity. Validation rejects a missing,
duplicate, unmatched, wrong-owner, or escaping scope relation before
evaluation.

The identity and folding transforms preserve or rebuild the unary carrier and
return the result to independent validation. Evaluation enters its child
directly, as it does for a validated representation conversion. It allocates
no heap cell, environment entry, continuation frame, runtime identity, or
registry state. An identity-free escaping closure therefore carries only its
ordinary erased representation values and lexical code.

### Failure ownership and resources

Parsing owns malformed local declaration shape and recovery. Resolution owns
constructor spelling, parameter and type names, sequential visibility, lexical
identity allocation, and source-scope teardown. Kind checking owns parameter
and representation kinds. Type checking owns `type.local-nominal-escape` after
zonking the closing outward type. Core construction and validation own forged
or inconsistent retained facts and scope relations only after source checking
succeeds.

Existing syntax, type-work, constraint-work, and Core budgets own the work in
their phases. New lexical name entries, local canonical facts, scope carriers,
and validator scope requirements charge before allocation or publication.
Representation traversal, substitution, kinding, conversions, and type escape
inspection reuse their existing iterative type operations and ledgers.

The implementation task must retain exact-success, one-unit-short failure,
retry, atomic scope teardown, and deep accepted and rejected evidence for each
new carrier. Failure publishes no checked module or partial lexical fact. This
proposal authorizes no production limit increase.

## Semantic delta

- Blocks admit sequential, private local `newtype` declarations.
- Each declaration introduces one stable compile-time lexical nominal identity
  and same-spelled constructor for the block remainder.
- Later declarations may shadow earlier nominal and constructor bindings;
  representations see only the preceding lexical type scope and their own
  parameters.
- Local identities are rigid and never generalized. Any occurrence in an
  outward type, row, scheme, or requirement is rejected.
- A closure may escape when its exposed computation is identity-free, even if
  its code captures and unwraps an erased local value.
- One independently validated, runtime-erased Core scope carrier authenticates
  local facts and conversions.

## Affected specification areas

- [Syntax grammar](../../spec/syntax.md#grammar) adds the local declaration.
- [Type binder identity and scope](../../spec/name-resolution.md#type-binder-identity-and-scope),
  [Type and constructor scope](../../spec/name-resolution.md#type-and-constructor-scope),
  and [Local scope](../../spec/name-resolution.md#local-scope) define lexical
  identity, sequential visibility, shadowing, and recursion exclusion.
- [Kinds, monotypes, and schemes](../../spec/static-semantics.md#kinds-monotypes-and-schemes),
  [Blocks](../../spec/static-semantics.md#blocks), and
  [Inference and rank-1 restrictions](../../spec/static-semantics.md#inference-and-rank-1-restrictions)
  define representation admission, rigid identity, generalization, and escape.
- [Failure ownership and constraint resources](../../spec/static-semantics.md#failure-ownership-and-constraint-resources)
  assigns diagnostics, precedence, and resource ownership.
- [Surface erasure](../../spec/elaboration.md#surface-erasure),
  [Module linking and entry generation](../../spec/elaboration.md#module-linking-and-entry-generation),
  [Explicit rank-1 operations](../../spec/elaboration.md#explicit-rank-1-operations),
  and [Validation boundary](../../spec/elaboration.md#validation-boundary)
  define retained local facts, conversion reuse, scope lowering, transforms,
  and independent authentication.
- [Type erasure](../../spec/dynamic-semantics.md#type-erasure) and
  [Tuples, constructors, and matches](../../spec/dynamic-semantics.md#tuples-constructors-and-matches)
  define unchanged allocation-free execution.
- [Specification overview](../../spec/README.md) records the capability and its
  exclusions.

## Resulting specification truth

After the complete product checkpoint integrates into `main`, a block may
introduce a private nominal representation identity for its lexical remainder.
The identity is stable for the source declaration, distinct from every module
or lexical nominal, and erased at runtime. Explicit construction and matching
reuse the module-`newtype` conversion semantics without allocation.

The identity cannot escape through a type, effect row, scheme, requirement, or
implicit package. A closure whose exposed computation is identity-free may
capture the erased value and use its conversion authority in code retained
beneath the local Core scope.

## Interactions

The change extends the nominal owner and registry boundary but does not add a
second parser, type algebra, unifier, constructor pipeline, conversion form,
or evaluator mechanism. Module `newtype`, ordinary local binding,
generalization, effect-row traversal, and closure capture remain the reusable
predecessors.

Scoped exact evidence may later use the lexical identity as an exact type, but
this proposal adds no local `impl`, evidence declaration, selection precedence,
or proof escape. Runtime resource acquisition may later require an identity
fresh per execution; the static identity introduced here is not that identity
and carries no handle or lifetime state.

## Non-goals

- local `type`, `effect`, `interface`, or `impl` declarations;
- mutually recursive or self-recursive local nominal declarations;
- implicit existential packaging or source-denotable existential types;
- per-call or runtime-fresh identities;
- representation-derived implementations, coercions, or subtyping;
- resource ownership, affine usage, checked discard, providers, hooks,
  cleanup, dynamic loading, concurrency, or asynchronous execution; and
- a general Core authority-scope framework.

## Required evidence

The product checkpoint must establish:

- syntax projection and recovery for the exact local form without admitting
  local visibility modifiers or other declaration families;
- sequential visibility, restoration, nesting, sibling distinctness,
  shadowing, outer-name use in a representation, and rejection of self or
  forward reference;
- parameter kinding, explicit wrap and irrefutable unwrap, distinct identities
  over equal representations, ordinary polymorphic consumption, and unchanged
  nominal interface evidence;
- the complete escape matrix: direct values, constructors, nested type
  positions, function domains and codomains, effect arguments, generalized
  schemes, identity-free representation results, accepted identity-free
  closure capture, exposed closure rejection, and excluded implicit
  existential packaging;
- use by a following `let rec` group while local `newtype` remains excluded
  from recursive-group membership;
- canonical local-fact retention without summary, import, export, or local
  implementation-search exposure;
- Core rejection of missing, duplicate, wrong-owner, escaping, and forged
  scope or conversion facts before runtime;
- preservation and revalidation through both Core transforms;
- deterministic representation execution, no wrapper allocation, and no
  runtime identity or scope state, including an escaping identity-free
  closure;
- exact resource success, one-unit-short atomic failure, retry, and iterative
  deep teardown for lexical facts and Core scope work; and
- the existing module-`newtype`, local binding, generalization, effect,
  pure-Core, transform, evaluator, and diagnostic corpora unchanged.
