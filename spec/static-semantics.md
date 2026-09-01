# Static Semantics

Ash has `Int`, `Bool`, `Unit`, rigid type variables, structural tuples,
parameterized nominal algebraic data types, unary functions, and effect rows. A
tuple contains at least two element types. A function has a value domain and a
computation codomain `A ! epsilon`, where `A` is a value type and `epsilon` is
an effect row. Source kinds contain `Type`, `EffectRow`, and right-associative
function kinds, subject to the binder restrictions below.

Type equality is one shared rule. `Int`, `Bool`, and `Unit` equal themselves;
tuples, term functions and their computation codomains, and unary type
applications compare structurally; type
variables compare by binder identity; nominal constructors compare by stable
declaration identity. Equal spelling or constructor shape does not make two
nominal declarations equal. Interface requirements are constraints rather
than monotypes. They do not participate in monotype equality or ordinary
unification. Effect rows are computation requirements rather than interface
requirements and never select implementation evidence.

The typing environment `GAMMA` maps resolved `BinderId` identities to rank-1
constrained schemes. Interface methods do not have binder identities. The
immutable method registry `MU` instead maps each resolved `MethodId` to its
owning `InterfaceId`, ordered interface parameters, optional determinant
positions, ordered method-local parameters, declared method value type,
declaration order, and provenance. A constrained
scheme has three fields:

```text
ConstrainedScheme =
    ordered outer (TypeVariableId, Kind) parameters
    ordered interface requirements
    source value type
```

The outer parameters quantify only the value type and the types within the
requirements. Looking up a scheme replaces every quantified parameter with a
fresh inference variable of the same fixed kind, instantiates the value type,
and creates one evidence obligation for each requirement in source order. A
scheme with no requirements has the ordinary `forall parameters. type`
behavior. Rigid variables from annotations never unify with a different type.

One registry method has a distinct method scheme under its owning interface
parameter vector:

```text
MethodScheme = forall method_parameters. method_value_type
```

The interface parameters remain free relative to this scheme and are owned by
the enclosing interface. A method scheme never enters `GAMMA`, and no source
occurrence can name it without instantiating every method parameter.

The immutable effect registry `PHI` maps every accessible `EffectId` to its
ordered fixed-kinded parameters, ordered operations, visibility, and
provenance. Each operation record contains its stable `OperationId`, spelling,
and one pure value-function type. `PHI` authenticates operation typing; it is
not a provider environment or handler registry.

The judgment `GAMMA |- expression ⇒ A ! epsilon` synthesizes a value type and
effect row, while `GAMMA |- expression ⇐ A ! epsilon` checks an expression
against an expected computation type.
These judgments also consult the fixed method registry `MU` and record pending
requirements on the exact constrained-term occurrences that create them. The
ordinary rules omit `MU`, `PHI`, and that structural output. The interface
section defines the distinct method-occurrence rule, and the selection section
defines how a definition closes the pending requirements.

## Kinds, monotypes, and schemes

Four environments determine value-type kinds, and `PHI` determines effect
instance formation:

- `DELTA` maps every in-scope resolved `TypeVariableId` to exactly one declared
  kind;
- `OMEGA` maps every live `InferenceVariableId` to exactly one fixed kind;
- `XI` maps every accessible `NominalTypeId` to its constructor kind; and
- `IOTA` maps every accessible `InterfaceId` to its nonempty ordered canonical
  parameter records and optional ordered determinant positions.

A nominal declared with ordered parameter kinds `kind_1` through `kind_n` has
the constructor kind obtained by the right fold
`kind_1 -> ... -> kind_n -> Type`. The declaration's ordered parameter records
are authoritative; any retained nominal-kind cache must equal this derivation.
Imported nominal and interface kinds come from authenticated body-free summary
facts and retain their defining identities.

The total synthesis judgment
`DELTA; OMEGA; XI |- monotype => kind` assigns a kind to every well-formed
monotype. `PHI` is an ambient input used when synthesis reaches a computation
codomain; the ordinary judgment omits it. `all_type` means that each listed
monotype synthesizes `Type` under the supplied environments. The last two rules
are owning checks: ordinary value positions require `Type`, while an interface
constraint requires one complete argument per declared interface parameter and
the corresponding kind at every position. Arity is checked before any
positional kind.

```sequent
family kind-synthesis:
  K-Primitive :=
    primitive in {Int, Bool, Unit}
    ===>
    DELTA; OMEGA; XI |- primitive => Type

  K-Variable :=
    DELTA(variable) = kind
    ===>
    DELTA; OMEGA; XI |- variable => kind

  K-Inference :=
    OMEGA(inference) = kind
    ===>
    DELTA; OMEGA; XI |- inference => kind

  K-Nominal :=
    XI(nominal) = kind
    ===>
    DELTA; OMEGA; XI |- nominal => kind

  K-Application :=
    DELTA; OMEGA; XI |- function_type => argument_kind -> result_kind
    DELTA; OMEGA; XI |- argument_type => argument_kind
    ===>
    DELTA; OMEGA; XI |- Apply(function_type, argument_type) => result_kind

  K-Tuple :=
    all_type(DELTA, OMEGA, XI, elements)
    ===>
    DELTA; OMEGA; XI |- Tuple(elements) => Type

  K-Function :=
    DELTA; OMEGA; XI |- domain => Type
    DELTA; OMEGA; XI; PHI |- codomain computation ok
    ===>
    DELTA; OMEGA; XI |- Function(domain, codomain) => Type

  K-Value-Type :=
    DELTA; OMEGA; XI |- monotype => Type
    ===>
    DELTA; OMEGA; XI |- value monotype ok

  K-Interface-Argument :=
    IOTA(interface) = (parameters, determination)
    length(arguments) = length(parameters)
    for each corresponding (argument_i, parameter_i),
      DELTA; OMEGA; XI |- argument_i => kind(parameter_i)
    ===>
    DELTA; OMEGA; XI; IOTA |- constraint Interface(arguments) ok
```

An unsaturated nominal constructor synthesizes its derived function kind. A
partial application synthesizes its residual kind. Either form is valid when
the owning rule accepts that kind. Resolution represents every admitted named
application as repeated unary `Apply(function_type, argument_type)` nodes,
folded from left to right. Equality, substitution, unification, occurs checks,
implementation matching, summary authentication, and validation use this
structural and injective form. Both the function and argument are immediate
strict subterms of an application.

Constructor payloads, global and method value types, pattern and term-binder
types, source expression types, entry results, and ordinary Core value
annotations use `K-Value-Type`. Requirements, method obligations,
implementation heads and prerequisites, and evidence goals use
`K-Interface-Argument`. An interface constraint has no monotype kind of its
own. An interface parameter without an annotation has kind `Type`, which
recovers the predecessor behavior at that argument position.

A scheme is distinct from a monotype and has no ordinary kind. It has the form
`forall (A_1 : kind_1) ... (A_n : kind_n). body`, with distinct binders and a
body accepted by `K-Value-Type` under the extended `DELTA`. A scheme cannot
occur as a type-application argument, tuple element, term-function domain or
codomain, term-binder type, or any other source monotype. A method scheme
remains separate in `MU`; the elaboration specification defines its sole
authenticated compiler-generated Core evidence position.

`EffectRow` is valid only as the complete kind of a global parameter or an
eligible generalized-local parameter. It cannot be the domain or codomain of a
kind arrow. Nominal, interface, implementation, effect, and method parameter
lists admit only their existing ordinary kinds. A row tail must resolve to a
global or eligible generalized-local parameter of kind `EffectRow`; a row
variable cannot occur in an ordinary value position, nominal or interface
argument, effect argument, or pattern.

Every omitted declaration kind annotation, and every binder introduced by an omitted global or implementation binder list, is fixed to `Type`. Ash does not infer a kind for those binders. This is the current phase-dependent language constraint, not a commitment against a later bounded declaration-local inference rule.

### Computation types and effect rows

An effect instance is one stable `EffectId` plus a complete ordered vector of
type arguments. Its arguments must match the declaration's arity and positional
kinds. Two instances are equal only when their identities and all zonked
arguments are structurally equal. An effect row is an unordered idempotent set
of exact instances with at most one open tail. Source order does not affect row
equality or handler order. Rendering orders known members canonically by exact
identity and structural arguments; that presentation order has no semantic
effect.

The following rules form effect instances, rows, and computation types.
`distinct_exact` compares the resolved identity and all zonked arguments.
`lacks(R)` is the set of instances known absent from the row variable `R`.

```sequent
family effect-row-formation:
  WF-Effect-Instance :=
    PHI(effect) = parameters, operations, visibility, provenance
    length(arguments) = length(parameters)
    for each corresponding (argument_i, parameter_i),
      DELTA; OMEGA; XI |- argument_i => kind(parameter_i)
    ===>
    DELTA; OMEGA; XI; PHI |- effect<arguments> instance ok

  WF-Closed-Effect-Row :=
    for each member_i,
      DELTA; OMEGA; XI; PHI |- member_i instance ok
    distinct_exact(members)
    ===>
    DELTA; OMEGA; XI; PHI |- { members } row ok

  WF-Open-Effect-Row :=
    DELTA(row_variable) = EffectRow
    for each member_i,
      DELTA; OMEGA; XI; PHI |- member_i instance ok
    distinct_exact(members)
    members subset-of lacks(row_variable)
    ===>
    DELTA; OMEGA; XI; PHI |- { members | row_variable } row ok

  WF-Computation :=
    DELTA; OMEGA; XI |- value_type => Type
    DELTA; OMEGA; XI; PHI |- effects row ok
    ===>
    DELTA; OMEGA; XI; PHI |- value_type ! effects computation ok
```

`WF-Effect-Instance` checks arity before positional kinds. The row rules reject
a repeated written member as `effect.duplicate`, even though inferred row
operations coalesce equal members. `WF-Open-Effect-Row` records that every
written known member is absent from its tail. `WF-Computation` keeps rows out of
ordinary value positions.

Row equality ignores known-member order and multiplicity after inference. Open
rows are equal only when their known sets, tail identity, and accumulated lacks
facts are equal after substitution. Type substitution descends through every
effect argument. Row substitution replaces a tail only with a row of kind
`EffectRow`, unions the replacement's known members with the enclosing known
members, and preserves all accumulated lacks facts. It rejects an occurs check
or any replacement containing an instance forbidden by those facts.

Row unification is kind-preserving first-order unification: it succeeds exactly
when a substitution makes both rows equal without violating an occurs check or
lacks fact. It aligns known members by exact instance identity and structurally
unifies their arguments. It never equates distinct effect identities or invents
a lacks fact.

Write `epsilon_1 union epsilon_2` for partial inferred union. It coalesces equal
known members. It succeeds for closed rows, and may retain one open tail only
when substitution has made the tails identical or closed the other tail and
every added known member is already absent from the retained tail. Two distinct
unsolved tails, or a member not known absent from a retained tail, produce
`effect.row-union-ambiguous`. An expected row may supply an existing lacks fact;
union never strengthens a tail merely to make the operation succeed. Schemes
retain no qualified row-union or membership constraints.

Effect weakening permits a computation inferred as `A ! epsilon_1` to check as
`A ! epsilon_2` when every requirement of `epsilon_1` is present in
`epsilon_2` under the same tail constraints. Synthesis retains the least row
established by the expression rules; weakening applies only while checking
against an expected computation. Exact removal
`epsilon remove E` removes only an explicitly established exact instance. Thus
`{E | R} remove E = {| R}`; removing a different instance from a closed row is
missing, and searching an unconstrained open tail is ambiguous. No rule removes
an effect by spelling or API shape. Rows have no semantic order or
multiplicity, effect subtyping or masking, or implicit removal. Weakening is a
checking relation; it does not change a synthesized least row.

Surface `A -> B` denotes `Function(A, B ! {})`. A written row changes only the
complete computation codomain to which it attaches. Consequently,
`A -> B -> C ! {E}` is a pure call from `A` returning a function whose call may
request `E`, while `A -> (B -> C) ! {E}` may request `E` while returning a pure
function.

The executable tests
`closed_rows_are_unordered_idempotent_exact_instance_sets`,
`substitution_reaches_exact_arguments_and_preserves_row_lacks`,
`open_row_union_requires_an_existing_lacks_fact`, and
`exact_removal_does_not_remove_another_instance_or_search_an_unknown_tail`
check the row algebra. `row_inference_unifies_exact_members_and_rejects_occurs`
checks row unification and its occurs check.

The executable test
`static_semantics_kind_synthesis_and_interface_argument_are_executable` checks
a higher-kinded interface argument, higher-kinded globals, and ordinary
execution:

```ash
type Option<A> =
    None
    | Some(A)

interface Transform<F : Type -> Type> {
    transform : (Int -> Int, F<Int>) -> F<Int>
}

impl Transform<Option> {
    transform (function, None) = None
    transform (function, Some(value)) = Some(function(value))
}

increment : Int -> Int
increment value = value + 1

apply_transform<F : Type -> Type> : (Int -> Int, F<Int>) -> F<Int> where Transform<F>
apply_transform pair = transform pair

fn relay<F : Type -> Type, A>(value : F<A>) -> F<A> {
    value
}

main : Unit -> (Option<Int>, Bool, Unit)
main () = (relay(apply_transform((increment, Some(41)))), true, ())
```

Kind failures retain structured expected and found kinds and the causal source
site. The following three executable examples distinguish the owning rules.
The unsaturated constructor in a value type is `kind.expected-type`:

```ash
type Option<A> =
    None
    | Some(A)

bad : Unit -> Option
bad () = None

main : Unit -> Unit
main () = ()
```

The implicit `F` binder is fixed to `Type`, so applying it is
`kind.not-applicable` rather than an invitation to infer a function kind:

```ash
legacy : F<Int> -> Unit
legacy value = ()

main : Unit -> Unit
main () = ()
```

The final example passes `Int` to an interface parameter declared with kind
`Type -> Type`, so it is `kind.argument`:

```ash
interface Higher<F : Type -> Type> {
    higher : F<Int> -> Unit
}

bad : Unit -> Unit where Higher<Int>
bad value = value

main : Unit -> Unit
main () = ()
```

### Row lifting for existing expression rules

The expression rules below use one row-lifting convention where they retain a
predecessor judgment without an explicit row. A literal, variable occurrence,
constructor occurrence, or function creation has row `{}`. An ordinary strict
form with evaluated expression children `e_1` through `e_n` has the partial
union of their rows, accumulated in the existing left-to-right checking order.
A match has the scrutinee row unioned with every arm-body row. A block has every
initializer row unioned with its remainder row. A checking judgment also
requires the synthesized row to weaken to the expected row. The value-type,
pattern, coverage, and interface-obligation premises remain unchanged.

Thus every later displayed `GAMMA |- e ⇒ A` abbreviates
`GAMMA |- e ⇒ A ! effects(e)`, and every `GAMMA |- e ⇐ A` abbreviates checking
against the computation expected at that site. The convention does not apply to
application, operation request, handler, or resume; their row equations are
stated explicitly. Partial union failure is
`effect.row-union-ambiguous`. Union records requirements and does not license
evaluation reordering.

## Primitive expressions

Literals and resolved variables synthesize types. Any expression that
synthesizes a structurally equal type checks against that expected type.

```sequent
family primitive-typing:
  T-Int :=
    ===>
    GAMMA |- n ⇒ Int

  T-Bool :=
    ===>
    GAMMA |- b ⇒ Bool

  T-Unit :=
    ===>
    GAMMA |- () ⇒ Unit

  T-Variable :=
    x : scheme in GAMMA
    instantiate(scheme) = type, obligations
    record_pending(occurrence(x), obligations)
    ===>
    GAMMA |- x ⇒ type

  T-Check-Inferred :=
    GAMMA |- expression ⇒ type_1
    type_1 = type_2
    ===>
    GAMMA |- expression ⇐ type_2
```

Here `n` ranges over integer literals, `b` over Boolean literals, and `x` over
resolved binder occurrences. `T-Variable` consults `GAMMA` by `BinderId`.
`instantiate` replaces all outer quantified variables at once and applies the
same substitution to the ordered requirements. An unconstrained occurrence
records an empty obligation sequence. The equality premise in
`T-Check-Inferred` uses the single type-equality rule above after inference
solutions are applied.

## Tuples and constructors

Tuple elements synthesize from left to right. A constructor declaration under
`Owner<A_1, ..., A_n>` contributes a scheme quantified over those declaration
parameters and their declared kinds. The payload and fully applied owner both
have kind `Type`; a data constructor has this checked rank-1 term scheme rather
than a separate constructor kind. Instantiating a nullary constructor produces
the applied owner type. Instantiating a payload constructor produces an
ordinary unary term function from its substituted semantic payload to that
owner. Multiple declared fields form one tuple payload.

```sequent
family data-typing:
  T-Tuple :=
    for each i, GAMMA |- element_i ⇒ type_i
    n >= 2
    ===>
    GAMMA |- (element_1, ..., element_n) ⇒ Tuple(type_1, ..., type_n)

  T-Nullary-Constructor :=
    constructor : forall parameters. Constructor(owner<parameters>, none)
    instantiate(parameters, owner<parameters>) = owner<arguments>
    ===>
    GAMMA |- constructor ⇒ owner<arguments>

  T-Payload-Constructor :=
    constructor : forall parameters. Constructor(owner<parameters>, payload)
    instantiate(parameters, Function(payload, owner<parameters>)) = constructor_type
    ===>
    GAMMA |- constructor ⇒ constructor_type
```

The constructor premises consult the immutable registry produced by name
resolution. Constructor application then follows `T-Apply`; it does not have a
special call rule.

## Functions and application

An anonymous function checks only when an expected function type supplies its
parameter and computation result. Function creation is pure; the body row is
stored in the function's latent computation codomain. Application first
synthesizes the function, then checks the argument against its domain, and
unions both strict-child rows with that latent row.

```sequent
family function-typing:
  T-Effectful-Function-Check :=
    pattern ⇐ domain => bindings
    exhaustive([pattern], domain)
    GAMMA, bindings |- body ⇐ codomain ! body_effects
    ===>
    GAMMA |- fn(pattern) { body }
      ⇐ Function(domain, codomain ! body_effects) ! {}

  T-Effectful-Apply :=
    GAMMA |- function
      ⇒ Function(domain, codomain ! call_effects) ! function_effects
    GAMMA |- argument ⇐ domain ! argument_effects
    result_effects
      = function_effects union argument_effects union call_effects
    ===>
    GAMMA |- function argument ⇒ codomain ! result_effects
```

`T-Effectful-Function-Check` preserves the existing pattern and coverage
checks. `T-Effectful-Apply` preserves strict evaluation order even though its
effect row is unordered. Any partial union failure follows the row-algebra rule
above.

An anonymous function normally checks from an expected function type. The one
additional synthesis site is an unannotated local binding whose initializer is
syntactically an anonymous function. That site allocates fresh inference
variables for the domain and codomain, checks the function, and applies the
local-generalization rule below. An anonymous function in any other synthesis
position is rejected with `type.function-needs-context`. The parameter position
is a pattern. Two or more syntactic parameters form one tuple pattern and
consume one tuple domain.
Because an anonymous or operational function has no alternate clauses,
`exhaustive([pattern], domain)` requires its singleton domain pattern to be
irrefutable under the same usefulness analysis as a local binding. The
`bindings` returned by pattern checking, rather than one distinguished binder,
extend the function body environment.

## Patterns, matches, and coverage

The judgment `pattern ⇐ type => bindings` checks a pattern against an expected
type and returns its typed binders. Wildcards return no binders. Boolean and
unit patterns require their corresponding primitive types. Tuple patterns
require equal tuple arity. A constructor pattern must belong to the expected
nominal type and must agree with the constructor's payload shape. Pattern
binders are pairwise distinct.

A match synthesizes its scrutinee once, checks every arm pattern against that
type, and gives the resulting bindings only to that arm body. All arm bodies
have one type. The typed usefulness relation over closed nominal sums, tuples,
`Bool`, `Unit`, binders, and wildcards must find each arm useful and must find
no witness outside all arms. A useless arm is rejected with
`coverage.redundant-case`; a remaining witness is reported with
`coverage.non-exhaustive`.

For a local or imported transparent nominal, coverage uses its complete
constructor family. An imported opaque or hidden nominal has no accessible
constructor pattern and is not treated as an empty sum. A binder or wildcard
can cover such a value without inspecting its representation.

```sequent
family match-typing:
  T-Match-Synthesize :=
    GAMMA |- scrutinee ⇒ input_type
    for each i, pattern_i ⇐ input_type => bindings_i
    for each i, useful(previous_patterns_i, pattern_i, input_type)
    GAMMA, bindings_1 |- body_1 ⇒ result_type
    for each i > 1, GAMMA, bindings_i |- body_i ⇐ result_type
    exhaustive(all_patterns, input_type)
    ===>
    GAMMA |- match scrutinee { arms } ⇒ result_type

  T-Match-Check :=
    GAMMA |- scrutinee ⇒ input_type
    for each i, pattern_i ⇐ input_type => bindings_i
    for each i, useful(previous_patterns_i, pattern_i, input_type)
    for each i, GAMMA, bindings_i |- body_i ⇐ expected_type
    exhaustive(all_patterns, input_type)
    ===>
    GAMMA |- match scrutinee { arms } ⇐ expected_type
```

A match has at least one arm. `T-Match-Synthesize` obtains its result type from
the first arm and checks every later arm against that type.
`T-Match-Check` propagates a result type supplied by the surrounding context to
every arm, including the first. This admits anonymous functions and other
checking-only forms in all arms when their context supplies a type.

The executable test
`static_semantics_contextual_match_checks_function_arms` checks this propagation:

```ash
fn choose(flag : Bool) -> Int -> Int {
    match flag {
        true => fn(value) {
            value + 1
        }
        false => fn(value) {
            value * 2
        }
    }
}

main : Unit -> Int
main () = choose true 41
```

The same usefulness relation checks equation groups. Each equation pattern
consumes one arrow domain, so `f left right = body` checks against two nested
arrows. All clauses have the same positive pattern count. The relation also
defines local-pattern irrefutability: a local `let` pattern is admitted only
when its singleton pattern set covers the initializer type.

The executable test `static_semantics_irrefutable_tuple_binding_is_executable`
checks local destructuring:

```ash
main : Unit -> Int
main () = {
    let (left, right) = (20, 22)
    left + right
}
```

## Blocks

Block bindings are checked from left to right. An annotated initializer checks
against its annotation. An unannotated initializer must synthesize its binding
type. The new pattern bindings are available only in the remainder. A block can
synthesize from its result or check by passing an expected type to its result.

```sequent
family block-typing:
  T-Block-Result :=
    GAMMA |- result ⇒ result_type
    ===>
    GAMMA |- { result } ⇒ result_type

  T-Block-Let-Inferred :=
    GAMMA |- initializer ⇒ binding_type
    pattern ⇐ binding_type => bindings
    exhaustive([pattern], binding_type)
    generalize_local(GAMMA, pattern, initializer, binding_type, bindings) = remainder_bindings
    GAMMA, remainder_bindings |- { remainder } ⇒ result_type
    ===>
    GAMMA |- { let pattern = initializer; remainder } ⇒ result_type

  T-Block-Let-Checked :=
    GAMMA |- initializer ⇐ binding_type
    pattern ⇐ binding_type => bindings
    exhaustive([pattern], binding_type)
    GAMMA, bindings |- { remainder } ⇒ result_type
    ===>
    GAMMA |- { let pattern : binding_type = initializer; remainder } ⇒ result_type

  T-Block-Check-Result :=
    GAMMA |- result ⇐ expected_type
    ===>
    GAMMA |- { result } ⇐ expected_type

  T-Block-Check-Let-Inferred :=
    GAMMA |- initializer ⇒ binding_type
    pattern ⇐ binding_type => bindings
    exhaustive([pattern], binding_type)
    generalize_local(GAMMA, pattern, initializer, binding_type, bindings) = remainder_bindings
    GAMMA, remainder_bindings |- { remainder } ⇐ expected_type
    ===>
    GAMMA |- { let pattern = initializer; remainder } ⇐ expected_type

  T-Block-Check-Let-Annotated :=
    GAMMA |- initializer ⇐ binding_type
    pattern ⇐ binding_type => bindings
    exhaustive([pattern], binding_type)
    GAMMA, bindings |- { remainder } ⇐ expected_type
    ===>
    GAMMA |- { let pattern : binding_type = initializer; remainder } ⇐ expected_type
```

`generalize_local` quantifies unsolved inference variables only when `pattern`
is one binder and `initializer` is syntactically an anonymous function. It
excludes inference variables free in `GAMMA` and preserves each selected
variable's fixed kind. Every other unannotated binding keeps the inferred
monotype, including an application that returns a function. An annotation
checks a monotype and introduces no type parameters. A use of a generalized
local binder instantiates its scheme as in `T-Variable`.

The first three rules synthesize a block type. The last three rules check a
block, carrying the expected type through its bindings to the result. Every
binding checks its complete pattern, requires that singleton pattern to cover
the initializer type, and extends the remainder with all returned bindings.
The checking rules overlap with `T-Check-Inferred` when the result synthesizes,
but also admit a result that itself needs an expected type, such as an anonymous
function. The semicolons in the binding conclusions separate semantic fields.
They do not add semicolon punctuation to Ash source.

The executable test
`static_semantics_contextual_block_example_is_executable` checks a block whose
anonymous-function result receives the binding annotation's expected type:

```ash
main : Unit -> Int
main () = {
    let constant : Unit -> Int = {
        fn(ignored) {
            1
        }
    }
    constant ()
}
```

The executable test
`static_semantics_higher_order_operational_example_is_executable` checks the
same rule path in an inline operational body with a function-valued result
annotation:

```ash
fn add(left : Int) -> Int -> Int {
    fn(right) {
        left + right
    }
}

main : Unit -> Int
main () = add 20 22
```

## Inference and rank-1 restrictions

Inference variables are compiler facts, not source types. Each inference
variable is registered in `OMEGA` with one fixed monomorphic kind before it
enters a type. Instantiating an outer scheme copies the corresponding declared
binder kind. Unification compares primitive and nominal identities, descends
structurally and injectively through unary applications, tuples, term
functions, computation codomains, and effect arguments, and checks kinds before
solving a variable. Row unification additionally applies the exact row algebra
and lacks constraints above. It may solve a
higher-kinded inference variable with a constructor or partial application of
the same kind. It cannot infer a kind, change the variable's registered kind,
synthesize a type lambda, abstract over mismatched application arguments, or
recover a missing or conflicting registry entry.

The occurs check visits both children of every unary application, each
computation row, and every effect argument, and rejects a solution containing
the variable being solved with `type.infinite`. While
checking one complete module, typing accumulates the substitution `THETA` and
records each allocated inference variable's causal origin in allocation order.
Successful module checking requires every allocated inference variable to
occur in the domain of `THETA`. Otherwise typing selects the first unsolved
identity in allocation order and reports `type.ambiguous` at its retained
causal origin. This check includes discarded expressions and unused
initializers. Every value-type and row inference variable must be solved or
generalized. Zonking removes every inference variable before a checked summary,
linked fact, or Core program is retained.

Global type parameters and generalized local parameters are rigid within their
definitions. A recursive self-use receives the same rigid arguments rather
than a fresh instantiation. A recursive call that would require a distinct
instantiation is rejected with `type.polymorphic-recursion`. Local recursive
annotations introduce no type parameters and remain monomorphic.

There are no source-denotable nested schemes or polymorphic function domains.
Generalization occurs only at global signatures and eligible local function
bindings. An eligible local may generalize inference variables of any fixed
monomorphic kind, but the variables remain outer scheme binders and the scheme
body must have kind `Type`. Source expressions cannot provide explicit type
arguments. Method schemes remain registry facts that each occurrence
instantiates; they do not make a polymorphic value available to source typing.
Global signatures may explicitly quantify complete `EffectRow` binders, and
the omitted global binder list discovers their first row-tail occurrences along
with ordinary type occurrences. Eligible local anonymous-function bindings may
generalize row variables not free in `GAMMA`, preserving their lacks facts.
Other local bindings remain monomorphic.

The executable test `static_semantics_rank_one_polymorphism_is_executable`
checks parameterized data, one implicitly quantified global, and one eligible
local generalization:

```ash
type Option<A> =
    None
    | Some(A)

id : A -> A
id value = value

main : Unit -> (Option<Int>, Bool)
main () = {
    let local = fn(value) {
        value
    }
    (id(Some(42)), local(false))
}
```

### Recursive block groups

Let `GAMMA_R` map every member of one nonempty recursive group to its required
declared monotype. All members enter the type environment before any initializer
is checked, and the same environment applies to the block remainder.

The initialization-safety judgment admits a direct anonymous function. It also
admits a data member when the initializer is rooted at a fully applied
constructor of the declared nominal type. A recursive occurrence under that
root may pass only through constructor or tuple construction, or occur in an
anonymous function body where evaluation delays it. A subtree with no
recursive occurrence may be any well-typed expression. An ordinary call,
primitive, match, or block cannot force or transport a recursive occurrence.

```sequent
family recursive-binding-typing:
  T-Block-Let-Rec-Synthesize :=
    GAMMA_R = { x_i : type_i | 1 <= i <= n }
    for each i, safe_rec(initializer_i)
    for each i, GAMMA, GAMMA_R |- initializer_i ⇐ type_i
    GAMMA, GAMMA_R |- { remainder } ⇒ result_type
    ===>
    GAMMA |- { let rec group; remainder } ⇒ result_type

  T-Block-Let-Rec-Check :=
    GAMMA_R = { x_i : type_i | 1 <= i <= n }
    for each i, safe_rec(initializer_i)
    for each i, GAMMA, GAMMA_R |- initializer_i ⇐ type_i
    GAMMA, GAMMA_R |- { remainder } ⇐ expected_type
    ===>
    GAMMA |- { let rec group; remainder } ⇐ expected_type
```

The semicolon separates the recursive declaration from the semantic remainder;
it is not Ash source punctuation. A nominal initializer without the required
constructor root is rejected with `recursion.unsafe-root`. A recursive
occurrence that crosses a forcing form is rejected with
`recursion.unguarded-use`.

The executable test
`static_semantics_rejects_unsafe_recursive_initialization` checks this rejected
program:

```ash
main : Unit -> Int
main () = {
    let rec value : Int = 1
    value
}
```

## Primitive operations

Addition and multiplication require two `Int` operands and synthesize `Int`.
Equality compares only integers and synthesizes `Bool`.

```sequent
family primitive-operation-typing:
  T-Add :=
    GAMMA |- left ⇐ Int
    GAMMA |- right ⇐ Int
    ===>
    GAMMA |- left + right ⇒ Int

  T-Multiply :=
    GAMMA |- left ⇐ Int
    GAMMA |- right ⇐ Int
    ===>
    GAMMA |- left * right ⇒ Int

  T-Integer-Equal :=
    GAMMA |- left ⇐ Int
    GAMMA |- right ⇐ Int
    ===>
    GAMMA |- left == right ⇒ Bool
```

The rules reject an operand that does not check as `Int`. The executable test
`static_semantics_operand_example_has_its_documented_reason` checks that this
module is rejected with `type.operator-operand`:

```ash
main : Unit -> Int
main () = true + 1
```

## Effects

An effect declaration has a possibly empty ordered parameter vector and a
nonempty ordered operation vector. Its parameters have the ordinary fixed
kinds already admitted for nominal declarations; none has kind `EffectRow`.
Operation spellings are unique within the declaration. Each operation type has
exactly one outer pure function arrow `P -> Q`, where `P` and `Q` are value
types formed under the effect's parameters. An operation has no local
parameters, requirements, body, or independently selectable visibility. A
public effect exports the whole authenticated API; a private effect remains
local.

Resolution assigns one stable `EffectId` from the defining module and
declaration order, and one stable `OperationId` from its owner and operation
order. Static checking authenticates those identities and the ordered
parameters and operation types in `PHI`. Equal spellings or signatures in two
modules remain distinct identities.

For an operation request, substituting the target effect instance's arguments
into the declared operation type produces its value domain and result. The
operand is evaluated first, and the request adds that exact instance to its
row.

```sequent
T-Perform :=
  operation_type(E<arguments>.op) = parameter -> result
  GAMMA |- operand ⇐ parameter ! operand_effects
  request_effects = operand_effects union { E<arguments> }
  ===>
  GAMMA |- perform E<arguments>.op operand ⇒ result ! request_effects
```

`T-Perform` neither selects a handler nor names a provider. If an open operand
row does not already exclude the requested instance, inferred union is
ambiguous; checking may use a lacks fact already present in its expected row.

A handler targets one exact well-kinded instance and contains exactly one
clause for every operation of that effect, in any source order. Each clause
pattern checks against the substituted operation domain and must be
irrefutable. Handling removes the target from the body row. Requirements of
other identities remain, while requirements introduced by clause evaluation,
including a same-instance request made directly by a clause, enter the output
row.

For an operation `op_i : P_i -> Q_i`, the clause receives bindings from a
`P_i` pattern and a fresh structural resume capability
`resume(Q_i, A, epsilon_out)`. Every clause checks against the handler's value
type and shared output row.

```sequent
T-Handle :=
  GAMMA |- body ⇒ A ! ({ E<arguments> } union rho)
  clauses cover each operation of E exactly once
  for each op_i : P_i -> Q_i,
    GAMMA, bindings(pattern_i : P_i);
      resume(Q_i, A, epsilon_out)
      |- clause_i ⇐ A ! epsilon_out, consumes-resume-once
  rho subset-of epsilon_out
  ===>
  GAMMA |- handle body with E<arguments> { clauses }
    ⇒ A ! epsilon_out

T-Resume :=
  active-resume = resume(Q, A, epsilon_out)
  GAMMA |- value ⇐ Q ! value_effects
  value_effects subset-of epsilon_out
  ===>
  GAMMA; active-resume |- resume value
    ⇒ A ! epsilon_out, consumes-resume
```

`T-Handle` chooses the least `epsilon_out` satisfying the body remainder and
every direct clause requirement. Effect weakening lets a clause with fewer
requirements check against that shared row. Ordinary completion of the handled
body passes its `A` value through; there is no source return clause.
`T-Resume` checks the resumed value against the selected operation result,
consumes the capability, and gives the resumed computation the handler's result
contract.

This complete handler discharges `Cell`, so `main` has a pure computation
codomain and evaluates to `42`:

```ash
effect Cell {
    read : Unit -> Int
    write : Int -> Unit
}

main : Unit -> Int
main () = handle (perform Cell.read ()) with Cell {
    read ignored => resume 42
    write value => resume ()
}
```

Resume consumption is a structural dataflow judgment with states `available`
and `consumed`. A clause starts in `available` and every normally completing
path must finish in `consumed`. Sequential evaluation passes the outgoing state
to the next expression. A match checks its scrutinee first, gives each arm the
same resulting state, and requires equal outgoing states from all arms. A
form with no resume occurrence otherwise preserves its incoming state. A
`resume` first checks its value expression under the incoming state, then
requires that result to remain `available` and changes it to `consumed`. Use in
`consumed` is `effect.resume-already-consumed`, and a normally completing clause
left in `available` is `effect.resume-not-consumed`. Divergence before a
syntactic resume remains ordinary divergence; this structural judgment does
not claim termination or convert divergence into discard.

Anonymous-function bodies, recursive members, and nested handler clauses are
barriers for an enclosing resume capability. An occurrence beyond one of those
barriers is `effect.resume-capture`; a nested handler clause receives only its
own capability. Resolution rejects `resume` outside an operation clause as
`effect.resume-outside-clause`. A capability has no source type or binder and
cannot be placed in a tuple, constructor, argument, result, local binding,
scheme, or stored function body.

The executable test `public_effect_identity_survives_facade_reexport` checks
effect declaration and summary identity. The tests
`closed_handler_discharges_exact_effect_and_keeps_main_pure`,
`strict_children_and_branches_union_rows_before_exact_discharge`, and
`handlers_forward_other_instances_remove_exactly_and_reintroduce_direct_requests`
check request, strict union, forwarding, exact removal, and clause
reintroduction. `resume_usage_accepts_exactly_once_in_every_match_branch` and
`resume_usage_rejects_zero_double_branch_and_capture` check structural
consumption and barriers. `written_duplicate_effect_row_has_exact_reason_code`
checks `effect.duplicate`, while
`effect_examples_have_exact_observations_and_reasons` checks the complete
handled example plus `entry.main-effects` and `effect.resume-not-consumed`.

## Interfaces and constrained schemes

An interface has a nonempty ordered vector of fixed-kinded parameters and a
nonempty ordered method list. An omitted parameter annotation means `Type`.
The interface may declare exactly one total determination edge. A determination edge is total: its nonempty, disjoint sides preserve declaration order and together name every interface parameter exactly once.
The left side supplies determinant positions; the right side is the dependent
complement. A dependent may occupy any declaration position.

Each method may have an explicit ordered list of fixed-kinded local parameters;
an omitted method-parameter kind means `Type`. Its value type has kind `Type`,
contains exactly its listed local parameters as its free variables outside the
interface parameter set, and has `Function` as its outermost constructor. With
no edge, every interface parameter must occur in each method value type. With
an edge, every determinant parameter must occur; a dependent parameter may
occur anywhere or nowhere. This occurrence rule is relational and does not
make a dependent an associated result. Interface declaration order fixes the
method positions used by checked evidence, and written method-parameter order
fixes each method scheme's binder order.

The following judgments check an interface method and then the complete
interface. `free_type_variables` and `occurs` compare resolved binder
identities, not spellings. The equation `method_type = domain -> codomain`
decomposes only the outermost constructor.

```sequent
family interface-well-formedness:
  WF-Interface-Method :=
    method_parameters = ordered declared parameters of method
    DELTA = kinds(interface_parameters) union kinds(method_parameters)
    DELTA; empty_OMEGA; XI |- method_value_type => Type
    free_type_variables(method_value_type) - set(interface_parameters)
      = set(method_parameters)
    required_parameters =
      if determination is absent then interface_parameters
      else parameters_at(determination.determinant_positions)
    every required_parameter occurs in method_value_type
    method_value_type = domain -> codomain
    ===>
    interface<interface_parameters> determination
      |-method method_name<method_parameters> : method_value_type ok

  WF-Interface :=
    IOTA(interface) = (interface_parameters, determination)
    interface_parameters is nonempty
    determination is absent or a total ordered partition of interface_parameters
    methods is nonempty
    for each method,
      interface<interface_parameters> determination |-method method ok
    ===>
    |-interface visibility interface<interface_parameters> determination
      { methods } ok
```

Resolved declaration checking supplies an empty `OMEGA`. `XI` contains all
accessible authenticated nominal kinds. `IOTA` contains authenticated imported
interfaces and pre-frozen canonical parameter and determinant records for all
local interfaces before the first local type-bearing declaration is checked.
`WF-Interface` authenticates the complete record. Only an entirely accepted
interface enters later checking.

After admission, a method occurrence consults `MU` by `MethodId`. It freshens
the whole interface vector in declaration order and then every method parameter
at the same fixed kinds. It applies one simultaneous substitution to the value
type. The complete interface argument vector creates one evidence obligation;
method arguments create none. The exact `MethodId`, ordered method arguments,
checked occurrence type, and selection remain private pending state until
whole-module inference closure.

```sequent
T-Method-Occurrence :=
  MU(method_id) =
    interface_id, interface_parameters, determination,
    method_parameters, method_value_type
  freshen(interface_parameters) = interface_arguments
  freshen(method_parameters) = method_arguments
  type = simultaneous_substitute(
    interface_parameters ++ method_parameters,
    interface_arguments ++ method_arguments,
    method_value_type)
  obligation = interface_id<interface_arguments>
  record_pending(occurrence(method_id), method_arguments, type, [obligation])
  ===>
  GAMMA; MU |- method_id ⇒ type
```

Evidence improvement and selection see the complete `obligation`. Neither
operation inspects, chooses, infers, or refines `method_arguments`. An
unresolved determinant argument is `constraint.ambiguous` when the owning
evidence scope closes. An otherwise unresolved method argument remains
`type.ambiguous` at whole-module inference closure. No kind inference,
higher-order matching, reversal of a determination edge, or inference of a
method-local argument follows from method instantiation.

A global signature carries an ordered requirement list after its complete
value type. When the declaration has an explicit binder list, that list must be
an ordered bijection with all free variables in the value type and
requirements, and its order becomes scheme order. An extra explicit binder is
`resolve.unused-type-parameter`; a free variable absent from a complete list is
`resolve.unknown-type`; and duplicate explicit binders are
`resolve.duplicate-type-parameter`.

When the declaration omits the binder list, free uppercase variables become
outer parameters in first-occurrence order: occurrences in the value type come
first, followed by first occurrences found only in requirements. Every such
implicit binder has kind `Type`. In either form, a requirement without a
determination edge requires every free variable in its complete application to
occur in the value type. For a determined interface, every free variable in
the determinant key slice must occur in the value type; a dependent-only binder
may remain quantified in the constrained scheme. Determination never
propagates between requirements.
Here `requirement_key` is the determinant slice for a determined interface and
the whole ordered application otherwise.

Requirements in one signature are compared in source order. Identity-equal
complete applications are `constraint.duplicate-requirement`. Identity-equal
interfaces and keys with different dependent tuples are
`constraint.determination-conflict`. A public global may require only public
interfaces. A private global may also require a private interface declared in
its own module.

The judgment below constructs the checked constrained scheme for either an
equational or operational global signature. `requirement_key` is the complete
application for a no-edge interface and only its determinant slice otherwise;
dependent-only variables remain quantified.

```sequent
WF-Global-Signature :=
  parameters = bind_signature_parameters(explicit_binders, value_type, requirements)
  DELTA = kinds(parameters)
  DELTA; empty_OMEGA; XI |- value value_type ok
  for each requirement, requirement is a resolved interface application
  for each requirement, DELTA; empty_OMEGA; XI; IOTA |- requirement ok
  requirements have no duplicate complete applications
  determined requirements for the same InterfaceId have no equal-key,
    unequal-dependent pair
  for each requirement,
    free_type_variables(requirement_key(requirement))
      is a subset of free_type_variables(value_type)
  visibility = public implies every required interface is public
  checked_scheme = ConstrainedScheme(parameters, requirements, value_type)
  ===>
  module |-signature visibility name : value_type where requirements ⇒ checked_scheme
```

Requirements remain explicit on module-level signatures. Body checking never
infers a requirement and adds it to a checked global or export summary.
Equational and operational presentations with the same value type and
requirements produce the same constrained scheme. The checked scheme retains
the ordered `(TypeVariableId, Kind)` records rather than a second authoritative
kind representation.

A method with an absent parameter list and another free variable, or a method
that omits any required interface parameter, is
`interface.method-parameter`. The
absent-list check precedes any deferred invalid application-kind failure.
Present-list kind failures belong to kind checking. After kind checking
succeeds, the required-parameter check precedes outer decomposition; a method
whose outermost constructor is not `Function` is
`interface.method-not-function`. Duplicate
complete requirements are `constraint.duplicate-requirement`; equal determined
keys with unequal dependent tuples are `constraint.determination-conflict`;
an undetermined key variable is `constraint.undetermined-parameter`; and a
public signature that exposes a private interface is
`constraint.private-interface`.

## Implementations

An implementation head fixes one complete interface application. When the
declaration has an explicit binder list, that list must be an ordered bijection
with the free variables across the complete head vector, and its order becomes
head-parameter order. A listed binder absent from the head is
`resolve.unused-type-parameter`; an unlisted free head variable is
`resolve.unknown-type`; and duplicate explicit binders are
`resolve.duplicate-type-parameter`. When the declaration omits the list, free
uppercase variables in the head become ordered rigid parameters in first-
occurrence order across all arguments, each fixed to kind `Type`.

For a determined interface, the selection key is the determinant slice of the
complete application. Without an edge, the selection key is the complete
application. A generic head is `impl.variable-head` only when every selection-
key argument is a bare type variable. The dependent-head free variables must
be a subset of the key free variables; otherwise admission fails with
`impl.determination-coverage`.

A prerequisite cannot bind a new parameter: every free variable in its
complete application must already occur somewhere in the complete head. A
prerequisite-only variable remains `impl.prerequisite-variable` rather than
becoming an implicit binder. Prerequisites are compared in source order: each
current prerequisite is compared with earlier prerequisites in their source
order, complete identity before key identity. The first classified pair owns
the failure. Complete identity is `constraint.duplicate-requirement`; an equal
determined key with a different dependent tuple is
`constraint.determination-conflict`.

The orphan rule admits an implementation in a module that owns the interface
or an outer nominal constructor of one selection-key argument. A nominal nested
below a foreign outer constructor does not establish ownership. Primitive and
structural key arguments have no nominal owner, so only the interface owner can
implement such a key. Dependent arguments do not contribute orphan ownership.

After freshening and alpha-normalizing a generic implementation, compare the
current selection-key tuple with each non-ground prerequisite selection-key
tuple. The tuples must have equal width. Each prerequisite component must be
identity-equal to or a strict syntactic subterm of the corresponding head
component, and at least one component must be strict. The comparison uses
resolved structure and identities. A ground prerequisite is exempt; a cycle
made only from ground complete applications is detected later during
selection. A public implementation must implement a public interface and may
name only public interfaces in its prerequisites.

These premises admit an implementation header. `owner` returns the defining
module of an interface or an outer nominal constructor, when one exists. Header
checking performs application arity before positional kinds; prerequisite pair
classification; variable-head, containment, determination-coverage, orphan,
decrease, and privacy checks in that order.

```sequent
WF-Implementation-Header :=
  parameters = bind_head_parameters(explicit_binders, head_arguments)
  DELTA = kinds(parameters)
  DELTA; empty_OMEGA; XI; IOTA |- constraint interface(head_arguments) ok
  for each prerequisite,
    DELTA; empty_OMEGA; XI; IOTA |- prerequisite ok
  prerequisites have no duplicate complete applications
  determined prerequisites for the same InterfaceId have no equal-key,
    unequal-dependent pair
  selection_key(head) is not an all-bare-variable tuple
  free_type_variables(prerequisites) is a subset of free_type_variables(head)
  free_type_variables(dependent_slice(head))
    is a subset of free_type_variables(selection_key(head))
  module = owner(interface)
    or module owns an outer nominal of selection_key(head)
  for each non-ground prerequisite,
    decreases(selection_key(prerequisite), selection_key(head))
  visibility = public implies interface and prerequisite interfaces are public
  checked_header = ImplementationHeader(
    visibility, parameters, interface, head_arguments, prerequisites)
  ===>
  module |-impl visibility interface<head_arguments> where prerequisites
    ⇒ checked_header
```

An implementation supplies every interface method exactly once and supplies no
other method. Contiguous equations with one method spelling form one method
definition. Method groups may appear in any order, but each definition checks
against its interface method type after simultaneously substituting the
complete head vector for the interface parameter vector and retaining the
method parameters. The implementation head and method parameters stay rigid as two ordered, distinguishable
sequences. Source equations do not inherit or bind the interface method's
parameter spellings. All ordinary globals and implementation methods in one
module share one simultaneous recursive scope.

Substitution acts on occurrences inside the method domain and codomain without
changing the outer `Function` constructor. The resulting `expected` type is
therefore callable when the positive-pattern equation group checks against it.

A generic implementation method has the conceptual checked scheme shown below.
Each prerequisite contributes its interface's method positions in prerequisite
and interface declaration order.

```text
forall implementation_head_parameters method_parameters.
    evidence(prerequisite_1) ->
    ... ->
    evidence(prerequisite_n) ->
    substituted_method_value_type
```

The membership judgment compares resolved method identities before any
implementation body is checked. The method-typing judgment then checks each
grouped definition against its substituted required type.
`GAMMA |-equations group ⇐ expected` applies the equational-clause typing,
usefulness, and exhaustiveness rules to the complete method group and returns
the pending obligations on its constrained-term occurrences. `close_and_select`
uses the selection judgment below to fill every such occurrence in source order.

```sequent
family implementation-method-checking:
  WF-Implementation-Membership :=
    declared_methods(interface) = required_methods
    grouped_methods(body) contains every required method exactly once
    grouped_methods(body) contains no method outside required_methods
    ===>
    |-impl-membership interface<head_arguments> { body } ok

  T-Implementation-Method :=
    method<method_parameters> : method_value_type in declared_methods(interface)
    expected = simultaneous_substitute(
      interface_parameters, head_arguments, method_value_type)
    head_parameters = ordered rigid parameters of head_arguments
    current = the exact current implementation header and identity
    abstracts = ordered abstract evidence for current.prerequisites
    head_parameters followed by method_parameters is the checked scheme order
    head_parameters are rigid while checking the method
    method_parameters are rigid while checking the method
    GAMMA; abstracts; current; effective
      |-equations grouped_methods(body, method) ⇐ expected, obligations
    close_and_select(abstracts, current, effective, empty_active, obligations)
      = selections
    ===>
    GAMMA; effective |-impl-method grouped_methods(body, method)
      ⇐ expected, selections
```

The abstract evidence in `T-Implementation-Method` has one requirement identity
per declared prerequisite in order. Substitution preserves kinds, so replacing
the interface parameters with the already checked head arguments leaves the
method value type at kind `Type`. Exact current-implementation selection may
use only the same rigid head and that abstract prerequisite evidence. A direct
recursive occurrence of this implementation method reuses its rigid method
arguments; a different instantiation is `type.polymorphic-recursion`. Other
method occurrences instantiate their declared schemes normally. Closing the
method fixes each selection but leaves its occurrence private until module
inference closure freezes the zonked interface and method arguments. The
`selections` output denotes those pending structural fields, not a detached
selection vector.

A public implementation that exposes a private implemented or prerequisite
interface is `impl.private-interface`. An all-variable selection key is
`impl.variable-head`; a prerequisite-only variable is
`impl.prerequisite-variable`; dependent coverage failure is
`impl.determination-coverage`; an owner violation is `impl.orphan`; and a
non-decreasing generic prerequisite is
`impl.prerequisite-not-decreasing`. Missing, repeated, and extra method groups
are `impl.missing-method`, `impl.duplicate-method`, and `impl.extra-method`.
Method body failures retain the existing `type.*`, `pattern.*`, and
`coverage.*` reasons.

The effective implementation environment of a module contains all its local
private and public implementations plus only the public implementation facts
selected by its targeted `impl Interface` items. A selector operates on its
direct dependency summary's public implementation closure, so it may select a
fact declared by that dependency or re-exported through it. Complete imports
and targeted name items admit no implementation facts. Multiple selected
routes to one stable implementation identity deduplicate before comparison.
The [name-resolution rules](name-resolution.md#imports-and-namespaces) choose
one deterministic effective route independently from any public re-export
route.

Every pair of distinct implementation heads for one interface in the effective
environment is freshened independently, preserving every binder kind. Matching
and unification use kind-preserving first-order application structure. If the
selection keys do not unify, the pair is coherent. If the keys and complete
applications unify, the environment is rejected with `impl.overlap`. If the
keys unify but the complete applications cannot unify, it is rejected with
`impl.determination-conflict`. For an interface without an edge, the key is the
whole application, so this reduces to the predecessor overlap rule.
Prerequisites, source order, dependency order, and import order never select a
winner. Header admission precedes environment construction, so an invalid local
header reports its own failure and cannot cause a secondary coherence failure.
The first module whose effective environment combines the two distinct facts
owns the failure and publishes no summary. Membership and bodies are checked
only after coherence succeeds.

```sequent
WF-Effective-Implementations :=
  local = admitted_local_impls(module)
  selected = selected_public_impls(implementation_items(module), dependency_summaries)
  effective = local union selected
  effective is deduplicated by stable implementation identity
  for each distinct pair for one interface,
    not unifies(freshen(selection_key(left)), freshen(selection_key(right)))
  ===>
  module |-implementations effective coherent
```

## Constraint satisfaction and checked evidence

Instantiating a constrained term creates one evidence obligation for each
requirement in source order. A method occurrence creates one obligation with a
complete application. Ordinary kind-aware bidirectional unification runs before
interface improvement.

Before improvement mutates inference state, the checker takes one fixed
snapshot of the determined obligations whose complete determinant keys contain
no unsolved inference variable. It visits only those obligations, once, in
source order. For each, the first applicable source is:

1. an abstract requirement with the same interface identity and identity-equal
   zonked key;
2. the exact current implementation with that key; or
3. the unique visible implementation whose independently freshened key
   kind-preservingly first-order matches the known key.

The source supplies its complete dependent tuple. Improvement is mandatory
when a source exists, even when ordinary typing already fixed every dependent.
The checker transactionally unifies the whole supplied tuple with the pending
application. A disagreement is `constraint.determination-conflict` and
publishes no partial inference solution. Improvement never guesses or refines a
key, reverses an edge, inspects prerequisites, constructs evidence, records a
selection, repeats to saturation, or unlocks an obligation outside the fixed
snapshot. It creates no cross-obligation or cross-requirement propagation.

After improvement, the owning closure begins root selection only when the
complete goal is zonked and contains no inference variable. Snapshot eligibility
gates only pending determined occurrence roots at their owning closure. Such a
root must have belonged to the fixed snapshot. An unresolved key, a known key
with no source and an unresolved dependent, or a pending determined root outside
the snapshot is `constraint.ambiguous`. An eligible inference-free complete root
with no matching evidence source is `constraint.unsatisfied`. A pending root for
an interface without an edge does not participate in the snapshot and retains
the predecessor full-application gate.

After that root gate succeeds, the evidence-selection judgment below carries no
snapshot context. A prerequisite generated by concrete selection has already
been substituted to a complete application. It uses ordinary full-application
selection and full-application active-cycle detection without snapshot
membership.

A selection candidate is freshened independently with its declared binder
kinds. First-order matching may substitute only that candidate's head
parameters, must preserve their kinds, and matches the complete application.
Matching cannot solve or refine a variable in the goal, synthesize a type
lambda, or use higher-order unification.

Selection receives the ordered abstract requirements of the current global or
implementation, an optional current implementation, the effective
implementation environment, an active-goal set, and one resolved complete
interface application. It does not receive the determination snapshot; the
owning closure has already applied that gate to the pending root. Selection
considers sources in this order:

1. An identity-equal complete abstract requirement from the current definition.
2. Exact current-implementation evidence for an implementation method's rigid
   complete head.
3. The unique matching concrete implementation in the effective environment.

Abstract evidence therefore shadows concrete evidence. Exact current evidence
uses the current implementation's already-abstract prerequisite evidence; it
does not freshly instantiate the implementation or select its prerequisites
again. The general concrete branch excludes the current implementation. A
concrete match may substitute only that implementation's bound head parameters.
It selects prerequisites recursively in declaration order.

The rules below describe successful selection. `earlier_source_absent` means
that the preceding entries in the ordered search above did not apply.
`select_all(abstracts, current, effective, active, goals)` applies this same
selection judgment to `goals` in order with the supplied abstract, current,
effective, and active contexts. It returns the corresponding ordered evidence
sequence and never consults the determination snapshot.

```sequent
family evidence-selection:
  Select-Abstract :=
    goal contains no inference variable
    requirement = identity_equal_complete_requirement(abstracts, goal)
    ===>
    abstracts; current; effective; active |- goal
      ⇓ Abstract(requirement, interface_methods(goal.interface))

  Select-Current-Implementation :=
    goal contains no inference variable
    no identity-equal complete abstract requirement exists
    current has the same interface and exact rigid complete head as goal
    ===>
    abstracts; current; effective; active |- goal
      ⇓ Implementation(current, identity, abstract_prerequisites, impl_methods(current))

  Select-Concrete-Implementation :=
    goal contains no inference variable
    earlier_source_absent(abstracts, current, goal)
    goal is not in active
    unique_kind_preserving_match(effective excluding current, goal)
      = implementation, substitution
    prerequisite_goals = substitute(substitution, implementation.prerequisites)
    select_all(abstracts, current, effective, active union {goal}, prerequisite_goals)
      = evidence
    ===>
    abstracts; current; effective; active |- goal
      ⇓ Implementation(implementation, substitution, evidence, impl_methods(implementation))
```

The matching substitution is applied to every prerequisite before recursive
selection. Sibling prerequisite goals preserve declaration order, share the
same abstract, exact-current, and effective environments, and keep their parent
goal active until their ordered selections complete. The implementation-header
containment rule ensures that substituting a complete matched head also makes
each prerequisite free of inference variables. These recursively created goals
were never pending occurrence roots and therefore need no snapshot membership.

If the concrete branch re-enters an active canonical complete interface
application,
selection reports `constraint.cycle`. If no implementation matches, it reports
`constraint.unsatisfied`. Coherent effective environments ensure that concrete
selection has at most one matching implementation after identity
deduplication. Candidate enumeration consults only the effective environment.
An implementation that is private in another module, or public but absent
because no implementation item selected an authorizing direct or re-export
route, contributes no candidate. Without another evidence source, the
obligation is `constraint.unsatisfied` at its constrained occurrence, and that
occurrence owns the failure.

For a name-only import, deterministic related labels identify the original
method or constrained-global declaration, the name import used by the
occurrence, and the owning interface. They do not reveal a private or
unselected implementation. If a selected implementation fails because one of
its prerequisites is unsatisfied, the labels additionally identify the
original implementation and method declarations and every import hop of the
chosen authorization route in order.

A local generalized function cannot acquire a new requirement.
For an eligible unannotated anonymous-function initializer, typing closes and
selects every obligation before `generalize_local` chooses generalized
inference variables. An obligation containing a would-be generalized variable
is therefore ambiguous. Other local forms remain monomorphic and close their
obligations at the enclosing global or implementation method. Recursive
constrained globals reuse their declared abstract requirements and cannot gain
polymorphic recursion.

Checked selections have two recursive forms. Each root retains one complete
interface application. An abstract selection records its requirement identity
and ordered interface methods. An implementation selection records the stable
implementation identity, its head substitution, its ordered
prerequisite selections, and its implementation-method identities. These are
compiler annotations, not source values or runtime dictionaries.

```text
EvidenceSelection =
    Abstract(requirement, methods)
  | Implementation(implementation, substitution, prerequisites, methods)
```

Every resolved method or constrained-global occurrence owns one structural
evidence field. A method field has one position for its interface requirement
and retains the exact `MethodId`, complete zonked interface arguments, ordered zonked
method arguments, checked occurrence type, and selection. A constrained-global
field follows the global signature's requirement order. The first closure that
owns an occurrence fixes its selection. An eligible unannotated anonymous-
function initializer closes before `generalize_local`; every other local
occurrence closes with its enclosing global or implementation method.

Selection may finish before the complete module substitution is closed. The
field therefore remains private pending state until whole-module inference
closure zonks every retained argument. Publication preflights and freezes all
occurrence fields atomically; an unsolved argument or any earlier failure
publishes neither a checked module nor a summary. The frozen field remains on
the checked definition returned by `T-Module`. Static checking neither joins a
detached selection list by source span nor repeats implementation selection.

The executable test
`static_semantics_generic_prerequisite_evidence_example_is_executable` checks
that a concrete generic implementation receives evidence for its strict-
subterm prerequisite:

```ash
type Option<A> =
    None
    | Some(A)

interface Equal<A> {
    equal : (A, A) -> Bool
}

impl Equal<Int> {
    equal (left, right) = left == right
}

impl Equal<Option<A>> where Equal<A> {
    equal (None, None) = true
    equal (Some(left), Some(right)) = equal(left, right)
    equal _ = false
}

main : Unit -> Bool
main () = equal(Some(1), Some(1))
```

The executable test
`static_semantics_determined_generic_prerequisite_uses_recursive_complete_selection`
checks that a determined prerequisite created by concrete selection uses the
ordinary recursive path rather than the pending-root snapshot gate:

```ash
type Option<A> =
    None
    | Some(A)

interface Measure<Key, Result> where Key -> Result {
    measure : Key -> Int
}

impl Measure<Int, Int> {
    measure value = value
}

impl<A> Measure<Option<A>, Option<A>> where Measure<A, A> {
    measure value = 42
}

main : Unit -> Int
main () = measure(Some(1))
```

## Globals and modules

An equational global signature must expose at least as many arrow layers as
each clause has patterns. The patterns receive those domains in order, and the
body checks against the remaining codomain. An inline operational header
supplies its domain and computation result directly. One typed parameter gives
that domain; multiple typed parameters combine into one tuple domain. Each
presentation contributes one rank-1 constrained scheme. All local global
schemes form `GAMMA_G` before any ordinary global or implementation method body
is checked.
Imported schemes come from immutable summaries of direct dependencies.

For these rules, `close_and_select` traverses the named obligation sequence in
source order with the supplied abstract, current, effective, and active
contexts. It fixes each pending occurrence selection and returns the ordered
pending fields retained by the body-checked definition. A global's abstract
context is its declared requirements, its current-implementation context is
absent, and its initial active-goal set is empty. The `selections` output does
not denote a separate side collection; `T-Module` owns its later atomic
publication after inference closure.

```sequent
family global-typing:
  T-Equational-Clause :=
    patterns ⇐ domains => bindings
    useful(previous_clauses, patterns, domains)
    GAMMA, bindings; abstracts; current; effective
      |- body ⇐ codomain ! effects, obligations
    ===>
    GAMMA; abstracts; current; effective |-clause name patterns = body
      ⇐ Function(domains, codomain ! effects), obligations

  T-Equational-Global :=
    checked_signature = forall parameters. requirements => definition_type
    definition_type = Function(domains, codomain ! effects)
    abstracts = ordered abstract evidence for requirements
    current = none
    effective = module's effective implementation environment
    parameters are rigid while checking clauses
    for each clause_i in source order,
      GAMMA; abstracts; current; effective
        |-clause clause_i ⇐ definition_type, obligations_i
    obligations = concatenate(obligations_i in source order)
    exhaustive(clauses, domains)
    close_and_select(abstracts, current, effective, empty_active, obligations)
      = selections
    ===>
    GAMMA; effective |-definition signature; clauses
      ⇒ name : checked_signature, selections

  T-Operational-Global :=
    checked_signature
      = forall parameters. requirements => Function(domain, codomain ! effects)
    definition
      = fn name(header_pattern : domain) -> codomain ! effects where requirements { body }
    abstracts = ordered abstract evidence for requirements
    current = none
    effective = module's effective implementation environment
    parameters are rigid while checking the header and body
    header_pattern ⇐ domain => bindings
    exhaustive([header_pattern], domain)
    GAMMA, bindings; abstracts; current; effective
      |- body ⇐ codomain ! effects, obligations
    close_and_select(abstracts, current, effective, empty_active, obligations)
      = selections
    ===>
    GAMMA; effective |-definition definition
      ⇒ name : checked_signature, selections
```

`T-Equational-Clause` checks one clause against the monotype opened from the
global signature. `T-Equational-Global` checks every contiguous clause under
the same rigid parameters and requires the complete group to be exhaustive
under the shared coverage relation. The global conclusion closes that scope by
retaining its outer parameters and ordered requirements. An empty parameter
sequence and empty requirement sequence produce a monomorphic unconstrained
scheme.

The definition judgments check parameters and bodies but do not determine
global visibility. While definition `i` is checked, its own environment entry
is the opened monotype plus its abstract requirements. Recursive
self-occurrences therefore use the same rigid arguments and abstract evidence.
Other local and imported globals remain constrained schemes and instantiate
freshly. For an operational global, one typed source parameter is
`header_pattern`; two or more typed source parameters normalize to one tuple
pattern and one tuple domain. Singleton exhaustiveness requires that pattern to
be irrefutable.

Module checking receives resolved identities and headers. Import admission
first authenticates immutable body-free nominal, binder, scheme, effect,
interface, and implementation facts. It rejects a duplicate or mismatched
canonical binder, an invalid nominal-kind derivation, an unbound type variable,
or any kind-invalid imported type or effect instance as an internal
dependency-summary failure. An alias, facade, opacity boundary, transitive
route, or dependency diamond cannot recompute a defining kind or effect
identity.

After resolution allocates all local nominal and parameter identities, kind
checking derives and freezes every local nominal constructor kind and every
canonical local effect and interface parameter vector and interface determinant
record before entering declaration-order checking. It then checks constructor
payloads, effect operations, global signatures, interface methods,
implementation heads, and prerequisites in deterministic dependency,
declaration, binder, and type traversal order. No body or public summary can
observe a partially admitted kind or effect registry.

The remaining static stages check interface declarations and admit
implementation headers, build and check the effective implementation
environment, check exact method membership, then check ordinary globals and
implementation method bodies in deterministic source and method order.
`THETA` is the accumulated kind-preserving first-order substitution described
above. Resolution has already staged the name and implementation facts selected
by public imports, but none enters a summary until all these checks succeed.

```sequent
family module-and-program-typing:
  T-Module :=
    imported kinded facts authenticate from direct dependency summaries
    allocate all local nominal and declaration-parameter identities
    XI = imported nominal kinds plus derived local nominal kinds
    PHI = authenticated imported effects plus checked local effects
    IOTA = imported interface parameter vectors and determinant positions
      plus pre-frozen local interface parameter vectors and determinant positions
    for each local constructor payload, DELTA; empty_OMEGA; XI |- value payload ok
    GAMMA_D = checked kinded schemes imported from direct dependency summaries
    each local effect satisfies the declaration checks above
    for each local interface, |-interface interface ok
    admitted_impls = admitted local implementation headers
    selected_impls = explicitly selected implementation facts from dependency summaries
    effective_impls = effective(admitted_impls, selected_impls)
    module |-implementations effective_impls coherent
    for each local implementation, |-impl-membership implementation ok
    GAMMA_G = all local schemes accepted by WF-Global-Signature
    GAMMA_M = checked schemes for all local implementation methods
    for each ordinary global or implementation method in deterministic source and method order,
      GAMMA_D, GAMMA_G, GAMMA_M |-body definition ok
    every inference variable allocated by these premises is in domain(THETA)
    checked_definitions
      = freeze_occurrence_evidence(body-checked definitions, apply(THETA))
    freeze_module_and_public(module, checked_definitions, admitted_impls,
      staged public name and implementation re-exports, apply(THETA))
      = checked_module, summary
    ===>
    summaries(direct_dependencies) |-module module ⇒ checked_module, summary

  T-Program :=
    modules are in dependency order
    for each module_i,
      summaries(direct_dependencies_i) |-module module_i ⇒ checked_module_i, summary_i
    checked_program = checked_modules in dependency order
    main is a local checked scheme in entry
    main is monomorphic Function(Unit, result_type ! {}) with no requirements
    closed(result_type)
    ===>
    |-program checked_program, entry ⇒ result_type
```

`T-Module` establishes all local global and implementation-method schemes
before checking any body, which creates one simultaneous recursive scope for
those definitions. Its inference premise closes inference over the complete
module, including types inferred only inside discarded expressions. All
retained schemes contain ordered `(TypeVariableId, Kind)` binders and a zonked
kind-`Type` body. `freeze_occurrence_evidence` preflights every staged
selection, zonks its interface and method arguments and occurrence type, and
publishes all fields together. It publishes none if any retained inference
variable or relationship is invalid.

`freeze_module_and_public` constructs the returned checked module from
`checked_definitions` and derives its body-free checked summary in one atomic
publication after the complete module succeeds. Any failure publishes neither
result. Public local declarations, effects, and implementations retain the facts
established by their owning judgments. The summary retains public kinds,
effects and operations, and the hidden kind and identity closure required by
public schemes, constructors, effects, interfaces, ordered parameters and
determinant positions, ordered method binders and bodies, complete
implementation heads, prerequisites, and selected evidence. Publicly selected
name and implementation re-exports preserve the
checked facts and defining identities from their dependency summary while
adding the current public spelling or authorization hop. Any import admission,
kind, header, overlap, membership, body, inference-closure, or selection failure
publishes no summary. The [name-resolution
specification](name-resolution.md#imports-and-namespaces) defines the summary's
public facts, required hidden closure, access effects, and authorization routes.
Summary admission authenticates complete interface-application arity and
positional kinds before classifying detached prerequisite pairs. It then uses
the same current-then-earlier source order and complete-before-key identity
precedence as source header admission.

The filled occurrence fields and checked modules become inputs to
[module linking and linked interface-evidence validation](elaboration.md#module-linking-and-entry-generation).
That specification owns their retention through linking and the validator's
authentication inventory. Core synthesis requires the validated result, and
neither validation nor synthesis selects implementations again.

`T-Program` checks each module after all its dependencies. The entry must
declare exactly one local `main`; an imported `main` cannot satisfy the
premise. Its checked scheme must have no type parameters, domain `Unit`, a
closed result, no requirements, and an empty latent effect row. The linked
entry must preserve that empty row. Entry failures have this order: missing
local `main`, polymorphic scheme, wrong domain, nonempty row, open result, then
constrained scheme. A nonempty row is `entry.main-effects`; no later boundary
reclassifies it. This insertion preserves the relative order of the predecessor
entry-shape failures. The closed `result_type` is the type observed for the
whole program, and `main` need not be public. Every evidence obligation in a
well-shaped `main` body must therefore select concrete evidence at its
occurrence.

Semicolons in these judgments separate semantic fields and are not source
punctuation. Resolution has already ensured global-name freshness and
equational name agreement.

The executable test `static_semantics_operational_tuple_pattern_is_executable`
checks a destructuring operational parameter:

```ash
fn add((left, right) : (Int, Int)) -> Int {
    left + right
}

main : Unit -> Int
main () = add(20, 22)
```

## Failure ownership and constraint resources

The first judgment that can establish a failure owns it. Parsing owns malformed
parameter lists and determination syntax. Resolution owns duplicate interface
binders and unknown names in a determination side. Interface-application
checking owns missing or extra arguments as `interface.argument-count` before
kind checking owns an arity-correct positional failure. Interface admission
owns an invalid partition as `interface.determination-parameter` and an
incomplete method seed as `interface.method-parameter`.

Lexing owns the reserved effect keywords. Parsing owns malformed effect
declarations, rows, requests, handlers, clauses, and resume forms. Resolution
owns unknown effects or operations, namespace and visibility failures, stable
identity assignment, row-tail scope, and `resume` outside a clause. Effect
instance arity precedes positional kind checking. Kind checking owns an invalid
effect argument, row tail, or forbidden use of `EffectRow`. Row formation owns
a duplicate written member and an unsatisfied lacks fact. Ordinary expression
typing owns operation operand and latent-row failures. Handler checking owns
target membership, clause coverage and patterns, the shared result and output
rows, and resume consumption and barriers. Entry checking owns a nonempty
linked entry row.

Implementation requirement pairs, visibility, head, prerequisite, coverage,
orphan, and termination failures belong to header admission. Effective-
environment construction owns `impl.overlap` and
`impl.determination-conflict`. Method membership and bodies belong to their
respective checks. Improvement owns a dependent disagreement as
`constraint.determination-conflict`; ambiguity, cycle, and unsatisfied failures
belong to the closing improvement-and-selection path. Linked and Core
validation own forged retained carriers only after all source checks succeed.
Kind checking owns the first kind rule that can establish an invalid resolved
source type:

- `kind.not-applicable` means the function position of a type application did
  not synthesize a function kind;
- `kind.argument` means a type-application argument did not match the function
  kind's domain, or an arity-correct interface argument did not match its
  positional interface parameter kind; and
- `kind.expected-type` means an owning `K-Value-Type` check found a kind other
  than `Type`.

Each kind diagnostic retains the causal application, argument, or value-type
site, the declaration site when it explains the found kind, and structured
expected and found kinds. Rendering does not reconstruct these fields from
diagnostic text. An unavailable implementation item, an interface used as an
ordinary type constructor, or a file-wide import-name conflict remains a
resolution failure. Earlier parser and resolution failures are not reclassified
by static checking.

Within one source unit, causal precedence is:

1. parsing and recovery, including effect forms;
2. name resolution, including effect identities, row-tail scope, and resume
   scope;
3. complete application arity, then positional argument kinds, followed by
   effect-row formation;
4. determination partition admission;
5. method-binder and method-kind checks, then method seed and function shape;
6. implementation prerequisites in current-then-earlier source order with
   complete identity before key identity, then variable-head, containment,
   determination coverage, orphan, decrease, and privacy;
7. effective-environment pair coherence;
8. implementation method membership and bodies;
9. per-occurrence ordinary and row unification, effect expression and handler
   checking, unresolved-key ambiguity, atomic improvement and dependent
   conflict, remaining dependent ambiguity, full-application selection,
   active-goal cycle detection, and unsatisfied evidence; and
10. whole-module inference closure and publication, entry checking, summary
    admission, linking, elaboration, and Core validation.

An earlier failure prevents publication to later boundaries. Existing
predecessor diagnostics within one listed family retain their internal order
unless a rule above narrows it. Traversal follows dependency, import, selector,
declaration, binder, type, requirement, and method order. Chosen authorization
routes follow their deterministic hop order, so one source program has a
deterministic first failure and label sequence.

One graph-wide interface-and-constraint work budget persists from dependency-
summary admission through effective-environment construction, header and body
checking, evidence selection, linking, and linked evidence validation. The
static stages charge proportional work before retaining or visiting interface
and implementation facts, each parameter and complete-application argument,
determinant position, selector expansion, effective and public route, summary
field, occurrence evidence field, coherence pair and key comparison,
improvement snapshot entry and candidate, obligation, selection candidate,
substitution, prerequisite edge, active complete goal, route hop, and linked
authentication fact. A retained simultaneous vector and any separately retained
owner index are charged independently before allocation. Validation of one
canonical improvement goal is charged once; each candidate and comparison
remains separately charged.
[Elaboration](elaboration.md#module-linking-and-entry-generation) defines the
link-retention and full-route-validation charges. Exhaustion at any stage is
`internal.resource.constraint-work`; validation has no separate resource
reason. Active-goal cycle detection precedes resource exhaustion for the same
retained selection work. Existing type-inference, Core-construction, and Core-
validation budgets remain separate, and the Core budgets begin only after
linked interface-evidence validation succeeds.

Effect syntax charges the existing syntax ledger. Effect and operation facts,
effect instances, computation codomains, row variables, row members, and lacks
facts charge the type-work ledger of the stage that visits or retains them.
Row equality, substitution, unification, union, weakening, and exact removal
charge each visited member, pending comparison, and lacks relation before the
work or retention occurs. Effect summaries, linked facts, and Core validation
charge their existing owning ledgers; they do not introduce a separate effect
budget. Exhaustion publishes no partial row, checked module, summary, or Core
program.

Kind traversal, cloning, equality, hashing, rendering, substitution,
unification, matching, summary admission, validation, and disposal use
iteration or explicit bounded work stacks. Resolved kind checking,
elaboration, and retained kind cloning charge their owning type-work ledger.
Method binder records, schemes, instantiation arguments, substitutions,
adapters, and Core types also charge their owning type-work ledger; binder-list
syntax charges the syntax budget. Core construction and independent Core
validation retain separate cumulative ledgers.
Interface, implementation, evidence, and linked-authentication traversal or
comparison charge the graph-wide constraint budget; retaining a structural
type, substitution, kind, or binder-kind record additionally charges the
applicable type-work ledger. A kind node, unary application node, or
binder-kind record is charged before its owning visit or retention. Retaining
a record also charges the type and kind nodes it copies. Comparing a kind pair
charges one comparison unit in the traversal's owning ledger. A failed
operation publishes no partial checked fact or summary.

These ledgers are bounded compiler-resource policy. They do not add runtime kind
values or evaluator work, alter effect evaluation, or make a resource ceiling
part of Ash value semantics.

Ash has no kind polymorphism, general higher-rank source values, explicit
source term type application, type lambdas, higher-order unification, broad
application-shaped local generalization, subtyping, implicit conversions,
explicit structural recursive-type operators, or polymorphic recursion.
Unauthenticated nested Core schemes remain invalid. Interfaces add no
associated declarations, associated-output projections or equations, multiple
or partial edges, neutral parameters, reverse or injective determination,
specialization, priority, default or negative implementations, inferred global
requirements, first-class dictionaries, runtime implementation lookup, or
interface-specific Core mechanism. Nominal declarations may refer to
themselves and to other nominal declarations in the same module. Recursive
global visibility does not cross a module boundary. The interface evidence
family is not effect-handler or provider authority, proof or proposition
evidence, common universal evidence, or an existential package. An effect row
is a computation requirement, and a lexical handler interprets only its exact
effect instance; neither is inferred from interface determination.
