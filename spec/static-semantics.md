# Static Semantics

Ash has `Int`, `Bool`, `Unit`, `String`, `Bytes`, rigid type variables, structural tuples,
parameterized nominal algebraic data types, unary functions, and effect rows. A
tuple contains at least two element types. A function has a value domain and a
computation codomain `A ! epsilon`, where `A` is a value type and `epsilon` is
an effect row. Source kinds contain `Type`, `EffectRow`, and right-associative
function kinds, subject to the binder restrictions below.

Type equality is one shared rule. `Int`, `Bool`, `Unit`, `String` and `Bytes` equal themselves;
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

A `newtype` representation is one monotype template under its declaration's
ordered parameter environment. The fully applied template must synthesize
`Type`; this check adds no kind inference or higher-rank representation. A
representation may contain primitives, parameters, structural tuples,
functions with computation codomains, ordinary nominals, and other `newtype`
nominals under the ordinary scope and kind rules. Kinding a computation
codomain checks every nested effect instance, including effect arguments that
contain a `newtype` identity.

After every module-level ordinary constructor payload and `newtype` representation
is kind-correct, static nominal admission constructs the directed
graph whose vertices are the module-level `newtype` declarations and whose edges
are `newtype` identities occurring anywhere in another representation. The directed graph containing only `newtype` representation edges must be acyclic.
Traversal follows declaration and structural type order; the first closing edge
owns `newtype.recursive-representation`. Its primary label identifies the
rejected representation occurrence, and its related labels identify the
declarations that complete the cycle. An ordinary data declaration ends this
graph traversal even if its payload refers back to the originating `newtype`.

A local `newtype` uses the same representation-kind check under its own
parameters and enclosing lexical type parameters. Its nominal kind depends
only on its declared parameter vector. Sequential scope rules out self and
forward representation references, so local declarations add no cycle pass.

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
    primitive in {Int, Bool, Unit, String, Bytes}
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

Every omitted declaration kind annotation and every binder introduced by an
omitted implementation binder list is fixed to `Type`. An omitted global list
discovers ordinary free type variables and effect-row-tail variables in their
shared first-occurrence order. A name occurring only in ordinary type positions
has kind `Type`; one occurring only as an effect-row tail has kind `EffectRow`;
using the same name in both roles is invalid. Ash does not infer a function
kind from use. This is the current phase-dependent language constraint, not a
commitment against a later bounded declaration-local inference rule.

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

Hook scopes use the distinct partial relation `scope_discharge(epsilon, H)`.
It removes `H` when explicitly present. If `H` is absent from the known members,
it leaves a closed row unchanged, or leaves an open row unchanged only when its
tail already lacks `H`. Otherwise discharge is ambiguous. This relation adds
no lacks fact and does not relax ordinary handler admission or exact removal.

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

  T-String :=
    s is a decoded string literal
    ===>
    GAMMA |- s ⇒ String

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

  T-Newtype-Constructor :=
    constructor : forall parameters. Newtype(owner<parameters>, representation)
    instantiate(parameters, Function(representation, owner<parameters>))
      = constructor_type
    ===>
    GAMMA |- constructor ⇒ constructor_type
```

The constructor premises consult the immutable registry produced by name
resolution. `T-Newtype-Constructor` defines explicit wrapping and does not make
the representation and nominal types equal. Every constructor application then
follows `T-Apply`; it does not have a special call rule.

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

An accessible `newtype` constructor pattern has exactly one subpattern, checks
that subpattern against the substituted representation, and explicitly unwraps
the nominal value. It is irrefutable for its owner. The constructor remains
unavailable through an opaque or hidden source route, and no pattern matches a
representation value as though it had the nominal type.

A match synthesizes its scrutinee once, checks every arm pattern against that
type, and gives the resulting bindings only to that arm body. All arm bodies
have one type. The typed usefulness relation over closed nominal sums, tuples,
`Bool`, `Unit`, binders, and wildcards must find each arm useful and must find
no witness outside all arms. A useless arm is rejected with
`coverage.redundant-case`; a remaining witness is reported with
`coverage.non-exhaustive`.

For a local or imported transparent ordinary nominal, coverage uses its
complete constructor family. For a transparent `newtype`, coverage treats its
sole constructor as complete without requiring a runtime tag test. An imported
opaque or hidden nominal has no accessible constructor pattern and is not
treated as an empty sum. A binder or wildcard can cover such a value without
inspecting its representation.

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

### Local nominal scope

A local `newtype` checks its remainder with its rigid nominal and unary
constructor in scope. Construction, irrefutable pattern matching, and
representation substitution use the same rules as module `newtype`. No
representation interface evidence transfers to the local nominal.

At each declaration boundary, the compiler zonks the outward computation and
rejects a local identity in its value type, effect row, generalized scheme, or
requirements. Traversal includes function domains and codomains, tuple members,
nominal applications, effect arguments, and row structure. Solving an inference
variable in a preceding or enclosing binding must not carry the identity
outside the declaration's scope either, even when the block returns `Unit`.
If later constraint improvement solves an outward inference variable, its
solution must satisfy the same boundary before checked publication. This check
does not change ordinary unification, improvement, or evidence-selection order.

In the following rules, `n` is the resolved lexical nominal identity, `P` its
ordered parameters, and `R` its representation template. Extending `XI` with
`n(P) = R` also makes its constructor scheme available. `outward` includes the
zonked result computation, any outward scheme or requirement, and the zonked
types of bindings that preceded the declaration. The semicolons separate
semantic fields and add no source punctuation.

```sequent
family local-newtype-typing:
  T-Block-Newtype-Inferred :=
    n(P) = R is resolved and kind-correct
    GAMMA; XI, n(P) = R |- { remainder } ⇒ A ! epsilon
    n does not occur in outward(GAMMA, A ! epsilon)
    ===>
    GAMMA; XI |- { newtype n(P) = R; remainder } ⇒ A ! epsilon

  T-Block-Newtype-Checked :=
    n(P) = R is resolved and kind-correct
    GAMMA; XI, n(P) = R |- { remainder } ⇐ A ! epsilon
    n does not occur in outward(GAMMA, A ! epsilon)
    ===>
    GAMMA; XI |- { newtype n(P) = R; remainder } ⇐ A ! epsilon
```

Escape is `type.local-nominal-escape`. Its primary label identifies the
expression or binding whose outward type contains the identity, and a related
label identifies the declaration. The following complete module is rejected
at `Hidden(1)`, related to `newtype Hidden`, even though `escaped` is unused:

```ash
main : Unit -> Int
main () = {
    let escaped = {
        newtype Hidden = Hidden(Int)
        Hidden(1)
    }
    0
}
```

The executable test `local_newtype_escape_example_has_owned_diagnostic` checks
the reason and source labels. Returning the constructor, an identity-exposing
closure, or a pair of a hidden value and its eliminator is rejected by the same
rule. The last case would require an existential package, which Ash does not
infer. Using the nominal or constructor name after the block instead fails
during name resolution.

A closure may escape when its exposed computation is identity-free, even if
its body captures and unwraps a local value. The
[local-newtype example](README.md#local-newtypes) executes this case. Returning
the unwrapped representation or consuming a local value through an ordinary
polymorphic function with an identity-free result is also valid.

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

Local nominal identities are rigid constants and are never generalized.
Eligible local functions may quantify unrelated inference variables under the
existing rules; that quantification cannot hide a nominal identity or create an
inferred local requirement.

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

## Source foreign declarations

Foreign declarations are passive. The admitted subset contains owner-free
calls with scalar or void results, and owner contracts with declared dependencies. Each library
has exactly one profile, `"x86_64-unknown-linux-gnu"`. Scalar representations
are signed or unsigned 8-, 32- or 64-bit integers, or `size_t`. These ABI
representations introduce no ordinary fixed-width Ash integer type.

Each symbol has one outer pure source arrow and a complete ordered parameter
vector containing only `Type` and `EffectRow` parameters. Omitted kinds are
`Type`. Parameters are retained even when they contribute no ABI operand.
Native symbol names are nonempty strings without NUL. Every scalar ABI input maps
exactly once to a source position whose selected type is mathematical `Int`, or
to a checked scalar constant from the same original library with the exact
declared representation;
negative or out-of-range source positions and missing or repeated ABI input
mappings reject. The source domain may contain a product, and dotted positions
select its nested leaves.

A scalar constant's mathematical literal must fit its declared representation.
It publishes an ordinary `Int` value under the library declaration's publication
mode; qualified, selected and re-exported references retain its defining binder.
Its value requires no C or header evaluation. A native constant operand retains
the original constant member, representation and value, independently of an
ordinary source reference to that value. Equal values or spellings do not make
another member interchangeable. Arbitrary constant expressions and header macro
evaluation remain outside this checkpoint.

A `sentinel Name : Representation = all_bits_one` declaration requires an exact
`function_address` representation in the same original library. It supplies
only the non-callable fixed operand role selected by
`operand N from constant Name`. That ABI input must name the sentinel's exact representation declaration;
another representation or equal-bit member is not interchangeable. Sentinel
members publish no ordinary term, `Int`, pointer, function or callable symbol.
They cannot supply a source-projected argument, an owner address, a scalar
predicate or a native result. `from null` does not provide this role. It supplies
only an explicitly admitted nullable address ABI input, with no State, view,
scalar or function-address authority. A sentinel grants no access or window permission.

An owner declaration introduces an opaque nominal state family without source
constructors. Its explicit owned position selects a `Type` formal. Canonical
admission retains every original parameter identity, kind and defining origin;
the current owner checkpoint rejects `EffectRow` and function-kind formals.
An owner address uses an `opaque` or `bytes` representation and one authenticated
teardown symbol from the same defining library. Declared dependencies retain
their original owner roles and exact preceding state applications; a same-shaped
or same-spelled state supplies no dependency authority.

An acquisition symbol maps its pointer result to the exact saturated state
family and returns the canonical
`Foreign.Call<Foreign.Output<Foreign.Nullable<State>>>` codec. A current-state
operand must select the matching state application in the source product; its
pointer ABI role does not accept an `Int` substitute. A teardown returns the
canonical `Foreign.Call<Foreign.Disposition<T>>` for its independent result and
records consumption or retention of the selected state. The executable resource
checkpoint below admits `void` teardown with `T = Unit` and scalar-status
teardown with `T = Int`. Scalar teardown requires `output result as scalar`,
exactly one Current operand, and `retained_dependents block`. Its total finite
alternatives test the raw Result against original same-representation declared
literals, with one final `otherwise`. Each alternative gives exactly one
consumed/retained fact for that Current position and exactly one readable
Result fact; a bare scalar cannot be unreadable. Repeated or contradictory
selectors, missing coverage and
mismatched positions reject. Owner libraries retain these original checked
literal facts separately from ordinary constant binders and native operand
selection. A result predicate grants neither source value nor operand authority.
Header evaluation remains outside this checkpoint. Byte-owner
preparation also checks its initialized extent against the selected
mathematical `Int` source leaf. This passive check supplies no byte access or
executable owner activation; an admitted resource scope supplies the separate
controlled execution boundary.

An owner-free scalar ABI result requires `output result as scalar` and an
`otherwise` outcome declaring `readable result`. Its source codomain is the
exact canonical `@builtin.foreign` type `Call<Int>`. A `void` result has no
output role or readability fact and has codomain `Call<Unit>`; `outcome
otherwise {}` provides its total empty outcome. `void` is not an ABI input. A
zero-argument C function has zero ABI operands, as in `abi () -> void`.

Declaration checking authenticates the canonical result nominal and constructor
identities, complete parameter kinds and defining origins. A same-spelled or
same-shaped client type does not replace the common codec. ABI preparation is
retained once per defining library, then bound to the original effect and
operation facts. Summaries preserve those immutable contracts and reject
changed table coverage, signature or parameter correspondence.

Owner-free native calls retain their exact effect instances in ordinary function
rows. Ordinary `handle` clauses cannot install a native symbol's interpreter.
Program compilation installs an explicit checked Core interpretation for the
entry's admitted owner-free native instances. Only those exact instances are
removed; the resulting entry row must be empty. An ordinary effect or unresolved
row tail cannot be discharged through this boundary.

Source contracts and checked Core confer no executable bridge binding. Execution
requires separately admitted bindings before Ash runs; ordinary execution with
missing bindings refuses without compiling or linking a host implicitly.
Owner acquisition and teardown requests are unavailable in ordinary callables,
and controlled state cannot occur in their parameters, results or captures. An admitted
source lifecycle phase authorizes only its exact original owner operations and
complete Type/Row instances. The owner-free program interpretation cannot
authorize these requests. Retained row arguments remain part of source identity
even when an owner application's native projection contains only Type arguments.

The common module also exports the pure functions
`Foreign.checked_i64 : Int -> Foreign.Call<Int>` and
`Foreign.checked_size_t : Int -> Foreign.Call<Int>`. Both have empty
effect rows.
For the GNU64 profile, the first accepts the inclusive range
`[-2^63, 2^63 - 1]`; the second accepts `[0, 2^64 - 1]`. Success returns the
unchanged mathematical `Int`; a range failure returns `ConversionFailed` with
an opaque `ConversionError`. Their original builtin function identities, type
annotations, provenance and result-codec allocation survive selected imports
and facade publication. Same-spelled client functions grant no builtin
authority.
These checks grant no native-call, access or ownership permission and do not
replace a later native call's exact operand conversion.

`Foreign.checked_nul : String -> Foreign.Call<Unit>` is an ordinary pure
preflight with the same original builtin identity and codec requirements. It
accepts an empty or nonempty string with no NUL byte and otherwise returns an
opaque conversion error. It supplies no native input, access, State, ownership
or call authority and does not replace native-call input preparation.

The canonical byte functions have empty ordinary effect rows and signatures
`Foreign.byte_read<S> : (S, Int) -> Foreign.Call<Int>` and
`Foreign.byte_write<S> : (S, Int, Int) -> Foreign.Call<Unit>`. Their generic state
parameter is compiler-sealed: only the exact descriptor-witnessed initialized
live state in an admitted source lifecycle or handler phase can authorize an
application. Ordinary instantiation with an arbitrary or merely compatible `S`,
including forwarding through an ordinary generic helper, grants no permission.
The result codec is the existing canonical `Foreign.Call` allocation, with an
opaque conversion error; this choice applies only to these byte primitives.

An input `nul` role requires ordinary `String`; a `bytes(length_position)` role
requires independent `Bytes` or UTF-8 bytes of `String`, with a checked integer length. `call_borrow` and
`copy` both forbid retaining the prepared Ash input address after return. They
are foreign assumptions about the callee, not permission to retain an Ash view.
An `out` operand declares private initialized storage and has no source operand.
The canonical result product contains the non-void result first, followed by
output slots in ABI order; zero fields use `Unit`, and one field is unwrapped.
Scalar results are bare `Int`; pointer and slot results retain their checked
`Output`/`Nullable` roles. One call may create at most one owner or finish one
owner, never both. An `offset_into` output becomes an independent integer offset
into its exact input, not an address.

An access family is constructor-free and retains its original owner, fresh
window position, extent convention and preserving member identities.
`copy_window Family<W, ...> from state { body }` introduces fresh `W` only in
the body and requires an authenticated live, pending or completing owner in a
permitted direct provider phase. Its sealed interpretation admits only that
original family's access-compatible members at the exact ordered Type/Row
actuals. The outer resource interpretation remains exact and nonquantified.
The current executable view-family application profile is Type-only; retained
Row tags are not silently projected away or admitted by matching shape.

Each view records its producing operation, exact owner/window and scalar keys.
An extent query requires that view and those same keys; known unequal keys
reject statically, and unknown keys require the runtime equality check before
native entry. Nullable, unreadable and non-null empty outputs remain distinct.
Windows cannot suspend, complete their owner, escape in values/evidence/rows,
or pass State/view permission through an ordinary callable.

`Foreign.copy_bytes<V> : (V, Foreign.Extent<V>) -> Foreign.Call<Bytes>` and
`Foreign.copy_nul<V> : (V, Int) -> Foreign.Call<Bytes>` require the exact sealed
live view in a direct provider window. `Foreign.Extent<V>` is opaque,
unconstructible and tied to that exact view. `extent_value<V> :
Foreign.Extent<V> -> Int` exposes only an independent copied length. Compatible
types, donor extents or ordinary generic instantiation supply no authority.
`Foreign.data_of<S, D> : S -> D` and `Foreign.replace_data<S, D> : (S, D) -> Unit`
use only the exact descriptor-supplied State/private-data relation in an admitted
phase. They grant no State transport or native-call permission to helpers.
Owner/access declarations and their parsed contracts alone grant no executable
permission.

## Source resource declarations

A source resource declaration retains its explicit owned position, complete
ordered Type/Row formals, input, native state, private data, acquisition,
completion and body-result report types. Its provider application, provided
effect, complete native interpretation list, codec and all lifecycle and handler
patterns retain defining identities and provenance. The family is a declaration;
it creates no activation. A foreign state family remains an ordinary opaque
nominal application and is distinct from a resource instance's access family.

The `owned` formal has kind `Type` and coincides with the foreign state family's
declared owned argument. Input and private data cannot contain the current owned
identity, and borrowed owner identities must be declared dependencies. Private
`D` cannot contain any current, provisional or enclosing native State token or
view, including inside tuples, ordinary ADT wrappers or a generic application.
This prohibition is checked in the defining header and after complete Type/Row
specialization. A permitted local enclosing State in acquisition or finish does
not authorize storing it in `D`. Ordinary declared-dependency access handles are
distinct and remain subject to exact identity, liveness and revocation checks.
Every native interpretation must match the original state owner and its complete
symbol arguments. The admitted list contains one acquisition, one Current
finish member and the exact permitted scalar query/usage members. The owner's original
declared host destructor is authenticated separately, even when source finish
selects a retaining member. A same-spelled symbol, swapped
argument, ordinary state ADT or ordinary effect cannot replace those facts.
Incorrect authored headers report `type.argument`.

The associated interface and effect have the same uniquely named methods and
operations. After substituting their complete arguments, each method has the
operation's exact value domain and result and the single associated effect
instance as its effect row. Declaration order need not agree. An existing
implementation, duplicate resource association, missing operation or mismatched
method cannot establish this relation. Ordinary implementation and `with`
selection cannot introduce the sealed provider. Selective imports and facades
retain original source headers and a passive declaration census for rejection;
neither record publishes additional names or executable evidence.

Acquisition introduces checked lexical forwarding for every associated method.
Ordinary namespace calls and constrained polymorphic helpers select that same
evidence. Each forwarding preserves the original method and operation identities,
complete Type/Row arguments, unchanged typed operand and exact provided effect.
Independent Core checking authenticates the source occurrence, generated binders
and request forest against their original association. Copying a claim or taking
evidence from another activation cannot grant authority.

Both report codecs authenticate ordinary library ADTs by their exact constructor
order and field types. Acquisition has `Acquired(State, D)` then `Refused(I)`;
completion has `Consumed`, `ConsumedFailure(E)` then `Retained(State, E)`.
The `scope` report has `NotAcquired(I)` then `Completed(Answer, Completion<E>)`, where
completion status has `Closed`, `ConsumedError(E)` then `RetainedError(E)`.
Constructor spellings alone grant no authority. The single result binder
`Answer` is replaced by the checked body type; independent `I` and `E` are
ordinary source types rather than fixed `Unit` errors.

The `acquired_only` report has `Success(Answer)` then `Failure(I)`, with no
completion-status field. Checking substitutes the report's actual type arguments
into its constructor payloads and compares those exact types. A one-parameter
`Outcome<T> = Success(T) | Failure(Error)` can therefore use a concrete acquisition
error; a generic error parameter follows the same check. Constructor names and
parameter positions do not select this codec. A consumed completion failure is
terminal rather than a successful report. Retention cannot be reported as a
successful `acquired_only` completion.

Acquire checks from the declared input to acquisition type. Finish checks from
`(State, D)` to completion type. Their patterns and the handlers' `(State, D)`
pattern must cover every value. Successful acquisition returns its witnessed
fresh native state and independent private payload. Refusal cannot publish that
state. A returning finish path preserves the recorded native disposition:
`Consumed` and `ConsumedFailure` require consumption; `Retained` requires an
attempted teardown that retained the same current state. Bare `Retained` or an
unconsumed `Consumed` does not authorize completion. Invalid authored lifecycle
or handler flow reports `type.argument`.

The compiler checks each original lifecycle and handler template once in its
defining module. Instances specialize that immutable code with complete
Type/Row substitutions and fresh local identities. Independent final Core
checking reconstructs the original correspondence; parsing, export summaries
and compiler copying claims cannot grant execution authority.

For `resource Family<arguments> handle = initializer { body }`, the initializer
checks in the preceding scope at the substituted input type. It runs once before
the fresh identity enters scope. The complete argument vector replaces only the
explicit owned position with that identity; all inherited positions keep their
Type or Row tags. The handle is a non-owning access value available inside the
body. The report type, outward effects, evidence and stored dependencies cannot
expose the fresh identity; an escape reports `type.resource-escape`.

This implementation checkpoint executes opaque and initialized byte owners,
including declared retained dependencies, with Type-only state-family arguments
and either report codec. Its `void` or scalar-status finish and
host-destruction contracts admit total consumed or retained dispositions. A
Current call can also be blocked before native entry while a retained dependent
remains live. Associated interfaces may contain multiple methods with the exact
operation types and rows described above; method-local type parameters remain
unsupported by this carrier. Resource and symbol arguments retain their
complete Type/Row vectors. The lifecycle checker admits native requests,
ordinary constructor and product assembly, sequential bindings, matches and
sealed byte calls. A byte call must retain its original canonical function,
TypeApplication and Apply occurrences, original state family and owner,
selected evidence and copied specialization. Both the caller and defining
declaration retain their complete ordered Type/Row actuals independently of
`S`, including arguments absent from the callable's value type. Branch-selected
canonical aliases retain each alternative's defining context. Independent Core
checks these relationships rather than granting permission from the monomorphic
operand type. Byte calls borrow the fresh acquired or current live state
without consuming it; their independent results cannot expose that state.
Ordinary outward requests in these phases must carry independent operands and
cannot synthesize native-state lineage. The instance's handler output is the
body row minus its exact provided instance, union the source handler's direct
ordinary requests. The scope's outward row additionally includes initializer,
acquisition and finish effects, removing only the listed exact native instances
from the interpreted phases. Other ordinary rows remain.

Capture/resume moves the same activation and owner without acquisition. Owned
discard completes acquired source scopes in structural order while required outer
resources remain live. It must retain the interpreters needed by source finish;
a running finish or unfinished closing operation cannot be abandoned. The
surrounding structural cleanup rules check these obligations independently.
Acquisition capture can retain an unpublished guard; discarding it revokes that
guard without inventing private data or a source finish input. A consumed
`ConsumedFailure(E)` during owned discard is terminal `ResourceCompletion` for
both codecs. Normal `scope` return still reports `ConsumedError(E)`.

Ordinary pure module-global helpers may consume and return independent lifecycle
payloads. Same-module and imported definitions preserve their complete ordered
Type/Row schemes and actual instances, including explicit ordinary annotations
that close an inferred effect row. Helper arguments and results cannot transport
native State or its view; a compatible function type grants no descriptor or
native-effect permission. Original and copied calls remain independently checked
against the same defining global.

Privileged lifecycle wrappers, source `given` forwarding and source-projected scalar
teardown operands remain unsupported. These
are checkpoint restrictions, not additional language rules for all resources;
the broader obligations remain in
[CP-0022](../docs/proposals/CP-0022-ash-authored-foreign-interfaces.md).
The compiler-owned cell rules below remain unchanged. Ordinary buffers use the
declared-source resource rules.

Dependency roles come from the original foreign owner declaration and are
instantiated before introducing the new owned identity. Input and private-data
traversal checks all typed access positions, including ordinary constructor
payloads, against these exact preceding activations. A same-typed donor,
undeclared identity or stale access is not a dependency witness. Retaining an
owner revokes ordinary source access and protects the same transitive dependency
closure. Required finish may obtain a physically live declared enclosing State;
this does not restore ordinary access or grant another native operand role.
Independent source, Core, specialization and image checks retain original header,
forest and complete Type/Row correspondence.

## Effects

An ordinary effect declaration has a possibly empty ordered parameter vector
and a nonempty ordered operation vector. Its parameters have the ordinary fixed
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
      |- clause_i ⇐ A ! epsilon_out, consumes-capability-once
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

T-Discard :=
  active-resume = resume(Q, A, epsilon_out)
  active-resume is available
  owned closure includes the selected capture and its contained live captures
  closing that closure preserves every outside and running completion owner
  each action is compatible with its surviving interpreter context
  epsilon_close is the least residual row of owned close execution
  ===>
  GAMMA; active-resume |- discard ⇒ Unit ! epsilon_close, consumes-resume
```

`T-Handle` chooses the least `epsilon_out` satisfying the body remainder and
every direct clause requirement. Effect weakening lets a clause with fewer
requirements check against that shared row. Ordinary completion of the handled
body passes its `A` value through; there is no source return clause.
`T-Resume` checks the resumed value against the selected operation result,
consumes the capability, and gives the resumed computation the handler's result
contract.
`T-Discard` consumes the same capability without resuming its captured
computation. Its result is `Unit`, not the handler's result type; subsequent
clause work still checks against the handler contract. Its inferred
`epsilon_close` includes the effects of actions invoked by closing the owned
capture after action-local and still-enclosing retained builtin cell
interpretation. It does not export a captured cell's local identity merely
because an action uses that cell before release. Surviving source handlers,
including clause-local handlers around discard, check and discharge residual
effects at their own boundaries. Discard is not universally pure.

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

Capability consumption is a structural dataflow judgment with states `available`
and `consumed`. A clause starts in `available` and every normally completing
path must finish in `consumed`. Sequential evaluation passes the outgoing state
to the next expression. A match checks its scrutinee first, gives each arm the
same resulting state, and requires equal outgoing states from all arms. A
form with no completion occurrence otherwise preserves its incoming state. A
`resume` first checks its value expression under the incoming state, then
requires that result to remain `available` and changes it to `consumed`.
`discard` requires `available` and changes it directly to `consumed`. Match
arms may choose different completion forms if their outgoing states agree.
Use in `consumed` is `effect.resume-already-consumed`. A normally completing
clause left in `available` is `effect.resume-not-consumed`. Divergence before a
syntactic completion remains ordinary divergence; this structural judgment does
not claim termination or convert divergence into discard.

Anonymous-function bodies, recursive members, supplied local evidence methods,
and nested handler clauses are
barriers for an enclosing resume capability. An occurrence beyond one of those
barriers is `effect.resume-capture`; a nested handler clause receives only its
own capability. Resolution rejects `resume` or `discard` outside an operation
clause as `effect.resume-outside-clause`. A capability has no source type or
binder and cannot be placed in a tuple, constructor, argument, result,
local binding, scheme, or stored function body.

Discard permission is distinct from duplication permission. Ordinary values
and their stored closure captures are duplicable, subject to the resource
lifetime rules below. The hidden continuation
capability is nonduplicable and nonescaping. Discard closes exactly the selected
owned capture. Each live clause boundary inside it contributes its owned
capture recursively at that boundary's structural position, and is consumed
once. A consumed capability adds no further capture. Non-owning registration
or handle associations do not authorize taking an enclosing owner. Required
completion outside the owned closure must remain reachable in untouched control.

Capture inference distinguishes stored values from latent requests. A helper
can store only ordinary values yet request an operation while its caller or an
internal clause has a live owner. For each possible request, inference follows
control through the nearest matching exact handler, including caller
continuations. A handler removes requests from its body, but its clauses bypass
that handler. A handler installed inside a live clause does not capture the
outer owner for requests confined to its own body. Resuming restores the
selected captured segment and its handlers; it does not replay the prefix
before capture. Discard must also preserve completion of owners outside the
abandoned segment whose scheduled work it skips.

Known functions, aliases, closures, recursive groups and imported functions
retain inferred control summaries. Possible paths join conservatively, without
merging unrelated exact effect identities. Generic type parameters may later
coincide; a proof cannot assume they remain distinct. Handler matching after
specialization must retain that possibility. Recursive analysis must finish
before publishing a permission. An unknown higher-order callee or open row
rejects discard when the relevant request's obligations cannot be proved
safely closable; this uncertainty alone does not reject resource-free resume-only code. There are no
source capture annotations or capture-polymorphic function types.

An unsafe or unproved discard has type-phase reason `effect.discard-unsafe`,
with its primary label on `discard` and causal request/call and live-owner
labels where known. Ordinary syntax, resolution, typing and structural usage
errors precede this capture check.

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

## Synchronous typed hooks

A hook API is an ordinary effect declaration with exactly one operation named
`publish`, whose domain and result are structurally equal under the
declaration's own parameters. Qualification precedes use-site substitution:
`Convert<A, B>` declaring `publish : A -> B` does not qualify even at
`Convert<Int, Int>`. Equal newtype representations do not establish equal
payload types. Hook APIs retain ordinary effect identities, parameter kinds
and visibility; their parameters cannot have kind `EffectRow`.

For an exact qualifying instance `H`, let `P` be its instantiated payload type.
`hook H { body }` supplies an identity handler for `H`.
`register H transformer { body }` checks an ordinary transformer from `P` to
`P`, evaluates that expression before acquisition, and retains it for the
scope. The body's result type `A` is independent of `P`.

The following rules use the scope-discharge relation above and existing partial
row union. `epsilon_init` describes evaluating the transformer expression;
`epsilon_callback` describes calling its resulting function. Their union is
subject to the existing least-row and expected-row constraints, not a new
row-union mechanism.

```sequent
family hook-scope-typing:
  T-Hook :=
    H is a well-kinded exact hook instance with payload P
    GAMMA |- body ⇒ A ! epsilon_body
    epsilon_out = scope_discharge(epsilon_body, H)
    stored dependencies and control completion are safe across the scope
    ===>
    GAMMA |- hook H { body } ⇒ A ! epsilon_out

  T-Register :=
    H is a well-kinded exact hook instance with payload P
    GAMMA |- transformer ⇐ (P -> P ! epsilon_callback) ! epsilon_init
    GAMMA |- body ⇒ A ! epsilon_body
    rho = scope_discharge(epsilon_body, H)
    epsilon_out = epsilon_init union rho union epsilon_callback union { H }
    stored dependencies and control completion are safe across the registration
    ===>
    GAMMA |- register H transformer { body } ⇒ A ! epsilon_out
```

The registration's generated clause forwards `H`, calls the transformer on the
forwarded result, and resumes with the transformed result. Its forwarded and
latent requirements remain in the outward row even if the body never
publishes. An unused callback does not execute. A root removes only its target,
not subscriber effects or another exact instance. Closed absent-target bodies
and open tails already known to lack the target are admitted; an unconstrained
tail remains ambiguous. Ordinary `handle` still requires an explicitly present
target in its body's least row.

The generated handler runs inside a registration completion owner. Selecting
its clause captures that handler and publisher-side frames, not its own owner.
Callback requests therefore use handlers surrounding the registration, not
handlers installed only around publication in its body. The callback's saved
ordinary values and lexical type/row instantiation retain their usual meaning.
Creating an ordinary closure under a handler does not store that handler.

Registration owners require completion even for pure callbacks and unused
bodies. Capture and resume preserve that obligation. Checked discard can close
a registration inside its owned abandoned control without invoking its
transformer or remaining publication callbacks. Subscriber-local discard must
preserve required completion outside that owned closure. Skipping an outside
owner or its scheduled resume remains `effect.discard-unsafe`.
Subscribers receive no surrounding resume capability.

Stored-dependency inference follows actual callback results, not merely their
types. A transformer can return a function with a new cell dependency while
retaining type `P -> P`; that result is permitted while its resource owner
surrounds the restored recipient, but cannot escape it. Callback captures,
tuples, selected evidence and imported factories obey the same rules as other
stored values. Forwarding checks the original payload against every crossed
owner before later transformers run. A later transformer that erases a
dependency cannot authorize an earlier unsafe transfer, including through an
empty identity root.

Generic target parameters may become equal after specialization. A scope must
therefore remain present even when its unspecialized body row appears to omit
its target. Dependency and completion inference preserve that possibility;
generic parameters are not fresh acquisition brands. An ordinary closure that
requests a static hook identity does not retain the active chain, but actual
stored resource dependencies remain subject to escape checking.

Malformed syntax and unknown targets retain their earlier-phase diagnostics.
Kind, ordinary type/row and structural continuation errors precede hook API
qualification. An otherwise well-formed non-hook target reports `type.hook-api`
at the target. Callback mismatches use ordinary type errors identifying the
registration's payload contract. Escape remains `type.resource-escape`; unsafe
discard retains its registration or pending-owner labels. Inference and
independent validation charge the existing owning work ledgers for added
relationships and scans.

## Scoped cleanup actions

In a cleanup expression, the action checks as `Unit -> Unit ! epsilon_cleanup`.
An anonymous function receives the `Unit` domain and result context while its
latent effects are inferred. Ordinary callback values, imported factories and
generic functions use the same type and row rules; cleanup does not require a
pure action or a universally closed row.

The scope has its body's value type. Its least outward row includes the
initializer's effects, the body's effects and the action's latent effects.
A handler installed only inside the body does not discharge the later action's
effects. A handler installed inside the action handles requests normally.
Callback shape errors use ordinary type diagnostics; missing outward effects
use ordinary row diagnostics.

The scope owns one invocation obligation independently of ordinary copies of
the callback. Completion analysis follows the actual callback, including its
imported and generic relationships. Starting the action consumes its eligibility
for another invocation but retains a required completion until it returns.
A discard may invoke an armed action in its owned closure. Skipping a running
action or unfinished close operation is `effect.discard-unsafe`; an
action-local discard may complete when the action, close operation and outside
owners still complete. Outward requests may capture and resume running cleanup.

Interpreter compatibility is checked at each action's structural closing
position. Lookup includes the action's own handlers, still-enclosing captured
boundaries and the surviving discard context, with exact lexical instantiation
and precedence. Body-local handlers already passed before that closing position
are excluded. Captured source and generated hook handlers are candidates for
this proof only; cleanup does not restore or execute them.

If the nearest matching candidate for an actual transitive action request is
a removed source or generated handler, abandonment reports
`effect.cleanup-context`, with discard, action and handler labels. An outer
same-instance handler or builtin cell interpreter cannot replace that candidate.
Action-local handlers, surviving outer handlers and still-live unshadowed
builtin cells remain usable. Unknown necessary interpreter requirements reject
the relevant abandonment, not every use of an ordinary callback. Imports,
generic coincidence and open rows retain their existing lexical authority;
neither guessed row exclusions nor a universal closed-row restriction applies.

Cleanup effects and interpreter requirements survive summaries even when a
captured handler discharged them from the original body's outward row.
Independent linked Core validation reconstructs the actual callback and closing
relationships, not a source permission or an empty discard annotation.

Stored-dependency checks apply to the saved body result, the action's captures
and its operation payloads. An action may access an enclosing cell while that
cell remains live, but cleanup does not authorize exporting its dependencies.
An escaping dependency remains `type.resource-escape`.

## Scoped cells and resource dependencies

The compiler-owned `@builtin.cell` module supplies one sealed API. The import
alias is chosen by the program; the following names denote the defining
identities, not privileged source spellings.

| Name | Contract |
| --- | --- |
| `Handle<R>` | Opaque type constructor of kind `Type -> Type`; cell access, with no source constructor. |
| `Provider<R>` | Exact sealed interface relation introduced only by acquisition. |
| `Ops<R>` | Effect with `read : Handle<R> -> Int` and `write : (Handle<R>, Int) -> Unit`. |
| `read` | Method `Handle<R> -> Int ! {Ops<R>}` requiring `Provider<R>`. |
| `write` | Method `(Handle<R>, Int) -> Unit ! {Ops<R>}` requiring `Provider<R>`. |

In `resource cell<R> c = initializer { body }`, the initializer checks as `Int`
in the preceding scope. Its effects remain outward. The body checks with a
fresh rigid kind-`Type` identity `R`, ordinary value `c : Handle<R>`, exact
`Provider<R>` evidence and a local interpreter for `Ops<R>`. The resource
expression has the body's value type. Its outward row is the union of the
initializer row and the body row after removing exactly `Ops<R>`; other
instances remain outward. Ordinary kind, type, row and structural continuation
checks precede resource dependency checking.

The identity cannot unify with an enclosing abstract parameter or another
acquisition's identity. The result type, outward row, escaping schemes and
retained evidence must not expose it. Source `impl` and `with` cannot supply
the sealed provider relation, but ordinary generic requirements may require
and forward it. Its generated methods request the exact cell effect; ordinary
exact source handlers retain lexical precedence without acquiring authority
to construct a handle or introduce provider evidence.

The scope owns release. A handle is duplicable access, not a separate release
owner. Aliases, aggregate fields, constructor transport, ordinary and imported
helpers, and repeated calls of capturing closures are permitted while their
owner remains live. Reading copies an `Int`; writing changes the cell and
returns `Unit`. Neither operation transfers ownership.

Inference tracks stored resource dependencies separately from request-carried
continuation obligations. These dependencies include actual retained handles,
callable captures, selected evidence methods and resource-indexed operation
metadata. They propagate through aliases, patterns, aggregate projections,
helpers, factories, recursive groups and polymorphic type and row
instantiation. An identity-free function result type does not erase a stored
dependency. An unused implementation environment entry does not by itself
make a constant closure resource-dependent.

A normally returning resource body must produce a value with no dependency on
the closing acquisition. An inner scope may return a dependency on a still-live
outer acquisition. Copied integers and closures retaining only those copies
may escape. Dependencies follow selected fields and actual calls; unrelated
fields and uncalled methods do not become dependencies merely because their
types match. Strict expressions publish a result only if their required
children complete normally.

The same rule covers operation operands. A source handler outside an
acquisition cannot receive a value dependent on that acquisition, even if the
resource body's eventual result is dependency-free. This applies to hidden
closure and evidence dependencies as well as explicit handles. Each owner is
checked separately: an outer-dependent payload may cross an unrelated inner
scope to a handler still inside its owner. The trusted interpreter at its own
resource boundary is an admitted recipient. Resource-free payloads may cross
to outer handlers, which may resume the captured scope.

Capture retains the resource scope's completion obligation. Checked discard
can release the scope when it belongs to the owned abandoned closure; skipping
required completion outside that closure remains unsafe. Discard confined
inside a resource scope remains permitted when outside completion obligations
are preserved. Normal and abandoned completion release inner scopes before
outer scopes, so an inner cleanup action can still use an enclosing cell.
Divergence remains divergence; checking does not prove eventual release.

Resource analysis runs even without a discard expression. It is finite and
conservative: unknown relevant higher-order behavior rejects escape or
abandonment when absence of a dependency cannot be proved. Known helper,
closure, import and row abstractions retain their inferred relationships;
they are not rejected merely for crossing an abstraction boundary. There are
no source lifetime, borrow or capture-polymorphism annotations.

A resource escape reports `type.resource-escape` at the escaping expression,
with acquisition and causal capture/call labels where known. Unsafe discard
keeps `effect.discard-unsafe` and relates the live resource obligation.
Ordinary syntax, resolution, kind, type and row failures retain precedence.
Invalid retained origin, identity, owner or provider facts are internal
validation failures, not alternative source authority.

Resource binder retention, inferred value and control relationships, exact
row contexts, summary admission and escape queries charge their existing
owning syntax, module, constraint, type, Core-construction and Core-validation
ledgers. Every proportional scan and retained collection charges before its
work or retention, including nullary effect instances and row lacks facts.
Exhaustion publishes no partial checked module or permission; ownership and
failure disposal are iterative, and a fresh sufficient budget permits retry.

Cell acquisition adds no general resource declarations, manual release,
general acquisition/destructor declarations, ownership transfer, existential package,
general foreign API, abort, exception, cancellation, suspension or general
cleanup. Local `newtype` keeps its separate erasure and escape rules; it does
not acquire a resource or its sealed authority.

## Scoped native buffers

`libraries/native_buffer.ash` declares a passive `calloc`/`free` library for the
supported GNU x86-64 profile. Its source contracts use the ordinary checked
resource, effect and foreign declarations; the compiler grants no authority to
the module's filename or exported spellings.

| Name | Contract |
| --- | --- |
| `Buffer<R>` | Declared resource family; its access value is duplicable while that exact owner is live. |
| `Provider<Buffer<R>>` | Sealed exact provider supplied by acquisition. |
| `Outcome<T>` | Ordinary data `Success(T)` or `Failure(Error)`. |
| `Error` | Ordinary nullary `InvalidLength`, `AllocationFailed`, `InvalidIndex`, `InvalidByte`. |
| `Ops<Buffer<R>>` | `length : Buffer<R> -> Int`, `read : (Buffer<R>, Int) -> Outcome<Int>`, `write : (Buffer<R>, Int, Int) -> Outcome<Unit>`. |
| `length`, `read`, `write` | Ordinary associated methods requiring the exact provider and operation instance. |

After importing the source module as `Buffer`,
`resource Buffer.Buffer<R> b = length { body }` checks its initializer as `Int`
in the preceding scope. The checked header introduces fresh rigid `R`, local
private native State, ordinary length data, the access value `b : Buffer<R>` and
its associated provider. No native State is stored in ordinary data. The
`acquired_only` codec yields `Outcome<T>` for body type `T`, including nested
`Outcome` values. The outward row retains ordinary effects after removing only
the exact associated/native instances listed by the original header.

Results, outward rows, stored captures, evidence and operation metadata cannot
export the acquired identity. An inner scope may return an outer dependency
whose owner remains live. Success projection preserves body dependencies;
allocation refusal supplies no access value. Capture and resume move the same
owner without reacquisition. Exact ordinary handlers retain precedence,
including generic coincidence and imported callbacks; ordinary row/lacks rules
continue to apply. Cleanup cannot replace a removed override with a default
source handler.

The provider proves neither allocation success nor numeric bounds. The library
and common checked primitives enforce those at runtime. Its current native
build does not add support for ordinary local-newtype/non-resource lexical
dictionary image records: those source/Core programs retain their independent
rules and receive the existing unsupported-build diagnostic.

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
outer parameters in first-occurrence order: ordinary type and effect-row-tail
occurrences in the value type share that order, followed by first occurrences
found only in requirements. A name occurring only in ordinary type positions
has kind `Type`; one occurring only as an effect-row tail has kind `EffectRow`;
using the same name in both roles is invalid. In either form, a requirement
without a determination edge requires every free variable in its complete
application to occur in the value type. For a determined interface, every free
variable in the determinant key slice must occur in the value type; a
dependent-only binder may remain quantified in the constrained scheme.
Determination never propagates between requirements.
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
An outer `newtype` is nominal for this rule exactly like ordinary data.

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
Here and in the global judgments, that helper also uses each occurrence's
retained lexical evidence scope, not the scope at closure time.

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

## Scoped exact evidence

A sequential `with Interface<arguments> { methods }` supplies one exact complete
application. Its arguments must be explicit, well-kinded, and inference-free;
enclosing rigid parameters are permitted. At least one active local nominal
must occur structurally in its selection key: all arguments for an interface
without a determination edge, or just the determinants otherwise. A local
nominal beneath another constructor counts. Occurrence only in a dependent
argument does not count. No head matching or representation-derived evidence
is introduced, and module implementation coherence and orphan rules are unchanged.

Two simultaneously active sources for the same interface cannot have
identity-equal keys. Identical complete applications are `evidence.duplicate`;
equal keys with unequal dependent tuples are `evidence.determination-conflict`.
Disjoint scopes may supply different methods for the same nominal identity.
Nested distinct nominal identities remain distinct keys.

The declaration supplies every interface method exactly once. Contiguous
equations form groups as in an implementation; groups may appear in any order.
Check membership before checking bodies. Substitute the complete interface
arguments into each required method type and check its equations with fresh,
independent rigid method parameters in declared order and kinds. Their spellings
do not enter the body's source type namespace. Existing pattern, coverage,
contextual checking, and closed effect-row rules apply unchanged.

Bodies see the preceding term and evidence scopes and retain the enclosing
definition's abstract and exact-current contexts. The new source is unavailable
in every supplied body, so it grants no implicit self or sibling selection.
Preceding ordinary values and recursive functions may be captured. Each method
is a resume barrier: an enclosing clause's capability cannot be captured
(`effect.resume-capture`), while a handler inside the method owns its own
capability. With no enclosing clause, `effect.resume-outside-clause` still owns
the failure. Admit the source only after every supplied method checks.

The source is available in the following block remainder, including bodies
defined there. Each pending occurrence retains that original lexical scope
through inference closure; leaving the block does not change its selection
context or force early closure. New occurrences outside cannot select it.
A checked closure may retain the selected ordinary method functions and their
captures. A selected `N -> Int` method can leave an inner evidence block while
an enclosing `N` remains active. At the nominal boundary, existing outward
type, row, scheme, requirement, and inferred-binding escape checks still apply.
An identity-free closure may cross that boundary. No lexical evidence fact is
exported through a scheme, inferred requirement, summary, import, or package.

This complete module is rejected with `evidence.missing-local-key`: a nominal
introduced at module level is not an active local nominal.

```ash
interface Read<A> {
    read : A -> Int
}

newtype Token = Token(Int)

main : Unit -> Int
main () = {
    with Read<Token> {
        read ignored = 42
    }
    read(Token(0))
}
```

## Constraint satisfaction and checked evidence

Evidence selection uses exact nominal identities. A `newtype` representation
supplies no interface evidence for its owner: an implementation for the
representation does not satisfy a goal for the `newtype`, and wrapping or
unwrapping does not copy, lift, or select evidence.

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
2. the exact current implementation with that key;
3. the lexical source with an identity-equal key in the occurrence's original
   scope; or
4. the unique visible implementation whose independently freshened key
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

In particular, lexical `R<N, Int>` conflicts with a pending root `R<N, Bool>`
during mandatory improvement. A recursively generated complete prerequisite
`R<N, Bool>` instead skips that different complete lexical application and may
use concrete evidence for `Bool`. Lexical evidence adds no key barrier to
recursive complete-goal selection.

A concrete implementation candidate is freshened independently with its declared binder
kinds. First-order matching may substitute only that candidate's head
parameters, must preserve their kinds, and matches the complete application.
Matching cannot solve or refine a variable in the goal, synthesize a type
lambda, or use higher-order unification.

Selection receives the ordered abstract requirements of the current global or
implementation, an optional current implementation, the occurrence's lexical
sources, the effective
implementation environment, an active-goal set, and one resolved complete
interface application. It does not receive the determination snapshot; the
owning closure has already applied that gate to the pending root. Selection
considers sources in this order:

1. An identity-equal complete abstract requirement from the current definition.
2. Exact current-implementation evidence for an implementation method's rigid
   complete head.
3. Identity-equal complete lexical evidence in the occurrence's original scope.
4. The unique matching concrete implementation in the effective environment.

Abstract and exact-current evidence therefore precede lexical evidence, which
precedes a matching generic concrete implementation. Exact current evidence
uses the current implementation's already-abstract prerequisite evidence; it
does not freshly instantiate the implementation or select its prerequisites
again. The general concrete branch excludes the current implementation. A
concrete match may substitute only that implementation's bound head parameters.
It selects prerequisites recursively in declaration order.

The rules below describe successful selection. `earlier_source_absent` means
that the preceding entries in the ordered search above did not apply.
`select_all(abstracts, current, lexical, effective, active, goals)` applies this same
selection judgment to `goals` in order with the supplied abstract, current,
lexical, effective, and active contexts. It returns the corresponding ordered evidence
sequence and never consults the determination snapshot.

```sequent
family evidence-selection:
  Select-Abstract :=
    goal contains no inference variable
    requirement = identity_equal_complete_requirement(abstracts, goal)
    ===>
    abstracts; current; lexical; effective; active |- goal
      ⇓ Abstract(requirement, interface_methods(goal.interface))

  Select-Current-Implementation :=
    goal contains no inference variable
    no identity-equal complete abstract requirement exists
    current has the same interface and exact rigid complete head as goal
    ===>
    abstracts; current; lexical; effective; active |- goal
      ⇓ Implementation(current, identity, abstract_prerequisites, impl_methods(current))

  Select-Lexical :=
    goal contains no inference variable
    earlier_source_absent(abstracts, current, goal)
    source = identity_equal_complete_source(lexical, goal)
    ===>
    abstracts; current; lexical; effective; active |- goal
      ⇓ Lexical(source, interface_methods(goal.interface))

  Select-Concrete-Implementation :=
    goal contains no inference variable
    earlier_source_absent(abstracts, current, lexical, goal)
    goal is not in active
    unique_kind_preserving_match(effective excluding current, goal)
      = implementation, substitution
    prerequisite_goals = substitute(substitution, implementation.prerequisites)
    select_all(abstracts, current, lexical, effective, active union {goal}, prerequisite_goals)
      = evidence
    ===>
    abstracts; current; lexical; effective; active |- goal
      ⇓ Implementation(implementation, substitution, evidence, impl_methods(implementation))
```

The matching substitution is applied to every prerequisite before recursive
selection. Sibling prerequisite goals preserve declaration order, share the
same abstract, exact-current, lexical, and effective environments, and keep their parent
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

Checked selections have three forms. Each root retains one complete
interface application. An abstract selection records its requirement identity
and ordered interface methods. A lexical selection records its distinct
source identity and ordered interface methods. An implementation selection records the stable
implementation identity, its head substitution, its ordered
prerequisite selections, and its implementation-method identities. These are
compiler annotations, not source values or runtime dictionaries.

```text
EvidenceSelection =
    Abstract(requirement, methods)
  | Lexical(source, methods)
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

The notation leaves occurrence-owned lexical contexts implicit here. Each
pending field supplies the lexical scope retained at its own occurrence;
`close_and_select` does not substitute the scope at closure time.

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

After resolution allocates all nominal and parameter identities, kind
checking derives and freezes every module-level nominal constructor kind and every
canonical local effect and interface parameter vector and interface determinant
record. Imported effect facts and the pre-frozen local effect headers supply
the identity and parameter authority needed while checking computation rows in
module-level constructor payloads and `newtype` representations. Those checks
include nested effect-instance arity, positional argument kinds, and row
formation in combined cross-declaration source and structural type order. Only
after all those types are kind-correct does checking construct and traverse the
module-level newtype-only representation graph. It then completes local effect-declaration,
global-signature, interface, implementation-head, and prerequisite checks in
deterministic dependency, declaration, binder, and type traversal order. No
body or public summary can observe a partially admitted kind or effect registry
or representation graph. Local-newtype representations are kind-checked under
their enclosing type scope when resolved-kind checking visits body annotations
in source order; they are not vertices of that module representation graph.

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
    PHI = authenticated imported effects plus pre-frozen local effect headers
    IOTA = imported interface parameter vectors and determinant positions
      plus pre-frozen local interface parameter vectors and determinant positions
    for each module-level constructor payload and newtype representation in combined order,
      DELTA; empty_OMEGA; XI |- value type ok
    the module-level newtype-only representation graph is acyclic
    local-newtype representations pass resolved body-annotation kind checks in lexical scope
    GAMMA_D = checked kinded schemes imported from direct dependency summaries
    each local effect completes the declaration checks above
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
    main is monomorphic Function(Unit, result_type ! effects) with no requirements
    effects is empty or a closed row of admitted owner-free native instances
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
`checked_definitions` and derives its source-body-free checked summary in one
atomic publication after the complete module succeeds. Any failure publishes
neither result. Public local declarations, effects, and implementations retain
the facts established by their owning judgments. The summary retains public
kinds, effects and operations, and the hidden kind and identity closure
required by public schemes, constructors, effects, interfaces, ordered parameters and
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
Publication also completes capture inference and retains the inferred control
summary of each exported function value. These private summaries carry the
type and effect identities needed to check calls after specialization, without
importing or reinferring dependency source bodies. Capture failure publishes
neither a checked module nor its summary.

For every module-owned `newtype` identity retained by a summary, the canonical hidden closure includes
its declaration kind, ordered parameters, sole constructor identity and owner,
representation template, access, origin, and representation provenance. A
transparent projection exposes the source facts authorized by visibility;
opaque and private projections do not expose the representation or constructor.
Checked lexical facts remain separate from this summary closure, as specified
by [elaboration](elaboration.md#module-linking-and-entry-generation).

The filled occurrence fields and checked modules become inputs to
[module linking and linked interface-evidence validation](elaboration.md#module-linking-and-entry-generation).
That specification owns their retention through linking and the validator's
authentication inventory. Core synthesis requires the validated result, and
neither validation nor synthesis selects implementations again.

`T-Program` checks each module after all its dependencies. The entry must
declare exactly one local `main`; an imported `main` cannot satisfy the
premise. Its checked scheme must have no type parameters, domain `Unit`, a
closed result and no requirements. Its latent effect row must be empty or a
closed row containing only admitted owner-free native instances. The linked
entry is wrapped by the explicit native Core interpretation when needed; its
outward row after exact subtraction must be empty. Entry failures have this
order: missing local `main`, polymorphic scheme, wrong domain, inadmissible effect
row, open result, then constrained scheme. An ordinary outward effect, unresolved
row tail or unsupported effect requirement is `entry.main-effects`. This preserves
the relative order of the predecessor entry-shape failures. The closed
`result_type` is the type observed for the whole program, and `main` need not be
public. Every evidence obligation in a well-shaped `main` body must therefore
select concrete or scoped exact evidence at its occurrence; `main` supplies no
abstract requirements.

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
`newtype` shape, parameter lists, and determination syntax. Resolution owns
duplicate names, `resolve.newtype-constructor-name`, inaccessible constructors,
duplicate interface binders, and unknown names in a determination side. Kind
checking owns invalid ordinary payload and newtype representation kinds.
Static nominal admission owns `newtype.recursive-representation` only after all
those payload and representation kind checks succeed. Interface-application
checking owns missing or extra arguments as `interface.argument-count` before
kind checking owns an arity-correct positional failure. Interface admission
owns an invalid partition as `interface.determination-parameter` and an
incomplete method seed as `interface.method-parameter`.

For local `newtype`, resolution additionally owns sequential visibility and
lexical identity assignment; kind checking owns the representation under the
enclosing type scope. Ordinary source typing owns `type.local-nominal-escape`
after zonking at the declaration's outward boundary. An earlier name, kind, or
ordinary typing failure retains its existing ownership. Linked and Core
validation reject forged local facts and scope relations only after source
checking succeeds.

For local evidence, resolution, application arity, and positional kinds precede
local-key admission. A missing active local nominal in the key is
`evidence.missing-local-key`. Active-key duplicate or conflict checking follows,
then complete method membership, then method bodies. A missing method is
`evidence.missing-method`, a repeated group is `evidence.duplicate-method`, and
an unrelated group is `evidence.extra-method`. Existing type, pattern, coverage,
improvement, and resume failures keep their owners.

Missing-key diagnostics label the new header. Duplicate and conflicting sources
label that header and relate the earlier header. Missing methods label the
header and relate the required interface method. Repeated groups label the
repeated name and relate the earlier group name; extra groups label that name
and relate the interface declaration. Forged checked source or selection facts
are internal validation failures, not source diagnostics.

Lexing owns the reserved effect keywords. Parsing owns malformed effect
declarations, rows, requests, handlers, clauses, and completion forms.
Resolution owns unknown effects or operations, namespace and visibility
failures, stable identity assignment, row-tail scope, and `resume` or `discard`
outside a clause.
Effect instance arity precedes positional kind checking. Kind checking owns
an invalid effect argument, row tail, or forbidden use of `EffectRow`.
Row formation owns a duplicate written member and an unsatisfied lacks fact.
Ordinary expression typing owns operation operand and latent-row failures.
Handler checking owns target membership, clause coverage and patterns,
the shared result and output rows, and capability consumption and barriers.
Capture checking owns unsafe
or unproved discard after ordinary checking succeeds. Entry checking owns a
nonempty linked entry row.

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

1. parsing and recovery, including `newtype` and effect forms;
2. name resolution, including nominal and effect identities, row-tail scope,
   and resume scope;
3. local effect-header formation, then module-level constructor-payload and
   `newtype`-representation kinds in combined declaration and structural type
   order, including effect-instance arity, positional argument kinds, and row
   formation encountered within those types;
4. the module-level newtype-only representation-cycle pass;
5. remaining effect declarations and complete applications, with arity before
   positional argument kinds and effect-row formation;
6. determination partition admission;
7. method-binder and method-kind checks, then method seed and function shape;
8. implementation prerequisites in current-then-earlier source order with
   complete identity before key identity, then variable-head, containment,
   determination coverage, orphan, decrease, and privacy;
9. effective-environment pair coherence;
10. implementation method membership and bodies;
11. per-occurrence ordinary and row unification, effect expression and handler
    checking, unresolved-key ambiguity, atomic improvement and dependent
    conflict, remaining dependent ambiguity, full-application selection,
    active-goal cycle detection, and unsatisfied evidence; and
12. whole-module inference closure, method ambiguity, capture checking, and
    publication, then entry checking, summary admission, linking, elaboration,
    and Core validation.

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
Capture-summary construction, composition, identity admission and validation
charge their existing owning work ledgers, including retained control and
type metadata, candidate comparisons and filtered scans. Capture queries use
finite control states and iterative walks; exhaustion publishes no partial
permission. A retry with sufficient work must agree with a fresh run.

Kind traversal, cloning, equality, hashing, rendering, substitution,
unification, matching, summary admission, validation, and disposal use
iteration or explicit bounded work stacks. Resolved kind checking,
elaboration, and retained kind cloning charge their owning type-work ledger.
Method binder records, schemes, instantiation arguments, substitutions,
adapters, and Core types also charge their owning type-work ledger; binder-list
syntax charges the syntax budget. Core construction and independent Core
validation retain separate cumulative ledgers.
Newtype declaration and constructor records, representation types and
substitutions, summary and linked facts, conversion nodes, generated binders
and functions, transform copies, and Core validation facts charge their
existing owning syntax, type-work, graph-wide, Core-construction, or
Core-validation ledgers. Every proportional allocation or traversal charges
before publication.
Lexical nominal and constructor names, canonical local facts, scope nodes,
and independent validator indices charge their owning ledger before allocation
or publication. Outward escape inspection charges the existing iterative type
and row traversal, including preceding binding types affected by inference.
Failure publishes no partial lexical registry or checked module; lexical scope
restoration and disposal remain iterative, and a fresh budget permits retry of
the same logical input. Local identities add no runtime resource ledger.
The module type-work ledger also owns newtype representation substitution and
graph construction and traversal. Each discovered representation occurrence,
retained edge or owner-index entry, pending-stack entry, and visited or active
entry charges before retention or traversal. This is not interface constraint
work. Exhaustion is `internal.resource.type-work`; it publishes no checked
module or summary. The partial graph is released iteratively, and the same
logical input may be retried with a replenished type-work budget.
Interface, implementation, evidence, and linked-authentication traversal or
comparison charge the graph-wide constraint budget; retaining a structural
type, substitution, kind, or binder-kind record additionally charges the
applicable type-work ledger. A kind node, unary application node, or
binder-kind record is charged before its owning visit or retention. Retaining
a record also charges the type and kind nodes it copies. Comparing a kind pair
charges one comparison unit in the traversal's owning ledger. A failed
operation publishes no partial checked fact or summary.

These ledgers are bounded compiler-resource policy. They do not add runtime kind
values or evaluator work, alter newtype erasure or effect evaluation, or make a
resource ceiling part of Ash value semantics.

Ash has no kind polymorphism, general higher-rank source values, explicit
source term type application, type lambdas, higher-order unification, broad
application-shaped local generalization, subtyping, implicit conversions,
explicit structural recursive-type operators, or polymorphic recursion.
Unauthenticated nested Core schemes remain invalid. Interfaces add no
associated declarations, associated-output projections or equations, multiple
or partial edges, neutral parameters, reverse or injective determination,
specialization, priority, default or negative implementations, inferred global
requirements, first-class dictionaries, runtime implementation lookup, or
interface-specific Core mechanism. Ordinary data declarations may refer to
themselves and to other nominal declarations in the same module; `newtype`
representations retain the narrower acyclic rule above. Recursive
global visibility does not cross a module boundary. The interface evidence
family is not effect-handler or provider authority, proof or proposition
evidence, common universal evidence, or an existential package. An effect row
is a computation requirement, and a lexical handler interprets only its exact
effect instance; neither is inferred from interface determination.
