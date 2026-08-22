# Static Semantics

Mini-Ash has `Int`, `Bool`, `Unit`, rigid type variables, structural tuples,
parameterized nominal algebraic data types, and unary functions. A tuple
contains at least two element types. Surface `domain -> codomain` denotes a
function type.

Kinds are internal. `Type` is the kind of every source-admitted value type. A
nominal declaration with `n` parameters has an internal constructor kind with
`n` `Type` inputs and one `Type` result. Source type applications must be
saturated, so no constructor-kinded type survives resolution.

Type equality is one shared rule. `Int`, `Bool`, and `Unit` equal themselves;
tuples, functions, and nominal arguments compare structurally; type variables
compare by binder identity; nominal constructors compare by stable declaration
identity. Equal spelling or constructor shape does not make two nominal
declarations equal.

The typing environment `GAMMA` maps resolved binder identities to rank-1
schemes. A scheme `forall parameters. type` quantifies only its outermost
monotype. Looking up a scheme replaces each quantified parameter with a fresh
inference variable. Rigid variables from annotations never unify with a
different type.
The judgment `GAMMA |- expression ⇒ type` synthesizes a type, while
`GAMMA |- expression ⇐ type` checks an expression against an expected type.

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
    instantiate(scheme) = type
    ===>
    GAMMA |- x ⇒ type

  T-Check-Inferred :=
    GAMMA |- expression ⇒ type_1
    type_1 = type_2
    ===>
    GAMMA |- expression ⇐ type_2
```

Here `n` ranges over integer literals, `b` over Boolean literals, and `x` over
resolved occurrences. `instantiate` replaces all outer quantified variables
at once. The equality premise in `T-Check-Inferred` uses the single
type-equality rule above after inference solutions are applied.

## Tuples and constructors

Tuple elements synthesize from left to right. A constructor declaration under
`Owner<A_1, ..., A_n>` contributes a scheme quantified over those declaration
parameters. Instantiating a nullary constructor produces the applied owner
type. Instantiating a payload constructor produces an ordinary unary function
from its substituted semantic payload to that owner. Multiple declared fields
form one tuple payload.

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
parameter and result types. Application first synthesizes the function, then
checks the argument against its domain.

```sequent
family function-typing:
  T-Function-Check :=
    pattern ⇐ domain => bindings
    exhaustive([pattern], domain)
    GAMMA, bindings |- body ⇐ codomain
    ===>
    GAMMA |- fn(pattern) { body } ⇐ Function(domain, codomain)

  T-Apply :=
    GAMMA |- function ⇒ Function(domain, codomain)
    GAMMA |- argument ⇐ domain
    ===>
    GAMMA |- function argument ⇒ codomain
```

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

choose true 41
```

The same usefulness relation checks equation groups. Each equation pattern
consumes one arrow domain, so `f left right = body` checks against two nested
arrows. All clauses have the same positive pattern count. The relation also
defines local-pattern irrefutability: a local `let` pattern is admitted only
when its singleton pattern set covers the initializer type.

The executable test `static_semantics_irrefutable_tuple_binding_is_executable`
checks local destructuring:

```ash
{
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
excludes inference variables free in `GAMMA`. Every other unannotated binding
keeps the inferred monotype, including an application that returns a function.
An annotation checks a monotype and introduces no type parameters. A use of a
generalized local binder instantiates its scheme as in `T-Variable`.

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
{
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

add 20 22
```

## Inference and rank-1 restrictions

Inference variables are compiler facts, not source types. Unification compares
primitive and nominal identities, descends structurally through applications,
tuples, and functions, and solves inference variables only with types of kind
`Type`. The occurs check rejects a solution containing the variable being
solved with `type.infinite`. If the program result still contains an unsolved
inference variable, typing rejects it with `type.ambiguous`.

Global type parameters and generalized local parameters are rigid within their
definitions. A recursive self-use receives the same rigid arguments rather
than a fresh instantiation. A recursive call that would require a distinct
instantiation is rejected with `type.polymorphic-recursion`. Local recursive
annotations introduce no type parameters and remain monomorphic.

There are no nested schemes or polymorphic function domains. Generalization
occurs only at global interfaces and eligible local function bindings. Source
expressions cannot provide explicit type arguments.

The executable test `static_semantics_rank_one_polymorphism_is_executable`
checks parameterized data, one implicitly quantified global, and one eligible
local generalization:

```ash
type Option<A> =
    None
    | Some(A)

id : A -> A
id value = value

{
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
{
    let rec value : Int = 1
    value
}
```

## Primitive operations

Addition and multiplication require two `Int` operands and synthesize `Int`.
Equality compares only integers in Mini-Ash and synthesizes `Bool`.

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
file is rejected with `type.operator-operand`:

```ash
true + 1
```

## Globals and programs

An equational interface must expose at least as many arrow layers as each
clause has patterns. The patterns receive those domains in order, and the body
checks against the remaining codomain. An inline operational header supplies
its domain and result directly. One typed parameter gives that domain; multiple
typed parameters combine into one tuple domain. Free uppercase names in either
interface become ordered implicit type parameters. Each form contributes one
rank-1 function scheme. All global schemes form `GAMMA_G` before any body is
checked.

```sequent
family global-and-program-typing:
  T-Equational-Global :=
    patterns ⇐ domains => bindings
    useful(previous_clauses, patterns, domains)
    GAMMA, bindings |- body ⇐ codomain
    ===>
    GAMMA |-clause name patterns = body ⇐ Function(domains, codomain)

  T-Operational-Global :=
    header_pattern ⇐ domain => bindings
    exhaustive([header_pattern], domain)
    GAMMA, bindings |- body ⇐ codomain
    ===>
    GAMMA |-definition fn name(header_pattern : domain) -> codomain { body } ⇒ name : Function(domain, codomain)

  T-Recursive-Program :=
    scheme_i = forall free_parameters_i. definition_type_i
    GAMMA_G = { name_i : scheme_i | 1 <= i <= n }
    for each i, GAMMA_G |-definition definition_i ⇒ name_i : scheme_i
    GAMMA_G |- result ⇒ result_type
    ===>
    |-program definitions; result ⇒ result_type
```

The complete equational group must also be exhaustive under the shared
coverage relation. The definition judgments check parameters and bodies but do
not determine global visibility. `T-Recursive-Program` establishes all global
schemes and synthesizes the file type from its required result expression.
Each body checks with its own parameters rigid, and recursive uses obey the
monomorphic-recursion rule above.
Semicolons in these judgments separate semantic fields and are not source
punctuation. Resolution has already ensured global-name freshness and
equational name agreement. For `T-Operational-Global`, one typed source
parameter is `header_pattern`; two or more typed source parameters normalize to
one tuple `header_pattern` and one tuple `domain`. Pattern checking returns all
body bindings, and singleton exhaustiveness requires the operational header to
be irrefutable.

The executable test `static_semantics_operational_tuple_pattern_is_executable`
checks a destructuring operational parameter:

```ash
fn add((left, right) : (Int, Int)) -> Int {
    left + right
}

add(20, 22)
```

Mini-Ash has no higher-rank or higher-kinded polymorphism, explicit source type
application, broad application-shaped local generalization, overloading,
subtyping, implicit conversions, explicit structural recursive-type operators,
or polymorphic recursion. Nominal declarations may refer to themselves and to
other nominal declarations in the same file.
