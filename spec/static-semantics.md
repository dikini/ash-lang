# Static Semantics

Ash has `Int`, `Bool`, `Unit`, rigid type variables, structural tuples,
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
declarations equal. Interface requirements are not `Type` variants and do not
participate in this equality rule or in ordinary unification.

The typing environment `GAMMA` maps resolved `BinderId` identities to rank-1
constrained schemes. Interface methods do not have binder identities. The
immutable method registry `MU` instead maps each resolved `MethodId` to its
owning `InterfaceId`, interface parameter, declared method type, declaration
order, and provenance. A constrained scheme has three fields:

```text
ConstrainedScheme =
    ordered outer type parameters
    ordered interface requirements
    source value type
```

The outer parameters quantify only the value type and the types within the
requirements. Looking up a scheme replaces every quantified parameter with a
fresh inference variable, instantiates the value type, and creates one evidence
obligation for each requirement in source order. A scheme with no requirements
has the ordinary `forall parameters. type` behavior. Rigid variables from
annotations never unify with a different type.

The judgment `GAMMA |- expression ⇒ type` synthesizes a type, while
`GAMMA |- expression ⇐ type` checks an expression against an expected type.
These judgments also consult the fixed method registry `MU` and record pending
requirements on the exact constrained-term occurrences that create them. The
ordinary rules omit `MU` and that structural output. The interface section
defines the distinct method-occurrence rule, and the selection section defines
how a definition closes the pending requirements.

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

Inference variables are compiler facts, not source types. Unification compares
primitive and nominal identities, descends structurally through applications,
tuples, and functions, and solves inference variables only with types of kind
`Type`. The occurs check rejects a solution containing the variable being
solved with `type.infinite`. While checking one complete module, typing
accumulates the substitution `THETA` and records each allocated inference
variable's causal origin in allocation order. Successful module checking
requires every allocated inference variable to occur in the domain of
`THETA`. Otherwise typing selects the first unsolved identity in allocation
order and reports `type.ambiguous` at its retained causal origin. This check
includes discarded expressions and unused initializers.

Global type parameters and generalized local parameters are rigid within their
definitions. A recursive self-use receives the same rigid arguments rather
than a fresh instantiation. A recursive call that would require a distinct
instantiation is rejected with `type.polymorphic-recursion`. Local recursive
annotations introduce no type parameters and remain monomorphic.

There are no nested schemes or polymorphic function domains. Generalization
occurs only at global signatures and eligible local function bindings. Source
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

## Interfaces and constrained schemes

An interface has one parameter of kind `Type` and a nonempty ordered method
list. Every method type contains that parameter, has `Function` as its
outermost constructor, and has no other free type variable. Interface
declaration order fixes the order of the method positions used by checked
evidence.

The following judgments check an interface method and then the complete
interface. `free_type_variables` compares resolved binder identities, not
spellings. The equation `method_type = domain -> codomain` decomposes only the
outermost constructor; it does not search `domain` or `codomain` for another
arrow. Resolution has already established method-name freshness.

```sequent
family interface-well-formedness:
  WF-Interface-Method :=
    free_type_variables(method_type) = {parameter}
    method_type = domain -> codomain
    ===>
    interface<parameter> |-method method_name : method_type ok

  WF-Interface :=
    methods is nonempty
    for each method, interface<parameter> |-method method ok
    ===>
    |-interface visibility interface<parameter> { methods } ok
```

After interface admission, a method occurrence consults `MU` by `MethodId`
rather than `GAMMA` by `BinderId`. The registry fact determines the method's
one-requirement constrained scheme. Instantiation records that requirement on
the occurrence for later selection.

```sequent
T-Method-Occurrence :=
  MU(method_id) = interface_id, parameter, method_type
  scheme = ConstrainedScheme([parameter], [interface_id<parameter>], method_type)
  instantiate(scheme) = type, [obligation]
  record_pending(occurrence(method_id), [obligation])
  ===>
  GAMMA; MU |- method_id ⇒ type
```

A global signature carries an ordered requirement list after its complete
value type. Free uppercase variables become candidate outer parameters in
first-occurrence order: first occurrences in the value type come first, then
first occurrences found only in requirements. An accepted requirement must use
only parameters that occur in the value type. This rejects a requirement-only
parameter instead of silently adding an inferred input. Requirements in one
signature must be distinct by interface identity and argument type. A public
global may require only public interfaces. A private global may also require a
private interface declared in its own module.

The judgment below constructs the checked constrained scheme for either an
equational or operational global signature. `determined` means that every type
variable in the requirement argument occurs in the value type.

```sequent
WF-Global-Signature :=
  parameters = ordered_free_parameters(value_type, requirements)
  for each requirement, requirement is a resolved interface application
  requirements are pairwise identity-distinct
  for each requirement, determined(requirement, value_type)
  visibility = public implies every required interface is public
  checked_scheme = ConstrainedScheme(parameters, requirements, value_type)
  ===>
  module |-signature visibility name : value_type where requirements ⇒ checked_scheme
```

Requirements remain explicit on module-level signatures. Body checking never
infers a requirement and adds it to a checked global or export summary.
Equational and operational presentations with the same value type and
requirements produce the same constrained scheme.

A method type that omits the interface parameter or introduces another free
type variable is `interface.method-parameter`. This check precedes the outer
decomposition. If it succeeds but the method type's outermost constructor is
not `Function`, the failure is `interface.method-not-function`. Duplicate
identity-equal global requirements are `constraint.duplicate-requirement`,
requirement-only parameters are `constraint.undetermined-parameter`, and a
public signature that exposes a private interface is
`constraint.private-interface`.

## Implementations

An implementation head fixes one interface application. Free uppercase
variables in the head become ordered rigid parameters in first-occurrence
order. A bare type-variable head is invalid. A prerequisite cannot bind a new
parameter: every free variable in a prerequisite must already occur in the
head. A public implementation must implement a public interface and may name
only public interfaces in its prerequisites.

The orphan rule admits an implementation in a module that owns the interface
or the outer nominal constructor of the head argument. Primitive and structural
heads have no nominal owner, so only the interface owner can implement them.
For example, an implementation for `Equal<Option<A>>` may be declared by the
owner of `Equal` or by the owner of `Option`; neither a third module nor the
owner of a nominal nested below the outer `Option` may declare it.

After freshening and alpha-normalizing a generic implementation, the type
argument of every non-ground prerequisite must be a strict syntactic subterm of
the head argument. The comparison uses resolved structure and identities. A
ground prerequisite is exempt from this check; a cycle made only from ground
prerequisites is detected later during selection.

These premises admit an implementation header. `owner` returns the defining
module of an interface or outer nominal constructor, when one exists.

```sequent
WF-Implementation-Header :=
  parameters = ordered_free_parameters(head_argument)
  head_argument is not a type variable
  free_type_variables(prerequisites) is a subset of parameters
  module = owner(interface) or module = owner(outer_nominal(head_argument))
  for each non-ground prerequisite,
    prerequisite.argument is a strict syntactic subterm of head_argument
  visibility = public implies interface and prerequisite interfaces are public
  checked_header = ImplementationHeader(visibility, parameters, interface, head_argument, prerequisites)
  ===>
  module |-impl visibility interface<head_argument> where prerequisites ⇒ checked_header
```

An implementation supplies every interface method exactly once and supplies no
other method. Contiguous equations with one method spelling form one method
definition. Method groups may appear in any order, but each definition checks
against its interface method type after substituting the head argument for the
interface parameter. The implementation head parameters stay rigid. All
ordinary globals and implementation methods in one module share one
simultaneous recursive scope.

Substitution acts on occurrences inside the method domain and codomain without
changing the outer `Function` constructor. The resulting `expected` type is
therefore callable when the positive-pattern equation group checks against it.

A generic implementation method has the conceptual checked scheme shown below.
Each prerequisite contributes its interface's method positions in prerequisite
and interface declaration order.

```text
forall head_parameters.
    evidence(prerequisite_1) ->
    ... ->
    evidence(prerequisite_n) ->
    substituted_method_type
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
    |-impl-membership interface<head_argument> { body } ok

  T-Implementation-Method :=
    method : method_type in declared_methods(interface)
    expected = substitute(interface_parameter, head_argument, method_type)
    head_parameters = ordered rigid parameters of head_argument
    current = the exact current implementation header and identity
    abstracts = ordered abstract evidence for current.prerequisites
    head_parameters are rigid while checking the method
    GAMMA; abstracts; current; effective
      |-equations grouped_methods(body, method) ⇐ expected, obligations
    close_and_select(abstracts, current, effective, empty_active, obligations)
      = selections
    ===>
    GAMMA; effective |-impl-method grouped_methods(body, method)
      ⇐ expected, selections
```

The abstract evidence in `T-Implementation-Method` has one requirement identity
per declared prerequisite in order. Exact current-implementation selection may
use only the same rigid head and that abstract prerequisite evidence. Closing
the method fills every occurrence-owned evidence field before the checked
method can enter the module result. The `selections` output denotes those
structural field contents, not a detached selection vector.

A public implementation that exposes a private implemented or prerequisite
interface is `impl.private-interface`. A bare variable head is
`impl.variable-head`; a prerequisite-only variable is
`impl.prerequisite-variable`; an owner violation is `impl.orphan`; and a
non-decreasing generic prerequisite is
`impl.prerequisite-not-decreasing`. Missing, repeated, and extra method groups
are `impl.missing-method`, `impl.duplicate-method`, and `impl.extra-method`.
Method body failures retain the existing `type.*`, `pattern.*`, and
`coverage.*` reasons.

The effective implementation environment of a module contains all its local
private and public implementations plus every public implementation defined by
a direct dependency. Complete and targeted imports both admit those anonymous
facts. A target selector changes source-name visibility only. An imported
implementation is not copied into the current module's export summary and is
therefore unavailable to a dependent that does not import its defining module
directly. Multiple direct routes to one stable implementation identity
deduplicate before comparison.

Every pair of distinct implementation heads for one interface in the effective
environment is freshened independently. If the heads unify, the environment is
rejected with `impl.overlap`. Prerequisites, source order, dependency order, and
import order never select a winner. Header admission precedes environment
construction, so an invalid local header reports its own failure and cannot
cause a secondary overlap failure. Membership and bodies are checked only after
overlap succeeds.

```sequent
WF-Effective-Implementations :=
  local = admitted_local_impls(module)
  effective = local union public_impls(direct_dependencies(module))
  effective is deduplicated by stable implementation identity
  for each distinct pair for one interface,
    not unifies(freshen(left.head), freshen(right.head))
  ===>
  module |-implementations effective coherent
```

## Constraint satisfaction and checked evidence

Instantiating a constrained term creates one evidence obligation for each
requirement in source order. Ordinary bidirectional typing determines the type
argument of each obligation. Selection cannot solve an inference variable to
make an implementation applicable. An obligation that still contains an
unsolved inference variable when its owning definition closes is
`constraint.ambiguous` before candidate or active-goal inspection.

Selection receives the ordered abstract requirements of the current global or
implementation, an optional current implementation, the effective
implementation environment, an active-goal set, and one resolved interface
application. It considers sources in this order:

1. An identity-equal abstract requirement from the current definition.
2. Exact current-implementation evidence for an implementation method's rigid
   head.
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
sequence.

```sequent
family evidence-selection:
  Select-Abstract :=
    goal contains no inference variable
    requirement = identity_equal_requirement(abstracts, goal)
    ===>
    abstracts; current; effective; active |- goal
      ⇓ Abstract(requirement, interface_methods(goal.interface))

  Select-Current-Implementation :=
    goal contains no inference variable
    no identity-equal abstract requirement exists
    current has the same interface and exact rigid head as goal
    ===>
    abstracts; current; effective; active |- goal
      ⇓ Implementation(current, identity, abstract_prerequisites, impl_methods(current))

  Select-Concrete-Implementation :=
    goal contains no inference variable
    earlier_source_absent(abstracts, current, goal)
    goal is not in active
    unique_match(effective excluding current, goal) = implementation, substitution
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
goal active until their ordered selections complete.

If the concrete branch re-enters an active canonical interface-and-type goal,
selection reports `constraint.cycle`. If no implementation matches, it reports
`constraint.unsatisfied`. Coherent effective environments ensure that concrete
selection has at most one matching implementation after identity
deduplication. Candidate enumeration consults only the effective environment.
An implementation that is private in another module, or public but reachable
only through a transitive dependency, contributes no candidate. Without
another evidence source, the obligation is `constraint.unsatisfied` at its
constrained occurrence, and that occurrence owns the failure. Its deterministic
related labels stop at the method or constrained-global declaration and any
relevant direct import. They never reveal the unavailable implementation or a
transitive import route.

A local generalized function cannot acquire a new requirement.
For an eligible unannotated anonymous-function initializer, typing closes and
selects every obligation before `generalize_local` chooses generalized
inference variables. An obligation containing a would-be generalized variable
is therefore ambiguous. Other local forms remain monomorphic and close their
obligations at the enclosing global or implementation method. Recursive
constrained globals reuse their declared abstract requirements and cannot gain
polymorphic recursion.

Checked selections have two recursive forms. An abstract selection records its
requirement identity and ordered interface methods. An implementation selection
records the stable implementation identity, its head substitution, its ordered
prerequisite selections, and its implementation-method identities. These are
compiler annotations, not source values or runtime dictionaries.

```text
EvidenceSelection =
    Abstract(requirement, methods)
  | Implementation(implementation, substitution, prerequisites, methods)
```

Every resolved method or constrained-global occurrence owns one structural
evidence field. A method field has one position for its interface requirement;
a constrained-global field follows the global signature's requirement order.
Typing fills the field exactly once at the first closure that owns the
occurrence. An eligible unannotated anonymous-function initializer closes
before `generalize_local`; every other local occurrence closes with its
enclosing global or implementation method. The filled field remains on the
checked definition returned by `T-Module`. Static checking neither joins a
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

## Globals and modules

An equational global signature must expose at least as many arrow layers as
each clause has patterns. The patterns receive those domains in order, and the
body checks against the remaining codomain. An inline operational header
supplies its domain and result directly. One typed parameter gives that domain;
multiple typed parameters combine into one tuple domain. Each presentation
contributes one rank-1 constrained scheme. All local global schemes form
`GAMMA_G` before any ordinary global or implementation method body is checked.
Imported schemes come from immutable summaries of direct dependencies.

For these rules, `close_and_select` traverses the named obligation sequence in
source order with the supplied abstract, current, effective, and active
contexts. It fills each occurrence's evidence field and returns the ordered
selections retained by the checked definition. A global's abstract context is
its declared requirements, its current-implementation context is absent, and
its initial active-goal set is empty. The `selections` output denotes the filled
structural fields in that definition, not a separate side collection.

```sequent
family global-typing:
  T-Equational-Clause :=
    patterns ⇐ domains => bindings
    useful(previous_clauses, patterns, domains)
    GAMMA, bindings; abstracts; current; effective
      |- body ⇐ codomain, obligations
    ===>
    GAMMA; abstracts; current; effective |-clause name patterns = body
      ⇐ Function(domains, codomain), obligations

  T-Equational-Global :=
    checked_signature = forall parameters. requirements => definition_type
    definition_type = Function(domains, codomain)
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
    checked_signature = forall parameters. requirements => Function(domain, codomain)
    definition = fn name(header_pattern : domain) -> codomain where requirements { body }
    abstracts = ordered abstract evidence for requirements
    current = none
    effective = module's effective implementation environment
    parameters are rigid while checking the header and body
    header_pattern ⇐ domain => bindings
    exhaustive([header_pattern], domain)
    GAMMA, bindings; abstracts; current; effective
      |- body ⇐ codomain, obligations
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

Module checking resolves all identities and headers before the judgments below.
It checks interface declarations and admits implementation headers, builds and
checks the effective implementation environment, checks exact method
membership, then checks ordinary globals and implementation method bodies in
deterministic source and method order. `THETA` is the accumulated first-order
substitution described above.

```sequent
family module-and-program-typing:
  T-Module :=
    GAMMA_D = checked schemes imported from direct dependency summaries
    for each local interface, |-interface interface ok
    admitted_impls = admitted local implementation headers
    effective_impls = effective(admitted_impls, direct_dependencies)
    module |-implementations effective_impls coherent
    for each local implementation, |-impl-membership implementation ok
    GAMMA_G = all local schemes accepted by WF-Global-Signature
    GAMMA_M = checked schemes for all local implementation methods
    for each ordinary global or implementation method in deterministic source and method order,
      GAMMA_D, GAMMA_G, GAMMA_M |-body definition ok
    every inference variable allocated by these premises is in domain(THETA)
    freeze_public(module, checked definitions, admitted_impls, apply(THETA)) = summary
    ===>
    summaries(direct_dependencies) |-module module ⇒ checked_module, summary

  T-Program :=
    modules are in dependency order
    for each module_i,
      summaries(direct_dependencies_i) |-module module_i ⇒ checked_module_i, summary_i
    checked_program = checked_modules in dependency order
    main is a local checked scheme in entry
    main is monomorphic Function(Unit, result_type) with no requirements
    closed(result_type)
    ===>
    |-program checked_program, entry ⇒ result_type
```

`T-Module` establishes all local global and implementation-method schemes
before checking any body, which creates one simultaneous recursive scope for
those definitions. Its inference premise closes inference over the complete
module, including types inferred only inside discarded expressions.

`freeze_public` atomically derives the body-free checked summary only after the
complete module succeeds. Every public interface or implementation fact in the
summary has therefore passed its owning judgment. Any header, overlap,
membership, body, inference-closure, or selection failure publishes no summary.
The [name-resolution specification](name-resolution.md#imports-and-namespaces)
defines the summary's public facts, required hidden closure, access effects, and
non-re-export boundary.

The filled occurrence fields and checked modules become inputs to
[module linking and linked interface-evidence validation](elaboration.md#module-linking-and-entry-generation).
That specification owns their retention through linking and the validator's
authentication inventory. Core synthesis requires the validated result, and
neither validation nor synthesis selects implementations again.

`T-Program` checks each module after all its dependencies. The entry must
declare exactly one local `main`; an imported `main` cannot satisfy the
premise. Its checked scheme must have no type parameters, domain `Unit`, a
closed result, and no requirements. Entry failures have this order: missing
local `main`, polymorphic scheme, wrong domain, open result, then constrained
scheme. The closed `result_type` is the type observed for the whole program,
and `main` need not be public. Every evidence obligation in a well-shaped
`main` body must therefore select concrete evidence at its occurrence.

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

The first judgment that can establish a failure owns it. Interface method and
global requirement failures belong to their well-formedness judgments.
Implementation visibility, head, prerequisite, orphan, and termination
failures belong to header admission; overlap belongs to effective-environment
construction; method membership and bodies belong to their respective checks;
and satisfaction failures belong to selection. Earlier parser and resolution
failures are not reclassified by static checking. Traversal follows dependency,
import, declaration, requirement, and method order, so one source program has a
deterministic first failure.

One graph-wide interface-and-constraint work budget persists from dependency-
summary admission through effective-environment construction, header and body
checking, evidence selection, linking, and linked evidence validation. The
static stages charge proportional work before retaining or visiting interface
and implementation facts, effective environments, overlap pairs, obligations,
candidates, substitutions, prerequisite edges, active goals, and evidence
nodes. [Elaboration](elaboration.md#module-linking-and-entry-generation) defines
the linking and validation charges. Exhaustion at any stage is
`internal.resource.constraint-work`; validation has no separate resource
reason. Active-goal cycle detection precedes resource exhaustion for the same
retained selection work. Existing type-inference, Core-construction, and Core-
validation budgets remain separate, and the Core budgets begin only after
linked interface-evidence validation succeeds.

Ash has no higher-rank or higher-kinded polymorphism, explicit source type
application, broad application-shaped local generalization, subtyping, implicit
conversions, explicit structural recursive-type operators, or polymorphic
recursion. Interfaces add no associated types, specialization, priority,
default or negative implementations, inferred global requirements, first-class
dictionaries, runtime implementation lookup, or interface-specific Core
mechanism. Nominal declarations may refer to themselves and to other nominal
declarations in the same module. Recursive global visibility does not cross a
module boundary.
