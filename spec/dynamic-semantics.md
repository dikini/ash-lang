# Dynamic Semantics

Ash evaluation is defined by one deterministic small-step relation over
configurations `CONFIG(heap, environment, control, continuation)`. The heap is
fresh for one evaluation and maps numeric locations to tuples, completed
constructors, uninitialized slots for recursive data or native reports, or
aliases. Tuple elements
and constructor payloads are runtime values. The environment maps resolved term
identities to runtime values. Effect execution also retains lexical type/row
instantiation in the environment, separately from term bindings. This metadata
is not a source value. The continuation records the remaining strict
work, including ordered lexical handler boundaries. A selected operation moves
one suffix of that continuation into a clause-owned captured continuation. The
suffix is moved, not copied. Its clause boundary records whether the unique
resume capability still owns that captured control or has consumed it.

Runtime values are arbitrary-precision integers, Booleans, unit, independent
immutable byte sequences, validated UTF-8 strings, lexical
functions, internal lexical polymorphic functions, payload-constructor
functions, opaque non-owning resource handles, or heap locations. A function
template becomes a lexical function with the recursive environment when its
binder is looked up. A location is an internal handle, not source-level
identity or observable mutation.

Pure Core type abstractions and applications erase without extending the
environment or allocating heap cells. Effect execution retains lexical
polymorphic functions and their validated instantiation so exact operation
identities remain meaningful across generic calls. No type or kind becomes a
source-inspectable value, and instantiation allocates no ordinary heap cell.
Validated newtype conversions and local nominal scopes are likewise erased
static operations rather than values.

## Initial configuration

Elaboration produces one validated linked Core expression: dependency-ordered
recursive global groups around the generated application of the entry module's
local `main` to unit. The final linked expression has an empty outward effect
row after mandatory owner-free native interpretation and exact discharge by
admitted source resource scopes. Evaluation starts
with that expression as control, a fresh empty heap and environment, and an
empty continuation:

```sequent
E-Program-Start :=
  elaborate(modules, entry) = linked_program
  validate(linked_program) = success
  required_source_native_bindings(linked_program) are admitted
  ===>
  INITIAL(modules, entry) = CONFIG(empty_heap, empty_environment, linked_program, empty_continuation)
```

`linked_program` is the dependency-ordered groups around `main ()` described in
[Elaboration](elaboration.md). The second premise requires independent
whole-program validation before evaluation. Neither premise performs module
loading at runtime. The ordinary recursive-binding and application rules enter
the linked groups and call `main`. Imports have no initialization step, and
modules are not runtime values.

For a program with owner-free source-native effects, the linked expression
includes the mandatory native interpretation described below. A source resource
scope instead retains its exact acquisition and teardown interpretations. Both
forms require their executable bindings before any Ash expression runs. The
binding premise is vacuous for a program requiring none. Binding admission
retains the exact original checked symbol and bridge authority, independently checked against
the validated program; a missing or changed binding is an internal failure.
It performs no Ash evaluation or implicit native compilation/linkage.

## Type instantiation and erasure

In Pure execution, entering either explicit Core type operation takes one step
to its retained term. Validation has already checked parameter scope, argument
arity, kinds,
and substitution, so evaluation does not inspect the parameters or arguments.

```sequent
family type-erasure-steps:
  E-Type-Abstraction :=
    execution uses Pure Core
    ===>
    CONFIG(heap, environment, TypeAbstraction(parameters, body), continuation) -> CONFIG(heap, environment, body, continuation)

  E-Type-Application :=
    execution uses Pure Core
    ===>
    CONFIG(heap, environment, TypeApplication(function, arguments), continuation) -> CONFIG(heap, environment, function, continuation)

  E-Newtype-Conversion :=
    ===>
    CONFIG(heap, environment, NewtypeConversion(owner, direction, child), continuation) -> CONFIG(heap, environment, child, continuation)

  E-Local-Nominal-Scope :=
    ===>
    CONFIG(heap, environment, LocalNominalScope(owner, body), continuation) -> CONFIG(heap, environment, body, continuation)
```

The unchanged heap and environment make erasure observable only as progress in
the machine. No source program can inspect a type parameter or type argument.
In Pure execution, method-local type arguments erase through `E-Type-Application`.
`E-Newtype-Conversion` also leaves the continuation unchanged. Independent
Core validation has already authenticated the owner, direction, child and
result types, representation substitution, and provenance, so evaluation does
not inspect conversion metadata or consult a registry.

`E-Local-Nominal-Scope` likewise enters its body directly with the same heap,
environment, and continuation. The owner has already been authenticated and
creates no runtime identity, environment entry, frame, or registry state. A
closure whose exposed computation is identity-free may retain ordinary erased
representation values and execute its lexical code after this step's body
returns; no runtime scope authority needs to survive with it.

Effect execution instead retains a type abstraction as a lexical polymorphic
function. Independent Core validation admits only inert values or variables,
transparent type operations, and authenticated generated evidence adapters
inside that abstraction, as described in [Elaboration](elaboration.md#explicit-rank-1-operations).
Retaining these forms does not delay a source effect or source function body.

A type application evaluates its function before entering the retained body.
It saves the caller's instantiation, substitutes all ordinary type and complete
row arguments under that caller context, and simultaneously binds the retained
parameters in the function's definition environment. Ordinary function creation
then captures that environment. A later call uses the closure's context, not
the caller's current type bindings. Recursive lookup likewise materializes a
polymorphic function from the definition context, rather than specializing a
shared template in place. Parameterized ordinary constructors retain their
existing constructor behavior; their type application needs no effect context.

The same lexical context travels with handlers and captured control. Request
selection compares exact effect instances after instantiating each side under
its own context. This is neither type inference from argument values nor a
machine-global mutable substitution. Types nested inside effect arguments,
including higher-kinded applications and function effect rows, participate in
the same validated substitution. Pure execution keeps the erasure rules above.

These Effect-only steps make retention and instantiation explicit.
`POLYMORPHIC` is an internal lexical function, not a type value.
`arguments` contains the ordered ordinary type and complete row arguments.
`instantiate_arguments` uses the saved caller context, and `bind_parameters`
extends the definition context simultaneously without changing term bindings.
`constructor_value` recognizes an ordinary payload-constructor function or
nullary constructor value; these need no retained effect instantiation.

```sequent
family effect-type-steps:
  E-Effect-Type-Abstraction :=
    execution uses Effect Core
    ===>
    CONFIG(heap, environment, TypeAbstraction(parameters, body), continuation) -> CONFIG(heap, environment, POLYMORPHIC(parameters, body, environment), continuation)

  E-Effect-Type-Application :=
    execution uses Effect Core
    ===>
    CONFIG(heap, environment, TypeApplication(function, arguments), continuation) -> CONFIG(heap, environment, function, TYPE-ARGUMENTS(arguments, instantiation(environment)) :: continuation)

  E-Effect-Type-Instantiate :=
    instantiated = instantiate_arguments(arguments, caller_instantiation)
    body_environment = bind_parameters(definition_environment, parameters, instantiated)
    ===>
    CONFIG(heap, environment_value, POLYMORPHIC(parameters, body, definition_environment), TYPE-ARGUMENTS(arguments, caller_instantiation) :: continuation) -> CONFIG(heap, body_environment, body, continuation)

  E-Effect-Constructor-Instantiate :=
    constructor_value(value)
    ===>
    CONFIG(heap, environment_value, value, TYPE-ARGUMENTS(arguments, caller_instantiation) :: continuation) -> CONFIG(heap, environment_value, value, continuation)
```

## Generated interface evidence

Linking preserves each checked interface selection. Linked interface-evidence
validation authenticates it, and Core synthesis lowers it before evaluation.
Determination metadata erases before Core synthesis. Complete interface
applications may survive through transforms and independent validation only in
inert static authentication relationships. Their ordered arguments have
already been substituted into authenticated method types, and the evaluator
does not inspect those relationships or make them control or state.
An abstract evidence method becomes an ordinary function parameter. A
polymorphic occurrence type-applies that parameter to its retained method-local
arguments; entering the Core application uses the type-instantiation behavior
above. A monomorphic concrete evidence method becomes a binder occurrence for the
implementation method in its defining module's recursive group. A polymorphic
concrete or exact-current method first enters its generated adapter type
abstraction and then the implementation method's complete type application.
Pure execution erases both operations; Effect execution retains the lexical
instantiation needed by operation identities. Looking up
the recursive function binder materializes a lexical closure under the existing
recursive-binding behavior.

A supplied lexical method uses ordinary nonrecursive binding, function closure,
and binder lookup. Its closure captures the preceding ordinary values required
by its body. A checked closure may retain that method after the evidence block
returns; a new occurrence outside the block cannot acquire its static evidence.
The lexical source identity and selection scope create no runtime value,
registry, scope frame, revocation check, or transition family.

The validated Core program may retain method authentication records and method
schemes as static authority, and a Core type application carries its retained
method arguments in control until the type application is entered.
The evaluator does not inspect method authentication records or method schemes.
It does not turn an interface identity, selection record, implementation
authorization route, method scheme, or method argument into a runtime value,
term binding, heap cell, interface lookup, or interface-specific transition.
Effect type applications retain instantiation as described above; this does
not turn method authentication or selection into runtime authority.

For a generic implementation method, lowering uses the recorded head
substitution to form an ordinary Core type application. When evaluation enters
that Core node, Pure execution erases it while Effect execution preserves its
validated arguments in lexical instantiation. The recorded selection route
itself does not reach the evaluator. The existing strict application transitions
then evaluate and apply
every recursively generated prerequisite method in declaration order. The
result is the lexical method closure that accepts the source value argument. At
a constrained-global call, the same transitions apply its evidence functions
before the surrounding source arguments because elaboration nested the
applications in that order. Abstract prerequisite evidence uses ordinary
environment lookup; concrete prerequisite evidence uses ordinary recursive
function lookup and closure materialization.

There is no runtime interface value, dictionary, interface or implementation
registry, implementation lookup, interface dispatch, registration step, or
interface-specific failure mode. Polymorphic method evidence uses the dialect's
ordinary function values and applications. It adds no interface-specific value,
environment-entry class, frame kind, lookup class, transition class, failure
reason, or runtime interface state. Evidence construction uses the dialect's
ordinary type operations, local and recursive binding, binder lookup and closure
materialization,
and the strict application transitions below. It adds no interface-specific
Core node or evaluation rule.
Improvement is a static inference operation and does not become a lookup,
transition, proof witness, effect handler, or existential package.

The executable test
`generic_prerequisite_evidence_has_a_bounded_unspecialized_evaluation_trace`
checks this program:

```ash
type Wrap<A> = Wrap(A)

interface Read<A> {
    read : A -> Int
}

impl Read<Int> {
    read value = value
}

impl Read<Wrap<A>> where Read<A> {
    read (Wrap(value)) = read value
}

main : Unit -> Int
main () = read(Wrap(42))
```

The test trace enters the source application, its evidence application, the
generic method's type application, and the variable occurrences for the
generic implementation method and concrete prerequisite method in that order.
A trace event enters an occurrence node, not a binder identity. The trace enters
the prerequisite occurrence before the source `Wrap(42)` argument and produces
`42`. It contains at most 32 node-entry events, and the machine reaches at most
six continuation frames. These bounds describe this fixed program. They follow
from the existing erasure, lookup, recursive-binding, and application
transitions; they are not a new transition or a bound on arbitrary prerequisite
chains.

## Bindings

A binding evaluates its initializer before matching the resulting value and
extending the environment for its body. Its pattern binders are not in scope in
the initializer. Static irrefutability makes match failure unreachable.

```sequent
family binding-steps:
  E-Let-Enter :=
    ===>
    CONFIG(heap, environment, let pattern = initializer; body, continuation) -> CONFIG(heap, environment, initializer, LET(pattern, body, environment) :: continuation)

  E-Let-Continue :=
    match(heap, value, pattern) = bindings
    environment' = extend(environment, bindings)
    ===>
    CONFIG(heap, environment_value, value, LET(pattern, body, environment) :: continuation) -> CONFIG(heap, environment', body, continuation)
```

`E-Let-Enter` saves the lexical environment that precedes the binding.
`E-Let-Continue` uses that environment plus the pattern bindings. Semicolons
separate semantic fields; Ash source does not contain semicolons.

## Recursive bindings

Entering a recursive group allocates one uninitialized slot per data member.
It then installs all direct-function templates and data locations in one
recursive environment entry. Constructor-guarded data initializers evaluate in
source order. Completing a data member stores an alias from its slot to the
initializer's constructed location. Lookup of a recursive data member returns
its slot without forcing the alias; lookup of a function member materializes a
lexical function from its template and the recursive environment.

```sequent
family recursive-binding-steps:
  E-Let-Rec-Allocate :=
    allocate_uninitialized(heap, data_members) = heap_1, data_bindings, pending
    environment_1 = extend_recursive(environment, function_templates, data_bindings)
    ===>
    CONFIG(heap, environment, let rec members; body, continuation) -> CONFIG(heap_1, environment_1, initialize(pending, body), continuation)

  E-Let-Rec-Initialize :=
    ===>
    CONFIG(heap, recursive_environment, initialize((initializer, member_location) :: rest, body), continuation) -> CONFIG(heap, recursive_environment, initializer, INITIALIZE_MEMBER(member_location, rest, body, recursive_environment) :: continuation)

  E-Let-Rec-Store :=
    heap_1 = store_alias(heap, member_location, value_location)
    ===>
    CONFIG(heap, environment_value, value_location, INITIALIZE_MEMBER(member_location, rest, body, recursive_environment) :: continuation) -> CONFIG(heap_1, recursive_environment, initialize(rest, body), continuation)

  E-Let-Rec-Body :=
    ===>
    CONFIG(heap, recursive_environment, initialize(empty, body), continuation) -> CONFIG(heap, recursive_environment, body, continuation)
```

Function templates and data locations enter scope before data initialization.
`data_bindings` maps every data member's binder identity to its preallocated
location. `pending` separately pairs each guarded data initializer with that
member's location in source order. `E-Let-Rec-Initialize` enters only the first
initializer and saves the remaining pairs, group body, and recursive
environment in a continuation.
When that initializer returns its constructed location, `E-Let-Rec-Store`
stores the alias and resumes the remaining initialization control. Repeating
these two one-step rules makes every intermediate heap and control state, and
therefore source order, explicit. A function-only group has an empty `pending`
sequence and proceeds through `E-Let-Rec-Body`; its templates were installed by
`E-Let-Rec-Allocate`.

A polymorphic function member has one outer `TypeAbstraction` node whose
nonempty parameter sequence contains all generalized parameters. Allocation
in Pure execution follows that wrapper to install the same function template;
ordinary evaluation still uses `E-Type-Abstraction`. Effect execution retains
the abstraction and definition instantiation with the template. Each lookup
materializes its own lexical polymorphic function; instantiating one occurrence
does not mutate the template or a sibling occurrence.

Reaching an uninitialized cell, an alias loop, or an invalid location is an
internal runtime failure. The static guardedness judgment makes those states
unreachable from accepted source. These rules provide allocation for explicit
recursive data; they do not add general laziness or source-visible mutation.

The executable test `dynamic_recursive_group_example_is_executable` exercises
mutual scope and lexical recursive closure materialization:

```ash
main : Unit -> Int
main () = {
    let rec first : Unit -> Int = fn(ignored) {
        second ()
    }
    and second : Unit -> Int = fn(ignored) {
        let retain : Unit -> Int = fn(value) {
            first value
        }
        42
    }
    first ()
}
```

## Application

Application evaluates the function before the argument. Once both are runtime
values, a lexical function matches its domain pattern, extends its captured
environment, and enters its body. A payload constructor allocates one
constructor cell with the argument value as its payload.

```sequent
family application-steps:
  E-Apply-Function :=
    ===>
    CONFIG(heap, environment, function argument, continuation) -> CONFIG(heap, environment, function, APPLY_FUNCTION(argument, environment) :: continuation)

  E-Apply-Argument :=
    ===>
    CONFIG(heap, environment_value, function_value, APPLY_FUNCTION(argument, environment) :: continuation) -> CONFIG(heap, environment, argument, APPLY_ARGUMENT(function_value) :: continuation)

  E-Beta :=
    function_value = closure(pattern, body, captured_environment)
    match(heap, argument_value, pattern) = bindings
    body_environment = extend(captured_environment, bindings)
    ===>
    CONFIG(heap, environment, argument_value, APPLY_ARGUMENT(function_value) :: continuation) -> CONFIG(heap, body_environment, body, continuation)

  E-Constructor-Apply :=
    function_value = constructor_function(constructor)
    heap_1, result_location = allocate(heap, constructor(constructor, argument_value))
    ===>
    CONFIG(heap, environment, argument_value, APPLY_ARGUMENT(function_value) :: continuation) -> CONFIG(heap_1, environment, result_location, continuation)
```

The continuation frames make the left-to-right order explicit. A closed,
well-typed program cannot apply an integer, Boolean, unit, tuple, or completed
constructor value.

## Tuples, constructors, and matches

Tuple elements evaluate strictly from left to right, after which one tuple cell
stores their runtime values. A nullary constructor occurrence allocates its completed
constructor cell. A payload constructor occurrence produces the callable value
used by `E-Constructor-Apply`.

Those allocation and tag-inspection rules apply to ordinary data constructors.
A newtype constructor and pattern have already lowered to validated wrap and
unwrap conversions. `E-Newtype-Conversion` enters their child without a heap
cell, tag comparison, copy, frame, or new failure mode.
The same erasure applies to module and local `newtype`. Capturing a local value
uses the ordinary closure environment and adds no wrapper allocation.

A match evaluates its scrutinee exactly once. Pattern matching follows aliases
only when it must inspect a tuple or constructor. It compares constructor
identities, visits tuple and payload components left to right, and returns the
pattern's binder-to-value map. Arms are tried in source order; only the first
matching arm body evaluates. Exhaustiveness makes complete failure unreachable.

```sequent
family match-steps:
  E-Match-Enter :=
    ===>
    CONFIG(heap, environment, match scrutinee { arms }, continuation) -> CONFIG(heap, environment, scrutinee, MATCH(arms, environment) :: continuation)

  E-Match-Select :=
    first_match(heap, scrutinee_value, arms) = pattern, body, bindings
    arm_environment = extend(environment, bindings)
    ===>
    CONFIG(heap, environment_value, scrutinee_value, MATCH(arms, environment) :: continuation) -> CONFIG(heap, arm_environment, body, continuation)
```

The same matching operation selects an equational clause after its declared
number of curried arguments has arrived.

## Primitive operations

Primitive operands evaluate from left to right. Addition and multiplication
operate on mathematical integers and cannot overflow. Integer equality is
`true` exactly when its operands denote the same integer. The rules below use
`expression -> expression'` as shorthand for the corresponding control and
continuation transition. An operand step threads its resulting heap into the
enclosing primitive evaluation; operand allocation and effects follow their
ordinary rules. A primitive reduction on integer values leaves its incoming
heap unchanged.

```sequent
family primitive-operation-steps:
  E-Add-Left :=
    left -> left'
    ===>
    left + right -> left' + right

  E-Add-Right :=
    right -> right'
    ===>
    n + right -> n + right'

  E-Add-Values :=
    n_3 is the mathematical sum of n_1 and n_2
    ===>
    n_1 + n_2 -> n_3

  E-Multiply-Left :=
    left -> left'
    ===>
    left * right -> left' * right

  E-Multiply-Right :=
    right -> right'
    ===>
    n * right -> n * right'

  E-Multiply-Values :=
    n_3 is the mathematical product of n_1 and n_2
    ===>
    n_1 * n_2 -> n_3

  E-Equal-Left :=
    left -> left'
    ===>
    left == right -> left' == right

  E-Equal-Right :=
    right -> right'
    ===>
    n == right -> n == right'

  E-Equal-Values :=
    b is true exactly when n_1 and n_2 are the same integer
    ===>
    n_1 == n_2 -> b
```

Here `n`, `n_1`, `n_2`, and `n_3` range over integer values, while `b` ranges
over Boolean values. The left rules propagate a step in the left operand. The
right rules apply only after the left operand is an integer value. The value
rules compute the primitive result.

## Owner-free scalar native execution

This section describes source-native scalar operands/results and zero-operand
`void` calls in the admitted Linux x86-64 GNU profile. Supported integer
representations are signed/unsigned 8-, 32- and 64-bit scalars and 64-bit
`size_t`. These calls create no resource activation or owning source value.
The ordinary source buffer library behavior remains described separately.

`NativeInterpret(S, body)` is a checked Core boundary installed for the program's
required owner-free native effects. It is not a source expression. Independent
validation checks its exact symbol identities, complete ordered Type/EffectRow
instances and row discharge; it removes only the listed native instances.
Ordinary outward effects still require their own interpretation.

Entering this boundary evaluates `body` with a continuation boundary retaining
`S` and the current lexical instantiation. Ordinary return removes that boundary
and passes the value outward. A source-native request evaluates its operand once,
then authenticates its original operation and checked symbol against the admitted
binding. Its complete actual vector must match a listed instance under the
request's and boundary's saved lexical instantiations. Every argument retains
its declared kind and position, including unused row arguments. The native
Type-only projection does not replace this complete source authority.
A source-native request never selects an ordinary source handler or a legacy
manifest binding. The native boundary and remaining continuation stay in place
through the synchronous call and its report.

Before calling native code, the machine traverses the checked operand paths,
charges mathematical-integer magnitude work, and narrows each borrowed `Int`
exactly into its declared representation. A value outside that representation's
range produces canonical `Foreign.ConversionFailed(error)` before invocation.
The error belongs to the original opaque `Foreign.ConversionError` type.
Constructing this refusal report also requires work and storage admission; an
internal refusal terminates without invoking native code.

Successful preparation retains stable native operands in ABI order. It prepays
bounded reply conversion and recording work and reserves the ordinary
`Foreign.Returned` constructor slot before publishing `CallReady`. Binding,
conversion, work or storage refusal before readiness invokes no native function.
These checks do not establish that the external binary obeys its authored
signature or foreign assumptions.

The following three steps separate invocation, recording and reporting.
`d` retains the exact admitted symbol/bridge and complete instantiated source
arguments. `p` retains the prepaid recording/report allowance and reserved
constructor slot. `native` denotes one synchronous external invocation under the
contract's assumptions; `raw` is a native scalar or a void reply. `report`
authenticates its expected representation, widens a scalar exactly to
mathematical `Int`, or supplies `Unit` for void, and initializes the reserved
constructor with canonical `Foreign.Returned`.

```sequent
family scalar-native-call-steps:
  E-Scalar-Native-Call :=
    native(d, operands) = raw
    ===>
    CONFIG(heap, environment, CallReady(d, operands, p), continuation) -> CONFIG(heap, environment, CallReturned(d, raw, p), continuation)

  E-Scalar-Native-Record :=
    ===>
    CONFIG(heap, environment, CallReturned(d, raw, p), continuation) -> CONFIG(heap, environment, CallRecorded(d, raw, p), continuation)

  E-Scalar-Native-Report :=
    report(heap, d, raw, p) = heap_1, value
    ===>
    CONFIG(heap, environment, CallRecorded(d, raw, p), continuation) -> CONFIG(heap_1, environment, value, continuation)
```

Only `CallReady` can invoke the function, and that step consumes readiness.
`CallReturned` retains no invocation capability. Recording is the next machine
step: it retains the raw reply and its admitted report slot without charging
work, allocating an Ash result, or performing a fallible check. No disposal,
reporting or continuation failure can precede this recording step.

Reporting consumes the allowance already deducted before invocation; it does
not charge the caller's ledger again. Unsigned 64-bit replies preserve their
full mathematical value. A `void` call reads no native result and reports
`Foreign.Returned(())`. Integer construction retains the runtime's existing
internal allocation limitations; a reserved constructor slot does not reserve
all physical storage inside mathematical integers.

A detectable internal failure after recording terminates evaluation without
returning to readiness, publishing a final result or retrying the external call.
This applies to report construction and later ordinary continuation work.
Already performed native side effects remain performed. A new evaluation has
fresh machine state and may make its own calls. Internal work/storage failures
are not `Foreign.ConversionFailed` outcomes.

An ordinary library may map an explicit bounded-copy `ConversionFailed` to a
diagnostic-unavailable result while retaining the captured native status. In
particular, absence of NUL within an admitted `copy_nul` bound does not require
truncation or an empty diagnostic. This source policy cannot catch internal
work/storage exhaustion or terminal post-call extraction failure, undo ownership
disposition, retry the native call or retain its owner in an ordinary result.

## Common scalar preflight

The pure common scalar checks invoke no native symbol. On a supported GNU64
host, a successful check reports `Foreign.Returned` containing the original
mathematical integer; only an out-of-range input reports
`Foreign.ConversionFailed` with the canonical opaque error. Work or storage
exhaustion and an unsupported host are terminal evaluator failures. The machine
prices the check and reserves its complete report before publishing any
constructor cell. A terminal refusal publishes no partial result. These checks
create no resource activation, state token, native readiness or destructor
obligation.

`Foreign.checked_nul` prepays a scan of the input's full UTF-8 byte length and
its complete ordinary reply. No NUL byte, including for the empty string,
produces `Returned(())`; any NUL produces `ConversionFailed` with the opaque
error. Work or storage exhaustion is terminal and publishes no partial result.
The pure scan performs no C call, prepares no pointer or owner, and leaves every
later native-call conversion mandatory.

A fixed non-callable sentinel is admitted from its original checked member and
representation before native invocation. The GNU64 bridge passes all-one
function-address bits as data in the declared ABI position, never forming or
invoking a Rust function value. This target ABI is a foreign assumption; the
declaration does not prove
external C behavior. Work, operand storage and the
complete ordinary reply remain admitted before C. Admission refusal publishes no sentinel
value, grants no callable permission and makes no native call. Scalar reply and
owner-disposition rules are unchanged.

## Source resource execution with native owners

The explicit checked-host profile and `checked_scope` have static source/Core
correspondence only. Evaluator and executable/private-image admission refuse
that codec and checked host metadata before acquisition. The rules in this
section describe ordinary executable owner resources; they do not implement
checked native outcomes, K discharge or host disposal.

The admitted product source resource scope combines an Ash initializer, acquire
and finish functions, private data `D`, and an associated ordinary effect handler.
This checkpoint supports opaque and initialized byte foreign owners with declared
dependencies and complete ordered Type/Row owner formals, with a Type-kind owned
identity. Acquisition admits scalar and NUL `String` inputs and exact declared
enclosing-State operands. Its owner comes from a direct pointer result or an
initialized opaque output slot alongside a scalar status and optional
input-relative offset. Canonical report fields retain ABI order. Finish and host
destruction contracts use the exact Current State and declared Enclosing pointer
operands, with checked original scalar constants at declared scalar ABI positions
and fixed non-callable sentinels at their exact function-address ABI positions.
The machine narrows these fixed operands and admits the complete call before
entering C. A `void` result has one unconditional disposition; a scalar result
selects consumed or retained from the original total status alternatives. Each
foreign symbol still retains its complete ordered Type and EffectRow arguments;
the native Type-only projection does not replace them. Source-projected scalar
teardown operands use the producer's explicit mappings to that owner's original
destructor ABI positions.
Exact borrowed scalar queries and lexical access/copy windows use the source
provider's authenticated phase and owner.

Ordinary pure module-global helpers transform only independent payloads inside
these lifecycle computations. Same-module and imported calls use the ordinary
function application rules and their complete Type/Row instances. Calling a
helper neither transfers native State nor changes the selected source phase,
owner or guard, and supplies no native-call permission.

Before any Ash expression runs, program admission checks both acquisition and
teardown bindings for every source resource scope against their exact original
checked symbols. Reconstructed executable images must independently admit the
original headers and defining acquire, finish and handler forests, then validate
each final scope's copied occurrences, substitutions and fresh identities.
Ordinary `NativeInterpret` grants no owner-call permission. An owner request
requires the matching validated source scope, its current acquire or finish
phase, exact copied request membership, and the complete effect instance under
that scope's saved lexical instantiation.

For an initialized byte owner, preflight projects the exact source leaf selected
by its original `initialized_bytes` fact and checks the mathematical value in
the GNU64 nonnegative `size_t` range. The path need not select a native ABI
operand. A negative or unrepresentable extent returns `Foreign.ConversionFailed`
before acquisition; work or storage refusal remains terminal. Readiness retains
the checked extent without creating memory access or an owner. Infallible
recording attaches that extent to the unique non-null guard under the declared
initialization and writability assumption. A null return establishes no region.
The resource's private payload cannot replace or enlarge this recorded extent.

The initializer evaluates once in the preceding environment. Before native
acquisition, the machine authenticates the original destructor and its total
outcome contract, specializes its complete source domain using the full Type/Row
owner and symbol mappings, and reserves
scope and guard storage, checks each scalar conversion, and reserves the native
report slots and recording/report work. A representable operand supplies its
stable ABI scalar; a conversion refusal produces canonical
`Foreign.ConversionFailed(error)` without invoking the native function. Missing
bindings, malformed authority, unsupported representations and internal work or
storage refusal cannot invoke acquisition.
Full domain specialization precedes operand selection even for an address-only
or fixed-operand destructor. Enclosing dependency selection compares complete
State applications, including inherited phantom Rows.

For acquisition, `d` retains the exact symbol, complete instance and sealed
destructor. `p` retains the admitted inline guard and prepaid report storage.
`g` is a unique guarded native address or the absence of an owner for a null
reply. The generated typed bridge arms `g` immediately when the native call
returns, before constructing an Ash result. The pointer remains inside that
guard and is never an ordinary Ash value. The following steps consume readiness,
record ownership, and publish the prepared report:

```sequent
family native-owner-native-call-steps:
  E-Native-Owner-Call :=
    native(d, operands) = raw
    arm(p, raw) = g
    ===>
    CONFIG(heap, environment, CallReady(d, operands, p), continuation) -> CONFIG(heap, environment, CallReturned(d, g, p), continuation)

  E-Native-Owner-Record :=
    ===>
    CONFIG(heap, environment, CallReturned(d, g, p), continuation) -> CONFIG(heap, environment, CallRecorded(d, g, p), continuation)

  E-Native-Owner-Report :=
    report_and_place(heap, continuation, d, g, p) = heap_1, continuation_1, value
    ===>
    CONFIG(heap, environment, CallRecorded(d, g, p), continuation) -> CONFIG(heap_1, environment, CallReported(value), continuation_1)
```

Only `CallReady` invokes the native function. Its return retains no invocation
capability. Recording is infallible, allocates no Ash result, and charges no
additional work; it precedes disposal, reporting and continuation failure.
Reporting uses the prepaid allowance and reserved constructor slots. For this
owner-address result it produces the checked roles corresponding to
`Foreign.Returned(Foreign.Readable(Foreign.Null))` or
`Foreign.Returned(Foreign.Readable(Foreign.NonNull(state)))`. A non-null state
contains the scope's activation key, not its address. The scope receives the
unique guard before the state report becomes available to Ash evaluation.

Ash acquisition policy then selects the resource codec's `Acquired(state, data)`
or `Refused(error)` role. Publication requires the recorded owner of this exact
activation; ordinary constructor creation cannot create ownership authority.
A successful publication binds a non-owning access handle for the body and
retains `D` in the scope. The body receives neither an owning value nor direct
access to `D`; the admitted Ash handler uses its saved state and private data.
Private `D` contains no native State token or view. A local enclosing State used
by admitted acquisition or finish is separate from ordinary stored payloads;
the runtime's sealed dependency and destruction operands also remain separate.
Ordinary declared-dependency access handles in `D` retain their original
identity, liveness and revocation obligations.
Acquisition refusal executes no body. If native acquisition already returned a
non-null owner, refusal destroys that unpublished owner once before delivering
`NotAcquired(error)` under `scope` or `Failure(error)` under `acquired_only`.
Null acquisition creates no destructor obligation.

Associated ordinary operations preserve the nearest exact handler rule. A nearer
ordinary source handler takes precedence over the resource handler. The resource
publishes checked lexical forwarding for all associated methods; ordinary calls
and constrained helpers request the corresponding operation with its unchanged
operand and complete effect arguments.

After selecting a source resource handler and before entering its clause, the
machine authenticates the exact activation, unique live guard and original owner.
It instantiates the request's value domain under the caller and traverses every
typed position containing this resource's access family, including tuple and
nominal constructor payloads. Each such value must be the non-owning access key of
that selected activation; a state view, stale or donor key cannot replace it.
The recorded private data does not authorize access. Work or storage refusal
enters no resource clause. This check does not add an outer resource requirement
to a nearer ordinary handler.

Quarantine denies ordinary resource operations. An already running admitted
dependent finish can obtain the exact local native State of its declared direct
dependency while that owner is physically live. The selected source handler,
typed State result, finishing guard and dependency slot must all agree. This
exception cannot recover an ordinary scalar read, create another owner or grant
a transitive native operand merely from membership in the lifetime closure.

The admitted resource clause uses its lexical state/data and ordinary
clause-owned `resume`; resumption continues the same activation without repeating
acquisition. Repeated executions allocate distinct activation keys. Nested source
resource scopes complete their own finish before their enclosing scope finishes.
Outward capture moves the source boundary and its same unique owner into the
continuation; resume restores that activation without acquisition or byte
reinitialization. Ordinary outward rows survive exact native interpretation.

A lexical copy window retains the exact selected provider, owner guard, family
and fresh window key. Its sealed native interpretation covers only the original
family's preserving operations with complete ordered actuals. A produced view
retains its exact originating call and scalar keys. Before an extent query
enters C, evaluated keys must equal the producing keys; a mismatch returns
ordinary `ConversionFailed` and invokes no extent callback. Missing, stale or
donor view/window/owner authority remains an admission failure. No window can
survive suspension, owner completion or escape.

`copy_bytes` prepays the exact matching initialized extent and complete reply
before reading. `copy_nul` admits both replies before scanning and pays before
each address read, examining at most the nonnegative bound plus one terminator
byte. It admits exact observed copy storage before publishing independent
`Bytes`. Missing termination returns `ConversionFailed`, never truncation.
Work/storage exhaustion is terminal and publishes no partial fallback. Null,
unreadable and non-null empty views remain distinct. UTF-8 decoding is separate.
Each native address read still relies on its original foreign validity contract.

Output slots start at zero/null before C. Raw outcomes are recorded and any
readable non-null owner enters its pending guard before fallible extraction,
diagnostics or result publication. Invalid post-call `offset_into` extraction
preserves that native outcome, disposes the unpublished partial owner and
terminates; it cannot become ordinary pre-call `ConversionFailed` or replay C.
A retained finish permits its listed completing diagnostics; a blocked owner
permits no native access, including ordinary scalar Borrow. Consumed owners
invalidate all same-owner aliases/views. A still-live enclosing owner remains
available under its own exact permission.

Before native acquisition, complete declared dependency arguments select exact
preceding activation slots. All dependency metadata, destruction operands,
counters and result storage are admitted before the callback. Consuming a child
removes its lifetime edges once and restores its enclosing owners' close
readiness. A live retained child blocks a consuming enclosing call before C
entry, independently of aliases or report values. Retention quarantines the same
owner and its transitive dependency closure, revoking ordinary source access.

After ordinary producer-input validation and before entering C, mapped scalar
inputs are projected and narrowed in original destructor ABI order. The complete
native destruction vector and invocation/report storage are reserved before the
call. An out-of-range capture returns ordinary `Foreign.ConversionFailed` with
no native call or fallback owner; work or storage exhaustion remains terminal.
Cleanup-only input leaves need not be operands of the producer's C ABI.

The guard retains immutable native scalar copies, separately from `D`, source
handlers and ordinary Finish arguments. A readable non-null direct result or
typed output owner is guarded immediately on return, including an error outcome.
Every host fallback uses the same reserved vector without Ash evaluation,
scalar conversion, allocation or admission work. Ordinary Finish uses its own
explicit arguments and latest `D`; it cannot replace the fallback snapshot.
A consumed Finish prevents an additional host destructor call.

Owned discard replaces abandoned source-body frames with their admitted finish
computations, from inner to outer, retaining required outer resource handlers and
live guards. It saves no abandoned body value and builds no `Scope` or `Success`
wrapper for it. Source finish can request an ordinary outside interpreter and
resume its own running computation; neither that running finish nor its required
outside interpreter may be skipped by discard. Internal admission and storage
refusals precede capture consumption and ownership transfer.

An acquisition discarded before publication revokes its pending guard once; it
does not manufacture `D` or invoke source finish. If capture preceded native
allocation, there is no destructor obligation. Normal acquisition refusal keeps
its existing independent report.

Normal body return saves its value and invokes the admitted Ash finish once.
Before the Current teardown, the machine authenticates the state token's exact
live activation and reserves its report storage while the scope still owns the
guard. Only successful preflight can detach that guard for consumption. The
consuming unconditional native `void` call destroys the address once and produces
a non-owning consumed receipt with the original authority, before Ash report
construction. Its returned-to-recorded transition is infallible. The prepaid
report supplies `Foreign.Returned(Foreign.Consumed(()))`; source finish maps it
to the resource codec's consumed completion. The scope records consumption
before publishing its report. Under `scope`, the source result remains
`Completed(body_value, completion)`. Under `acquired_only`, normal consumed
completion produces `Success(body_value)`; neither codec flattens a nested body
result. A witnessed consumed completion mapped to `ConsumedFailure(error)` is
terminal under `acquired_only`, reported as `runtime.resource-completion`, and
publishes no success or acquisition failure. Recorded consumption still prevents
a second native release. On owned discard, a consumed finish returning
`ConsumedFailure(error)` is terminal `runtime.resource-completion` under either
codec and publishes no abandoned scope report. Normal `scope` completion instead
retains `ConsumedError(error)` alongside the saved body result. An admitted
native retained disposition records the same owner before report
construction and revokes its ordinary source access. Normal `scope` completion
reports `Completed(body_value, RetainedError(error))`. On owned discard, witnessed
`Retained(state, error)` is terminal `runtime.resource-completion`; it publishes
no abandoned body or scope report and does not continue the discarding clause.
The owner's separately admitted host destructor may later consume that same
owner once. That host release cannot turn failed source completion into success.
Host destruction attempts dependents before their enclosing owners. A successful
host consumption removes the same recorded edges; a retained host disposition
keeps those edges and blocks enclosing destruction. That incomplete destruction
is terminal, is not retried and supplies no successful source cleanup report.
Unresolved native objects remain protected until process termination.

For scalar-status teardown, readiness prepays the complete raw-status
traversal, reply conversion and recording/report work, and reserves both the
successful report cells before C. The typed
callback returns a raw scalar; only the original finite alternatives select
consumed or retained. The machine records that disposition and dependency-edge
changes before converting or reporting the result. A readable result produces
`Foreign.Returned(Foreign.Consumed(status))` or
`Foreign.Returned(Foreign.Retained(status))`. Raw scalar results must always be
readable; a contract declaring an unreadable scalar rejects before execution.
A post-call extraction failure preserves the witnessed disposition and
terminates without a raw reply, `ConversionFailed`, or source continuation.
It cannot restore consumed State or replay teardown. The same retained owner
remains subject to its separately admitted safe host destruction. Pre-call
conversion refusal remains an ordinary `Foreign.ConversionFailed` with no C
entry. Complete reply storage is admitted before entry;
converting the admitted GNU64 scalar to mathematical `Int` requires no later
allocation. Work or storage exhaustion remains terminal.

A retained dependent blocks any Current teardown before C. Its report is
`Foreign.Returned(Foreign.BlockedDependent)` with no scalar payload or
fabricated native status. Host destruction selects its disposition from the
same original contract, records it without an Ash result, and preserves the
existing one-attempt dependency order and incomplete-destruction protection.
Successful later host consumption cannot change an earlier source
`RetainedError` or failed discard.

An internal failure after a native return never retries the call or recreates
readiness. A live guard, including one not yet published to the body, invokes its
sealed original destructor once during host destruction. A consumed receipt
has no destructor callback, so failure during finish reporting cannot repeat
teardown. Host destruction allocates no Ash result and runs no source finish or
handler. Foreign side effects remain performed; internal exhaustion is not a
source conversion or completion outcome. A fresh evaluation has fresh machine
state and may perform its own acquisition. These rules assume the authored
foreign contract holds; linking and checked Core do not prove external binary
validity, and divergence or external process termination provides no eventual
release guarantee.

## Common initialized byte access

`Foreign.byte_read<S>` and `Foreign.byte_write<S>` borrow an initialized live
state from the admitted source acquire, handler or finish phase. The call retains
its selected original canonical occurrence and complete ordered caller and
defining declaration Type/Row instances. Runtime admission authenticates that
correspondence, the exact activation and original owner, and the unique live
guard. A compatible state type, stale or donor token, consumed state, or private
data cannot replace any of these facts. Borrowing does not consume the guard or
change ordinary handler selection and precedence.

The original guard supplies the initialized writable extent. After ordinary
strict argument evaluation, admission checks the index in the GNU64 `size_t`
range and against that extent before inspecting or charging conversion of a
write's byte value. A valid byte is an integer in `[0, 255]`. An invalid index or
byte returns canonical `Foreign.ConversionFailed(error)` without reading or
writing native memory. A zero extent remains owned and refuses every index.
Internal work or storage exhaustion is terminal and supplies no conversion
result. A valid index with insufficient byte-conversion work therefore differs
from an invalid index whose complete refusal report is affordable.

Before a read or write callback, the machine disposes owned call-specialization
metadata, charges bounded operation and result work, and fallibly reserves and
initializes the complete reply cell. Readiness retains only that unpublished
cell and a borrowed guard with the checked index. A read returns an unsigned byte;
converting `[0, 255]` to the mathematical `Int` uses existing inline integer
storage and cannot allocate or refuse. A write has an already checked byte and
an initialized Unit reply. Both callbacks fill or preserve the prepared payload
and publish its location without further charging, reservation or allocation.
Rejected write admission leaves native memory unchanged.

In the following steps, `ready(g, index, slot)` already authenticates the original
call and live guard and prepays the complete reply. `slot` belongs exclusively to
readiness; these steps have no fallible admission premise after native access.

```sequent
family initialized-byte-access-steps:
  E-Byte-Read :=
    read_byte(g, index) = byte
    fill_returned(slot, Int(byte)) = heap_1, value
    ===>
    CONFIG(heap, environment, ByteReadReady(g, index, slot), continuation) -> CONFIG(heap_1, environment, value, continuation)

  E-Byte-Write :=
    write_byte(g, index, byte) = ()
    publish_returned_unit(slot) = value
    ===>
    CONFIG(heap, environment, ByteWriteReady(g, index, byte, slot), continuation) -> CONFIG(heap, environment, value, continuation)
```

The returned value is ordinary `Foreign.Returned(Int)` or
`Foreign.Returned(())`; neither reply owns or exposes the state. Later continuation
failure cannot replay the callback. The scope still owns exactly one release
obligation until teardown consumes it. External initialization and writability
remain foreign-contract assumptions; checked source, binding and image admission
do not prove the external binary's memory validity. These byte primitives do
not grant separate copy-window, dependency or outward-control permission.

## Effect handlers and completion

`HANDLER(handler, instance, clauses, environment)` is an ordered lexical
continuation boundary. `REQUEST(operation, instantiation)` and
`RESUME(handler, owner)` are ordinary strict frames for their operands. The
request retains its lexical instantiation. `CLAUSE(handler, owner, state)` is
the selected clause boundary; its state is either `live(captured)` or
`consumed`. The captured value owns the selected handler boundary and all
intervening continuation entries up to the request. It contains no source
value and cannot escape the clause.

Entering a handler evaluates its body with a new innermost boundary. Ordinary
completion removes that boundary and passes the value outward:

```sequent
family handler-boundary-steps:
  E-Handle-Enter :=
    ===>
    CONFIG(heap, environment, handle body with instance { clauses }, continuation) -> CONFIG(heap, environment, body, HANDLER(handler, instance, clauses, environment) :: continuation)

  E-Handle-Return :=
    ===>
    CONFIG(heap, environment_value, value, HANDLER(handler, instance, clauses, handler_environment) :: continuation) -> CONFIG(heap, environment_value, value, continuation)
```

The static handler identity determines `handler`. Its clauses are exhaustive
for `instance`, so ordinary body return and operation selection are the only
reachable ways to leave the boundary.

A request first evaluates its one operand. For a non-source-native operation,
once that operand is a value, `select_nearest` searches outward for the innermost accepting source-handler
or cell boundary. The source-handler branch below requires its exact effect
identity and instantiated type arguments to equal the operation's instance,
with no nearer accepting cell boundary. The request saves its lexical instantiation
before operand evaluation; each candidate uses its own saved handler context.
It returns the matching clause, the handler's saved
environment, an owner identity, the moved segment through that boundary, and
the continuation outside it:

```sequent
family request-steps:
  E-Perform-Operand :=
    ===>
    CONFIG(heap, environment, perform operation operand, continuation) -> CONFIG(heap, environment, operand, REQUEST(operation, instantiation(environment)) :: continuation)

  E-Request-Select :=
    operation is not a source-native symbol
    requested = instantiate(instance(operation), request_instantiation)
    select_nearest(continuation, requested) = clause, handler_environment, handler, owner, captured, outer
    no nearer cell boundary accepts requested
    clause = operation pattern => body
    match(heap, operand_value, pattern) = bindings
    clause_environment = extend(handler_environment, bindings)
    ===>
    CONFIG(heap, environment_value, operand_value, REQUEST(operation, request_instantiation) :: continuation) -> CONFIG(heap, clause_environment, body, CLAUSE(handler, owner, live(captured)) :: outer)
```

The move performed by `E-Request-Select` removes the selected handler and every
intervening nonmatching boundary while the clause runs. An operation requested
directly by that clause therefore reaches only handlers in `outer`. Row order
does not participate in `select_nearest`.

`resume` first evaluates its argument under the surrounding clause control.
When the argument is a value, `restore` atomically consumes the matching live
owner and reinstalls the selected handler plus the captured intervening
control in their original lexical nesting. The clause continuation stays below
that restored segment:

```sequent
family resume-steps:
  E-Resume-Operand :=
    nearest_clause_owner(continuation, handler, owner) = live(captured)
    ===>
    CONFIG(heap, environment, resume(handler, owner, expression), continuation) -> CONFIG(heap, environment, expression, RESUME(handler, owner) :: continuation)

  E-Resume-Restore :=
    continuation = RESUME(handler, owner) :: clause_control
    split_owner(clause_control, handler, owner) = clause_prefix, live(captured), outer
    restored = restore(captured, clause_prefix ++ CLAUSE(handler, owner, consumed) :: outer)
    ===>
    CONFIG(heap, environment_value, value, continuation) -> CONFIG(heap, environment_value, value, restored)

  E-Clause-Return :=
    ===>
    CONFIG(heap, environment_value, value, CLAUSE(handler, owner, consumed) :: outer) -> CONFIG(heap, environment_value, value, outer)
```

`restore` preserves the captured order: the selected handler surrounds the
resumed computation, and any crossed handlers regain their original
outer-to-inner nesting inside it. The ordinary continuation rules evaluate the
restored computation. When that computation returns through the restored
segment, `clause_prefix` continues after the `resume` expression. After the
remaining clause control finishes, `E-Clause-Return` removes the consumed
clause boundary and returns the clause value to `outer`. There is no transition
that clones a captured continuation or changes `consumed` back to `live`.

`discard` consumes the matching live owner without restoring its captured
segment as executable body control. It has no operand. Checked discard retains
the clause continuation and its surrounding control, closes owned abandoned
scopes, then returns unit at the discard expression:

```sequent
E-Discard :=
  split_owner(continuation, handler, owner) = clause_prefix, live(captured), outer
  closing = owned_close_control(captured)
  ownership validation and fallible initial preparation succeed
  remaining = clause_prefix ++ CLAUSE(handler, owner, consumed) :: outer
  ===>
  CONFIG(heap, environment, discard(handler, owner), continuation) -> CONFIG(heap, environment, (), closing ++ CLOSE :: remaining)
```

Here `owned_close_control` retains cell, registration and armed cleanup owners
in structural innermost-to-outermost order. A contained live clause contributes
its capture recursively at that clause's position and is consumed once;
consumed clauses contribute no capture. Non-owning associations do not add
owners. `CLOSE` denotes required completion of this close operation: after the
last owner closes it returns `()` into the unchanged clause continuation.
These are internal control descriptions, not source expressions.

Closing does not resume abandoned expressions or clause suffixes, invoke pending
callbacks from abandoned publications, or restore captured source handlers.
It never resumes abandoned
control with a dummy body result. Cells release their payloads; registrations
remove their entries without invoking their transformers; cleanup owners
invoke their actions through ordinary application before advancing outward.
Still-enclosing builtin cells remain available until their own closing positions.

Preflight validates and prepares the owned transfer before consuming the
capability or releasing capture accounting. Initial failure leaves both
unchanged. After source actions start, later internal failure does not roll
back earlier effects, repeat actions or guarantee remaining invocations.
Traversal and host disposal remain iterative for deeply nested captures.
After closing and the remaining clause work, `E-Clause-Return` applies as after
resume. A running action or unfinished `CLOSE` cannot itself be abandoned;
outward requests may capture and resume it.

Static checking and Effect Core validation make an unmatched request, a
missing owner, a second completion, an unsafe discard, or an invalid capture
boundary unreachable from accepted source. If one appears after successful
validation, evaluation reports an internal malformed-Core or machine failure.
Ash has no source-level
unhandled-operation, abort, exception, cancellation, or unwind result.

## Scoped cell execution

A cell scope owns one current payload root. Legacy `resource cell<R>` scopes
retain integer payloads and their unary API. Generic `Cell.Cell<R,T>` scopes
retain an ordinary checked value of the fixed type `T`; aggregate and callable
values use the ordinary shared value representation. Its handle is an opaque,
non-owning activation key: copying a handle, closure or environment does not
copy the mutable slot or its release obligation. The ordinary value heap owns
no resource boundary, including through unused closure environment entries.

Acquisition first evaluates the initializer exactly once in the preceding
environment. Legacy initialization requires an integer. Generic initialization
returns the checked `T` value before the new owner exists. The machine checks
capacity and prepares the new scope, handle binding, lexical instantiation and
complete `Ops<R,T>` authority before publishing a generic owner. Successful
acquisition creates a fresh activation, distinct from every earlier successful
execution, even at the same source site. Failure publishes none of the new
scope or authority. It is an internal failure, not a source allocation branch.

The following legacy rules describe entry and normal release. `RESOURCE_INIT`
retains the initializer's following body and preceding environment. `CELL(a, n)`
owns payload `n` for activation `a`. `bind_cell` binds `c` to the non-owning handle
for `a` and binds the rigid identity `R` to `a` in lexical instantiation; it
does not place `n` in the value heap. The acquisition premise includes all
capacity and fallible preparation, before publication.

```sequent
family resource-boundary-steps:
  E-Resource-Initialize :=
    ===>
    CONFIG(heap, environment, resource cell<R> c = initializer { body }, continuation) -> CONFIG(heap, environment, initializer, RESOURCE_INIT(R, c, body, environment) :: continuation)

  E-Resource-Acquire :=
    n is an integer
    acquisition preparation succeeds with fresh activation a
    bind_cell(heap, resource_environment, R, c, a) = heap_1, body_environment
    ===>
    CONFIG(heap, environment_value, n, RESOURCE_INIT(R, c, body, resource_environment) :: continuation) -> CONFIG(heap_1, body_environment, body, CELL(a, n) :: continuation)

  E-Resource-Return :=
    ===>
    CONFIG(heap, environment_value, value, CELL(a, n) :: continuation) -> CONFIG(heap, environment_value, value, continuation)
```

Static checking ensures that the returning value does not depend on `a`.
An inner return releases the inner cell before continuing inside its outer
scope. An escaped independent snapshot retains its ordinary shared value after
release. Reading a snapshot does not freeze cells reachable through it.

Requests retain their lexical type and row instantiation as described above.
An activation binding travels through generic applications, returned closures,
handler environments and captured control. A closure from an outer execution
therefore continues to request its outer activation when called inside another
execution of the same source site, including when its dependency appears only
in operation metadata rather than a term capture. The machine does not infer
activation from operand values or use a global substitution environment.

Request selection searches source-handler and cell boundaries in ordinary
innermost-to-outermost order. A cell boundary accepts only its authenticated
builtin operation at its exact activation; generic selection also checks the
complete instantiated `R,T` arguments. Nonmatching boundaries are passed.
A nearer exact source handler intercepts the request by the existing handler
rules. Its interception creates neither a handle nor provider authority.

For a request selected by a legacy cell boundary, the operand handle must equal
that boundary's activation. `read` returns a copied payload integer and leaves
the scope in place. `write` requires the tuple `(handle, integer)`, replaces the
owned payload and returns `Unit`. Alias resolution and complete operand,
operation and activation checks precede any mutation. Malformed operands or
identity disagreement are internal failures, not source use-after-release.

For generic cells, `read` returns the current ordinary value and preserves
shared aggregate identity; it performs no deep payload traversal. Earlier read
results remain unchanged by later replacements. `write` takes `(handle, value)`
and replaces the current root with that checked `T` value. Complete operation,
type and activation authentication, paid alias resolution, proportional scalar
or origin copying, and fallible reply/trace preparation precede publication or
replacement. Preparation refusal leaves the root unchanged; effects already
performed while evaluating the operands remain performed. The primitive invokes
no user callback. Internal failure while disposing a replaced last-owned value
terminates execution with incomplete teardown; it is neither a preparation
refusal nor a source cleanup transition.

An exact source handler's intercepted read returns its actual reply, and an
intercepted write performs no builtin replacement. Clause, other-handler and
resumed-computation writes still update the slot in control order. Merely
reading, replacing or dropping a payload containing native access neither
consumes its native owner nor restores quarantined authority. A subsequent
native operation must pass the ordinary native liveness checks.

An outward resource-free request may capture a cell boundary. Capture moves
the owned scope into the continuation; resume moves it back in its original
order. Neither movement changes live-cell usage or duplicates a payload.
Completion after resumption applies `E-Resource-Return` normally. Checked
discard closes cells inside its recursively owned capture using the same
release transition, after validating the transfer. Static checking additionally
proves that discard skips no required completion outside that owned closure;
execution does not rescan suspended source bodies to establish that proof.

Cell capacity counts live owned payloads, including captured scopes, rather
than total acquisitions. Normal or abandoned release makes capacity reusable;
a later acquisition still receives a fresh key. Deep normal completion and internal
failure disposal release cells, captured control and environments iteratively.
Internal disposal is not a source cleanup transition. Divergence remains
divergence, and no abort, destructor callback, cancellation or foreign cleanup
path is added. Resource-free Pure execution allocates no resource registry,
resource frame or live cell.

## Scoped native-buffer execution

The passive Ash library `libraries/native_buffer.ash` supplies buffer policy.
`resource Buffer.Buffer<R> b = length { body }` uses the common declared-source
resource machine and the checked `acquired_only` codec, not a fixed evaluator
adapter. The current generated bridge profile is `x86_64-unknown-linux-gnu`.
Native execution requires the generated linked host; ordinary interpreted
execution refuses the missing binding before running Ash.

The initializer runs once before acquisition. Length must be positive and at
most `2^63 - 1`, within the selected host size/pointer-offset bounds. The
library's checked conversions and native operand preflight return
`Failure(InvalidLength)` without entering C for an invalid length. For a valid
initialized extent `n`, common readiness charges its proportional `n + 2`
initialization/fixed-release work before calling C, in addition to ordinary
extent validation and complete guard/report/publication admission. Arithmetic
overflow or insufficient internal work/storage is terminal, with no native
entry, publication, retry or limit increase. Earlier initializer effects remain
committed.

`calloc(n, 1)` returning null yields `Failure(AllocationFailed)` without a body
or access activation. Its checked successful outcome promises initialized,
writable zeroed bytes; this is a foreign assumption tested with real libc, not
an allocator guarantee inferred by the compiler. The admitted guard owns the
same native allocation through acquisition, body and finish until consumption.
Original source header, copied call/Type/Row correspondence, live activation and
the selected exact guard remain separate authorities. Address reuse or a
same-shaped donor never revives access.

Ordinary exact operation overrides retain precedence. The selected associated
source handler obtains local authenticated State; common byte primitives check
extent, initialization and write permission. `length` returns the stored `Int`.
`read` returns `Success(byte)` in `[0, 255]` or `Failure(InvalidIndex)`.
`write` checks the index before byte conversion, returning `InvalidIndex` or
`InvalidByte` inside `Failure` as appropriate. It prepares the ordinary success
value and the common complete reply before mutation. Refusal leaves bytes
unchanged; success returns `Success(())`. Invalid Core/activation authority and
internal exhaustion are terminal, never ordinary library errors.

Normal completion runs inner cleanup with required outer resources live, then
calls the checked `free` finish once and returns `Success(body_value)`. A body
error or nested `Outcome` remains inside that success. Capture/resume moves the
same owner. Owned discard skips the abandoned suffix and wrapper, runs admitted
finish in structural order, then continues the discarding clause. An acquisition
inside running cleanup completes normally with its own wrapper. Neither running
cleanup nor required outside completion may be abandoned.

Internal failure uses the common safe host-destruction/dependency rules without
replaying source finish or undoing earlier writes. A destruction failure
preserves the primary error and reports incomplete cleanup. Fixed release
reservation does not promise eventual release under divergence, process death
or a dishonest foreign contract. Common runtime guards remain; the former
handwritten native-buffer adapter and special dispatch are absent. Cell behavior
is unchanged.

## Synchronous hook execution

`hook H { body }` enters an exact identity handler for the qualifying hook API.
Its `publish` clause resumes with the incoming payload unchanged. An inner root
for exactly `H` cuts off the surrounding chain until that root returns; other
instances retain their existing interpretation.

`register H transformer { body }` evaluates `transformer` exactly once in the
preceding context. Successful preparation acquires a fresh registration
activation and enters its body. A non-interpreting owner retains the callback
outside the generated exact handler. The activation is distinct on every
successful execution, including overlapping executions of one source site.
It is not a source value or a resource identity supplied as an effect argument.

The generated handler uses the ordinary request and completion rules. Its
clause forwards the incoming payload to the older chain, applies the saved
callback to the returned payload by ordinary function application, and resumes
with that result. For outer registration A and inner registration B,
publication computes `B(A(payload))`. Each repeated registration participates
separately. The body's result is returned unchanged after its registration
is removed normally; the result need not have the hook's payload type.

Selecting B captures its handler and publisher-side control, while B's owner
remains outside that capture. Its callback therefore runs under handlers
surrounding its registration, not handlers installed only around publication.
Its saved lexical term, type and row environment remains ordinary closure
state. A nearer exact source handler can intercept publication under the
existing rules; hook syntax gives no sealed interpretation authority.

A publication inside B's callback sees the then-active older prefix, not B or
younger registrations held in captures. A temporary registration inside that
callback affects publications only in its own body. A nested root cuts off
the older prefix for its exact target. Neither operation inserts callbacks into
the original publication's pending sequence, replays a completed prefix or
reevaluates an initializer. Explicit recursive calls may still diverge.

Forwarding or an outward callback request can move younger registration owners,
their pending callbacks and cells into captured control. Resume restores those
same owners and activation keys in order, without reacquisition or duplication.
Consumed clause boundaries may remain below restored handlers while their
remaining clause computation completes. Registration ownership therefore does
not require the owner and generated handler to remain adjacent.

Normal scope completion removes its callback entry and releases registration
capacity exactly once, inner before outer. An external ordinary copy of the
callback remains callable but retains no registration authority. A closure
containing a request to a static hook identity uses the chain active when that
closure is called, not the chain present when it was created.

Live-registration capacity counts owners in both active and captured control.
Capture and resume do not change that count; normal release makes capacity
reusable. Acquisition checks capacity and prepares all fallible state before
publishing an activation. Stale or duplicated non-owning activation facts are
rejected before invocation or mutation. The machine moves, rather than copies,
owning registration frames.

Checked discard can close registration owners inside its owned capture,
including recursively owned captures, without invoking abandoned publication
callbacks. It cannot bypass required completion outside that closure.
Subscriber-local discard remains valid when those outside owners and scheduled
resumes still complete. Internal work, allocation or capacity failure disposes
registrations, cells, environments
and captured control iteratively. It runs no source cleanup or destructor
callback and does not roll back earlier callback effects. Divergence promises
no eventual deregistration.

Publication over N participating registrations performs N ordinary callback
applications and their forwarding/resume steps, in addition to handler search
and callback work. Added scans and retained relationships charge the existing
evaluator work ledger. There is no machine-global registry, copied whole-chain
snapshot, priority sort or second callback evaluator. Hook-free Pure execution
allocates no registration owner or live-registration storage.

## Scoped cleanup actions

A cleanup expression evaluates its action once in the preceding environment.
Only after this initialization and fallible acquisition preparation succeed
does it acquire an invocation obligation and enter its body. Abandonment before
that acquisition owns no invocation of the action. Copying the ordinary callable
does not acquire another obligation.

Normal completion saves the body value and invokes the retained action with
`()`, using ordinary function application in the same evaluator. The action's
`Unit` result is ignored; its completion returns the saved body value unchanged.
An unused or pure body does not remove the acquired obligation. Nested actions
complete in structural innermost-to-outermost order, while still-enclosing cell
and registration owners remain available until their own closing positions.

Capture and resume transfer the owner without invoking or duplicating its
action. Starting an action makes it ineligible for another invocation, but
retains its unfinished completion. Outward requests may capture and resume
this running state; they may not abandon it. Actions may acquire and complete
nested scopes through the same rules.

An invocation attempt is not a proof of termination or successful native
release. Internal exhaustion or termination provides no source-cleanup
guarantee. Host teardown remains iterative, does not replay completed actions
and does not roll back effects already performed.

### Typed failure reporting

Recoverable cleanup failure uses ordinary source effects and data. An explicit
`CloseResult<E>` with alternatives `Closed` and `CloseFailed(E)` can feed a
`reportClose` adapter: `Closed` returns unit; `CloseFailed(error)` performs
`CleanupFailure<E>.report error`, whose result is unit. The adapter does not
retry. These names denote source declarations, not privileged runtime forms.

A surrounding collector retains `Report<A, E>`, containing the body value `A`
and a `Failures<E>` list. On each report it resumes with `()`, then prepends
that error to the returned list. This preserves emission order while allowing
all remaining actions to finish. A collector that aborts by skipping a running
action or close operation is not admitted.

The body value may be `Outcome<T, P>`: its primary failure `P` is preserved
separately from cleanup errors `E`. Success is preserved too; the first cleanup
error is the primary cleanup failure, followed by later errors. With no cleanup
errors, the collector retains the body outcome unchanged. Different cleanup
error types require an explicit
sum or independently collected report effects, not implicit boxing or a common
error domain. Ignored failure constructors have no automatic reporting meaning.

The [complete tool example](../docs/tools/ash.md) retains primary `7` and cleanup
errors `22, 11`, yielding `72211`. The corresponding normal return retains
`Success 42` with the same error order. Reporting does not relax stored-payload
dependency checks, promise native release, or convert internal failure into a
source outcome.

## Observation

Successful evaluation of the generated entry application retains the heap
with the result value. The observation pairs that value with the closed result
type established for `main`. Observation renders tuples and constructors
structurally. A constructor with a tuple
payload renders its components as constructor fields. A location already on
the active rendering path renders as `<cycle>`. Removing a location from the
active path after its subtree means shared acyclic data renders in full at each
occurrence. Function values render as `<function>`.

Successful observation retains no live resource scope, registration owner,
cleanup obligation or captured continuation.
The observed heap may retain copied values and unused non-owning handle
entries, but owns no released cell payload.

A completed `newtype` value renders exactly as its representation value because
no wrapper or constructor tag reaches the heap. The observation's separately
retained closed result type still renders the nominal newtype spelling and its
applied type arguments. Nested ordinary data in a representation keeps its
ordinary structural rendering and allocation. Observation performs no runtime
nominal-registry lookup and adds no special newtype value case.

Evaluation reports uninitialized access, alias loops, invalid locations, an
impossible complete-pattern failure, malformed effect control, and runtime
capacity exhaustion as structured internal runtime failures. They are not
source-language error outcomes.

The executable test `dynamic_cyclic_data_observation_is_finite` checks guarded
allocation and active-path rendering:

```ash
type Stream =
    Next(Int, Stream)

main : Unit -> Stream
main () = {
    let rec ones : Stream = Next(1, ones)
    ones
}
```

## Derived multi-step notation

The relation `configuration ->* configuration'` is the reflexive transitive
closure of the configuration step `->`. It is useful for derivations but does
not form a second normative evaluation relation.

```sequent
family derived-multi-step:
  E-Multi-Refl :=
    ===>
    configuration ->* configuration

  E-Multi-Step :=
    configuration_1 -> configuration_2
    configuration_2 ->* configuration_3
    ===>
    configuration_1 ->* configuration_3
```

`E-Multi-Refl` permits zero steps. `E-Multi-Step` prefixes one normative step to
a derived sequence.

## Representative derivations

The following matrix connects each derivation to its executable specification
test. Every case first enters its module's recursive global group and applies
`main` through `E-Let-Rec-Allocate`, `E-Let-Rec-Body`, and `E-Beta`. The matrix
lists the principal rules after that common entry prefix. The prose derivations
omit grouping erased by elaboration and use renamed binders where needed to show
distinct lexical identities.

| Case | Executable test | Principal rule sequence |
| --- | --- | --- |
| `V-003` | `dynamic_binding_derivation_example_v003_is_executable` | `E-Let-Enter`, `E-Let-Continue`, `E-Add-Values` |
| `V-001` | `dynamic_primitive_derivation_example_v001_is_executable` | `E-Add-Right`, `E-Multiply-Values`, `E-Add-Values` |
| `V-002` | `dynamic_application_derivation_example_v002_is_executable` | `E-Beta`, `E-Add-Values` |
| `V-004` | `dynamic_capture_derivation_example_v004_is_executable` | `E-Let-Enter`, `E-Let-Continue`, `E-Beta`, `E-Add-Values` |
| `V-008` | `dynamic_nested_application_derivation_example_v008_is_executable` | Strict application frames, two `E-Beta` steps, and integer primitives |
| `EFFECT-001` | `nested_forwarding_restores_intervening_handlers_in_original_order` | `E-Handle-Enter`, `E-Perform-Operand`, `E-Request-Select`, `E-Resume-Operand`, `E-Resume-Restore`, `E-Clause-Return` |

### Binding and shadowing: V-003

```ash
main : Unit -> Int
main () = {
    let value = 1
    let value = value + 1
    value
}
```

Elaboration gives the two `value` binders distinct identities. The first
`E-Let-Continue` extends the environment for the second initializer.
`E-Add-Values` produces `2`, and the second continuation extends the result
environment with that integer value. Thus `main ()` evaluates to `2`.

### Primitive precedence: V-001

```ash
main : Unit -> Int
main () = 1 + 2 * 3
```

Precedence produces `1 + (2 * 3)`. Because the left addition operand is already
a value, `E-Add-Right` carries the `E-Multiply-Values` step to obtain `1 + 6`.
`E-Add-Values` then produces `7`.

### Application: V-002

```ash
increment : Int -> Int
increment value = value + 1

main : Unit -> Int
main () = increment 41
```

The module's `increment` and `main` globals elaborate as one two-member
recursive binding. `E-Let-Rec-Allocate` installs both function templates
without allocating a data slot. The empty initialization sequence enters the
generated entry application through `E-Let-Rec-Body`. The common entry
`E-Beta` enters the body of `main`; looking up `increment` then materializes its
closure. A second `E-Beta` extends that closure's captured environment with the
integer value `41`, and `E-Add-Values` produces `42`.

### Lexical capture: V-004

```ash
main : Unit -> Int
main () = {
    let offset = 40
    let add_offset : Int -> Int = fn(value) {
        value + offset
    }
    add_offset 2
}
```

The first `E-Let-Continue` binds the integer value `40` directly. The function
captures that lexical environment, and the second binding stores the closure
value directly. `E-Beta` extends the captured environment with the integer
value `2`; `E-Add-Values` then produces `42`. This is lexical rather than
dynamic scope.

### Nested application: V-008

```ash
increment : Int -> Int
increment value = value + 1

fn double(value : Int) -> Int {
    value * 2
}

main : Unit -> Int
main () = double (increment 20)
```

The three globals elaborate as one recursive group. Allocation installs the
`increment`, `double`, and `main` function templates in the recursive
environment; it allocates no data slots. After the common entry `E-Beta` enters
the body of `main`, strict application frames evaluate `increment 20` before
applying `double`: `E-Beta` enters `20 + 1`, then `E-Add-Values` produces `21`.
The outer `E-Beta` enters `21 * 2`, and `E-Multiply-Values` produces `42`.

### Forwarding and deep resume: EFFECT-001

```ash
effect Ask {
    ask : Int -> Int
}

effect Mark {
    mark : Int -> Int
}

main : Unit -> Int
main () = handle (
    handle ({
        let answered = perform Ask.ask 1
        perform Mark.mark answered
    }) with Mark {
        mark value => resume (value + 10)
    }
) with Ask {
    ask value => {
        let continued = resume (value + 1)
        continued + 100
    }
}
```

The two `E-Handle-Enter` steps activate `Ask` outside `Mark`. The `Ask.ask`
request crosses the nonmatching `Mark` boundary, so `E-Request-Select` moves
that boundary with the selected `Ask` boundary and enters the `Ask` clause with
both absent. `E-Resume-Restore` reinstalls `Ask` around the captured remainder
and restores `Mark` inside it. The resumed `Mark.mark 2` request therefore
selects `Mark`; its clause resumes with `12`. `E-Clause-Return` first returns
from the `Mark` clause and then from the `Ask` clause after the final addition,
producing `112`. The executable trace asserts this exact selection,
restoration, request, resume, and clause-return order.
