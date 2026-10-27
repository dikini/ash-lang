# Dynamic Semantics

Ash evaluation is defined by one small-step relation over configurations
`CONFIG(heap, environment, control, continuation)`. Its Ash control transitions
are deterministic relative to fixed admitted native bindings and the outcomes
of their external calls; it does not determine or guarantee those outcomes.
The heap is
fresh for one evaluation and maps numeric locations to tuples, completed
constructors, uninitialized slots for recursive data, or
aliases. It also retains region-owned allocation records with pending or
initialized disposition, backing locator, extent/alignment and actual residency.
Tuple elements and constructor payloads are runtime values. The environment maps resolved term
identities to runtime values. Effect execution also retains lexical type/row
instantiation in the environment, separately from term bindings. This metadata
is not a source value. The continuation records the remaining strict
work, including ordered lexical handler boundaries, selected allocation views,
prospective/live/closing region activations, pending initialization and saved
paired completion. These extend the same configuration, not another machine. A selected operation moves
one suffix of that continuation into a clause-owned captured continuation. The
suffix is moved, not copied. Its clause boundary records whether the unique
resume capability still owns that captured control or has consumed it.

Runtime values are arbitrary-precision integers, Booleans, unit, immutable
byte sequences, validated UTF-8 strings, lexical
functions, canonical builtin functions, internal lexical polymorphic functions,
payload-constructor functions, opaque data-pointer Address values, opaque non-owning resource handles,
or heap locations. A function
template is code metadata. Effect execution stores the lexical callable once
when its function expression or recursive member is materialized; lookup returns
that stored callable. Pure execution retains its allocation-free template lookup. A location is an internal handle, not source-level
identity or observable mutation.

Pure Core type abstractions and applications erase without extending the
environment or allocating heap cells. Effect execution retains lexical
polymorphic functions and their validated instantiation so exact operation
identities remain meaningful across generic calls. No type or kind becomes a
source-inspectable value, and type/row instantiation alone allocates no ordinary
heap cell.
Validated newtype conversions and local nominal scopes are likewise erased
static operations rather than values.

## Initial configuration

Elaboration produces one validated linked Core expression: an explicit host-backed
root outside dependency-ordered recursive global groups and the generated
application of local main to unit, with required native interpretation. Root
establishment precedes every module closure record. Host startup/control storage
prepares the initial provider; no arbitrary Source computation runs without a
selection and no alternate Source heap supplies fallback storage. The final
outer expression has an empty row; the inner main application retains its row. Evaluation starts
with that expression as control, a fresh empty heap and environment, and an
empty continuation:

```sequent
E-Program-Start :=
  elaborate(modules, entry) = linked_program
  validate(linked_program) = success
  supplied native bindings are admitted against the original symbols of linked_program
  ===>
  INITIAL(modules, entry) = CONFIG(empty_heap, empty_environment, linked_program, empty_continuation)
```

`linked_program` includes the generated root around the dependency-ordered groups
and `main ()` described in
[Elaboration](elaboration.md). The second premise requires independent
whole-program validation before evaluation. Neither premise performs module
loading at runtime. The ordinary recursive-binding and application rules enter
the linked groups and call `main`. Imports have no initialization step, and
modules are not runtime values.

Native-binding admission checks the entries actually supplied against the
original symbol facts of validated Core before Ash execution. It does not check
that every possible native request has a binding; the empty supplied table
satisfies this association check. When a native boundary is selected, invocation
requires the entry for that exact original symbol. A missing selected entry is
a terminal runtime failure after operand evaluation and boundary selection,
before the callback is called. A nearer ordinary source handler requires no
callback lookup. Admission performs no implicit native compilation or linking.

## Region construction and close steps

Write `CONFIG(H, E, c, K)` for the same configuration above. H retains region
allocation records and K retains selection, pending construction and completion.
The following named steps refine that relation. A prospective activation is not
live access; a pending record exposes no readable initialized object. Allocate
and release remain the fixed ordinary pair of one successful region setup.

| Step | Preconditions and state change |
| --- | --- |
| EnterPrepare | Reserve fresh prospective a; bind R to a for provider/body lexical instantiation. Evaluate the provider once under the preceding selection. Failure publishes no live access or completion owner. |
| EnterLive | Complete preparation, publish that same a with its fixed pair/discipline and one completion owner, then bind body access r. |
| SelectEnter/Return | Require live actual access, install explicit default forwarding to that owner and restore preceding selection on return. Acquire no owner and relocate no value. |
| ContextQuery | A Unit request returns the selected dependency-bearing view. Cleanup retains it beside its once-evaluated action; the action/payload does not cross that query. |
| RegionAllocate | Evaluate explicit context/request operands. Keep the serviced segment separate from outside control. At the actual live/closing owner's structural interpretation position, call its saved allocate member with lexical instantiation and saved preceding allocation selection. Body-local handlers do not move into callback control. |
| Request | After required children evaluate in order, retain fields/captures/layout locally, form an independent immediate usable-bytes/alignment descriptor, and perform the exact explicit request. Existing one-shot handler selection moves its captured segment. |
| Supply/Register | Under the native/module contract, obtain fresh disjoint backing; check actual owner, requested layout and stated extent/alignment; register one pending record. Refusal creates no successful record or initialized access. |
| ResumeStorage | Consume the ordinary continuation capability once; restore same activations, selections, serviced segment and pending construction. Check owner/record/layout compatibility without replaying operands. |
| Initialize/Publish | Write through compatible fresh pending storage using retained local fields/captures and their actual dependencies. After complete initialization/reply preparation, mark initialized once and return access with residency/dependency facts. Reused/mismatched records fail construction. |
| Project/Use | Require initialized storage and valid dependencies. An independent outer referenced value can shed its container dependency; an inline view retains it. Aliases/views never relocate values. |
| Capture/Resume | Move/restore the segment and its pending progress once above the saved clause continuation. Preserve outside frames and original owner enclosure; do not recompute activation identities or reset completed construction. |
| Discard | Check structural owned close and surviving interpreters, consume the capture once, revoke unpublished access and account/dispose pending records under their allocator contract. Close inner obligations in order without replaying abandoned code. |
| CloseBegin | Require that an ordinary result does not depend on the closing region; finish inner cleanup/dependent uses while backing is live. Root observation completes before root close. Begin the saved original release once; its unfinished completion remains required. |
| CloseFinish | After successful release completion, revoke access and bulk-retire that region's records; restore enclosing control. Other regions/shared allocator state remain valid. Copies of access own no close. |

A successful supplied layout includes the object's complete persistent
representation: tuple fields, nominal discriminant/payload, actual closure
captures, and persistent Bytes/String/large-Int backing where applicable.
Charging capacity while retaining that representation elsewhere is not supplied
storage. Request size arithmetic is checked; alignment is nonzero and supported,
and stated extent/alignment must satisfy the request. A zero-byte success grants
no readable bytes and initializes only a genuinely zero-readable-storage layout;
it still has its own allocation record/accounting. The backing adapter checks
association/layout and creates pending storage; a raw Address or phantom R alone
proves neither native validity nor initialized access.

The owner service remains available through required cleanup and release, at its
original position and preceding allocation selection. It does not restore a
removed public backend handler. Action-local handlers or surviving interpreters
must discharge the actual backend requirements; the existing cleanup-context and
running-completion restrictions still apply.

An ordinary function expression requests its record/captures once at creation.
Calls retain its lexical values/type context but use the caller's selection for
fresh construction. Integer results retain the conservative residency required
by static admission even when their runtime representation is immediate.

Refusal uses ordinary effects: a clause may resume only with valid successful
storage or, when checked, discard and return its ordinary result. Old objects and
performed effects are not rolled back. Reporting uses pre-existing/surrounding
storage or host entry reporting, not construction in a failed region. Internal
work/control/storage exhaustion remains terminal and has no source-cleanup
guarantee. At root entry, declared allocation refusal uses checked disposal and
the existing host observation/reporting foundation, distinguishing it from
internal exhaustion without constructing an error in the failed root. If required
close fails, report that actual failure rather than a clean refusal. Physical validity, freshness/disjointness and successful reclamation
remain native/module contract assumptions; returning from a broken native
release does not prove its physical promise. No fallback, source unwind or
quarantine protocol is introduced.

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
function. Independent Core validation admits ordinary function materialization,
inert constructor values or variables, transparent type operations, and
authenticated generated evidence adapters
inside that abstraction, as described in [Elaboration](elaboration.md#explicit-rank-1-operations).
Retaining these forms does not delay a source effect or source function body.

Evaluating an admitted abstraction that directly materializes a function creates
its generic record once, with actual term captures and lexical metadata but its
generalized parameters unbound. Authenticated deferred captures are retained
without eagerly executing evidence adapter spines. Transparent aliases/variables
and constructors forward without copying.

A type application evaluates its function, saves caller instantiation, substitutes
ordinary type and complete row arguments under that caller context, and binds
them simultaneously in an immutable view of the retained definition context.
Direct-callable instantiation does not recreate the record, enter a source
function body or mutate sibling views. A later call uses that lexical type/term context while fresh construction
uses the caller's allocation selection. Recursive lookup returns the stored
generic callable. Parameterized ordinary constructors retain their
existing constructor behavior; their type application needs no effect context.

The same lexical context travels with handlers and captured control. Request
selection compares exact effect instances after instantiating each side under
its own context. This is neither type inference from argument values nor a
machine-global mutable substitution. Types nested inside effect arguments,
including higher-kinded applications and function effect rows, participate in
the same validated substitution. Pure execution keeps the erasure rules above.

These Effect-only steps make retention and instantiation explicit.
`POLYMORPHIC` retains the stored generic callable, not a type value.
`prepare_generic` follows the admitted body shape. It materializes a direct
generic function or a capture-bearing deferred record once through the
selected-region path, retaining pending progress, actual captures and definition
metadata with generalized parameters unbound. Forwarding an existing callable
reuses its record; code-only constructors need no callable record. An
authenticated deferred body remains unevaluated at creation. In
`POLYMORPHIC(parameters, stored, definition_environment)`, `stored` distinguishes
a direct callable from an authenticated deferred body, and the retained
environment includes its captured term values. `direct_callable(stored)` selects
the first case; `authenticated_deferred_body(stored)` yields the second case's
retained body. `instantiate_view` changes only immutable lexical instantiation
metadata. Instantiating a deferred body instead evaluates its ordinary term
computation under the bound capture environment; any genuinely new Function
result materializes there in the existing prerequisite order.
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
    CONFIG(heap, environment, TypeAbstraction(parameters, body), continuation) -> CONFIG(heap, environment, prepare_generic(parameters, body, environment), continuation)

  E-Effect-Type-Application :=
    execution uses Effect Core
    ===>
    CONFIG(heap, environment, TypeApplication(function, arguments), continuation) -> CONFIG(heap, environment, function, TYPE-ARGUMENTS(arguments, instantiation(environment)) :: continuation)

  E-Effect-Type-Instantiate :=
    direct_callable(stored)
    instantiated = instantiate_arguments(arguments, caller_instantiation)
    body_environment = bind_parameters(definition_environment, parameters, instantiated)
    ===>
    CONFIG(heap, environment_value, POLYMORPHIC(parameters, stored, definition_environment), TYPE-ARGUMENTS(arguments, caller_instantiation) :: continuation) -> CONFIG(heap, environment_value, instantiate_view(stored, body_environment), continuation)

  E-Effect-Deferred-Instantiate :=
    authenticated_deferred_body(stored) = body
    instantiated = instantiate_arguments(arguments, caller_instantiation)
    body_environment = bind_parameters(definition_environment, parameters, instantiated)
    ===>
    CONFIG(heap, environment_value, POLYMORPHIC(parameters, stored, definition_environment), TYPE-ARGUMENTS(arguments, caller_instantiation) :: continuation) -> CONFIG(heap, body_environment, body, continuation)

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
arguments; an entered Core application uses the type-instantiation behavior
above. A monomorphic concrete evidence method becomes a binder occurrence for
the implementation method in its defining module's recursive group. A polymorphic
concrete or exact-current method retains a generated adapter over the
implementation method's complete type application. Pure execution erases these
operations; Effect execution preserves their validated arguments in lexical
instantiation, including authenticated forwarding without executing the retained
adapter spine. Effect lookup returns the once-materialized recursive callable;
Pure lookup retains its allocation-free template behavior.

A supplied lexical method uses ordinary nonrecursive binding, function closure,
and binder lookup. Its closure captures the preceding ordinary values required
by its body. A checked closure may retain that method after the evidence block
returns; a new occurrence outside the block cannot acquire its static evidence.
The lexical source identity and selection scope create no runtime value,
registry, scope frame, revocation check, or transition family.

The validated Core program may retain method authentication records and method
schemes as static authority. A retained Core type application records its complete
method arguments; Effect execution preserves their validated instantiation in
lexical metadata, including when an authenticated adapter forwards an existing
callable without entering that application node. The evaluator does not inspect
method authentication records or method schemes. It does not turn an interface
identity, selection record, implementation authorization route, method scheme,
or method argument into a runtime value, term binding, heap cell, interface
lookup, or interface-specific transition. Effect type applications retain
instantiation as described above; this does not turn method authentication or
selection into runtime authority.

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
function lookup. A genuinely new Function result from a prerequisite term
application materializes at that ordered creation site.

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
`42`. Root startup and once-created capture records add ordinary construction
work around this named ordering. The test's fixed-program resource ceilings do
not define allocation budgets, semantic limits or a bound on arbitrary
prerequisite chains.

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

In Effect execution, entering a recursive group reserves its recursive identities
and uninitialized data slots. It materializes direct ordinary function members
once in source member order, retaining their recursive environment and selected
residency, before guarded data initialization. Lookup returns stored callables.
In Pure execution, the existing allocation-free templates and data locations
are installed together as follows. Constructor-guarded data initializers evaluate in
source order. Completing a data member stores an alias from its slot to the
initializer's constructed location. Lookup of a recursive data member returns
its slot without forcing the alias. Only Pure lookup materializes a lexical
function from its template and the recursive environment.

```sequent
family recursive-binding-steps:
  E-Let-Rec-Allocate :=
    execution uses Pure Core
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

In the Pure rules, function templates and data locations enter scope before
data initialization.
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

Effect function materialization uses these steps in the same configuration.
`reserve_recursive` publishes only internal recursive identities/data slots;
`functions` lists direct function initializers in source order. The existing
`initialize` control below runs guarded data only after all stored callables are
ready. Completed materialization and pending data state survive capture/resume
without replay. Abandonment accounts for unpublished construction but does not
roll back previous effects or initialized records.

```sequent
family effect-recursive-materialization:
  E-Effect-Rec-Reserve :=
    execution uses Effect Core
    reserve_recursive(heap, environment, members) = heap_1, environment_1, functions, data
    ===>
    CONFIG(heap, environment, let rec members; body, continuation) -> CONFIG(heap_1, environment_1, materialize(functions, data, body), continuation)

  E-Effect-Rec-Function :=
    ===>
    CONFIG(heap, environment, materialize((binder, initializer) :: rest, data, body), continuation) -> CONFIG(heap, environment, initializer, STORE_FUNCTION(binder, rest, data, body, environment) :: continuation)

  E-Effect-Rec-Store :=
    environment_1 = store_recursive_callable(recursive_environment, binder, callable)
    ===>
    CONFIG(heap, environment_value, callable, STORE_FUNCTION(binder, rest, data, body, recursive_environment) :: continuation) -> CONFIG(heap, environment_1, materialize(rest, data, body), continuation)

  E-Effect-Rec-Data :=
    ===>
    CONFIG(heap, environment, materialize(empty, data, body), continuation) -> CONFIG(heap, environment, initialize(data, body), continuation)
```

A polymorphic function member has one outer `TypeAbstraction` node whose
nonempty parameter sequence contains all generalized parameters. Allocation
in Pure execution follows that wrapper to install the same function template;
ordinary Pure evaluation still uses `E-Type-Abstraction`. Effect execution
materializes and retains the generic record once with its lexical captures.
Lookup and type application reuse that record; instantiated views do not mutate
it or a sibling view.

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
environment, and enters its body. Its lexical instantiation remains fixed while
fresh body construction uses the caller's selected allocation context. The
callable record and captures do not move or reinitialize. A payload constructor
initializes a supplied nominal record with the argument as payload in Effect
execution; the direct allocation rule below applies to Pure Core.

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
    execution uses Pure Core
    function_value = constructor_function(constructor)
    heap_1, result_location = allocate(heap, constructor(constructor, argument_value))
    ===>
    CONFIG(heap, environment, argument_value, APPLY_ARGUMENT(function_value) :: continuation) -> CONFIG(heap_1, environment, result_location, continuation)
```

The continuation frames make the left-to-right order explicit. A closed,
well-typed program cannot apply an integer, Boolean, unit, tuple, or completed
constructor value.

## Tuples, constructors, and matches

Tuple elements evaluate strictly from left to right before their completed
record is published. Effect construction requests the selected owner's supplied
storage and initializes it locally with these retained operands; Pure Core uses
its ordinary tuple cell. Effect nullary constructors use the same supplied
nominal-record path. Code-only payload-constructor values allocate no closure
record; generated wrappers do so only when lowered to ordinary Function.
Persistent Bytes/String backing, large Int digits and actual closure captures
follow the same selected-owner request, initialization and publication discipline.
Known immediate values need no backing record.

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

## Native symbol execution

Write `a_p` for an Address value whose private data pointer is `p`, and `a_null`
for the null Address. These are metavariables for existing opaque runtime values,
not Ash constructors, literals, integers or image constants. Pointer equality
here means data-pointer equality, including null; it establishes neither
allocation identity nor validity. Address copies preserve the pointer and
create no allocation, release or resource dependency.

Let `f_null`, `f_is_null` and `f_equal` denote the canonical builtin function
values exported as `null`, `is_null` and `equal` by `@builtin.foreign`. Ordinary
application evaluates the function and its one argument before these rules use
the existing `APPLY_ARGUMENT` frame. `tuple_fields(heap, value)` follows only
ordinary heap aliases and reads an ordinary tuple cell in source order; it does
not inspect memory behind an Address. The three value rules leave the Ash heap
and continuation below the application unchanged and perform no foreign call.

```sequent
family address-value-steps:
  E-Address-Null :=
    ===>
    CONFIG(heap, environment, (), APPLY_ARGUMENT(f_null) :: continuation) -> CONFIG(heap, environment, a_null, continuation)

  E-Address-Is-Null :=
    b is true exactly when p is the null data pointer
    ===>
    CONFIG(heap, environment, a_p, APPLY_ARGUMENT(f_is_null) :: continuation) -> CONFIG(heap, environment, b, continuation)

  E-Address-Equal :=
    tuple_fields(heap, pair_value) = (a_p, a_q)
    b is true exactly when p and q are equal data pointers
    ===>
    CONFIG(heap, environment, pair_value, APPLY_ARGUMENT(f_equal) :: continuation) -> CONFIG(heap, environment, b, continuation)
```

The internal term `NativeInterpret(body, interpretations)` denotes the validated
Effect Core boundary described in [Elaboration](elaboration.md#surface-erasure).
Its entries retain exact original symbols and their effect instances.
`NATIVE(interpretations, boundary_environment)` is a lexical continuation
boundary, not a source value, host token or resource owner. Entering it preserves
the body environment; ordinary body completion removes only that boundary.

```sequent
family native-boundary-steps:
  E-Native-Enter :=
    ===>
    CONFIG(heap, environment, NativeInterpret(body, interpretations), continuation) -> CONFIG(heap, environment, body, NATIVE(interpretations, environment) :: continuation)

  E-Native-Body-Return :=
    ===>
    CONFIG(heap, environment_value, value, NATIVE(interpretations, boundary_environment) :: continuation) -> CONFIG(heap, environment_value, value, continuation)
```

A symbol request evaluates its operand with `E-Perform-Operand` below. Boundary
selection uses the same innermost-first order as ordinary handlers and cells.
In the rules below, `prefix` contains exactly the continuation entries nearer
than the displayed native boundary. No entry in it may accept the requested
instance. Thus a nearer matching source handler uses `E-Request-Select` instead,
without looking up or invoking a native binding. An unrelated nearer boundary
is crossed by the search but remains in the continuation.

`entry` retrieves the exact original symbol for the operation from the selected
boundary, together with its handled effect instance. That instance is compared
under the boundary's saved lexical instantiation, while the request uses its own
saved instantiation. `linked_binding(symbol)` retrieves the generated host's typed bridge callback,
not a C callback argument or an Ash function pointer. It is associated
with that same original symbol; equal display names or operation coordinates
alone do not authenticate a replacement binding.

`marshal(heap, domain, operand_value) = arguments, keepalive` is metanotation
for the supported source-to-C mapping, not a source operation or a new memory
interface. For whole Unit and `()`, the pointer vector and `keepalive` are empty.
For whole Address and `a_p`, they are `[p]` and empty. For whole Bytes and `bytes`,
they are `[backing(bytes)]` and `[bytes]`. For a flat Address/Bytes tuple,
`tuple_fields` supplies its fields and these pointer vectors and retained Bytes
values concatenate in source order. `backing(bytes)` denotes its existing
readonly backing pointer; retaining that Bytes value keeps this backing alive.
No length, terminator, encoding conversion, copying or mutable view is added.
Empty Bytes promises no readable byte, and its pointer does not encode emptiness.
Unsupported source domains have already been rejected statically.

The callback-outcome premise describes one synchronous external invocation, not
a pure query or a retryable test. Its Bytes `keepalive` values remain retained
from marshaling through callback return and result conversion. An Address reply
preserves its pointer, including null; a C void reply becomes `()` without
reading a C result. Both rules consume only the request frame and return to the
same continuation, including every crossed and selected boundary. They create
no clause owner, captured continuation, resume or discard capability.

```sequent
family native-request-steps:
  E-Native-Address-Return :=
    requested = instantiate(instance(operation), request_instantiation)
    continuation = prefix ++ NATIVE(interpretations, boundary_environment) :: outer
    no boundary in prefix accepts requested
    entry(interpretations, operation) = symbol, handled
    instantiate(handled, instantiation(boundary_environment)) = requested
    linked_binding(symbol) = callback
    marshal(heap, domain(symbol), operand_value) = arguments, keepalive
    result_type(symbol) = Address
    callback(arguments) returns data pointer p while keepalive is retained
    ===>
    CONFIG(heap, environment_value, operand_value, REQUEST(operation, request_instantiation) :: continuation) -> CONFIG(heap, environment_value, a_p, continuation)

  E-Native-Void-Return :=
    requested = instantiate(instance(operation), request_instantiation)
    continuation = prefix ++ NATIVE(interpretations, boundary_environment) :: outer
    no boundary in prefix accepts requested
    entry(interpretations, operation) = symbol, handled
    instantiate(handled, instantiation(boundary_environment)) = requested
    linked_binding(symbol) = callback
    marshal(heap, domain(symbol), operand_value) = arguments, keepalive
    result_type(symbol) = Unit
    callback(arguments) returns C void while keepalive is retained
    ===>
    CONFIG(heap, environment_value, operand_value, REQUEST(operation, request_instantiation) :: continuation) -> CONFIG(heap, environment_value, (), continuation)
```

These transitions apply under the declaration's assumed native signature and
readonly backing contract. The compiler does not verify foreign correctness or
termination. For fixed bindings and a fixed external outcome sequence, each
returning invocation determines one result and one continuation step. A callback
that does not return supplies no return step; the rules promise no progress of
foreign code. External effects are not represented by an additional Ash heap or
foreign-world object, and Unit-returning calls may still have external effects.

Internal work/storage, binding or callback-interface failures are terminal
runtime failures, not source error constructors or alternative successful
transitions. Failure after an invocation does not retry it or undo its external
effects. Bindings express ordinary error results and scoped cleanup in Ash; an
Address result alone triggers no release. Native code must not mutate or free
managed Bytes. Retained or returned backing pointers require the binding module
to keep the original Bytes alive for every later native use; producing `a_p`
does not capture or infer this relation.

No arbitrary memory read/write, Address-to-Bytes/String conversion, numeric ABI,
out-pointer storage or compiler-managed foreign lifecycle is supplied. Ordinary
cleanup and resource completion rules below continue to govern Ash control.

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

A request first evaluates its one operand. Once that operand is a value,
`select_nearest` searches outward for the innermost accepting source-handler,
cell or native interpretation boundary. The source-handler branch below requires its exact effect
identity and instantiated type arguments to equal the operation's instance,
with no nearer accepting cell or native interpretation boundary. The request saves its lexical instantiation
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
    requested = instantiate(instance(operation), request_instantiation)
    select_nearest(continuation, requested) = clause, handler_environment, handler, owner, captured, outer
    no nearer cell or native interpretation boundary accepts requested
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
resumed-computation writes still update the slot in control order. Reading,
replacing or dropping an Address payload performs no native memory operation
and creates no release obligation.

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

Successful evaluation retains root backing through result observation and
required completion. The existing host observation foundation retains the
observed root storage after successful ownership transfer and releases it with
its last observation owner; no closed custom region remains live and no value
is relocated. This is distinct from source region access or a source finalizer.
The result value remains paired with its heap. The observation pairs that value with the closed result
type established for `main`. Observation renders tuples and constructors
structurally. A constructor with a tuple
payload renders its components as constructor fields. A location already on
the active rendering path renders as `<cycle>`. Removing a location from the
active path after its subtree means shared acyclic data renders in full at each
occurrence. Function values render as `<function>`. Address values render as `<address>`
without disclosing or dereferencing the pointer.

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
