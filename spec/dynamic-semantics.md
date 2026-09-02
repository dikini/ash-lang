# Dynamic Semantics

Ash evaluation is defined by one deterministic small-step relation over
configurations `CONFIG(heap, environment, control, continuation)`. The heap is
fresh for one evaluation and maps numeric locations to tuples, completed
constructors, uninitialized recursive data slots, or aliases. Tuple elements
and constructor payloads are runtime values. The environment maps resolved term
identities to runtime values. The continuation records the remaining strict
work, including ordered lexical handler boundaries. A selected operation moves
one suffix of that continuation into a clause-owned captured continuation. The
suffix is moved, not copied. Its clause boundary records whether the unique
resume capability still owns that captured control or has consumed it.

Runtime values are arbitrary-precision integers, Booleans, unit, lexical
functions, payload-constructor functions, or heap locations. A function
template becomes a lexical function with the recursive environment when its
binder is looked up. A location is an internal handle, not source-level
identity or observable mutation.

Core type abstractions and applications are static evidence. They are not
runtime values, do not extend the environment, and allocate no heap cells.
Validated newtype conversions are likewise erased static operations rather
than values.

## Initial configuration

Elaboration produces one validated linked Core expression: dependency-ordered
recursive global groups around the generated application of the entry module's
local `main` to unit. Static checking has already established an empty entry
effect row. Evaluation starts with that expression as control, a fresh empty
heap and environment, and an empty continuation:

```sequent
E-Program-Start :=
  elaborate(modules, entry) = linked_program
  validate(linked_program) = success
  ===>
  INITIAL(modules, entry) = CONFIG(empty_heap, empty_environment, linked_program, empty_continuation)
```

`linked_program` is the dependency-ordered groups around `main ()` described in
[Elaboration](elaboration.md). The second premise requires independent
whole-program validation before evaluation. Neither premise performs module
loading at runtime. The ordinary recursive-binding and application rules enter
the linked groups and call `main`. Imports have no initialization step, and
modules are not runtime values.

## Type erasure

Entering either explicit Core type operation takes one step to its retained
term. Validation has already checked parameter scope, argument arity, kinds,
and substitution, so evaluation does not inspect the parameters or arguments.

```sequent
family type-erasure-steps:
  E-Type-Abstraction :=
    ===>
    CONFIG(heap, environment, TypeAbstraction(parameters, body), continuation) -> CONFIG(heap, environment, body, continuation)

  E-Type-Application :=
    ===>
    CONFIG(heap, environment, TypeApplication(function, arguments), continuation) -> CONFIG(heap, environment, function, continuation)

  E-Newtype-Conversion :=
    ===>
    CONFIG(heap, environment, NewtypeConversion(owner, direction, child), continuation) -> CONFIG(heap, environment, child, continuation)
```

The unchanged heap and environment make erasure observable only as progress in
the machine. No source program can inspect a type parameter or type argument.
Method-local type arguments erase through `E-Type-Application`.
`E-Newtype-Conversion` also leaves the continuation unchanged. Independent
Core validation has already authenticated the owner, direction, child and
result types, representation substitution, and provenance, so evaluation does
not inspect conversion metadata or consult a registry.

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
arguments; entering the Core application uses `E-Type-Application`. A
monomorphic concrete evidence method becomes a binder occurrence for the
implementation method in its defining module's recursive group. A polymorphic
concrete or exact-current method first enters its generated adapter type
abstraction and then the implementation method's complete type application.
`E-Type-Abstraction` and `E-Type-Application` erase both operations. Looking up
the recursive function binder materializes a lexical closure under the existing
recursive-binding behavior.

The validated Core program may retain method authentication records and method
schemes as static authority, and a Core type application carries its retained
method arguments in control until `E-Type-Application` erases that node.
The evaluator does not inspect method authentication records or method schemes.
It does not turn an interface identity, selection record, implementation
authorization route, method scheme, or method argument into a runtime value,
environment entry, heap cell, frame, lookup, or transition choice.

For a generic implementation method, lowering uses the recorded head
substitution to form an ordinary Core type application. When evaluation enters
that Core node, `E-Type-Application` erases it to its function without inspecting
the type arguments. The recorded substitution itself does not reach the
evaluator. The existing strict application transitions then evaluate and apply
every recursively generated prerequisite method in declaration order. The
result is the lexical method closure that accepts the source value argument. At
a constrained-global call, the same transitions apply its evidence functions
before the surrounding source arguments because elaboration nested the
applications in that order. Abstract prerequisite evidence uses ordinary
environment lookup; concrete prerequisite evidence uses ordinary recursive
function lookup and closure materialization.

There is no runtime interface value, dictionary, interface or implementation
registry, implementation lookup, interface dispatch, registration step, or
interface-specific failure mode. Polymorphic method evidence uses ordinary
function values and applications but adds no new evaluator value class,
environment-entry class, frame kind, lookup class, transition class, failure
reason, or runtime interface state. Evidence construction uses only type
erasure, recursive binding, ordinary binder lookup and closure materialization,
and the strict application transitions below. It adds no Core node and requires
no new evaluation rule.
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
follows that wrapper to install the same function template; ordinary evaluation
still uses `E-Type-Abstraction`. No type wrapper becomes part of a closure.

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
continuation transition within one unchanged heap configuration.

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

## Effect handlers and resume

`HANDLER(handler, instance, clauses, environment)` is an ordered lexical
continuation boundary. `REQUEST(operation)` and `RESUME(handler, owner)` are
ordinary strict frames for their operands. `CLAUSE(handler, owner, state)` is
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
`select_nearest` searches outward through continuation boundaries for the
nearest handler whose exact effect identity and zonked type arguments equal the
operation's instance. It returns the matching clause, the handler's saved
environment, an owner identity, the moved segment through that boundary, and
the continuation outside it:

```sequent
family request-steps:
  E-Perform-Operand :=
    ===>
    CONFIG(heap, environment, perform operation operand, continuation) -> CONFIG(heap, environment, operand, REQUEST(operation) :: continuation)

  E-Request-Select :=
    select_nearest(continuation, instance(operation)) = clause, handler_environment, handler, owner, captured, outer
    clause = operation pattern => body
    match(heap, operand_value, pattern) = bindings
    clause_environment = extend(handler_environment, bindings)
    ===>
    CONFIG(heap, environment_value, operand_value, REQUEST(operation) :: continuation) -> CONFIG(heap, clause_environment, body, CLAUSE(handler, owner, live(captured)) :: outer)
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

Static checking and Effect Core validation make an unmatched request, a
missing owner, a second resume, or an invalid capture boundary unreachable from
accepted source. If one appears after successful validation, evaluation
reports an internal malformed-Core or machine failure. Ash has no source-level
unhandled-operation, abort, exception, cancellation, or unwind result.

## Observation

Successful evaluation of the generated entry application retains the heap
with the result value. The observation pairs that value with the closed result
type established for `main`. Observation renders tuples and constructors
structurally. A constructor with a tuple
payload renders its components as constructor fields. A location already on
the active rendering path renders as `<cycle>`. Removing a location from the
active path after its subtree means shared acyclic data renders in full at each
occurrence. Function values render as `<function>`.

A completed `newtype` value renders exactly as its representation value because
no wrapper or constructor tag reaches the heap. The observation's separately
retained closed result type still renders the nominal newtype spelling and its
applied type arguments. Nested ordinary data in a representation keeps its
ordinary structural rendering and allocation. Observation performs no runtime
nominal-registry lookup and adds no special newtype value case.

Evaluation reports uninitialized access, alias loops, invalid locations, an
impossible complete-pattern failure, malformed effect control, and captured-
control capacity exhaustion as structured internal runtime failures. They are
not source-language error outcomes.

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
