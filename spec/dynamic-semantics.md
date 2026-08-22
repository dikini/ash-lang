# Dynamic Semantics

Mini-Ash evaluation is defined by one deterministic small-step relation over
configurations `CONFIG(heap, environment, control, continuation)`. The heap is
fresh for one evaluation and maps numeric locations to tuples, completed
constructors, uninitialized recursive data slots, or aliases. Tuple elements
and constructor payloads are runtime values. The environment maps resolved term
identities to runtime values. The continuation records the remaining strict
work.

Runtime values are arbitrary-precision integers, Booleans, unit, lexical
functions, payload-constructor functions, or heap locations. A function
template becomes a lexical function with the recursive environment when its
binder is looked up. A location is an internal handle, not source-level
identity or observable mutation.

Core type abstractions and applications are static evidence. They are not
runtime values, do not extend the environment, and allocate no heap cells.

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
```

The unchanged heap and environment make erasure observable only as progress in
the machine. No source program can inspect a type parameter or type argument.

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
separate semantic fields; Mini-Ash source does not contain semicolons.

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

A polymorphic function member may have one or more outer
`TypeAbstraction` nodes around its function value. Allocation follows those
wrappers to install the same function template; ordinary evaluation still uses
`E-Type-Abstraction`. No type wrapper becomes part of a closure.

Reaching an uninitialized cell, an alias loop, or an invalid location is an
internal runtime failure. The static guardedness judgment makes those states
unreachable from accepted source. These rules provide allocation for explicit
recursive data; they do not add general laziness or source-visible mutation.

The executable test `dynamic_recursive_group_example_is_executable` exercises
mutual scope and lexical recursive closure materialization:

```ash
{
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

## Observation

Successful evaluation retains the heap with the result value. Observation
renders tuples and constructors structurally. A constructor with a tuple
payload renders its components as constructor fields. A location already on
the active rendering path renders as `<cycle>`. Removing a location from the
active path after its subtree means shared acyclic data renders in full at each
occurrence. Function values render as `<function>`.

Evaluation reports uninitialized access, alias loops, invalid locations, and an
impossible complete-pattern failure as structured internal runtime failures.
They are not source-language error outcomes.

The executable test `dynamic_cyclic_data_observation_is_finite` checks guarded
allocation and active-path rendering:

```ash
type Stream =
    Next(Int, Stream)

{
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
test. The prose derivations omit grouping erased by elaboration and use renamed
binders where needed to show distinct lexical identities.

| Case | Executable test | Principal rule sequence |
| --- | --- | --- |
| `V-003` | `dynamic_binding_derivation_example_v003_is_executable` | `E-Let-Enter`, `E-Let-Continue`, `E-Add-Values` |
| `V-001` | `dynamic_primitive_derivation_example_v001_is_executable` | `E-Add-Right`, `E-Multiply-Values`, `E-Add-Values` |
| `V-002` | `dynamic_application_derivation_example_v002_is_executable` | `E-Let-Rec-Allocate`, `E-Let-Rec-Body`, `E-Beta`, `E-Add-Values` |
| `V-004` | `dynamic_capture_derivation_example_v004_is_executable` | `E-Let-Enter`, `E-Let-Continue`, `E-Beta`, `E-Add-Values` |
| `V-008` | `dynamic_nested_application_derivation_example_v008_is_executable` | `E-Let-Rec-Allocate`, `E-Let-Rec-Body`, strict application frames, `E-Beta`, and integer primitives |

### Binding and shadowing: V-003

```ash
{
    let value = 1
    let value = value + 1
    value
}
```

Elaboration gives the two `value` binders distinct identities. The first
`E-Let-Continue` extends the environment for the second initializer.
`E-Add-Values` produces `2`, and the second continuation extends the result
environment with that integer value. Thus the file evaluates to `2`.

### Primitive precedence: V-001

```ash
1 + 2 * 3
```

Precedence produces `1 + (2 * 3)`. Because the left addition operand is already
a value, `E-Add-Right` carries the `E-Multiply-Values` step to obtain `1 + 6`.
`E-Add-Values` then produces `7`.

### Application: V-002

```ash
increment : Int -> Int
increment value = value + 1

increment 41
```

The global elaborates as a one-member recursive binding.
`E-Let-Rec-Allocate` installs its function template in the recursive
environment without allocating a data slot. The empty initialization sequence
then enters the file result through `E-Let-Rec-Body`. Looking up `increment`
materializes the closure value. `E-Beta` extends its captured environment with
the integer value `41`, and `E-Add-Values` produces `42`.

### Lexical capture: V-004

```ash
{
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

double (increment 20)
```

The two globals elaborate as one recursive group. Allocation installs both
function templates in the recursive environment; it allocates no data slots.
Strict application frames evaluate `increment 20` before applying `double`:
`E-Beta` enters `20 + 1`, then `E-Add-Values` produces `21`. The outer
`E-Beta` enters `21 * 2`, and `E-Multiply-Values` produces `42`.
