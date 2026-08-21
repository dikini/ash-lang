# Dynamic Semantics

Mini-Ash evaluation is defined by one deterministic small-step relation
`expression -> expression'` over elaborated semantic terms. Integer values are
arbitrary-precision mathematical integers. The other values are `true`,
`false`, `()`, and anonymous functions.

The notation `substitute(body, x, value)` means capture-avoiding substitution.
It specifies lexical binding without requiring an implementation to rewrite
syntax at runtime.

## Bindings

A binding evaluates its initializer before making the resulting value available
in its body. Its binder is not in scope in the initializer.

```sequent
family binding-steps:
  E-Let-Step :=
    initializer -> initializer'
    ===>
    let x = initializer; body -> let x = initializer'; body

  E-Let-Value :=
    ===>
    let x = value; body -> substitute(body, x, value)
```

`E-Let-Step` propagates one initializer step. `E-Let-Value` removes a completed
binding through capture-avoiding substitution. Semicolons separate semantic
fields; Mini-Ash source does not contain semicolons.

## Application

Application evaluates the function before the argument. Once both are values,
beta reduction substitutes the argument into the lexical function body.

```sequent
family application-steps:
  E-Apply-Function :=
    function -> function'
    ===>
    function argument -> function' argument

  E-Apply-Argument :=
    argument -> argument'
    ===>
    (fn(x) { body }) argument -> (fn(x) { body }) argument'

  E-Beta :=
    ===>
    (fn(x) { body }) value -> substitute(body, x, value)
```

`E-Apply-Argument` applies only when the function position is already a
function value. A closed, well-typed program cannot apply an integer, Boolean,
or unit value.

## Primitive operations

Primitive operands evaluate from left to right. Addition and multiplication
operate on mathematical integers and cannot overflow. Integer equality is
`true` exactly when its operands denote the same integer.

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

## Derived multi-step notation

The relation `expression ->* result` is the reflexive transitive closure of
`->`. It is useful for derivations but does not form a second normative
evaluation relation.

```sequent
family derived-multi-step:
  E-Multi-Refl :=
    ===>
    expression ->* expression

  E-Multi-Step :=
    expression_1 -> expression_2
    expression_2 ->* expression_3
    ===>
    expression_1 ->* expression_3
```

`E-Multi-Refl` permits zero steps. `E-Multi-Step` prefixes one normative step to
a derived sequence.

## Representative derivations

The following matrix connects each derivation to its executable specification
test. The prose derivations omit grouping erased by elaboration and use renamed
binders where needed to show distinct lexical identities.

| Case | Executable test | Principal rule sequence |
| --- | --- | --- |
| `V-003` | `dynamic_binding_derivation_example_v003_is_executable` | `E-Let-Value`, `E-Let-Step`, `E-Add-Values`, `E-Let-Value` |
| `V-001` | `dynamic_primitive_derivation_example_v001_is_executable` | `E-Add-Right`, `E-Multiply-Values`, `E-Add-Values` |
| `V-002` | `dynamic_application_derivation_example_v002_is_executable` | `E-Let-Value`, `E-Beta`, `E-Add-Values` |
| `V-004` | `dynamic_capture_derivation_example_v004_is_executable` | `E-Let-Value`, `E-Let-Value`, `E-Beta`, `E-Add-Values` |
| `V-008` | `dynamic_nested_application_derivation_example_v008_is_executable` | two `E-Let-Value` steps, `E-Apply-Argument` with `E-Beta`, `E-Apply-Argument` with `E-Add-Values`, `E-Beta`, `E-Multiply-Values` |

### Binding and shadowing: V-003

```ash
{
    let value = 1
    let value = value + 1
    value
}
```

Elaboration gives the two `value` binders distinct identities. The first
`E-Let-Value` substitutes `1` into the second initializer. `E-Let-Step` uses
`E-Add-Values` to reduce that initializer from `1 + 1` to `2`. The final
`E-Let-Value` substitutes `2` into the result. Thus the file reduces to `2`.

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

The global elaborates to a binding of `increment` to a function value.
`E-Let-Value` substitutes that function into the file result, `E-Beta`
substitutes `41` for its parameter, and `E-Add-Values` reduces `41 + 1` to
`42`.

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

The first `E-Let-Value` substitutes `40` into the function body without
capturing its parameter. The second substitutes the resulting function value
for `add_offset`. `E-Beta` then substitutes `2` for the parameter, and
`E-Add-Values` reduces `2 + 40` to `42`. This is lexical rather than dynamic
scope.

### Nested application: V-008

```ash
increment : Int -> Int
increment value = value + 1

fn double(value : Int) -> Int {
    value * 2
}

double (increment 20)
```

The two global bindings first substitute their function values into the result.
The outer function is already a value, so `E-Apply-Argument` reduces
`increment 20` first: `E-Beta` exposes `20 + 1`, then `E-Add-Values` produces
`21`. The outer `E-Beta` exposes `21 * 2`, and `E-Multiply-Values` produces
`42`.
