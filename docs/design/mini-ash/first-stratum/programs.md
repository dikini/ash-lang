# First-stratum programs

> These cases are informative evidence governed by
> [DN-0016](../../DN-0016-first-mini-ash-corpus.md). Their source notation and
> expected behavior are provisional and do not define current Ash.

The cases begin from the suggested function forms in
[DN-0005](../../DN-0005-surface-function-definitions.md): globals have one
explicit interface, operational and equational definitions can share callable
semantics, and local functions are ordinary values. The global forms have
different definitional strengths: equations expose pattern clauses, while an
inline operational body exposes an explicit match and ordered body structure. A
different spelling belongs in the corpus only when it answers a named concern
and records the evidence it gives up.

The [grammar](grammar.md) describes the provisional layout used below. A valid
case states the value and type that candidate components should agree on. A
rejected case states the stage and structured problem that candidates should
preserve; [diagnostics.md](diagnostics.md) defines span and rendering criteria.

## Valid programs

### V-001: precedence

```ash
1 + 2 * 3
```

The multiplication groups before addition. The program has type `Int` and
evaluates to `7`.

### V-002: one function, two definitions

The equational presentation uses one external interface and an irrefutable
equation head:

```ash
increment : Int -> Int
increment value = value + 1

increment 41
```

The inline operational presentation puts its one interface in the header:

```ash
fn increment(value : Int) -> Int {
    value + 1
}

increment 41
```

This form is likely to be familiar to people arriving from TypeScript, Rust,
C++, or Java.

Both variants have type `Int` and evaluate to `42`. Their binder-only bodies may
lower to the same or similar typed callable structure, but the corpus preserves
their definitional distinction and presentation-specific provenance for later
pattern, coverage, diagnostic, and tooling work.

### V-003: local shadowing

```ash
{
    let value = 1
    let value = value + 1
    value
}
```

The initializer of the second binding refers to the first binding. Its body
refers to the second binding. The program has type `Int` and evaluates to `2`.

### V-004: expected-typed lexical capture

```ash
{
    let offset = 40
    let add_offset : Int -> Int = fn(value) {
        value + offset
    }
    add_offset 2
}
```

The binding annotation supplies the expected function type, and the function
body resolves `offset` in its lexical environment. The program has type `Int`
and evaluates to `42`. Candidate runtime representations must model the
captured binding as inspectable Ash data rather than a Rust closure.

### V-005: concrete higher-order application

```ash
fn apply(operation : Int -> Int) -> Int {
    operation 41
}

apply (fn(value) {
    value + 1
})
```

The inline global interface supplies the operational parameter type, and the
application supplies an expected type to the anonymous argument. The program
has type `Int` and evaluates to `42`; no type scheme or generalization is
involved.

### V-006: unit result

```ash
()
```

The program has type `Unit` and evaluates to the unit value `()`.

### V-007: primitive equality

```ash
(20 + 1) == 21
```

Integer equality produces `Bool`. The program evaluates to `true`.

### V-008: mixed global presentations and nested applications

```ash
increment : Int -> Int
increment value = value + 1

fn double(value : Int) -> Int {
    value * 2
}

double (increment 20)
```

Equational and operational definitions coexist without creating two application
forms. The inner application is evaluated before the outer application. The
program has type `Int` and evaluates to `42`.

## Cross-stratum definition pressure

These cases are not candidates for the first retained semantic increment. They
add only enough pattern and match structure to expose the primary definitional
difference between equations and inline operational bodies.

### X-001: exhaustive Boolean definition

The equational definition exposes its pattern partition directly:

```ash
negate : Bool -> Bool
negate true = false
negate false = true

negate true
```

The inline operational definition writes the corresponding match explicitly:

```ash
fn negate(value : Bool) -> Bool {
    match value {
        true => false
        false => true
    }
}

negate true
```

Both programs evaluate to `false`. Pattern checking and coverage should use the
same rule boundaries. The equation group elaborates to a function with a match
body comparable to the match already present in the operational definition.

### X-002: missing Boolean case

The equational variant omits one clause:

```ash
negate : Bool -> Bool
negate true = false

negate true
```

The inline operational variant omits the corresponding match arm:

```ash
fn negate(value : Bool) -> Bool {
    match value {
        true => false
    }
}

negate true
```

Both definitions fail the shared coverage check with `false` as the missing
case. Their diagnostics point to different source structures while reporting
the same missing pattern.

### X-003: type-directed definition and application grouping

The equational pattern list follows successive arrows and produces a curried
function:

```ash
add : Int -> Int -> Int
add left right = left + right

add 20 22
```

The inline operational comma-separated parameter list is tuple syntax. It forms
one product domain, and its application supplies one tuple value:

```ash
fn add(left : Int, right : Int) -> Int {
    left + right
}

add (20, 22)
```

Both programs evaluate to `42`, but their function types and application
structure differ. The first elaborates toward nested function values; the second
elaborates toward one function over a product domain. A tuple-domain equation
would use one tuple pattern rather than reinterpret the comma list.

## Rejected parser input

### P-001: missing result expression

```ash
fn increment(value : Int) -> Int {
    value + 1
}
```

The parser reaches the end of the file after a complete definition but before
the required result expression.

### P-002: unclosed parenthesized argument

```ash
increment : Int -> Int
increment value = value + 1

increment (41
```

The parser reports the unclosed parenthesized argument at `(` and points to the
end of input as the location where `)` was expected.

### P-003: two recoverable syntax failures

```ash
fn increment(value : Int) -> Int {
    value +
}

increment (41
```

The first failure is a missing right operand. After recovering at the closing
brace, the parser reports the unclosed final argument without emitting additional
errors caused only by either missing expression.

## Rejected resolution cases

### R-001: unknown name

```ash
missing 1
```

Resolution rejects `missing` and identifies its use as the primary span.

### R-002: duplicate global definition

```ash
value : Int -> Int
value input = input

fn value(input : Int) -> Int {
    input + 1
}

value 1
```

Global names are unique in this provisional file model. Resolution points to the
second interface and labels the first definition as related context. Local
lexical bindings may shadow outer bindings, as V-003 demonstrates.

## Rejected typing cases

### T-001: global interface mismatch

```ash
answer : Int -> Bool
answer value = value

answer 42
```

The equation body has type `Int`, but the explicit global interface requires a
`Bool` result.

### T-002: invalid primitive operand

```ash
true + 1
```

Addition requires two `Int` operands. The left operand has type `Bool`.

### T-003: non-function application

```ash
41 1
```

The function position has type `Int`, not a function type.

### T-004: argument mismatch

```ash
identity : Int -> Int
identity value = value

identity true
```

The function requires an `Int` argument, but the supplied argument has type
`Bool`. The diagnostic relates the argument to the global interface's domain.

## Growth discipline

Add a case when it distinguishes a component candidate or closes an agreement
gap among the evidence documents. Do not add a construct merely to resemble a
larger language. Recursion begins the next stratum and may justify Boolean
branching or another base-case form there.
