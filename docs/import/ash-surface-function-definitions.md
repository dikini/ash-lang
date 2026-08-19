# Ash Surface Function Definitions: Initial Design Note

**Status:** Initial design direction; syntax remains provisional  
**Scope:** Surface syntax for function definitions, local functions, typing, and basic exhaustiveness  
**Out of scope:** Core serialization, guards, contracts, refinements, and dependent typing

## 1. Motivation

The Ash reboot needs a surface syntax that serves two established ways of reading functions:

- **equationally**, as a mapping specified by cases; and
- **operationally**, as a body containing explicit sequencing and control flow.

The two presentations have equivalent expressive power and elaborate to the same typed core. They are nevertheless not equally useful for explaining every function. Structural recursion and algebraic decomposition are often clearest as equations, while imperative, effectful, or control-flow-dominant code is usually clearest as an operational body.

Ash therefore intends to support both presentations deliberately. This is a surface-language choice, not a distinction in the core language or type system.

## 2. Core and surface separation

The Ash core is intended primarily as a generated, fully elaborated representation. Every core term has all required type information regardless of how its source was written. Church-style and Curry-style serializations of the same typed core are therefore equivalent choices of convenience and aesthetics.

This note concerns only the programmer-facing surface language.

## 3. Typing policy

### 3.1 Globals

Every global binding is explicitly typed, even when its type could be inferred.

This policy provides stable module interfaces, supports separate checking, makes recursion predictable, and avoids global inference becoming part of the initial reboot.

### 3.2 Locals

Local definitions may be inferred, but only to the level supported by Ash's local inference algorithm.

An expected type may flow into a local function expression:

```ash
let render : Item -> Text = fn(item) {
    item.render()
}
```

When there is no sufficient expected type, Ash may require parameter, result, or binding annotations. Local polymorphic generalization, recursive inference, constraint inference, and effect inference remain separate type-system decisions.

### 3.3 Presentation versus typing power

Church-style and Curry-style presentations do not imply different type systems. The relevant difference is where typing evidence appears:

- inline annotations place evidence in the function syntax;
- external signatures state it separately;
- local inference reconstructs omitted evidence during elaboration.

Ash can consequently use explicit global interfaces, locally inferred terms, and a fully typed elaborated core without contradiction.

## 4. Global function definitions

### 4.1 Equational form

An equational function has one external signature followed by a contiguous group of equations:

```ash
length : List<A> -> Nat

length([])        = 0
length(_ :: rest) = 1 + length(rest)
```

The signature applies to the entire clause group. Repeating types within individual clauses would defeat the concision and specification value of the form.

The left-hand side of an equation is a **definitional head**, not a call expression. Its arguments are patterns. The right-hand side is an expression.

### 4.2 Operational form

An operational function has explicit parameter binders and a body:

```ash
length : List<A> -> Nat

fn length(values) {
    match values {
        []        => 0
        _ :: rest => 1 + length(rest)
    }
}
```

An inline-typed spelling may also be useful for familiarity and for self-contained definitions:

```ash
fn length<A>(values: List<A>) -> Nat {
    match values {
        []        => 0
        _ :: rest => 1 + length(rest)
    }
}
```

Whether both external and inline typing are accepted for global operational definitions remains a surface-policy question. In all cases, the global must be explicitly typed exactly once.

### 4.3 Intended style distinction

Use equations when top-level pattern partitioning is the dominant explanation of the function:

```ash
depth : Tree<A> -> Nat

depth(Leaf(_))          = 1
depth(Node(left, right)) = 1 + max(depth(left), depth(right))
```

Use an operational body when sequencing or explicit control flow is the dominant explanation:

```ash
process_jobs : Queue<Job> -> Result<Report, Error>

fn process_jobs(queue) {
    let mut report = Report.new()

    while let Some(job) = queue.next() {
        if job.cancelled() {
            continue
        }

        let result = execute(job)?
        report.record(result)
    }

    report
}
```

Function length is not the criterion. A multiline equation may remain equational, and a small function may still use an operational body.

## 5. Elaboration and semantic equivalence

An equation group elaborates to ordinary pattern matching in an operational body. Conceptually:

```ash
length([])        = 0
length(_ :: rest) = 1 + length(rest)
```

becomes:

```ash
fn length(argument) {
    match argument {
        []        => 0
        _ :: rest => 1 + length(rest)
    }
}
```

A single equation with an irrefutable binder:

```ash
compute(input) = {
    let normalized = normalize(input)
    process(normalized)
}
```

degenerates to an operational body without a meaningful match:

```ash
fn compute(input) {
    let normalized = normalize(input)
    process(normalized)
}
```

Thus the equational form contains the ordinary one-body case. Conversely, an arbitrary operational body does not necessarily lift into useful pattern equations without restructuring, duplication, or helper functions. The styles are equally powerful but not symmetrically translatable into idiomatic forms.

Both forms normalize to the same elaborated representation. The distinction should survive only as source provenance for diagnostics and tooling.

## 6. Local and anonymous functions

Local functions are anonymous function values introduced through `let`, `let rec`, or inline expression use. Ash does not need an additional local named-function declaration form.

### 6.1 Operational anonymous function

```ash
let transform = fn(value) {
    normalize(value)
}
```

Recursive:

```ash
let rec visit = fn(node) {
    match node {
        Leaf(value)     => consume(value)
        Branch(children) => children.map(visit)
    }
}
```

Inline callback:

```ash
events.map(fn(event) {
    handle(event)
})
```

### 6.2 Equational anonymous function

The compact anonymous equational form uses `\` to mark function construction and braces to group equations:

```ash
let rec length = \ {
    []        = 0
    _ :: rest = 1 + length(rest)
}
```

Inline callback:

```ash
values.map(\ {
    None        = default
    Some(value) = transform(value)
})
```

Multiple arguments use a comma-separated pattern list:

```ash
let rec zip = \ {
    [], _                    = []
    _, []                    = []
    x :: xs, y :: ys         = (x, y) :: zip(xs, ys)
}
```

The form is directly related to global equations: remove the repeated global name and group the anonymous equations under `\ { ... }`.

The `\` marker is preferred over `_` as an anonymous head because `_` already denotes a wildcard or discarded binder. It is preferred over `fn { ... }` because `fn` suggests an operational body.

### 6.3 Destructuring

Local binding retains one uniform form:

```ash
let pattern = expression
```

Examples:

```ash
let Some(value) = result
let (left, right) = pair
let transform = fn(value) { normalize(value) }
let classify = \ {
    None        = Missing
    Some(value) = Present(value)
}
```

Because anonymous equation patterns occur on the right-hand side, they do not conflict with destructuring patterns introduced by `let`.

### 6.4 Recursion

`let rec` introduces recursive local function bindings:

```ash
let rec length = \ {
    []        = 0
    _ :: rest = 1 + length(rest)
}
```

```ash
let rec length = fn(values) {
    match values {
        []        => 0
        _ :: rest => 1 + length(rest)
    }
}
```

For an eager initial language, `let rec` should initially be restricted to function values. General recursive values require separate decisions about initialization, cyclic data, and runtime failure.

## 7. Exhaustiveness discipline

Ash should present exhaustiveness through a simple total-control-flow rule:

> Every conditional expression defines a result for every input.

### 7.1 Conditionals

Every `if` expression requires an `else`:

```ash
if condition {
    first
} else {
    second
}
```

Ash should not silently insert `Unit`, `None`, or a runtime failure for a missing branch.

### 7.2 Matches

A nontrivial `match` requires a catchall or `else` branch:

```ash
match status_code {
    200  => Success
    404  => Missing
    else => Unexpected
}
```

The catchall may be omitted when coverage is trivially established by an irrefutable pattern or by enumerating every top-level constructor of a closed algebraic type:

```ash
match optional {
    None        => default
    Some(value) => use(value)
}
```

```ash
match values {
    []        => empty
    _ :: rest => nonempty(rest)
}
```

The relevant notion is a finite, closed top-level constructor space, not a finite set of values.

Equational definitions follow the same coverage rules.

## 8. Deferred guard and contract cluster

The initial reboot does not include guards. In particular, it does not include guarded clauses such as:

```ash
classify(Value(x)) when valid(x) = Present(x)
```

The following related features are intentionally deferred:

- clause guards;
- preconditions and postconditions;
- type and value invariants;
- refinement predicates;
- type-level constraints;
- value-dependent type information;
- proof or evidence terms;
- static versus runtime contract enforcement.

These features overlap semantically and should be designed together rather than introduced as unrelated syntax. Ash is not currently committing to a fully dependently typed language.

If arbitrary runtime guards are later added, a conservative exhaustiveness rule is available: guarded clauses do not establish guaranteed coverage, so an unguarded remaining case or catchall is required. More powerful guard-aware coverage would require a deliberately restricted, decidable predicate language and is outside the initial reboot.

## 9. Tooling, diagnostics, and LLMs

Supporting both function styles adds little core semantic complexity but meaningful surface-ecosystem cost:

- form-specific diagnostics and source mapping;
- formatter and language-server support;
- navigation, rename, extraction, and documentation behavior;
- parity tests between equivalent definitions;
- style fragmentation and code-review policy;
- additional syntax for humans and language models to learn.

The forms should therefore remain syntactically distinct and must not be mixed within one global definition.

The standard library, documentation, and teaching material should use deliberate style choices. Paired, compiler-verified examples can teach the relationship between equations and explicit `match`. Project guidance may prefer equational, operational, or contextual style, but such preferences should normally be lint policy rather than language validity.

LLM-facing guidance should require:

- preserving the existing style during edits;
- selecting one style per function;
- using equations for pattern-dominant specifications;
- using operational bodies for sequencing and control-flow-dominant code;
- avoiding hybrid forms;
- converting styles only when explicitly requested.

## 10. Rejected or disfavored alternatives

### Inline types repeated on equations

```ash
fn length<A>([]: List<A>) -> Nat = 0
fn length<A>(_ :: rest: List<A>) -> Nat = 1 + length(rest)
```

This is too repetitive and obscures the case structure.

### Pattern-headed procedural declaration

```ash
fn length<A>(List<A>) -> Nat {
    []        = 0
    _ :: rest = 1 + length(rest)
}
```

This creates a special clause-body syntax even though an explicit `match` adds little noise.

### `fn` for anonymous equations

```ash
fn {
    []        => 0
    _ :: rest => 1 + length(rest)
}
```

This is recognizable as a function but conflicts with the intended operational reading of `fn`.

### `_` as anonymous equation head

```ash
{
    _ []        = 0
    _ _ :: rest = 1 + length(rest)
}
```

This overloads the wildcard symbol and creates difficult visual and grammatical ambiguity.

### Bare anonymous equation block

```ash
{
    []        = 0
    _ :: rest = 1 + length(rest)
}
```

This is compact but may be confused with an ordinary block, record, or future assignment syntax. The `\` marker communicates anonymous function construction immediately.

## 11. Open questions

The following remain unresolved:

1. How the right-hand side of an equation is delimited, especially for multiline expressions.
2. Whether clause separation is determined by layout, punctuation, braces, or some combination.
3. Whether global operational definitions support both external and inline type placement.
4. The exact amount of local function inference, including generalization, recursion, constraints, and effects.
5. The syntax and semantics of mutual local recursion.
6. Whether `else` and wildcard catchalls are both supported and, if so, whether they differ diagnostically.
7. The eventual unified design for guards, contracts, invariants, refinements, and value-dependent typing.
8. How assignment or mutation syntax interacts with definitional `=`.

## 12. Initial implementation obligations

The initial implementation should test at least:

- a valid exhaustive global equation group;
- a valid global operational equivalent;
- a valid anonymous equational function bound with `let`;
- a valid recursive anonymous equational function bound with `let rec`;
- an inline anonymous equational callback;
- local procedural functions with inferred and explicit expected types;
- rejection of an untyped global;
- rejection of a non-exhaustive constructor match;
- acceptance of complete closed-constructor enumeration;
- mandatory `else` for `if`;
- identical evaluation results for paired equational and operational definitions;
- correct source diagnostics after equation-to-match elaboration;
- rejection of mixed equational and procedural definitions for one global.

## 13. Provisional summary

The current direction is:

- The core is fully typed and independent of surface annotation style.
- Globals are always explicitly typed.
- Locals use inference only within Ash's supported limits.
- Global functions may be equational or operational.
- Equations emphasize specification by cases.
- `fn` bodies emphasize sequencing and explicit control flow.
- Anonymous functions have procedural `fn(...) { ... }` and compact equational `\ { ... }` forms.
- Local functions are anonymous values introduced through `let`, `let rec`, or inline use.
- Equational definitions elaborate to pattern matching and share its coverage rules.
- Every `if` has an `else`; nontrivial matches require a catchall, with closed-constructor enumeration as the principal exception.
- Guards and the broader contract/refinement design are intentionally deferred.
