# DN-0005: Surface Function Definitions

- ID: `DN-0005`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0002: Core Representation](DN-0002-core-representation.md), [DN-0003: Parser Architecture](DN-0003-parser-architecture.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0007: Data and Pattern Typing](DN-0007-data-and-pattern-typing.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md)

> This design note is informative and non-normative. It explores candidates; it does not define current Ash, accept surface syntax, or require any implementation. All syntax is illustrative.

## Question

Can the first coherent language offer both equational and operational presentations of functions without creating two function semantics, two typing disciplines, or ambiguous local-binding forms?

## Context and scope

Some functions read most clearly as mappings defined by cases. Others read most clearly as bodies with explicit sequencing and control flow. This note explores whether Ash should support both presentations while elaborating both to the same typed semantics.

The scope is:

- global equational and operational presentations;
- the placement of typing evidence at global and local boundaries;
- anonymous and local functions, including local recursion;
- parameter grouping and its relationship to the declared function type;
- equation-to-match elaboration and source provenance;
- surface consequences for parsing, diagnostics, formatting, and tooling.

Pattern typing, irrefutability, and coverage are explored in [DN-0007](DN-0007-data-and-pattern-typing.md). Typed elaboration targets are explored in [DN-0008](DN-0008-typed-core-and-elaboration.md). Guards, contracts, refinements, and value-dependent typing remain a connected future design cluster rather than assumptions of this note.

## Suggested design rules

### Treat the two presentations as one semantic function form

> Suggested rule: Equational and operational definitions are distinct surface presentations of the same function semantics and elaborate to the same typed representation.

An equational presentation emphasizes case partitioning:

```ash
length : List<A> -> Nat

length([])        = 0
length(_ :: rest) = 1 + length(rest)
```

Under this candidate, the left-hand side is a definitional head rather than a call expression: the name identifies the definition and its arguments are patterns. The illustrative call-like spelling would not give the head ordinary call-expression semantics.

An operational presentation emphasizes an explicit body:

```ash
length : List<A> -> Nat

fn length(values) {
    match values {
        []        => 0
        _ :: rest => 1 + length(rest)
    }
}
```

Supporting both would be a surface-language choice. Neither presentation would imply a different notion of application, polymorphism, or function type.

### Give global definitions one explicit interface

> Suggested rule: A global function has one explicit type interface, whether its body is equational or operational.

An external signature can apply to a contiguous equation group. Repeating parameter and result types on every equation would obscure the cases:

```ash
depth : Tree<A> -> Nat

depth(Leaf(_))           = 1
depth(Node(left, right)) = 1 + max(depth(left), depth(right))
```

An operational definition could use the same external form or a self-contained inline form:

```ash
fn depth<A>(tree: Tree<A>) -> Nat {
    // ...
}
```

Whether both placements are admitted remains open. The candidate policy is that a definition supplies its interface exactly once. Explicit global interfaces could support stable module boundaries, separate checking, and predictable recursion without making global inference part of the first coherent language.

### Let types determine parameter grouping

> Suggested rule: Parameter grouping follows the function type rather than an independent surface notion of arity.

An operational parameter list such as `fn(x, y) { ... }` is a candidate spelling for a function with a tuple domain, `(A, B) -> C`. Nested function expressions would express `A -> (B -> C)`.

For equations, the declared type would determine whether a pattern list decomposes one product domain or introduces successive function layers. This avoids declaring all Ash functions inherently curried or inherently n-ary.

### Make local functions ordinary values

> Suggested rule: Local functions are anonymous function values introduced by ordinary bindings, recursive bindings, or expression use; no separate local named-function declaration is required.

Operational examples:

```ash
let transform = fn(value) {
    normalize(value)
}

events.map(fn(event) {
    handle(event)
})
```

An anonymous equational candidate uses an explicit construction marker and grouped clauses:

```ash
let classify = \ {
    None        = Missing
    Some(value) = Present(value)
}
```

Multiple domain components could use a pattern list:

```ash
let rec zip = \ {
    [], _                    = []
    _, []                    = []
    x :: xs, y :: ys         = (x, y) :: zip(xs, ys)
}
```

Keeping anonymous equations on the right-hand side preserves one binding shape, `let pattern = expression`, and avoids confusing them with destructuring patterns on the left.

Expected types may flow into local function expressions:

```ash
let render : Item -> Text = fn(item) {
    item_to_text(item)
}
```

When no expected type determines enough information, annotations may be required. The amount of inference and local generalization belongs to [DN-0006](DN-0006-initial-type-system.md).

### Mark recursive local bindings explicitly

> Suggested rule: Local recursion is introduced explicitly, and the first coherent language may restrict recursive bindings to function values.

```ash
let rec visit = fn(node) {
    match node {
        Leaf(value)      => consume(value)
        Branch(children) => children.map(visit)
    }
}
```

Restricting the initial candidate to functions avoids silently deciding initialization order, cyclic-data behavior, or failure semantics for general recursive values. Mutual recursion and polymorphic recursion remain separate questions.

### Elaborate equations through ordinary matching

> Suggested rule: An equation group elaborates to an ordinary function and pattern match, with the same pattern typing and coverage rules as an explicit `match`.

Conceptually, the earlier `length` equations become a function over a generated argument followed by a match. A single irrefutable equation can omit a meaningful match:

```ash
compute(input) = {
    let normalized = normalize(input)
    process(normalized)
}
```

This can elaborate like:

```ash
fn compute(input) {
    let normalized = normalize(input)
    process(normalized)
}
```

The relationship is not intended as a source-to-source equivalence rule. An arbitrary operational body may require restructuring, duplication, or helpers before it reads naturally as equations.

### Preserve style provenance without preserving style semantics

> Suggested rule: Surface presentation survives elaboration only as nonsemantic provenance for diagnostics and source mapping; edits preserve that presentation unless conversion is explicitly requested.

A definition would not mix equations with an operational body. Retained provenance lets tools diagnose original patterns and navigate an equation group as one definition. Style guidance could recommend equations for pattern-dominant definitions and operational bodies for sequencing- or control-flow-dominant definitions without making the preference a validity rule; paired, compiler-checked examples could demonstrate their shared semantics without encouraging hybrid definitions.

## Candidate directions

### One presentation only

Choosing only operational bodies would minimize grammar and tooling surface. Choosing only equations would emphasize functional decomposition. Either choice would remove style parity costs, but each would make some functions less direct to read and teach.

### Two deliberately distinct presentations

This is the candidate developed above. It spends surface and tooling complexity to let case-dominant and control-flow-dominant functions remain visibly different while sharing semantics.

### One syntax with hybrid clause bodies

A form such as a pattern-headed procedural declaration could attempt to combine the styles:

```ash
fn length<A>(List<A>) -> Nat {
    []        = 0
    _ :: rest = 1 + length(rest)
}
```

It is compact, but creates a special clause-body grammar even though an explicit match is available and makes the boundary between the two presentations less clear.

### Anonymous-equation markers

Candidates include `\ { ... }`, `fn { ... }`, `_` as an anonymous head, or a bare clause block. The backslash candidate signals function construction without reusing the wildcard. `fn { ... }` is familiar but weakens the proposed operational reading of `fn`. A wildcard head is visually and grammatically ambiguous. A bare block can collide with ordinary blocks, records, or assignment syntax.

### Type placement for operational globals

The surface could allow only external signatures, only inline parameter/result annotations, or either spelling with exactly one interface. The choice affects parser simplicity, local visual context, documentation, and consistency with equation groups; it need not change typing power.

Repeating inline types on every equation is another candidate, but it makes the clause group noisy and weakens the value of one shared interface:

```ash
fn length<A>([]: List<A>) -> Nat = 0
fn length<A>(_ :: rest: List<A>) -> Nat = 1 + length(rest)
```

## Interactions and architectural pressure

- [DN-0003](DN-0003-parser-architecture.md) must compare equation grouping, multiline right-hand sides, clause separators, layout, and the ambiguity of `=` without selecting syntax to suit one parser framework.
- [DN-0006](DN-0006-initial-type-system.md) explores explicit global interfaces, expected-type propagation, recursion, generalization, and the distinction between tuple-domain and nested-arrow functions.
- [DN-0007](DN-0007-data-and-pattern-typing.md) supplies one pattern-typing and coverage account for both equations and explicit matches. A total-control-flow discipline is one candidate, but this note does not accept it.
- [DN-0008](DN-0008-typed-core-and-elaboration.md) explores whether both presentations can elaborate to equivalent typed Core while retaining useful provenance.
- Effects, mutation, and richer control flow are architectural pressure for keeping an operational presentation available. They are not requirements for the first coherent language.
- Guards, contracts, invariants, refinements, propositions, and proof evidence overlap in coverage and typing. Adding one guard spelling early could prejudge that cluster.
- Two presentations impose real costs on diagnostics, formatters, language servers, navigation, extraction, documentation, style guidance, and model-generated code. Those costs should be measured rather than dismissed as “only syntax.”

## Evidence and experiments

A parser-and-elaborator experiment should be limited to the cases and observations listed below and use provisional syntax only. It should be discarded unless a later decision retains its findings; it does not establish Ash grammar or semantics.

Compare the candidates with:

- an exhaustive global equation group and an operational equivalent;
- a single multiline equation whose right-hand side contains local bindings;
- tuple-domain and nested-arrow functions, including multiple equations;
- operational and equational anonymous callbacks;
- inferred, expected-typed, and annotated local functions;
- rejection of a global definition with no explicit interface under the explicit-interface candidate;
- ordinary recursive local functions and a rejected non-function recursive value;
- invalid mixed-presentation definitions;
- complete and incomplete closed-constructor matches, plus an `if` candidate with and without `else`;
- incomplete and ambiguous source that probes clause recovery and diagnostics;
- source locations preserved through equation-to-match elaboration;
- formatter, rename, navigation, and documentation prototypes over equation groups.

The comparison should record:

- whether paired definitions produce equivalent typed Core and evaluation results;
- how much form-specific parser and elaborator code each candidate needs;
- whether diagnostics point to the original clause and pattern;
- whether type-directed parameter grouping is predictable from source;
- whether anonymous equation syntax is distinguishable from blocks, records, wildcards, and assignment;
- whether one-style-per-definition can be checked without grammar accidents.

Coverage experiments belong jointly with [DN-0007](DN-0007-data-and-pattern-typing.md), and Core equivalence experiments belong jointly with [DN-0008](DN-0008-typed-core-and-elaboration.md).

## Open questions

- Does the benefit of two presentations justify their ecosystem and teaching cost?
- How are multiline equation right-hand sides and adjacent clauses delimited?
- Does layout, punctuation, braces, or a combination determine equation grouping?
- Should operational globals allow external signatures, inline signatures, or both?
- How does equation syntax expose the grouping determined by tuple domains and nested arrows?
- What anonymous-equation marker remains clear beside wildcard, block, record, and future assignment syntax?
- How does definitional `=` coexist with any future assignment or mutation syntax?
- How much local function inference is useful before annotations become preferable?
- What syntax and typing discipline should mutual local recursion use?
- Should `else` and wildcard catchalls both exist, and should they differ diagnostically?
- Can guard design wait without forcing an awkward later interaction with equations and coverage?
- Which provenance must elaboration retain for diagnostics, refactoring, formatting, and documentation?
