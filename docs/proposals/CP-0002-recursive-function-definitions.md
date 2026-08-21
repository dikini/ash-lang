# CP-0002: Recursive Function Definitions

- ID: `CP-0002`
- Status: accepted
- Related: [AD-0004: Small-Step Semantic Method](../decisions/AD-0004-small-step-semantic-method.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0005: Surface Function Definitions](../design/DN-0005-surface-function-definitions.md), [DN-0006: Initial Type System](../design/DN-0006-initial-type-system.md), [DN-0007: Data and Pattern Typing](../design/DN-0007-data-and-pattern-typing.md), [DN-0008: Typed Core and Elaboration](../design/DN-0008-typed-core-and-elaboration.md), [DN-0015: Mini-Ash Phase](../design/DN-0015-mini-ash-phase.md), [DN-0019: Primitive Feature Composition](../design/DN-0019-primitive-feature-composition.md), [TASK-0008: Implement Recursive Function Definitions](../tasks/TASK-0008-implement-recursive-function-definitions.md)

> This proposal is not current Ash. Its accepted status authorizes an
> implementation task; the specification remains authoritative until the
> implementation, tests, and specification update merge together.

## Current behavior

Global definitions and local bindings are sequential and nonrecursive. A
global body cannot refer to its own definition or a later global. A local
initializer cannot refer to its own binder or to a later local binding.

Mini-Ash has monomorphic structural function types and requires an explicit
interface for every global function. A local annotation can supply the expected
function type needed to check an anonymous function. Core represents functions
and nonrecursive bindings, and the explicit evaluator creates lexical closures
when it enters function values.

## Proposed behavior

Mini-Ash admits recursive functions through two scope forms:

- every global function in a file is visible in every global body and in the
  file result, so self recursion, mutual recursion, and forward references need
  no additional global marker;
- a local recursive group uses `let rec` for its first member and `and` for
  each additional member.

Every local recursive member requires a type annotation and a direct anonymous
function initializer. The whole group enters scope before any initializer is
resolved or checked. The members therefore see themselves and one another,
and all group members remain visible in the following block remainder.

An ordinary local `let` remains sequential and nonrecursive. An occurrence in
its initializer still uses the incoming scope rather than the binder being
defined.

### Surface grammar

The grammar adds `rec` and `and` as reserved words. It admits an arbitrary
expression after `=` so the front end can issue an initialization-specific
diagnostic for a well-formed non-function initializer. Static semantics then
requires that expression to be a direct `function_expression`.

```ebnf
block ::= "{" line_end { local_declaration line_end } expression [ line_end ] "}" ;
local_declaration ::= local_binding | recursive_binding_group ;
local_binding ::= "let" identifier [ ":" type ] "=" expression ;
recursive_binding_group ::=
  "let" "rec" recursive_member
  { line_end "and" recursive_member } ;
recursive_member ::= identifier ":" type "=" expression ;
```

All other grammar remains unchanged. A recursive group is one local
declaration even when it occupies several logical lines. `and` outside a
recursive group is not a declaration. A missing member after `and`, a missing
annotation, and a missing initializer each have an owned recovery path that
synchronizes at the next logical declaration or enclosing block boundary.

This example defines a local mutually recursive group. It terminates without a
conditional because the backward reference occurs in an unused closure:

```ash
{
    let rec first : Unit -> Int = fn(ignored) {
        second ()
    }
    and second : Unit -> Int = fn(ignored) {
        let remember : Unit -> Int = fn(value) {
            first value
        }
        42
    }
    first ()
}
```

### Name resolution

Resolution allocates every global binder and checks global-name freshness
before resolving any global body. It installs the complete global scope for
all bodies and the file result. The two names of an equational global must
still agree, and both surface presentations still define exactly one global.

For a local recursive group, resolution allocates every member identity and
checks freshness within the group before resolving any initializer. It then
resolves all initializers in the incoming scope extended by every group member.
That extended scope also applies to the following block remainder. A local
recursive member may shadow an outer binder, but two members of one group may
not use the same spelling.

Forward references are available only between file globals and between members
of one explicit local recursive group. They do not make later ordinary local
bindings visible early.

### Recursive initialization safety

Recursive initialization has a separate static judgment from expression
typing. In this increment, only a direct anonymous function is safe because
creating it delays access to recursive names until application. A block that
computes a function, an alias to a function, and every non-function expression
are unsafe recursive initializers even when their type is a function type.

An unsafe initializer is rejected with `recursion.unsafe-initializer`. The
diagnostic identifies the complete initializer as primary, relates it to the
recursive group and declared type, and explains that a recursive member must
be initialized directly with `fn`.

This rule does not introduce implicit thunking, memoization, black-hole
detection, initialization order, or observable laziness. A later algebraic-data
proposal may extend the safety judgment to constructor-guarded values and add
the allocation semantics needed for cyclic structures. That later work must
not reinterpret this proposal as accepting general recursive values.

### Static semantics

Recursive definitions reuse the existing monomorphic type algebra and
bidirectional expression judgments. Let `GAMMA_R` be the finite mapping from
every recursive group member to its declared monotype. All annotations are
available before any member body is checked.

The rules below require the initialization-safety judgment `safe_rec` and then
check each direct function against its declared type. They extend the ordinary
environment for the remainder without creating inference variables,
generalization, polymorphic recursion, recursive types, or a new type form.

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

Here each `initializer_i` is the direct anonymous function assigned to `x_i`.
The semicolon separates the recursive declaration from the semantic remainder;
it is not Ash source punctuation.

Every global already has an explicit monomorphic function type. Let
`GAMMA_G` map all file globals to those declared types. Each definition checks
in `GAMMA_G`, and the file result synthesizes in the same environment.

```sequent
family recursive-global-typing:
  T-Recursive-Program :=
    GAMMA_G = { name_i : definition_type_i | 1 <= i <= n }
    for each i, GAMMA_G |-definition definition_i ⇒ name_i : definition_type_i
    GAMMA_G |- result ⇒ result_type
    ===>
    |-program definitions; result ⇒ result_type
```

This replaces sequential global typing. The existing presentation-specific
definition rules continue to check each parameter and body after the complete
global environment has been established.

### Typed elaboration and validation

Global definitions and local recursive groups elaborate through one recursive
Core computation form. A recursive binding contains a nonempty ordered set of
typed binders and ordinary typed function nodes followed by one body node.
Both global presentations continue to converge on the existing function
representation and retain their presentation-specific provenance.

Recursive references are ordinary stable binder occurrences. They do not form
ownership edges between Core nodes, so the arena graph remains acyclic. The
recursive binding form is the only new pure Core node family needed by this
increment.

The independent Core validator checks:

- a recursive group is nonempty and defines every binder exactly once;
- every initializer is an admitted function node whose type equals its binder
  type;
- all group binders are in scope in every initializer and in the body;
- outer binders retain ordinary lexical scope;
- child handles, node types, dialect membership, and provenance are valid;
- recursive binder occurrences do not weaken the existing acyclic Core-graph
  invariant.

Traversal and transformation APIs must visit every initializer and the body
without allocating an incidental child collection at each node. Identity and
local transforms must preserve or rebuild the recursive group and pass
independent validation.

### Dynamic semantics

The small-step account uses a recursive closure value
`rec_closure(group, i)`. It denotes member `i` of `group` together with all
members needed to resolve recursive references. This is specification notation,
not a second surface value or an observable closure identity.

Entering a recursive binding substitutes the corresponding recursive closure
for every group binder in the remainder. Applying one substitutes both the
argument and all recursive closures into the selected member body.

```sequent
family recursive-binding-steps:
  E-Let-Rec :=
    closures = { x_i := rec_closure(group, i) | 1 <= i <= n }
    ===>
    let rec group; body -> substitute_many(body, closures)

  E-Rec-Apply-Argument :=
    argument -> argument'
    ===>
    rec_closure(group, i) argument -> rec_closure(group, i) argument'

  E-Rec-Beta :=
    closures = { x_j := rec_closure(group, j) | 1 <= j <= n }
    body_i' = substitute(body_i, parameter_i, value)
    ===>
    rec_closure(group, i) value -> substitute_many(body_i', closures)
```

The ordinary application rule still evaluates the function position first.
`E-Rec-Apply-Argument` supplies its strict argument step after the function
position is a recursive closure value. Capture-avoiding substitution keeps
recursive and parameter binders distinct.

The retained evaluator implements these rules with one explicit recursive
environment frame. The frame stores inspectable function templates and its
lexical parent; it does not store closures that point back to the same frame.
Looking up a group member materializes a closure rooted at that definition
frame. This preserves lexical scope, avoids dynamic-scope capture from the
caller, and does not introduce Rust closures or an owning reference cycle.

Machine transitions remain first-order control data. Ordinary recursion does
not capture, expose, or type a continuation and does not add effect machinery.

## Semantic delta

Global function scope changes from sequential to file-wide. Local blocks gain
explicit recursive groups whose annotated direct-function members have
simultaneous scope. Recursive calls evaluate through lexical recursive closures.
Ordinary local bindings and all existing expression, function, primitive, and
evaluation-order rules remain unchanged.

## Affected specification areas

Implementation changes:

- [Syntax](../../spec/syntax.md#grammar) for `let rec` groups and reserved
  words;
- [Name Resolution](../../spec/name-resolution.md) for file-wide global scope
  and simultaneous local recursive scope;
- [Static Semantics](../../spec/static-semantics.md) for initialization safety
  and monomorphic recursive checking;
- [Elaboration](../../spec/elaboration.md) for recursive Core lowering and
  provenance;
- [Dynamic Semantics](../../spec/dynamic-semantics.md) for recursive closures
  and application steps.

Executable examples and tool diagnostics change with the implementation.

## Resulting specification truth

After implementation, tests, documentation, and specification changes merge:

- every global function may refer to itself and any other global in its file;
- `let rec ... and ...` introduces one simultaneous local recursive group;
- every local recursive member has a declared monotype and a direct anonymous
  function initializer;
- recursive definitions use the existing monomorphic type forms and expression
  typing rules;
- recursive calls preserve lexical scope and strict argument evaluation;
- ordinary `let` remains sequential and nonrecursive;
- cyclic data and general recursive values remain unavailable.

## Interactions

- AD-0004 governs the primary small-step account.
- AD-0005 requires grammar-local parsing, token-complete recovery, and a hard
  projection boundary before semantic stages.
- AD-0006 requires stable binder identities, explicit scope operations,
  bidirectional checking, and structured diagnostic causes.
- AD-0007 requires a closed typed Core dialect, independent validation,
  exhaustive consumers, and retained transform evidence.
- AD-0008 requires an explicit first-order evaluator and host-stack-independent
  recursion depth.
- DN-0005 and DN-0006 support explicit local recursion and monomorphic checking
  against declared types. This proposal resolves those questions only for the
  current monomorphic function subset.
- DN-0007 owns later constructor and cyclic-data pressure. Constructor guarding
  can extend initialization safety only with an accepted data proposal.
- [DN-0009](../design/DN-0009-effects-handlers-and-continuations.md)'s effect
  handlers and continuation kinds do not change ordinary recursive function
  semantics. Future handler work must decide captured continuation
  representation separately.
- DN-0019's Float experiment suggests measuring cross-stage representation
  joins and compiler-directed maintenance discovery. Its feature packaging,
  compile-time switches, and CLI admission machinery do not transfer to this
  increment.

## Non-goals

This proposal does not add:

- general recursive values, implicit laziness, thunks, memoization, black-hole
  detection, initialization effects, or constructor backpatching;
- algebraic data, constructors, cyclic structures, patterns, matches, or
  coverage;
- type inference variables, recursive type equations, polymorphic recursion,
  generalization, universals, higher-kinded types, interfaces, or modules;
- effects, handlers, continuations, CPS conversion, mutation, resources, or
  concurrency;
- arbitrary forward references between ordinary local declarations;
- a user-facing recursion limit or a second evaluator;
- feature flags, compiler-extension registration, or separate distribution.

## Required evidence

The implementation task must land code, tests, the normative specification,
and executable documentation together. It must provide:

- parser and projection tests for one- and multi-member groups, exact spans,
  reserved words, missing annotations and initializers, missing members after
  `and`, stray `and`, balanced recovery, and rejection of recovery nodes at
  projection;
- resolver tests for global self recursion, mutual recursion, forward
  references, local simultaneous scope, outer capture, shadowing, duplicate
  group members, ordinary nonrecursive `let`, binder identities, and scope
  restoration after failure;
- typing tests for explicitly annotated monomorphic groups, mutual calls,
  argument and result failures, unsafe recursive initializers, and absence of
  new type forms or inference behavior;
- Core validation rejection of empty groups, duplicate binders, non-function
  initializers, binder/type disagreement, invalid scope, foreign handles,
  invalid provenance, and cyclic ownership edges;
- identity and local-transform evidence covering recursive groups;
- evaluator tests for self and mutual calls, forward references, lexical
  capture rather than caller capture, strict argument order, inspectable
  closures, shared recursive environments, and iterative destruction without
  owning cycles;
- deep valid recursive groups and call chains on a deliberately small Rust
  stack, with explicit machine growth rather than proportional host-stack
  growth;
- paired equational and inline-operational global recursion with distinct
  origins and common recursive Core behavior;
- structural diagnostics and rendered CLI evidence for every new parse,
  resolution, initialization, and typing failure;
- source-provenance tests for group, member, annotation, function, parameter,
  body, recursive occurrence, and generated lowering causes;
- exact library and CLI observations for representative recursive programs,
  including a program that prints `42 : Int`;
- executable tests for every new specification example and documented
  diagnostic;
- a changed-site and maintenance-discovery report comparing this structurally
  different cross-stage feature with the transferable DN-0019 findings;
- Markdown, link, authority, and formal-notation review plus
  `cargo xtask verify`.

If implementation reveals a required change to surface scope, initialization
safety, typing, dynamic semantics, or observable diagnostics, work returns to
this proposal before proceeding.
