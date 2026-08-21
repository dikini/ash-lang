# CP-0001: First Mini-Ash Nucleus

- ID: `CP-0001`
- Status: accepted
- Related: [TASK-0006: Implement the First Mini-Ash Nucleus](../tasks/TASK-0006-implement-first-mini-ash-nucleus.md), [AD-0004: Small-Step Semantic Method](../decisions/AD-0004-small-step-semantic-method.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0016: First Mini-Ash Corpus Stratum](../design/DN-0016-first-mini-ash-corpus.md)

> This proposal is not current Ash.

## Current behavior

The canonical specification states that Ash has no executable language,
compiler, runtime, syntax, static semantics, or dynamic semantics.

## Proposed behavior

This proposal introduces the first retained Mini-Ash language increment: a
single-file, monomorphic, pure-functional nucleus with primitive values,
immutable bindings, first-class unary functions, and strict application.

The proposal adopts the behavior exercised by `V-001` through `V-008` in
[DN-0016's evidence package](../design/mini-ash/first-stratum/programs.md).
Those cases become required evidence only through this proposal. The
`X-NNN` cases remain informative future pressure.

### Source files and lexical structure

A source file is UTF-8 text. Identifiers and reserved words use the ASCII forms
defined by the grammar below. Comments, escapes, Unicode identifiers, and a byte
order mark are not accepted in this increment.

Spaces and horizontal tabs separate tokens where needed. The lexer recognizes
LF and CRLF as line-break sequences; bare CR is invalid. Each sequence has its
exact one-byte or two-byte source span and counts as one line break. Delimiters
establish lexical line-break contexts. At file level and inside the nearest
enclosing block, a line-break sequence produces one logical line boundary.
Inside a parenthesized expression, type, or parameter list, it is whitespace
rather than a boundary. Entering a braced block establishes a block context
even when the block occurs inside outer parentheses; its internal line breaks
are therefore boundaries. Leaving the block restores the surrounding
parenthesized context. Blank logical lines are ignored.

An unparenthesized infix expression occupies one logical line. A binding
initializer or equation body may extend through balanced parentheses or through
a complete nested block or function body. This rule does not use indentation or
implicit continuation after an operator.

### Surface grammar

The grammar deliberately excludes the provisional corpus's Boolean patterns,
matches, tuples, product types, and multiple-parameter forms. A program contains
sequential global definitions followed by one result expression. Application
binds more tightly than multiplication, multiplication more tightly than
addition, and addition more tightly than non-associative equality. Function
arrows associate to the right. Juxtaposed application, multiplication, and
addition each associate to the left.

```ebnf
program ::= { global_definition line_end } expression [ line_end ] ;

global_definition ::= equational_global | inline_operational_global ;
equational_global ::= external_interface line_end equation ;
external_interface ::= identifier ":" type ;
equation ::= identifier binder "=" expression ;
inline_operational_global ::=
  "fn" identifier "(" typed_binder ")" "->" type block ;

block ::= "{" line_end { local_binding line_end } expression [ line_end ] "}" ;
local_binding ::= "let" identifier [ ":" type ] "=" expression ;
function_expression ::= "fn" "(" binder ")" block ;

expression ::= block | function_expression | equality_expression ;
equality_expression ::= additive_expression [ "==" additive_expression ] ;
additive_expression ::= multiplicative_expression { "+" multiplicative_expression } ;
multiplicative_expression ::=
  application_expression { "*" application_expression } ;
application_expression ::= primary_expression { primary_expression } ;
primary_expression ::=
  integer
  | boolean
  | unit
  | identifier
  | parenthesized_expression ;
parenthesized_expression ::= "(" expression ")" ;

binder ::= identifier ;
typed_binder ::= identifier ":" type ;
type ::= atomic_type [ "->" type ] ;
atomic_type ::= "Int" | "Bool" | "Unit" | parenthesized_type ;
parenthesized_type ::= "(" type ")" ;

identifier ::= /[a-z_][a-zA-Z0-9_]*/ ;
integer ::= /0|[1-9][0-9]*/ ;
boolean ::= "true" | "false" ;
unit ::= "(" ")" ;
line_end ::= /logical-newline-in-file-or-block-context/ ;
```

The reserved words are `fn`, `let`, `Int`, `Bool`, `Unit`,
`true`, and `false`. Parentheses group expressions and types without
introducing a semantic node after surface elaboration. Juxtaposition associates
to the left, so `f a b` parses as `(f a) b`. The grammar admits only one
equational binder and one operational or anonymous parameter in this increment.

An inline operational global places its interface in its header:

```ash
fn increment(value : Int) -> Int {
    value + 1
}
```

An equational global places one interface before one binder-only equation:

```ash
increment : Int -> Int
increment value = value + 1
```

The two spellings have distinct source structure and provenance. Their
binder-only bodies may elaborate to the same typed function structure.

### Name resolution

Resolution assigns a stable binder identity to every definition and occurrence
before typechecking.

Global definitions are sequential and nonrecursive. A global initializer may
refer to earlier globals, but not to itself or a later global. A global binder
enters scope only after its complete definition. Defining a second global with
the same spelling is an error.

Local bindings are sequential and nonrecursive. The initializer is resolved in
the incoming scope; the new binder is visible only in the remainder of the
block. A local binding may shadow an earlier local or global binder.

The names in an equational interface and its equation must agree. Function
parameters are visible only in their function body and may shadow an outer
binder. Every occurrence must resolve to exactly one binder.

### Types and static semantics

The type algebra contains exactly `Int`, `Bool`, `Unit`, and
`Function(domain, codomain)`. The surface arrow denotes
`Function` and associates to the right. Types are equal exactly when their
structures are equal.

The judgments `GAMMA |- expression ⇒ tau` and
`GAMMA |- expression ⇐ tau` respectively synthesize and check a type.
`GAMMA` maps resolved binder identities to monotypes. Integer, Boolean,
unit, and resolved-variable expressions synthesize their types. An expression
that synthesizes a structurally equal type also checks against the expected
type.

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
    x : tau in GAMMA
    ===>
    GAMMA |- x ⇒ tau

  T-Check-Inferred :=
    GAMMA |- expression ⇒ tau_1
    tau_1 = tau_2
    ===>
    GAMMA |- expression ⇐ tau_2
```

Here `n` ranges over integer literals, `b` over Boolean literals,
and `x` over resolved occurrences. The equality premise is structural type
equality, not a host-language equality shortcut.

An anonymous function checks only against an expected function type. Its
parameter receives the expected domain while its body checks against the
expected codomain. Application first synthesizes a function type, then checks
the argument against its domain.

```sequent
family function-typing:
  T-Function-Check :=
    GAMMA, x : domain |- body ⇐ codomain
    ===>
    GAMMA |- fn(x) { body } ⇐ Function(domain, codomain)

  T-Apply :=
    GAMMA |- function ⇒ Function(domain, codomain)
    GAMMA |- argument ⇐ domain
    ===>
    GAMMA |- function argument ⇒ codomain
```

An anonymous function in synthesis position is rejected with a structured
missing-expected-type reason. This increment does not infer a fresh parameter
type or add parameter annotations to anonymous functions.

A block is typed from left to right. An annotated initializer checks against its
annotation. An unannotated initializer must synthesize a type. In either case,
the new binder has that type only in the remaining bindings and result. A block
can synthesize from its result or check by passing an expected type to its
result.

```sequent
family block-typing:
  T-Block-Result :=
    GAMMA |- result ⇒ result_type
    ===>
    GAMMA |- { result } ⇒ result_type

  T-Block-Let-Inferred :=
    GAMMA |- initializer ⇒ binding_type
    GAMMA, x : binding_type |- { remainder } ⇒ result_type
    ===>
    GAMMA |- { let x = initializer; remainder } ⇒ result_type

  T-Block-Let-Checked :=
    GAMMA |- initializer ⇐ binding_type
    GAMMA, x : binding_type |- { remainder } ⇒ result_type
    ===>
    GAMMA |- { let x : binding_type = initializer; remainder } ⇒ result_type

  T-Block-Check-Result :=
    GAMMA |- result ⇐ expected_type
    ===>
    GAMMA |- { result } ⇐ expected_type

  T-Block-Check-Let-Inferred :=
    GAMMA |- initializer ⇒ binding_type
    GAMMA, x : binding_type |- { remainder } ⇐ expected_type
    ===>
    GAMMA |- { let x = initializer; remainder } ⇐ expected_type

  T-Block-Check-Let-Annotated :=
    GAMMA |- initializer ⇐ binding_type
    GAMMA, x : binding_type |- { remainder } ⇐ expected_type
    ===>
    GAMMA |- { let x : binding_type = initializer; remainder } ⇐ expected_type
```

The first three rules synthesize a block type. The last three rules check a
block, carrying the expected type through its bindings to the result. The
checking rules overlap with `T-Check-Inferred` when the result synthesizes, but
also admit a result that itself needs an expected type, such as an anonymous
function. The semicolons in these block judgments separate semantic fields.
They do not add semicolons to the surface language.

Addition and multiplication require two `Int` operands and synthesize
`Int`. Equality in this increment compares only integers and synthesizes
`Bool`.

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

An equational global whose interface is
`Function(domain, codomain)` checks its equation binder at `domain`
and its body at `codomain`. An inline operational global derives the
same function type from its parameter and result annotations and checks its body
the same way. Both add the resulting global binder only to the following source.
The final program expression synthesizes the program type.

The definition judgment returns the type contributed to the following program
scope. The program judgment checks one definition in the incoming scope before
checking the remainder with the new global binder. The final rule synthesizes
the file's type from its result expression.

```sequent
family global-and-program-typing:
  T-Equational-Global :=
    GAMMA, parameter : domain |- body ⇐ codomain
    ===>
    GAMMA |-definition name : Function(domain, codomain); name parameter = body ⇒ name : Function(domain, codomain)

  T-Operational-Global :=
    GAMMA, parameter : domain |- body ⇐ codomain
    ===>
    GAMMA |-definition fn name(parameter : domain) -> codomain { body } ⇒ name : Function(domain, codomain)

  T-Program-Definition :=
    GAMMA |-definition definition ⇒ name : definition_type
    GAMMA, name : definition_type |-program remainder ⇒ result_type
    ===>
    GAMMA |-program definition; remainder ⇒ result_type

  T-Program-Result :=
    GAMMA |- result ⇒ result_type
    ===>
    GAMMA |-program result ⇒ result_type
```

The semicolon in the equational and program judgments separates semantic
fields; it is not surface punctuation. Resolution has already ensured that
`name` is fresh at file scope and that an equational interface and
equation agree. An equational interface that does not expose one function
domain and codomain has no applicable definition rule and produces a structured
interface-shape error.

This increment has no inference variables, generalization, polymorphism,
unification solver, overloading, subtyping, implicit conversion, or recursive
typing environment.

### Typed elaboration and validation

Typed elaboration produces one named pure structured-Core dialect assembled
from feature-local families for literals, variables, functions, bindings,
applications, and primitive operations. Every binder and expression node
exposes its structural type and causal source provenance.

Both global presentations elaborate to typed function values for this
binder-only increment. Whole-program elaboration turns sequential globals into
nested nonrecursive bindings around the result. Block bindings use the same
semantic binding structure. Presentation provenance records whether a function
came from an equation or an inline operational body.

The pure computation boundary has no inhabitable effect operations. No
placeholder `Impure` form, handler, effect continuation, or CPS region exists.

An independent validator checks:

- binder scope and binder-use identity;
- every node and binder type;
- application domain agreement;
- primitive operand and result types;
- membership in the selected Core dialect;
- required causal source provenance.

Only validated Core may reach evaluation. A validator failure is an internal
compiler failure rather than a source-language type error.

### Dynamic semantics

The normative relation `expression -> expression'` takes one deterministic
small step over the elaborated semantic terms. Values are arbitrary-precision
integer literals, Boolean literals, `()`, and anonymous function values.
Capture-avoiding substitution is the specification device for lexical binding;
it does not require the evaluator to rewrite syntax at runtime.

Bindings evaluate their initializer before substituting the value into the
body.

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

In these rules `value` ranges only over the value forms named above. The
binder `x` is not in scope in `initializer`.

Application evaluates the function first and the argument second. Once both are
values, beta reduction substitutes the argument into the lexical function body.

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

The second rule applies only after the function position is a function value.
A closed, well-typed, validated program cannot apply another value kind.

Primitive operations evaluate their operands from left to right. Addition and
multiplication produce mathematical integers and cannot overflow. Equality
returns `true` exactly when its integer operands are equal.

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

Here `n`, `n_1`, `n_2`, and `n_3` range over
integer values, while `b` ranges over Boolean values. The
zero-or-more-step relation is the reflexive transitive closure of the one-step
relation; it is derived notation rather than a second normative semantic
account.

The retained evaluator implements these rules with AD-0008's explicit
first-order control loop, typed frame data, and inspectable closures and
environments. The evaluator does not define semantics independently from these
rules.

### Executable behavior

The retained executable accepts exactly one source-file path:

```text
ash <source-file>
```

It reads one UTF-8 file and runs the complete parse, projection, resolution,
typed-elaboration, validation, and evaluation pipeline.

Success writes one line to standard output and exits with status zero:

```text
value : Type
```

Integers, Booleans, and unit use their source spellings. A function result uses
`<function> : domain -> codomain`. Functions remain inspectable internal
data; the display does not expose their captured environment or make function
identity observable in the language. Type output uses right-associated arrows
and parenthesizes a function-valued domain, so every structural function type
has one rendering.

Source, input, or internal failures write a diagnostic to standard error, write
no success value, and exit nonzero. Host panics, Rust stack overflow, and
unchecked representation failures are not Ash behavior.

### Diagnostics

Diagnostics are structured before rendering. Each contains a semantic category,
a primary source label, zero or more related source labels, expected and found
forms where relevant, causal context, and help only when the correction follows
from established facts.

The implementation adopts the behavior of `P-001` through `P-003`,
`R-001` through `R-002`, and `T-001` through `T-004`.
It also reports a specific typing reason when an anonymous function occurs
without an expected type. Exact colors, gutters, punctuation, and prose are
renderer behavior rather than language semantics.

The parser cases require these structured reasons and recovery outcomes:

| Case | Reason | Primary location | Required context |
| --- | --- | --- | --- |
| `P-001` | `parse.expected-result` | End of input | Any preceding global is complete; the file still requires a result expression. |
| `P-002` | `parse.unclosed-group` | Opening `(` | End of input is where `)` was required. |
| `P-003` | `parse.expected-operand`, then `parse.unclosed-group` | `+`, then the later opening `(` | Recovery stops at the operational body's closing brace and does not emit errors derived only from the first missing expression. |

The semantic cases require these structured reasons and causal relationships:

| Case | Reason | Primary fact | Related fact |
| --- | --- | --- | --- |
| `R-001` | `resolve.unknown-name` | Unresolved occurrence | A suggestion only when an in-scope spelling justifies it |
| `R-002` | `resolve.duplicate-global` | Second global name | First global name and definition |
| Equation name disagreement | `resolve.equation-name-mismatch` | Name in the equation head | Name in the external interface |
| `T-001` | `type.definition-result` | Equation body type | Required result type in its interface |
| `T-002` | `type.operator-operand` | Incorrect operand type | Primitive operator and required `Int` type |
| `T-003` | `type.not-applicable` | Non-function in function position | Whole application when useful |
| `T-004` | `type.argument` | Argument type | Function domain and its causal annotation |
| Non-function equational interface | `type.equation-interface-not-function` | Type in the external interface | Equation head that requires one function domain |
| Annotated binding initializer | `type.binding-initializer` | Initializer expression | Binding annotation that supplies the expected type |
| Anonymous function without context | `type.function-needs-context` | Anonymous function | Nearest position that required synthesis |

Internal validator tests use distinct scope, node-type, application-type, and
provenance reasons for `I-001` through `I-004`. These identify a
compiler invariant failure and do not report a source error category.

Parser recovery may retain missing and error nodes in the concrete syntax
representation. Projection fails while any such node remains. Later semantic
stages do not run on recovered placeholders. Resolution, typing, and validation
stop evaluation when they report a failure.

Diagnostics should combine Elm-style focused explanation with Rust-style
primary and related labels. Structural tests assert the category, source spans,
expected and found information, causal relationship, and cascade behavior
independently from rendered snapshots.

## Semantic delta

Current Ash has no language behavior. After this change, Ash accepts exactly the
single-file language described above, rejects programs outside that language,
assigns types through the stated monomorphic bidirectional rules, evaluates
accepted programs through the stated deterministic small-step rules, and
provides one executable observation of the final type and value.

## Affected specification areas

Implementation changes the
[Current Ash](../../spec/README.md#current-ash) statement and adds separate
normative specification documents for:

- lexical structure and logical line boundaries;
- surface grammar and precedence;
- scope and name resolution;
- types and static semantics;
- typed presentation elaboration;
- values and small-step dynamic semantics.

Executable invocation, output, diagnostics, and exit behavior are documented as
tool behavior derived from the implemented pipeline, not as additional language
semantics.

## Resulting specification truth

After implementation, tests, executable documentation, and specification
changes merge together:

- Ash is a single-file monomorphic pure-functional language with the exact
  forms in this proposal.
- Every accepted file has one result expression and one synthesized program
  type.
- Name resolution is lexical, sequential, and nonrecursive.
- Functions are unary, first class, lexical, and strict in their arguments.
- The two global function presentations share binder-only callable semantics
  while retaining different source provenance.
- `Int` is arbitrary precision for the accepted non-negative literals and
  operations.
- Evaluation is deterministic and strict in the stated left-to-right order.
- The `ash` executable reports the final value and type or a structured
  failure.

## Interactions

- AD-0004 governs the normative small-step presentation.
- AD-0005 governs the parser and recovery boundaries without changing this
  grammar.
- AD-0006 governs resolution, bidirectional typed elaboration, and structured
  semantic failures.
- AD-0007 governs typed Core dialect assembly, validation, and the uninhabited
  effect-operation boundary.
- AD-0008 governs the retained evaluator machine without becoming semantic
  authority.
- Equational and inline operational globals preserve the distinction explored
  by [DN-0005](../design/DN-0005-surface-function-definitions.md). General
  patterns and explicit matches remain later work.
- The external railroad and sequent renderers need the conformance work already
  recorded by AD-0003. Their state does not change the canonical Markdown.

## Non-goals

This proposal does not include:

- recursion, forward references, mutually recursive globals, or modules;
- products, tuples, records, algebraic data, constructor patterns, general
  patterns, matches, or coverage;
- multiple function parameters or curried multi-binder equations;
- polymorphism, kinds beyond `Type`, inference variables,
  generalization, a constraint solver, type classes, interfaces, or evidence
  passing;
- negative literals, subtraction, division, integer narrowing, machine integer
  overflow, or overloaded equality;
- effects, handlers, continuation capture, CPS, concurrency, cancellation,
  mutation, I/O, or resource protocols;
- comments, Unicode identifiers, indentation syntax, implicit operator-line
  continuation, semicolons, or formatter behavior;
- a parser library, concrete syntax-tree library, diagnostic-rendering library,
  Core storage scheme, provenance storage scheme, or frame-composition
  mechanism;
- a REPL, stdin programs, package or module discovery, compilation artifacts,
  optimization, or backend code generation.

## Required evidence

An accepted implementation task must land the implementation, tests,
specification, and executable documentation together. It must provide:

- positive end-to-end tests for every `V-001` through `V-008`
  presentation, with exact type, value, standard output, and success status;
- an end-to-end function-valued result test covering opaque value display and
  unambiguous structural type rendering;
- lexer and parser tests for every grammar production, token span, logical-line
  rule, LF and CRLF span, bare-CR rejection, precedence level, associativity
  rule, grouping case, reserved word, and adopted `P-NNN` recovery case;
- rejection tests at the owning stage for tuple and match syntax,
  multiple-parameter and multi-binder definitions, recursion and forward
  references, polymorphic syntax, comments, semicolons, negative literals, and
  Unicode identifiers;
- parser-locality evidence showing that one additional operator and one
  additional nested-form probe change only their feature parser and the closed
  dialect assembly data required by AD-0005;
- a projection-boundary test proving that concrete syntax with any missing or
  error node cannot produce the resolver's surface AST;
- resolver tests for sequential global scope, lack of recursion and forward
  references, local initializer scope, shadowing, duplicate globals, interface
  and equation name agreement, unknown names, and binder-use identity;
- bidirectional typing tests for synthesis, checking, anonymous functions with
  and without expected types, both global presentations, blocks, application,
  structural function types, and each primitive operation;
- literal, addition, multiplication, equality, output, and trace tests using
  integers beyond signed and unsigned 64-bit range;
- structural diagnostic tests for `P-001` through `P-003`,
  `R-001` through `R-002`, `T-001` through `T-004`,
  equation-name disagreement, a non-function equational interface, missing
  function context, and justified cascade suppression;
- one static-policy locality probe showing that changing a resolution or typing
  rule changes its owning rule outcome without changing unrelated callers;
- complete typed Core representations for the positive cases and independent
  validator rejection of the `I-001` through `I-004` invariant
  failures;
- independent validator rejection of a node from outside the selected Core
  dialect;
- exhaustive review of every node in the selected Core dialect, one
  feature-local extension probe, and a bounded compile-time operation-family
  probe showing AD-0007's future seam without inhabiting an effect operation in
  Mini-Ash;
- identity traversal and one local typed transform followed by validation and
  evaluation-preservation tests;
- small-step derivations for representative binding, application, primitive,
  lexical-capture, and nested-application programs, with verbal explanations;
- evaluator tests for function-before-argument and left-before-right operation
  order, lexical capture, higher-order application, inspectable closures, and
  deep explicit-frame growth without proportional Rust call-stack growth;
- end-to-end failures for parse, resolution, typing, input, and internal
  validation paths, with no Rust panic and no success output;
- source-provenance tests connecting generated bindings and functions to the
  correct equation, interface, operational header, parameter, body, argument,
  and annotation spans;
- Markdown lint, relative-link and anchor validation, notation review, and
  `cargo xtask verify`.

Any implementation discovery that changes the grammar, scope, typing, dynamic
rules, value rendering, or rejection behavior returns to this proposal before
the implementation task proceeds.
