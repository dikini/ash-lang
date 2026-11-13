# Declaration-macro grammar

> This design records the transition as it was developed. References below to
> proposed work, current behavior, implementation and evidence describe that
> historical stage. The [specification](../../../spec/syntax-expansion.md)
> describes the language; [TASK-0068](../../tasks/TASK-0068-top-level-declaration-macros.md)
> records delivery and remaining verification.

This grammar records the declaration-macro surface accepted in historical
[CP-0034](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/proposals/CP-0034-top-level-declaration-macros.md).
The derive-specific grammar is in [derive authoring and grammar](derive-syntax.md).
The [language grammar](../../../spec/syntax.md#grammar) is authoritative.

## Definitions and imports

The following productions add a public declaration syntax definition to module
syntax. `identifier`, `upper_identifier`, `expression`, `block`, `line_end`, and
`qualified_term_reference` use the existing Ash grammar. A `macro_name` after
`$` can be lowercase or uppercase. A declaration capture binding can also use
a reserved word as its metaname; a declaration template can read that capture
using the same spelling, including in repetitions. This does not change the
accepted expression-macro matcher grammar, derive or generator binding names,
ordinary variables or the identifier consumed by an `ident` capture. The
`matcher_literal`, `template_literal` and `repetition_separator` lexical
classes are defined immediately below.

In an escape block or inline escape expression only, the ordinary expression
grammar additionally admits `$` followed by a capture or generator name as a
primary expression. It reads that syntax value as specified by CP-0034;
quotation holes use ordinary Ash variables. This does not change `from` seed expressions.

```ebnf
declaration_syntax_definition ::=
  "pub" "syntax" "declaration" ":" "(" identifier ")"
  { matcher_item } "=>"
  ( declaration_template [ generator_clause ] | "using" identifier ) ;
macro_name ::= identifier | upper_identifier ;
capture_name ::= macro_name | reserved_word ;
matcher_item ::= matcher_capture | matcher_repeat | matcher_group | matcher_literal ;
matcher_capture ::= "$" capture_name ":" fragment_kind ;
fragment_kind ::= "ident" | "expr" | "type" | "pattern" | "declaration" ;
matcher_repeat ::=
  "$" "(" { matcher_item } ")" [ repetition_separator ] repetition_operator ;
repetition_operator ::= "*" | "+" ;
matcher_group ::=
  "(" { matcher_item } ")" | "{" { matcher_item | line_end } "}" ;
matcher_literal ::= /matcher-literal-token/ ;
repetition_separator ::= /repetition-separator-token/ ;

declaration_template ::= "{" { template_item } "}" ;
template_item ::= template_splice | template_escape | template_repeat | template_group
  | template_literal | line_end ;
template_splice ::= "$" capture_name ;
template_escape ::= "$" ( block | inline_escape_body ) ;
inline_escape_body ::= "{" expression "}" ;
template_repeat ::=
  "$" "(" { template_item } ")" [ repetition_separator ]
  repetition_operator [ generator_clause ] ;
template_group ::= "(" { template_item } ")" | "{" { template_item } "}" ;
template_literal ::= /template-literal-token/ ;

generator_clause ::=
  "with" "{" [ line_end ] generator_binding
  { line_end generator_binding } [ line_end ] "}" ;
generator_binding ::= "$" macro_name "from" seed_expression "step" step_reference ;
step_reference ::= identifier | qualified_term_reference ;
seed_expression ::= /ash-expression-with-capture-splices/ ;
reserved_word ::= /a reserved word listed in lexical structure/ ;
```

A matcher literal is an Ash token other than `$`, `=>`, a logical line end,
or a group delimiter; group delimiters are represented by `matcher_group`.
A template literal is an Ash token other than `$`, a logical line end, or a
group delimiter; groups and line ends have their own productions. A repetition
separator is one Ash token other than `$`, `=>`, `*`, `+`, a logical line end,
or a group delimiter. Its spelling and kind are literal. `seed_expression` uses
the ordinary Ash expression grammar recursively, with `$` followed by a
`macro_name` added as an alternative to `primary_expression`. That splice
must name an `expr` capture available at the clause's repetition depth. Its
captured expression is checked by ordinary Ash rules in the compile-time
environment. The seed
ends before the first `step` token at its current syntactic level. Parenthesize
an expression that needs that spelling as an ordinary name at that level.

For `template_escape`, a logical line end immediately after the opening `{`
selects `block`; otherwise the braces contain exactly one expression, followed
by `}` without a logical line end at the escape's own level. Nested expression
forms follow their existing balancing and logical-line rules. Inline escape
bodies have no outer local-declaration list; the ordinary `block` production is
unchanged. The same escape forms apply inside expression quotes.

The matcher header ends at `=>` on its logical line; parentheses follow the
existing logical-line rules, and braced groups contain their own line ends.
The template's outer braces are delimiters and are not emitted. A `with` block
after the template or a template repetition is a directive and is not emitted.
In those positions `with {` starts a generator clause, whose first non-line-end
token must be `$`; other `with` occurrences remain ordinary template tokens.
The same definition context and syntax import rules as CP-0033 apply. A
transformer after `=> using` is an ordinary global in the defining module, as
in slice 1. A macro's own syntax definitions cannot be invoked in that module.

`declaration: (name)` is a contextual header, not a new globally reserved
identifier. The parentheses are required: slice 1 permits the colon as a
matcher literal but prohibits matcher groups. Thus an expression syntax named
`declaration` with `:` and an identifier as matcher literals keeps its slice 1
meaning. A module-level definition cannot silently change category based on
which importer later uses it.

CP-0034 makes `syntax` a reserved word in all identifier positions upon
implementation, instead of the current contextual word. Existing user-defined identifiers
named `syntax`, including macro names and import aliases, must be renamed.
The existing compiler-owned path `@builtin.compiler.syntax` remains valid.
The word `declaration` remains contextual. Test both the rejected old names
and unaffected names such as `syntax_value` and `declaration`; retain the
compiler-owned path and existing syntax-definition and targeted-import forms.
The [accepted quotation and escape forms](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/proposals/CP-0034-top-level-declaration-macros.md#executable-template-escapes-and-expression-subtemplates)
specify their staging and capture access. Outside an escape, a macro template
still processes its own `$name` splices, including those inside a quotation in
its output; an unbound outer splice remains an outer-template error. An escape
is an explicit boundary for ordinary Ash code and nested quotation holes.

## Invocation and matcher contract

A module declaration position accepts an invocation whose leading lowercase
identifier is an explicitly imported declaration-syntax name. The selected
definition supplies the remaining matcher; it is not a general parser callback
and there is no ordinary-declaration fallback. A matcher can be empty, in which
case only its leading name is written. A module-level logical line ends an
invocation; a complete balanced group can span lines. The selected macro's
literal tokens, captures, groups and repetitions consume the remainder. Reject
trailing unmatched tokens and recovery-bearing or incomplete captures.

`ident` consumes one lowercase or uppercase identifier. `expr`, `type` and
`pattern` consume one complete fragment in their existing Ash category.
`declaration` consumes a braced group containing exactly one complete ordinary
module declaration; the braces delimit the capture and are not part of the
captured declaration. This permits a signature and all its equations to span
lines. A captured type or newtype may contain a deriving clause. Captures
retain source contexts, lexical boundaries and origins.

For a non-final variable-length capture, its next literal, enclosing group
delimiter, repetition separator or invocation boundary supplies the stop
token. The first such token at the capture's syntactic level ends it; nested
parentheses, braces and a complete type argument list do not expose their inner
tokens to the outer stop. The prefix must parse completely in its category.
There is no speculative backtracking to a later stop: use a different delimiter
or a balanced group when the delimiter is also needed inside the capture.
Adjacent captures without an intervening literal or group boundary and a
repetition whose body can consume no token are definition errors.

Matcher capture names are unique. `*` accepts zero or more iterations and `+`
accepts one or more. Separators occur between iterations, never before the first
or after the last. Nested repetitions preserve their tree shape and source
order. The matcher uses the next separator only when it can start another
complete iteration; a trailing separator is an invocation error. When a literal
can both terminate a repetition and start its following matcher item, reject
the definition as ambiguous rather than select an arbitrary interpretation.

## Template and generator contract

Every splice refers to a matcher capture or generator in scope. It preserves
the captured syntax category and context; the declaration output parser checks
its position after expansion. A repeated capture is used only under the
corresponding template repetition. At least one captured sequence at that
depth drives a template repetition. Multiple drivers must have the same length
in their current enclosing iteration; otherwise expansion fails atomically.
An inner capture's outer sequence can drive an enclosing repetition even when
its only splice occurs in a nested template repetition.
`*` emits zero iterations for an empty driver; `+` rejects an empty driver.
Nested repetitions use the selected outer elements as their inner sequences.

Generator bindings and matcher captures have unique names within the macro.
A binding's `from` expression can use captured expressions in its lexical
repetition scope. The referenced ordinary Ash step function has type
`A -> (A, B)`: its result contains the next state followed by the generated
value. For the expression splices in the generator cases, `B` is
`Syntax.ExpressionFragment`. The seed and function are checked by ordinary
Ash rules; no conversion interface or macro-specific type checker is added. Caller-supplied seeds can use inline expressions and checked imports,
not globals of the caller module that are unavailable at expansion time.
Definition-site references retain their checked defining context. Generator
initialization, iteration caching, nesting, error propagation and host effects
are specified in the [generator design](declaration-slice.md#generator-assisted-templates).

Output is an ordered sequence of complete ordinary module declarations and
permitted nested declaration invocations, without re-lexing generated text.
Imports, syntax definitions, missing or recovery nodes and trailing tokens are
rejected. Reject an import or syntax definition written literally in a template
at definition admission; reject a prohibited declaration constructed by a
procedure or splice at output admission. Admit or reject an invocation
atomically. Expand nested invocations
in source order under the existing bounds, preserving source contexts and
origins. Declaration invocations and deriving clauses expand in source order,
as specified in the companion. After expansion, resolve and type-check the
resulting ordinary declarations.

## Boundaries requiring retained evidence

The lexical token vocabulary and punctuation-to-kind mapping are specified in
[lexical structure](../../../spec/lexical-structure.md#public-token-kinds).
Interface and artifact versioning are separate language-interface concerns;
slice 1 specifies no version-selection mechanism. CP-0034 adds the closed
`TokenKind` cases `SyntaxKeyword` and `Dollar` for `syntax` and `$` so quoted
expressions can pass through the existing syntax service. Its concrete use must be
checked against the retained expression-slice parser and the complete fixture
corpus, including ambiguous stops, nested repetitions and every output form.
