# Provisional first-stratum grammar

> This grammar is informative evidence governed by
> [DN-0016](../../DN-0016-first-mini-ash-corpus.md). It is parser input for
> comparison and does not define current Ash syntax.

The grammar begins from the suggested forms in
[DN-0005](../../DN-0005-surface-function-definitions.md). An equational global
has one external interface, while an operational global carries its interface
inline. A local function is an ordinary anonymous value, and expected types may
flow from a binding or application into that value.

The grammar uses a provisional `line_end` token to make the examples parseable
without deciding Ash's eventual layout rules. Blank lines are ignored. An
operational body or expression block uses braces; its local bindings occupy
complete lines and its final expression supplies the block result.

The following productions say that a source file contains zero or more typed
global definitions followed by one result expression. Application binds more tightly
than multiplication, multiplication binds more tightly than addition, and
equality is non-associative. Function arrows associate to the right. Regex
literals describe lexical forms for display and are not executable regular
expressions.

```ebnf
program ::= { global_definition line_end } expression [ line_end ] ;

global_definition ::= equational_global_definition | inline_operational_definition ;
equational_global_definition ::= external_interface line_end equation_group ;
external_interface ::= identifier ":" type ;
equation_group ::= equation { line_end equation } ;
equation ::= identifier pattern { pattern } "=" expression ;
inline_operational_definition ::= "fn" identifier typed_parameter_tuple "->" type block ;

block ::= "{" line_end { local_binding line_end } expression [ line_end ] "}" ;
local_binding ::= "let" identifier [ ":" type ] "=" expression ;
function_expression ::= "fn" parameter_tuple block ;
match_expression ::= "match" expression match_block ;
match_block ::= "{" line_end match_arm { line_end match_arm } [ line_end ] "}" ;
match_arm ::= pattern "=>" expression ;

expression ::= block | function_expression | match_expression | equality_expression ;
equality_expression ::= additive_expression [ "==" additive_expression ] ;
additive_expression ::= multiplicative_expression { "+" multiplicative_expression } ;
multiplicative_expression ::= application_expression { "*" application_expression } ;
application_expression ::= primary_expression { primary_expression } ;
primary_expression ::= integer | boolean | unit | identifier | parenthesized_expression | tuple_expression ;
parenthesized_expression ::= "(" expression ")" ;
tuple_expression ::= "(" expression "," expression { "," expression } ")" ;

binder ::= identifier ;
binder_list ::= binder { "," binder } ;
parameter_tuple ::= "(" binder_list ")" ;
typed_binder ::= identifier ":" type ;
typed_binder_list ::= typed_binder { "," typed_binder } ;
typed_parameter_tuple ::= "(" typed_binder_list ")" ;
tuple_pattern ::= "(" pattern "," pattern { "," pattern } ")" ;
pattern ::= binder | boolean | tuple_pattern ;
type ::= atomic_type [ "->" type ] ;
atomic_type ::= "Int" | "Bool" | "Unit" | parenthesized_type ;
parenthesized_type ::= "(" type [ "," type { "," type } ] ")" ;

identifier ::= /[a-z_][a-zA-Z0-9_]*/ ;
integer ::= /0|[1-9][0-9]*/ ;
boolean ::= "true" | "false" ;
unit ::= "(" ")" ;
line_end ::= /newline-or-equivalent-layout-boundary/ ;
```

Whitespace separates tokens where concatenation would otherwise be ambiguous.
Blank lines do not add `line_end` tokens. The words `fn`, `let`, `match`, `Int`,
`Bool`, `Unit`, `true`, and `false` are reserved. Comments, Unicode identifier
rules, numeric ranges, and source encodings remain outside this corpus slice.

An equational interface and its body must use the same name. This agreement is a
resolution obligation rather than a context-sensitive EBNF production. An
inline operational definition supplies its interface exactly once through its
parameter and result annotations.

Parameter grouping follows types rather than a second semantic notion of arity.
Whitespace-separated equational head patterns introduce successive function
domains and therefore require successive arrows such as `A -> B -> C`;
applications supply those arguments through left-associated juxtaposition,
`f a b`. An
inline operational comma-separated parameter list is tuple syntax: it
decomposes one product domain such as `(A, B) -> C`, and application supplies
one tuple value, `f (a, b)`. An equation over a
product domain likewise uses one parenthesized tuple pattern, `f (a, b) = ...`,
rather than a curried head. X-003 records this distinction without adding
products to the first retained boundary.

The whitespace-separated equation head deliberately refines DN-0005's
illustrative parenthesized spelling. It follows the successive-arrow type
directly and avoids presenting `f (a, b)` as curried when parentheses and a comma
denote one product argument.

The inline operational form resembles function declarations in TypeScript,
Rust, C++, and Java. That familiarity is evidence for onboarding and source
locality, not proof that Ash should accept the form. Equational definitions are
likewise familiar to people coming from SML, OCaml, Haskell, and related
languages. More importantly, their pattern clauses expose coverage and
decomposition directly. An equivalent inline operational definition writes an
explicit `match` around its body. After pattern checking and elaboration, both
forms should converge toward the same or similar typed callable Core.

DN-0005's `fn depth<A>(tree: Tree<A>) -> Nat` example also carries type
parameters. This monomorphic stratum retains the inline interface shape but
omits `<A>` and type application; their syntax belongs to the later polymorphic
stratum.

DN-0005 also illustrates an operational body with an external interface. The
first-stratum grammar omits that weak baseline because it adds another spelling
without exposing a distinct body structure or interface-placement strength. A
parser comparison may sketch it if implementation evidence contradicts this
judgment.

The Boolean alternatives in `pattern` and the `match_expression` production
exist for X-001 and X-002 only. The tuple productions and multi-parameter forms
also support X-003. Together they expose cross-stratum definition pressure; they
do not add general patterns, matches, or products to the first retained feature
boundary.

## Parser pressure

The grammar requires a candidate to demonstrate:

- grouping an external interface with an equational body;
- parsing an inline operational interface without creating a second function
  type or application semantics;
- declaration repetition followed by a required result expression;
- right-associated function types;
- type-directed distinction between curried equation heads and grouped
  operational parameters;
- block-local bindings and final-expression results;
- anonymous operational functions in binding and argument positions;
- Boolean equation groups and equivalent explicit matches for the cross-stratum
  definition probe;
- left-associated application by juxtaposition and three infix precedence
  levels;
- non-associative equality, rejecting `1 == 1 == true` rather than grouping it;
- recovery at a closing brace or global boundary without turning each newline
  inside an expression into a cascade;
- precise spans for names, delimiters, operators, interfaces, bodies, and whole
  definitions.

## Unresolved alternatives

The comparison must not treat these details as accepted design:

- a final expression versus a distinguished result binding;
- whether later evidence justifies adding the external-interface operational
  baseline while still requiring exactly one interface;
- the exact layout token, semicolon policy, and multiline-equation boundary;
- braces around operational bodies and expression blocks;
- the marker for anonymous equational functions;
- tuple-pattern spelling once product data and patterns enter the corpus;
- the selected primitive operators and precedence table.

The earlier `def` and parameter-annotated arrow-lambda sketch is not a corpus
candidate: it departed from DN-0005 without a named concern or contrary evidence.
Future alternatives must state the specific parsing, typing, diagnostic, or
tooling question they answer and compare what they lose from the suggested
forms.
