# Syntax

A Mini-Ash file contains zero or more nominal type declarations, zero or more
global function definitions, and exactly one result expression. The file does
not declare a module and cannot import another file.

## Grammar

The following grammar is the complete Mini-Ash surface grammar. Each `;`
terminates an EBNF production; it is not Ash source punctuation.

```ebnf
program ::=
  { type_declaration line_end }
  { global_definition line_end }
  expression [ line_end ] ;

type_declaration ::=
  "type" upper_identifier "=" [ line_end ] constructor_declaration
  { line_end "|" constructor_declaration } ;
constructor_declaration ::=
  upper_identifier [ "(" type { "," type } ")" ] ;

global_definition ::= equational_global | inline_operational_global ;
equational_global ::= external_interface line_end equation { line_end equation } ;
external_interface ::= identifier ":" type ;
equation ::= identifier pattern { pattern } "=" expression ;
inline_operational_global ::=
  "fn" identifier "(" typed_pattern { "," typed_pattern } ")"
  "->" type block ;

block ::=
  "{" line_end { local_declaration line_end } expression [ line_end ] "}" ;
local_declaration ::= local_binding | recursive_binding_group ;
local_binding ::= "let" pattern [ ":" type ] "=" expression ;
recursive_binding_group ::=
  "let" "rec" recursive_member
  { line_end "and" recursive_member } ;
recursive_member ::= identifier ":" type "=" expression ;
function_expression ::= "fn" "(" pattern { "," pattern } ")" block ;
match_expression ::=
  "match" expression "{" line_end
  match_arm { line_end match_arm } [ line_end ] "}" ;
match_arm ::= pattern "=>" expression ;

expression ::= block | function_expression | match_expression | equality_expression ;
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
  | upper_identifier
  | parenthesized_expression ;
parenthesized_expression ::=
  "(" expression [ "," expression { "," expression } ] ")" ;

pattern ::=
  identifier
  | "_"
  | boolean
  | unit
  | upper_identifier [ "(" pattern { "," pattern } ")" ]
  | parenthesized_pattern ;
parenthesized_pattern ::=
  "(" pattern ")"
  | "(" juxtaposed_constructor_pattern ")"
  | "(" pattern "," pattern { "," pattern } ")" ;
juxtaposed_constructor_pattern ::=
  upper_identifier ( pattern | juxtaposed_constructor_pattern ) ;
typed_pattern ::= pattern ":" type ;
type ::= atomic_type [ "->" type ] ;
atomic_type ::= "Int" | "Bool" | "Unit" | upper_identifier | parenthesized_type ;
parenthesized_type ::= "(" type [ "," type { "," type } ] ")" ;

identifier ::= /[a-z_][a-zA-Z0-9_]*/ ;
upper_identifier ::= /[A-Z][a-zA-Z0-9_]*/ ;
integer ::= /0|[1-9][0-9]*/ ;
boolean ::= "true" | "false" ;
unit ::= "(" ")" ;
line_end ::= /logical-newline-in-file-or-block-context/ ;
```

`line_end` is the logical boundary defined by
[lexical structure](lexical-structure.md#whitespace-and-logical-lines).
Braces delimit blocks, and parentheses group expressions and types. A block
contains ordered local declarations and one result expression. An ordinary
`let` is sequential. A `let rec` declaration is one simultaneous group; each
following `and` member occupies another logical line. Neither the file nor a
block uses a trailing semicolon.

Every recursive member has a required type annotation. The grammar accepts an
arbitrary initializer expression so static semantics can distinguish safe
function or constructor-rooted initialization from malformed syntax.

The executable test `syntax_local_recursive_group_example_is_executable`
checks a two-member recursive group. The second function retains a reference
back to the first without calling it, so the program terminates with `42`:

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

## Precedence and associativity

From tightest to loosest, the expression levels are juxtaposed application,
multiplication, addition, and equality. Application, multiplication, and
addition associate to the left. Equality is non-associative, so `a == b == c`
is invalid. Function arrows associate to the right, so `Int -> Int -> Int`
means `Int -> (Int -> Int)`.

Commas construct a tuple expression or tuple type with at least two elements.
`(value)` remains grouping and `()` remains unit. A constructor has zero or
one semantic payload. Two or more declared fields form one tuple payload, so
`Node(left, right)` applies the unary constructor value `Node` to the tuple
`(left, right)`.

A block or anonymous function can occur as an application operand only through
parenthesization. For example, `apply (fn(value) { ... })` passes an anonymous
function as one argument.

## Global function presentations

An equational global places its type interface before its binder-only equation.
The executable test `syntax_equational_global_example_v002_is_executable`
checks this complete file:

```ash
increment : Int -> Int
increment value = value + 1

increment 41
```

An inline operational global places its parameter and result annotations in
the function header. The executable test
`syntax_inline_operational_global_example_v002_is_executable` checks this
complete file:

```ash
fn increment(value : Int) -> Int {
    value + 1
}

increment 41
```

An equational clause has a positive pattern count, and every contiguous clause
for one name has the same count. Each pattern consumes one arrow layer, so
multi-pattern equations remain curried. An operational header with two or more
typed patterns has one tuple domain. An anonymous function with two or more
patterns likewise receives one tuple domain from its expected type.

Patterns are ordinary binders, `_`, Boolean and unit patterns, tuples, and
nested constructors. Integer, record, guarded, or, and as-patterns are not in
the grammar. Parentheses group a pattern. Within that grouping, a constructor
pattern may place its single payload after the constructor, so `(Leaf value)`
has the same pattern structure as `Leaf(value)` and `(Outer Inner value)` nests
the two constructors. Match arms occupy separate logical lines.

The two presentations have different type-directed elaboration, described in
[Elaboration](elaboration.md#function-presentations).
