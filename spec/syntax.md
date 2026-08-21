# Syntax

A Mini-Ash file contains zero or more global function definitions followed by
exactly one result expression. The file does not declare a module and cannot
import another file.

## Grammar

The following grammar is the complete Mini-Ash surface grammar. Each `;`
terminates an EBNF production; it is not Ash source punctuation.

```ebnf
program ::= { global_definition line_end } expression [ line_end ] ;

global_definition ::= equational_global | inline_operational_global ;
equational_global ::= external_interface line_end equation ;
external_interface ::= identifier ":" type ;
equation ::= identifier binder "=" expression ;
inline_operational_global ::=
  "fn" identifier "(" typed_binder ")" "->" type block ;

block ::=
  "{" line_end { local_declaration line_end } expression [ line_end ] "}" ;
local_declaration ::= local_binding | recursive_binding_group ;
local_binding ::= "let" identifier [ ":" type ] "=" expression ;
recursive_binding_group ::=
  "let" "rec" recursive_member
  { line_end "and" recursive_member } ;
recursive_member ::= identifier ":" type "=" expression ;
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

`line_end` is the logical boundary defined by
[lexical structure](lexical-structure.md#whitespace-and-logical-lines).
Braces delimit blocks, and parentheses group expressions and types. A block
contains ordered local declarations and one result expression. An ordinary
`let` is sequential. A `let rec` declaration is one simultaneous group; each
following `and` member occupies another logical line. Neither the file nor a
block uses a trailing semicolon.

Every recursive member has a required type annotation. The grammar accepts an
arbitrary initializer expression so static semantics can distinguish an unsafe
recursive initializer from malformed syntax. Static semantics restricts the
initializer to a direct anonymous function.

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

Both forms define one unary function. The inline operational header uses
familiar tuple-like punctuation, but its parentheses delimit one typed binder.
They do not construct a tuple. Mini-Ash has no multi-parameter operational
header, tuple expression, product type, general pattern, or multi-binder
equation. Richer pattern matching is a possible later extension rather than
current syntax.

The two presentations have different type-directed elaboration, described in
[Elaboration](elaboration.md#function-presentations).
