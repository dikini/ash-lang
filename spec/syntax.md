# Syntax

Each Ash source file defines one unnamed passive static module. A module
contains zero or more imports followed by zero or more declarations. It has no
module header, source-declared signature, or file result expression. An import
affects compile-time visibility; it does not define a runtime module value or
run initialization.

The source path selected for execution identifies the entry module. The entry
contract requires a local global named `main`; [Static
Semantics](static-semantics.md) defines its type requirements.

## Grammar

The following grammar is the complete Ash surface grammar. Each `;` terminates
an EBNF production; it is not Ash source punctuation.

```ebnf
module ::= { import_declaration line_end } { module_declaration line_end } ;
module_declaration ::=
    type_declaration
  | interface_declaration
  | implementation_declaration
  | effect_declaration
  | global_definition ;

import_declaration ::=
    "import" module_path
      ( "as" upper_identifier | targeted_import )
  | "pub" "import" module_path targeted_import ;
targeted_import ::=
  "(" import_item { "," import_item } ")" ;
module_path ::= relative_module_path | absolute_module_path ;
relative_module_path ::= identifier { "." identifier } ;
absolute_module_path ::= "@" identifier "." identifier { "." identifier } ;
import_item ::=
    import_name [ "as" import_name ]
  | "impl" upper_identifier ;
import_name ::= identifier | upper_identifier ;

type_declaration ::=
  [ "pub" [ "opaque" ] ]
  "type" upper_identifier [ type_parameters ] "=" [ line_end ] constructor_declaration
  { line_end "|" constructor_declaration } ;
type_parameters ::=
  "<" type_parameter { "," type_parameter } ">" ;
type_parameter ::= upper_identifier [ ":" kind ] ;
kind ::= kind_atom [ "->" kind ] ;
kind_atom ::= "Type" | "EffectRow" | "(" kind ")" ;
constructor_declaration ::=
  upper_identifier [ "(" type { "," type } ")" ] ;

effect_declaration ::=
  [ "pub" ] "effect" upper_identifier [ type_parameters ]
  "{" line_end
  effect_operation { line_end effect_operation } [ line_end ]
  "}" ;
effect_operation ::= identifier ":" type ;

interface_declaration ::=
  [ "pub" ] "interface" upper_identifier interface_parameters
  [ interface_determination ]
  "{" line_end
  interface_method { line_end interface_method } [ line_end ]
  "}" ;
interface_parameters ::= "<" type_parameter { "," type_parameter } ">" ;
interface_determination ::=
  "where" determination_side "->" determination_side ;
determination_side ::=
  upper_identifier
  | "(" upper_identifier { "," upper_identifier } ")" ;
interface_method ::= identifier [ type_parameters ] ":" type ;

implementation_declaration ::=
  [ "pub" ] "impl" [ type_parameters ]
  interface_application [ where_clause ]
  "{" line_end
  [ impl_equation { line_end impl_equation } [ line_end ] ]
  "}" ;
impl_equation ::= identifier pattern { pattern } "=" expression ;

global_definition ::= equational_global | inline_operational_global ;
equational_global ::=
  [ "pub" ] global_signature line_end equation { line_end equation } ;
global_signature ::= identifier [ type_parameters ]
  ":" type [ where_clause ] ;
equation ::= identifier pattern { pattern } "=" expression ;
inline_operational_global ::=
  [ "pub" ] "fn" identifier [ type_parameters ]
  "(" typed_pattern { "," typed_pattern } ")"
  "->" computation_type [ where_clause ] block ;

where_clause ::= "where" constraint { "," constraint } ;
constraint ::= interface_application ;
interface_application ::=
  interface_reference "<" type { "," type } ">" ;
interface_reference ::=
  upper_identifier | upper_identifier "." upper_identifier ;

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
handler_expression ::=
  "handle" expression "with" effect_instance
  "{" line_end
  handler_clause { line_end handler_clause } [ line_end ]
  "}" ;
handler_clause ::= identifier pattern "=>" expression ;
resume_expression ::= "resume" expression ;

expression ::=
    block
  | function_expression
  | match_expression
  | handler_expression
  | resume_expression
  | equality_expression ;
equality_expression ::= additive_expression [ "==" additive_expression ] ;
additive_expression ::=
  multiplicative_expression { "+" multiplicative_expression } ;
multiplicative_expression ::=
  application_expression { "*" application_expression } ;
application_expression ::= primary_expression { primary_expression } ;
primary_expression ::=
  integer
  | boolean
  | unit
  | unqualified_term_reference
  | qualified_term_reference
  | perform_expression
  | parenthesized_expression ;
unqualified_term_reference ::= identifier | upper_identifier ;
qualified_term_reference ::= upper_identifier "." import_name ;
perform_expression ::= "perform" operation_reference primary_expression ;
operation_reference ::= effect_reference [ type_arguments ] "." identifier ;
parenthesized_expression ::=
  "(" expression [ "," expression { "," expression } ] ")" ;

pattern ::=
  identifier
  | "_"
  | boolean
  | unit
  | constructor_reference [ "(" pattern { "," pattern } ")" ]
  | parenthesized_pattern ;
constructor_reference ::=
  upper_identifier | upper_identifier "." upper_identifier ;
parenthesized_pattern ::=
  "(" pattern ")"
  | "(" juxtaposed_constructor_pattern ")"
  | "(" pattern "," pattern { "," pattern } ")" ;
juxtaposed_constructor_pattern ::=
  constructor_reference ( pattern | juxtaposed_constructor_pattern ) ;
typed_pattern ::= pattern ":" type ;
type ::= atomic_type | atomic_type "->" computation_type ;
computation_type ::= type [ "!" effect_row ] ;
atomic_type ::=
  "Int"
  | "Bool"
  | "Unit"
  | nominal_type_reference [ type_arguments ]
  | parenthesized_type ;
nominal_type_reference ::=
  upper_identifier | upper_identifier "." upper_identifier ;
type_arguments ::= "<" type { "," type } ">" ;
parenthesized_type ::= "(" type [ "," type { "," type } ] ")" ;
effect_row ::=
  "{"
    [ effect_instance { "," effect_instance } [ "|" row_variable ]
    | "|" row_variable ]
  "}" ;
effect_instance ::= effect_reference [ type_arguments ] ;
effect_reference ::=
  upper_identifier | upper_identifier "." upper_identifier ;
row_variable ::= upper_identifier ;

identifier ::= /[a-z_][a-zA-Z0-9_]*/ ;
upper_identifier ::= /[A-Z][a-zA-Z0-9_]*/ ;
integer ::= /0|[1-9][0-9]*/ ;
boolean ::= "true" | "false" ;
unit ::= "(" ")" ;
line_end ::= /logical-newline-in-module-or-block-context/ ;
```

`line_end` is the logical boundary defined by [lexical
structure](lexical-structure.md#whitespace-and-logical-lines). Imports must
precede every module declaration. Both import lists and declaration lists may
be empty. A private import may be complete or targeted. A public import must be
targeted. A targeted import list contains at least one item. Neither a module
nor a block uses a trailing semicolon.

A relative module path contains one or more lowercase path segments. An
absolute path starts with `@`, contains a lowercase root name, and has at least
one path segment beneath that root. Paths contain neither filename-extension
syntax nor current-directory or parent-directory segments. A complete import
uses one uppercase local alias:

```ash
import helpers.math as Math
```

A targeted import selects one or more public names and may rename each selected
spelling. This fragment selects a term, a type, and a constructor:

```ash
import @std.collections.list (map, Option as ListOption, Some)
```

A targeted implementation item writes `impl` followed by one uppercase public
interface spelling. It cannot be renamed and binds no source name. Name items
and implementation items are independent, so selecting an interface or method
name does not select its implementations:

```ash
import equality (Equal, equal, impl Equal)
```

`pub import` uses the same targeted list and re-exports each selected name or
implementation channel. It has no qualified `as Module` form. [Name
resolution](name-resolution.md#imports-and-namespaces) defines selection,
availability, and re-export identity.

An imported module member uses one uppercase module alias and one member
spelling. Terms may have lowercase or uppercase member spellings, as in
`List.map` and `List.Some`. Type and constructor occurrences use uppercase
members, as in `List.Option` and `List.Some`. Qualification has exactly these
two components; it does not repeat the dependency's path.

An unmodified declaration is private. On a declaration, `pub` marks a global,
nominal type, interface, effect, or implementation as public. On an import, `pub`
re-exports the selected channels. `pub opaque type` exports the nominal name
without exporting its constructors. `opaque` is valid only between `pub` and
`type`; constructors cannot carry individual modifiers. An equational global
writes `pub` once before its global signature, not on its equation heads. An
inline operational global writes `pub` before `fn`.

An interface declaration has one or more ordered parameters, an optional
determination edge, and a nonempty body of method signatures. Each side of an
edge is nonempty. Parentheses are optional for a one-name side and required for
a multiple-name side. A method may place one `type_parameters` list between
its name and colon. It has no visibility modifier, requirement, or body. An
implementation has no source name. Its body contains only equations; an
equation has no separate visibility modifier, signature, type-parameter list,
or requirement. Implementation equations use the same pattern and expression
grammar as equational-global clauses, and the body may be empty. The grammar
provides no associated declaration, associated-output projection, default
method, named implementation, general determination graph, or runtime
dictionary form.

An effect declaration has zero or more ordered parameters and one or more
operations. Each operation writes one lowercase name and one type with exactly
one outer function domain. That outer operation result has no effect-row
annotation; the requested instance comes from the enclosing effect. An
operation has no parameter list, requirement, visibility modifier, body,
default, or associated declaration.

A present method `type_parameters` list is nonempty by the existing production
and uses the same optionally kinded `type_parameter` entries as other
declarations. An absent list is syntactically distinct. Missing separators,
kinds, or the closing angle bracket are syntax failures; recovery does not
publish a partial method binder list.

Every declaration-level type binder uses `type_parameter`. Its optional kind
annotation contains `Type`, `EffectRow`, a function kind, or a parenthesized
kind. Static semantics restricts `EffectRow` to complete global and eligible
generalized-local binders and forbids it beneath a kind arrow. The spellings
`Type` and `EffectRow` are contextual: they denote kinds only inside a kind
annotation and remain ordinary `upper_identifier` spellings elsewhere. For
example, this complete entry module declares and uses a nominal type named
`Type`:

```ash
type Type = Type

main : Unit -> Type
main () = Type
```

Nominal declarations always write a parameter list when they have parameters.
An interface always writes its nonempty parameter list. Either global
presentation may place an optional parameter list after the global name, and
an implementation may place one after `impl`. [Name
resolution](name-resolution.md#type-binder-identity-and-scope) defines the
explicit and omitted-list binder policies.

A declaration `where` clause contains one or more comma-separated interface applications
and has no trailing comma. It remains on its declaration header's logical line.
It follows the complete value type in either global presentation and the
complete interface application in an implementation head. A constraint is
therefore not part of a global's result type. The `where` immediately after an
interface parameter list instead introduces that interface's determination
edge. Each interface application has a nonempty ordered type-argument list and
may use an unqualified interface name or one qualified by a module alias.

Braces delimit blocks, and parentheses group expressions and types. A block
contains ordered local declarations and one result expression. An ordinary
`let` is sequential. A `let rec` declaration is one simultaneous group; each
following `and` member occupies another logical line.

Every recursive member has a required type annotation. The grammar accepts an
arbitrary initializer expression so static semantics can distinguish safe
function- or constructor-rooted initialization from malformed syntax.

A nominal declaration binds its ordered type parameters only in its
constructor payload types. A named source type may occur without arguments or
with one or more comma-separated arguments. Syntax does not require a nominal
constructor to be saturated and does not distinguish nominal constructors from
type parameters. Resolution distinguishes them by identity; static semantics
checks each resulting application against its kinds. Source expressions have
no explicit type abstraction or type-application form; `value<Type>` is not an
expression.

A function result may carry a row of exact effect instances and at most one row
tail. Omitting `! effect_row` means the empty row. A row tail is one uppercase
variable after `|`; name resolution and static semantics require it to denote an
admitted `EffectRow` binder. Effect arguments use the same nonempty ordered
`type_arguments` form as named types. Empty rows write `{}`, closed rows list
instances, and open rows either append `| R` to known instances or write only
`| R`.

`perform` consumes one primary-expression operand. A non-primary operand must be
parenthesized. A handler contains one or more clauses, each with one operation
name, one pattern, and one expression body. `resume` consumes one expression;
name resolution and static semantics restrict it to its owning operation
clause.

The executable test `syntax_local_recursive_group_example_is_executable`
checks a complete entry module containing a two-member recursive group. The
second function retains a reference back to the first without calling it, so
the program terminates with `42`:

```ash
main : Unit -> Int
main () = {
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

`perform` has primary-expression precedence after consuming its single primary
operand. `handle` and `resume` have the same loose prefix boundary as `match`:
their operand extends to the handler delimiter or the end of the surrounding
expression. A handled or resumed expression must be parenthesized to serve as
an application or infix operand. Therefore `resume x + y` resumes with `x + y`,
while `(resume x) + y` resumes with `x` and then adds `y`.

`!` attaches to the complete computation codomain immediately to its left after
parentheses are applied. Thus `A -> B -> C ! {E}` is a pure call from `A` that
returns a function whose call from `B` may request `E`. In `A -> (B -> C) !
{E}`, the call from `A` may request `E` while returning a pure function.

Kind arrows also associate to the right, so `Type -> Type -> Type` means
`Type -> (Type -> Type)`. Parentheses may instead group a kind on either side
of an arrow.

Commas construct a tuple expression or tuple type with at least two elements.
`(value)` remains grouping and `()` remains unit. A constructor has zero or one
semantic payload. Two or more declared fields form one tuple payload, so
`Node(left, right)` applies the unary constructor value `Node` to the tuple
`(left, right)`.

A block or anonymous function can occur as an application operand only through
parenthesization. For example, `apply (fn(value) { ... })` passes an anonymous
function as one argument.

## Global function presentations

An equational global places its global signature before one or more contiguous
pattern clauses. The executable test
`syntax_equational_global_example_v002_is_executable` checks this complete
entry module:

```ash
increment : Int -> Int
increment value = value + 1

main : Unit -> Int
main () = increment 41
```

An inline operational global places its parameter and result annotations in
the function header. The executable test
`syntax_inline_operational_global_example_v002_is_executable` checks this
complete entry module:

```ash
fn increment(value : Int) -> Int {
    value + 1
}

main : Unit -> Int
main () = increment 41
```

Either global presentation may append a `where` clause to its header. The
executable test
`syntax_constrained_global_presentations_are_executable`
checks that both presentations admit the same constraint syntax:

```ash
interface Equal<A> {
    equal : (A, A) -> Bool
}

impl Equal<Int> {
    equal (left, right) = left == right
}

same_equational : (A, A) -> Bool where Equal<A>
same_equational pair = equal pair

fn same_operational(pair : (A, A)) -> Bool where Equal<A> {
    equal pair
}

main : Unit -> (Bool, Bool)
main () = (same_equational (1, 1), same_operational (1, 1))
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
