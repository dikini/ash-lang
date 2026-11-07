# Derive authoring and grammar: working design

This companion develops derive-specific syntax for
[CP-0034](../../proposals/CP-0034-top-level-declaration-macros.md). The
derive-authoring forms and derive-specific grammar below were approved as the
working design, along with a `deriving` clause on top-level types and newtypes
and Rust-like additive derivation. CP-0034 remains proposed; these choices are
neither current Ash nor implementation authority. They reuse the
declaration-template and syntax-service proposals in the
[declaration design](declaration-slice.md).

## Authoring forms

A declarative derive binds the subject's declared type name directly. For
example, `marker` emits an ordinary implementation for a nongeneric subject:

```text
import api (Marker, mark)

pub syntax derive: (marker) $target:ident => {
    impl Marker<$target> {
        mark _ = true
    }
}
```

`$target` is chosen by the derive author. It is bound to the original type or
newtype name, including its syntax context and origin; the caller does not
supply it separately. This is a fixed subject-name binding, not a matcher for
the rest of the subject. An invalid generated implementation is rejected by
ordinary Ash checking. In particular, this simple example does not generate
the type parameters needed for a generic subject.

A procedural derive uses the slice 1 transformer form:

```text
pub syntax derive: (indexed) => using expand_indexed

expand_indexed : S.Input -> S.MacroResult ! {S.Ops}
```

The snippet omits the ordinary Ash function body and assumes `S` is an alias
for `@builtin.compiler.syntax`. The function receives a compiler-issued
`Input`. `S.capture(input, 0)` returns the subject as
`Captured(DeclarationCapture(subject))`. The function can use
`declaration_syntax` to inspect its ordered syntax, construct an output
`Syntax`, and return `Expanded(output)` or `Rejected(diagnostic)`. This permits
a derive to inspect constructor lists, payload syntax and generic parameters
without requiring type or implementation queries. The
[indexed derive fixture](fixtures/indexed/README.md) contains a complete
transformer and caller graph for a nongeneric, nullary-constructor example.
The [deriving-clause fixtures](fixtures/derives/README.md) also include a
procedural one-parameter newtype derive using a fresh hygienic type parameter.

The subject-name binding is optional on either authoring form. If written, it
is also available to a procedural transformer as capture index 1, an
`IdentifierCapture` retaining the name's origin. Without it, index 1 is
`MissingCapture`. Index 0 is always the subject. These derive-specific capture
positions do not change capture ordering for expression or declaration macros.

Declarative derives reuse declaration templates. They are suitable when the
subject name alone supplies the needed variation. Inspection of a variable
number of constructors or generic parameters is provided by the procedural
form; this proposal does not add a separate declaration-pattern language.
Both forms can emit any ordinary top-level declaration admitted for declaration
macros, subject to normal checking and visibility rules.

For example, a procedural derive for a generic newtype could emit the following
ordinary implementation. It must reconstruct and bind the type parameter;
splicing the name `Box` into the fixed `marker` template above is insufficient.

```text
pub newtype Box<A> = Box(A)
    deriving (generic_marker)

impl<A> Marker<Box<A>> {
    mark _ = true
}
```

The implementation shown is the derive's intended output, not a second
declaration to write alongside the derive invocation. Its type-parameter
binding and any needed constraints are the derive author's responsibility and
are verified by ordinary Ash checking.

## Grammar

This grammar specifies the proposed derive definition, deriving clause, and
replacement top-level type and newtype productions. `identifier`,
`upper_identifier`, `line_end`, `type_parameters`, `type`, and
`constructor_declaration` use the current Ash grammar. `declaration_template`
and `generator_clause` use the [declaration-macro grammar](declaration-grammar.md).
The optional `generator_clause` has the same
trailing `with` form and rules as a declaration template. A derive name or
subject-binding name is a lowercase `identifier`; the bound subject is the
uppercase name from the type declaration.

```ebnf
derive_syntax_definition ::=
  "pub" "syntax" "derive" ":" "(" identifier ")" [ derive_name_binding ] "=>"
  ( declaration_template [ generator_clause ] | "using" identifier ) ;
derive_name_binding ::= "$" identifier ":" "ident" ;

type_declaration ::=
  [ "pub" [ "opaque" ] ] "type" upper_identifier [ type_parameters ]
  "=" [ line_end ] constructor_declaration
  { line_end "|" constructor_declaration } [ line_end deriving_clause ] ;
newtype_declaration ::=
  [ "pub" [ "opaque" ] ] "newtype" upper_identifier [ type_parameters ]
  "=" upper_identifier "(" type ")" [ line_end deriving_clause ] ;
deriving_clause ::= "deriving" "(" identifier { "," identifier } [ "," ] ")" ;
```

The list is nonempty and permits a trailing comma. The clause starts at the
logical line after its subject, as in the approved examples. Parentheses obey
Ash's existing logical-line rules. `syntax`, `derive`, and `deriving` are
contextual in these forms; the latter two remain ordinary identifiers in other
positions. The `derive: (name)` header also clearly separates the definition
from an expression macro named `derive`. Slice 1 expression matchers must end
in an expression capture, so the previously proposed derive forms were already
distinguishable by their complete headers; the parenthesized spelling provides
the same explicit category boundary as declaration syntax. The grammar adds no
attribute syntax, derive arguments, qualified
derive names, or deriving clauses to other declarations. Explicit syntax
imports and renames use CP-0033's `syntax` selector. Add
`derive_syntax_definition` to the syntax-definition alternatives accepted at
module level and to the public syntax exports selectable by that import form;
it is not a local declaration form.

At the boundary immediately following a type or newtype, `deriving (` selects
the clause before considering a declaration-macro invocation. If an imported
declaration macro is locally named `deriving` and its invocation at that
boundary begins with `(`, rename its syntax import to invoke it there. A
normal global named `deriving` followed by `:` remains an ordinary declaration.
An unknown or non-derive name inside a clause is an error at that name, with no
ordinary-declaration fallback. This precedence resolves an ambiguity introduced
by declaration macros; it must be checked against the retained slice 1 parser.

For example, `deriving ()` is invalid, `deriving (marker,)` is valid, and a
clause attached to an `interface` or a function is invalid. A syntax import can
rename a derive, and the clause uses that local spelling. A `pub opaque type`
or `pub opaque newtype` may have a clause; opacity and access to its
constructors continue to follow the ordinary rules.

## Expansion and hygiene

Each listed name resolves to an explicitly imported derive macro. The defining
module cannot invoke its own syntax definitions, as in slice 1. Process a
clause from left to right. Every derive receives the same complete original
subject, including its deriving clause, and not the declarations emitted by an
earlier derive. The original subject is retained once. Append each derive's
ordered output after it in list order; check all output using the ordinary
declaration, visibility, duplicate and implementation rules. Listing a derive
twice invokes it twice; ordinary checking rejects any conflicting output.

After applying all derives on a subject, process deriving clauses on generated
types and newtypes and any generated declaration invocations in output order,
using their own syntax contexts, before expanding the next source declaration.
The first expansion failure in this order is reported. The existing bounded
expansion policy covers recursion. If any derive or nested expansion fails, the
subject and that deriving clause's output are not published.

Caller-derived names, type parameters and constructors retain their source
contexts. Names written in a derive template keep its definition context;
local introduced helpers follow slice 1 hygiene; top-level declarations obey
ordinary duplicate-name rules. Imports and ordinary callers do not gain
access to the derive owner's private helpers. Generated `impl` versus
`pub impl` uses ordinary Ash visibility: a public implementation can be
selected by an importing module through `impl Interface`; a private one remains
local. A derive author must emit the desired form.

Diagnostics identify the relevant derive name, subject and macro definition;
errors in generated declarations also retain the relevant source origins. An
unsupported subject shape may be rejected by the derive itself. Normal Ash
resolution and type checking diagnose invalid generated declarations.

## Proposal boundaries

The preceding productions specify the derive-specific surface and reuse the
proposed shared declaration-template grammar. The indexed fixture's ordinary
Ash function bodies were checked against a stand-in syntax service, and the
generic example's body was checked against the in-progress slice 1 service.
Neither derive execution path has run. A general generic derive must reconstruct
all of its subject's parameters and constraints with correct binding contexts;
the simple declarative name binding does not do this for it. The fixture set includes opaque types, derive ordering, generated-subject
failure and unused malformed and unresolved templates. These fixed inputs still
need independent review against the proposed grammar before proposal acceptance.
