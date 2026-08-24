# Name Resolution

Name resolution gives each module, definition, constructor, type parameter, and
term binder an identity and connects every occurrence to exactly one such
identity. Later phases use identity, not source spelling or import route, to
distinguish declarations.

## Module paths and identity

The source path passed to an Ash tool is the entry module. Its containing
directory is the implicit root for that module and its relative imports. A
relative module path starts in the importing source's directory. Its segments
name child directories and a final `.ash` file. Thus `import math as Math`
resolves `./math.ash`, while `import helpers.math as Math` resolves
`./helpers/math.ash`.

An absolute path starts at a configured named module root. For example,
`import @std.collections.list as List` resolves `collections/list.ash` beneath
the configured `std` root. A module reached through a named root retains that
root as an owner for its relative descendants.

The loader canonicalizes roots and imported targets. A target must remain
inside its owning root. Each canonical source is admitted once and receives one
identity that remains stable and unique within that compilation. Different
aliases, relative and absolute routes, symbolic-link routes, or overlapping
named roots to the same canonical source do not create another module identity.

A canonical source reached through more than one root retains every owning
root. Each of its relative descendants must remain inside every retained root,
regardless of the order in which routes to that source are discovered.

The complete dependency graph must be acyclic. A module may use only the
dependencies named by its own imports. Checked modules are ordered with every
dependency before its dependents. Dependency order and import source order
select the first reported failure deterministically.

## Imports and namespaces

A complete import binds the dependency's public namespaces under its uppercase
alias. It does not copy declarations or change their identities. Public terms,
types, and constructors are available through qualified occurrences such as
`List.map`, `List.Option`, and `List.Some`. A qualified occurrence must use an
alias bound by an import in the same module.

A targeted import binds only the selected public spellings as unqualified
names. An `as` clause changes the local spelling without changing the imported
identity. One selector considers the term, nominal-type, and constructor
namespaces. If a public type and constructor share the selected uppercase
spelling, the selector imports both; type, expression, and pattern syntax still
distinguish their uses. A rename changes the local spelling in every namespace
selected by that item.

The module-level term namespace contains global functions and constructors.
The nominal-type namespace is distinct, so one selector may bind a same-spelled
type and constructor. Module aliases occupy a distinct syntactic role but may
not share their file-wide spelling with another alias, targeted binding, or
local module declaration. Imported terms and constructors may not conflict in
the expression namespace, and imported types may not conflict in the type
namespace. A second import or later module declaration never silently shadows
an imported file-wide binding. Block-local binders retain their ordinary
lexical shadowing behavior.

A repeated module alias is rejected with
`resolve.duplicate-module-alias`. A targeted binding or other imported
file-wide binding that conflicts as described above is rejected with
`resolve.import-conflict`.

Selecting a private spelling or a spelling that the dependency does not export
is rejected with `resolve.unavailable-export`. Attempting to select or use a
constructor withheld by opacity is rejected with
`resolve.opaque-constructor`. Imports do not re-export imported bindings; only
declarations local to the module can be public.

Resolution uses each already checked dependency's immutable export summary.
The summary supplies public identities, checked rank-1 schemes, accessible
constructor facts, and hidden identity facts required by those schemes. It
contains no dependency body or mutable dependency scope. Importing a scheme
does not infer or generalize it again. Imports are installed in source order;
local type declarations and global declarations are each resolved in source
order after their module-wide identities are allocated.

## Type and constructor scope

All nominal type declarations in one module are mutually visible, including in
their own and earlier constructor payloads. Resolution allocates each nominal
identity in source order before resolving any payload type. Two local type
declarations cannot share a spelling.

Every constructor receives a stable identity under its owning nominal type.
Local constructors form one module-wide term namespace and must have distinct
spellings across all local declarations. Constructor names do not conflict
with ordinary lowercase term names unless an import rename gives them the same
spelling. A type occurrence must name a local or imported nominal type, an
in-scope type parameter, or one of `Int`, `Bool`, and `Unit`. An uppercase term
or pattern occurrence must name an accessible local or imported constructor.

A parameterized nominal declaration allocates distinct type-parameter
identities in source order. Those parameters are visible throughout that
declaration's constructor payloads and nowhere else. A declaration cannot
repeat a parameter spelling. A parameter shadows a same-spelled unqualified
nominal type inside its declaration. Because every parameter has kind `Type`,
applying it as a type constructor is rejected with `resolve.type-kind`. A
nominal type application must supply exactly the declaration's arity; bare and
partially applied nominal constructors are rejected with
`resolve.type-argument-count`.

## Public, private, and opaque declarations

Declaration visibility affects access from other modules, not scope inside the
defining module. The three nominal visibility modes are:

- `type` exports neither the nominal name nor any constructor;
- `pub opaque type` exports the nominal name, identity, arity, and parameters,
  but no constructor; and
- `pub type` exports the nominal name and its complete constructor set.

All three modes leave the type name and constructors available inside the
defining module. Individual constructors cannot have separate visibility.

A public opaque type can appear by name in an importing module's annotations
and global interfaces. Its constructors cannot occur there as values or
patterns, whether targeted or qualified. Importers may define new functions
over the named type and obtain values from exported smart constructors without
inspecting its representation.

A public transparent type makes its constructors available as values and
patterns. Constructor identities and payload types remain those of the defining
module. Renaming or reaching the same declaration through another route
preserves those identities. Equal spellings or representations from different
declarations do not make their nominal or constructor identities equal.

A public global scheme may contain a private nominal identity from its defining
module. The identity remains the same wherever it occurs in that module's
public schemes, but importers receive neither its source type name nor any
constructor. An importer may infer a local binding for such a value and pass it
among imported functions whose schemes contain the same identity. It cannot
name the hidden type in an annotation or write a new module-level global
interface that requires that name. A diagnostic may display an occurrence as
`Carrier.<private Hidden>` to distinguish identities; this display does not add
a resolvable name.

## Global scope

All global function names declared in one module form a simultaneous scope.
Each global body can refer to itself, an earlier global, or a later global in
the same module. Imported globals enter only through the qualified or targeted
bindings created by their imports; an import cycle cannot create a
cross-module recursive group.

Each global interface implicitly binds its free uppercase type names in
first-occurrence order. Those type parameters scope over that global's header,
patterns, and body. They do not enter another global interface. Thus
`identity : A -> A` declares one rank-1 type parameter without adding source
type-parameter punctuation to the function name.

Two local globals cannot have the same name. In an equational definition, the
name in the external interface must equal the name at every equation head.

## Local scope

A block resolves its bindings from left to right. A local initializer uses the
scope before its binder, so the binding is nonrecursive. The binder is visible
in later bindings and in the block result. A local may shadow an earlier local,
global, or targeted import. The stable identities keep the definitions
distinct.

A `let rec ... and ...` group allocates every member identity before resolving
any initializer. Every initializer therefore sees all members, and all members
remain visible in the following block remainder. A member may shadow an outer
binder, but two members of one group cannot have the same spelling.

A function parameter is visible only in its body and may shadow an outer
binder. Parentheses and other grouping syntax do not introduce a scope.

Pattern binders enter scope together after the complete pattern resolves. A
spelling cannot occur twice in one pattern. Match-arm binders are visible only
in that arm body. Equation-pattern binders are visible only in their clause
body. A local `let` pattern contributes its binders to the later block
remainder, not to its initializer.

Forward references exist only among globals declared in one module and members
of one explicit local recursive group. An ordinary `let` does not see itself or
a later local declaration.

The executable test `resolution_global_recursive_scope_example_is_executable`
checks mutual visibility across the two global presentations in a complete
entry module:

```ash
first : Unit -> Int
first ignored = second ()

fn second(ignored : Unit) -> Int {
    let retain : Unit -> Int = fn(value) {
        first value
    }
    42
}

main : Unit -> Int
main () = first ()
```

## Unresolved names

Every occurrence must resolve. The executable test
`resolution_unknown_name_example_has_its_documented_reason` checks that this
complete entry module is rejected with `resolve.unknown-name`:

```ash
main : Unit -> Int
main () = missing 1
```

A diagnostic may suggest an in-scope name only when its spelling justifies that
suggestion. Suggestions do not change resolution. Cross-module diagnostics
retain the importing occurrence as their primary location. A cross-module type
diagnostic also relates the exported declaration that supplied the imported
type.
