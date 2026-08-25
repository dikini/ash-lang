# Name Resolution

Name resolution gives each module, nominal type, constructor, interface,
method, anonymous implementation, requirement, type parameter, and term binder
an identity and connects every occurrence to exactly one such identity. Later
phases use identity, not source spelling or import route, to distinguish
declarations.

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
alias. It does not copy declarations or change their identities. Public globals,
nominal types, interfaces, methods, and constructors are available through
qualified occurrences such as `List.map`, `List.Option`, `List.Equal`,
`List.equal`, and `List.Some`. A qualified occurrence must use an alias bound by
an import in the same module.

A targeted import binds only the selected public spellings as unqualified
names. An `as` clause changes the local spelling without changing the imported
identity. One selector considers the term namespace, the shared
nominal-type/interface name namespace, and the constructor namespace. If a
public nominal type or interface and a constructor share the selected uppercase
spelling, the selector imports both exported declarations; constraint, type,
expression, and pattern syntax still distinguish their uses. A public method may
be targeted independently of its interface, and an interface may be targeted
without importing any method spelling. A rename changes the local spelling in
every namespace selected by that item.

The module-level term namespace contains global functions, interface methods,
and constructors. Interface spellings occupy the nominal-type name namespace,
although an interface does not denote an ordinary value type. Module aliases
occupy a distinct syntactic role but may not share their file-wide spelling
with another alias, targeted binding, or local module declaration. Imported
globals, methods, and constructors may not conflict in the expression
namespace, and imported nominal types and interfaces may not conflict in their
shared type-name namespace. A second import or later module declaration never
silently shadows an imported file-wide binding. Block-local binders retain
their ordinary lexical shadowing behavior.

A repeated module alias is rejected with
`resolve.duplicate-module-alias`. A targeted binding or other imported
file-wide binding that conflicts as described above is rejected with
`resolve.import-conflict`.

Selecting a private spelling or a spelling that the dependency does not export
is rejected with `resolve.unavailable-export`. Attempting to select or use a
constructor withheld by opacity is rejected with
`resolve.opaque-constructor`. Imports do not re-export imported bindings; only
declarations local to the module can be public.

Implementation declarations have no source spelling and cannot be qualified,
targeted, or renamed. Both complete and targeted imports establish the same
direct dependency, so either form makes every public implementation fact
defined by that dependency available. Target selectors change source names but
do not filter implementation availability. Imported implementation facts do not
enter the importer's export summary and are not re-exported to its dependents.
Alternate direct routes to one implementation identity retain one fact.

Resolution uses each already checked dependency's immutable export summary.
The summary supplies public identities, checked constrained rank-1 schemes,
accessible constructor facts, public interface and implementation facts, and
hidden identity or interface-shape facts required to close those public facts.
The compiler produces this summary after checking the module; Ash source does
not declare it. It contains no dependency body or mutable dependency scope.
Importing a scheme does not infer or generalize it again.

A public constrained global or public implementation may refer to an interface
defined by one of its module's dependencies. Its summary retains that foreign
interface's checked parameter and method shape so an importer can authenticate
the public fact. This hidden closure creates no source binding, cannot be
qualified or targeted through the summary, and may retain nominal identities
needed by method types without exporting their names or constructors. It does
not re-export any implementation fact imported from the interface's defining
module.

Imports are installed in source order. Local nominal types, interfaces,
implementations, and globals are each resolved in source order after their
module-wide identities are allocated.

## Interface, implementation, and requirement identities

Resolution allocates stable identities from canonical defining ownership and
declaration order:

- an `InterfaceId` combines the defining `ModuleId` with the interface
  declaration;
- a `MethodId` combines its `InterfaceId` with method declaration order;
- an `ImplId` combines the defining `ModuleId` with the anonymous
  implementation declaration;
- an `ImplMethodId` combines its `ImplId` with the implemented `MethodId`;
- a `RequirementId` combines its owning global `BinderId` or `ImplId` with
  requirement declaration order; and
- each implementation method receives a hidden `BinderId` qualified by its
  defining module.

Aliases, targeted renames, and alternate routes never participate in these
identities. Every interface, method, implementation, implementation method,
requirement, and hidden implementation-method binder is allocated before a
global or implementation-method body is resolved. An implementation method
head resolves its spelling to the interface's `MethodId`; it does not introduce
a lexical term binding. The hidden binder names the checked method body for
later compiler phases, not for Ash source.

An interface application is valid only in a constraint or implementation head.
Using an interface as an ordinary value type is `resolve.type-kind`. Naming a
nominal type, type parameter, or other non-interface declaration where an
interface is required is `resolve.interface-kind`.

A local interface conflicts with another interface, a nominal type, or a
file-wide module alias of the same spelling. A local method conflicts with a
global, another method, or a targeted term binding of the same spelling,
including a constructor renamed to lowercase. Interface names do not conflict
with lowercase terms or constructors in their distinct syntactic namespaces.
These conflicts use `resolve.duplicate-type`, `resolve.duplicate-global`, or
`resolve.import-conflict` according to the declarations involved.

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

An `interface` declaration without `pub` is private. Its interface spelling and
method spellings remain local to the defining module. `pub interface` exports
the interface identity, parameter, ordered methods, checked method signatures,
and their spellings as one declaration unit. A method cannot have visibility
separate from its interface. Public implementation facts are anonymous: `impl`
keeps the fact local, while `pub impl` makes the checked fact available to
direct dependents without creating an exported source name.

A public opaque type can appear by name in an importing module's annotations
and global signatures. Its constructors cannot occur there as values or
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
signature that requires that name. A diagnostic may display an occurrence as
`Carrier.<private Hidden>` to distinguish identities; this display does not add
a resolvable name.

### Interfaces over hidden and opaque carriers

Interface method access does not make a hidden carrier nameable. In this
sibling-file program, `carrier.ash` publishes an interface and an implementation
whose head retains its private nominal identity:

```ash
type Hidden = Hidden(Int)

pub interface Transform<A> {
    transform : A -> A
}

pub impl Transform<Hidden> {
    transform value = value
}

pub make : Int -> Hidden
make value = Hidden(value)

pub read : Hidden -> Int
read (Hidden value) = value
```

A complete import in `main.ash` exposes `Carrier.transform` and establishes the
direct dependency that supplies the public implementation fact. The result of
`Carrier.make` carries the same hidden nominal identity used by that fact, even
though the importer has no spelling for it:

```ash
import carrier as Carrier

main : Unit -> Int
main () = Carrier.read(Carrier.transform(Carrier.make(42)))
```

This program observes `42 : Int`. The importer cannot write `Hidden` in an
annotation, select it from `Carrier`, or use its constructor. The public
implementation exports no source name.

Opacity withholds constructors while retaining a public nominal name. The
defining `token.ash` module may use its own constructor in an implementation
body:

```ash
pub opaque type Token = Token(Int)

pub interface Equal<A> {
    equal : (A, A) -> Bool
}

pub impl Equal<Token> {
    equal (Token(left), Token(right)) = left == right
}

pub make : Int -> Token
make value = Token(value)
```

Its sibling `main.ash` can name `Token.Token`, call the public method, and use
the direct dependency's public implementation fact without gaining constructor
access:

```ash
import token as Token

main : Unit -> Bool
main () = Token.equal(Token.make(42), Token.make(42))
```

This program observes `true : Bool`. The importer cannot construct or pattern
match `Token.Token`; the implementation body remains in the defining module.

## Global scope

All global function names declared in one module form a simultaneous scope.
Each global body can refer to itself, an earlier global, or a later global in
the same module. Imported globals enter only through the qualified or targeted
bindings created by their imports; an import cycle cannot create a
cross-module recursive group.

Local implementation-method bodies join the same simultaneous module group as
ordinary globals. A source method occurrence resolves to its interface
`MethodId`, not to a particular implementation body's hidden binder. The hidden
binder preserves the body's stable identity for later phases without adding a
source-visible name.

Each global signature implicitly binds its free uppercase type names in
first-occurrence order. Those type parameters scope over that global's header,
patterns, and body. They do not enter another global signature. Thus
`identity : A -> A` declares one rank-1 type parameter without adding source
type-parameter punctuation to the function name.

Two local globals cannot have the same name. In an equational definition, the
name in the global signature must equal the name at every equation head.

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

Every resolved imported global or interface-method occurrence also retains the
exact source import binding used by that occurrence: the complete import
declaration or the targeted selector item, including a rename. This provenance
lets a diagnostic relate the route the program actually wrote when several
routes reach one identity. It does not participate in semantic identity,
implementation availability, or evidence selection.
