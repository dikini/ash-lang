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

An ordinary absolute path starts at a configured named module root. For example,
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

### Compiler-owned cell module

`@builtin.cell` denotes one compiler-owned module, without a configured root
or filesystem source. `builtin` is a reserved root name: configuring it as a
filesystem root fails with `invocation.reserved-root` before filesystem
inspection. The modules specified beneath that root are `@builtin.cell`,
`@builtin.bytes`, `@builtin.string` and `@builtin.foreign`. Unknown paths, including
`@builtin.cell.extra`, fail
with `module.unknown-builtin`.

The module exports exactly `Handle`, `Provider`, `Ops`, `read` and `write`.
Complete imports, targeted imports, renaming and public re-exports preserve
their defining identities. Direct and facade routes reach the same module;
a facade creates no additional provider authority. An ordinary file named
`cell.ash` or copied API declarations have no compiler-owned origin.

A module containing a `resource cell` expression must directly import `@builtin.cell`.
Either a complete or targeted import satisfies this requirement, independently
of which public names the targeted import selects. Importing only a facade
does not; resolution reports `resolve.resource-builtin-required`. Helpers that
do not acquire a resource may use the ordinary re-exported API.

`Handle` has no source-accessible constructor or pattern. Source `impl` and
local `with` declarations cannot introduce the exact builtin `Provider`
relation. Acquisition introduces its authenticated lexical evidence; ordinary
name resolution or copied signatures cannot grant that authority.

### Ordinary native-buffer library

`libraries/native_buffer.ash` is an ordinary passive source module. A configured
root may expose it as `@ffi.native_buffer`; the root name and file basename grant
no compiler authority. Imports, renaming and public re-exports preserve its
original resource family, sealed provider and ordinary result identities.
`resource Buffer.Buffer<R> b = length { body }` resolves that declared family
through the imported alias. A facade may re-export the original declaration;
no direct builtin import is required. Copied API names or equal function shapes
do not supply the original resource header or provider.

The former `@builtin.native_buffer` path is unknown. The lowercase
`resource native_buffer` designator is no longer a builtin resource form.

### Compiler-owned foreign result module

`@builtin.foreign` is admitted once per compilation graph and has no runtime
initialization. Its public `ConversionError` is an opaque ordinary nominal
type with no source-accessible constructors. Its other public declarations
are ordinary transparent data types with one kind-`Type` parameter each:

| Type | Constructors |
| --- | --- |
| `Call<T>` | `Returned(T)` and `ConversionFailed(ConversionError)` |
| `Output<T>` | `Unreadable` and `Readable(T)` |
| `Nullable<T>` | `Null` and `NonNull(T)` |
| `Disposition<T>` | `Consumed(T)`, `Retained(T)` and `BlockedDependent` |

Complete and targeted imports, aliases and re-exports preserve those nominal
and constructor identities. Ordinary same-spelled declarations do not supply
the canonical native result codec. Constructing an ordinary result grants no
native interpreter, ownership or access permission.

### Source foreign-library identities

A foreign library introduces a defining native-library identity without a
nested source namespace. Each admitted symbol introduces a module-owned native
effect with one `call` operation. Symbols share the ordinary effect spelling
namespace and inherit the library's publication mode. Foreign representations
occupy an ABI namespace and introduce no ordinary Ash type. An owner member
introduces a constructor-free nominal state family in the ordinary type
namespace. Its original ordered formal records, explicit owned position,
representation and teardown reference remain associated with the defining
library. Libraries in one module require disjoint member spellings.

Imports and re-exports preserve the original effect, operation, library and
contract identities. Summaries retain descriptors only with selected or
signature-referenced effect facts. A private native effect referenced by a
public signature remains a hidden checking fact; it does not become an
exported source spelling. Display aliases do not replace defining provenance
or result-codec authority.

### Source resource families

A source resource declaration introduces a family in the type namespace. Its
identity is distinct from every instance identity and from a foreign owner
state family. The complete written parameter vector scopes over the header,
acquire and finish clauses, and handler clauses. `owned` must select one of
those parameters with kind `Type`; its position need not be first. The single
parameter introduced by `result ... for <Answer>` scopes over that result type
only. Lifecycle and handler patterns retain their ordinary binding behavior.

Public imports and targeted re-exports retain the original family identity,
complete parameter vector and body-free header, including all exact native
interpretations and defining provenance. A display alias cannot change the
owned position, argument tags or native symbol identity. Source resource code
travels as the original checked defining code through compiler preparation;
an export summary neither contains that code nor grants execution permission.
Private header dependencies retain checking identity without becoming public
source names.

The current publication checkpoint requires a provider interface declared
beside a public source resource to be public. Its shared-interface closure can
retain imported hidden interface facts, but cannot yet retain a same-module
private provider interface. This is an implementation limitation, not a new
visibility rule for resource declarations.

## Imports and namespaces

A complete import binds the dependency's public namespaces under its uppercase
alias. It does not copy declarations or change their identities. Public globals,
nominal types, resource families, interfaces, effects, methods, operations, and constructors are
available through qualified occurrences such as `List.map`, `List.Option`,
`List.Equal`, `List.State`, `List.State.get`, `List.equal`, and `List.Some`. A
qualified occurrence must use an alias bound by an import in the same module. A
complete import is private and selects no implementation facts.

Hook and registration targets use these same effect names and defining
identities, including through renaming and public re-export. There is no
separate hook namespace or compiler-owned hook module. Importing a hook API or
transformer makes it available but installs no registration.

A targeted name item binds only the selected public spelling as an unqualified
name. An `as` clause changes the local spelling without changing the imported
identity. One name item considers the term namespace, the shared
nominal-type/interface/effect name namespace, and the constructor namespace. If
a public nominal type, interface, or effect and a constructor share the selected
uppercase spelling, the item imports both exported declarations; constraint,
type, effect, expression, and pattern syntax still distinguish their uses. A
public method may be targeted independently of its interface, and an interface
may be targeted without importing any method spelling. A rename changes the
local spelling in every namespace selected by that item.

A targeted implementation item has the form `impl Interface`. Resolution uses
the uppercase spelling in the dependency's public interface namespace and
selects every public implementation fact for that exact `InterfaceId` from the
dependency summary's public implementation closure. The item binds no source
name and cannot be renamed. A qualified import and a targeted name item select
no implementation facts. Conversely, an implementation item does not bind the
interface or any method spelling.

Every import establishes one direct dependency regardless of which channel it
selects. A private targeted import makes its selected names and implementation
facts available only in the importing module. A public import must be targeted.
It creates the same local bindings and implementation availability, then stages
each selected name under its local spelling and each selected implementation
fact for the module's checked public summary. Re-exporting a name preserves its
original global binder, nominal, constructor, interface, effect, method, or
operation identity. Re-exporting an implementation preserves its original
`ImplId`, checked head,
prerequisites, method identities, and defining method binders. A facade creates
no forwarding declaration or implementation.

The module-level term namespace contains global functions, interface methods,
and constructors. Interface and effect spellings occupy the nominal-type name
namespace, although neither denotes an ordinary value type. Operations remain
inside their owning effect and do not enter the module-level term namespace.
Module aliases occupy a distinct syntactic role but may not share their
file-wide spelling with another alias, targeted binding, or local module
declaration. Imported
globals, methods, and constructors may not conflict in the expression
namespace, and imported nominal types, interfaces, and effects may not conflict
in their shared uppercase namespace. A second import or later module
declaration never
silently shadows an imported file-wide binding. Block-local binders retain
their ordinary lexical shadowing behavior.

A repeated module alias is rejected with
`resolve.duplicate-module-alias`. A targeted binding or other imported
file-wide binding that conflicts as described above is rejected with
`resolve.import-conflict`.

Selecting a private spelling or a spelling that the dependency does not export
is rejected with `resolve.unavailable-export`. Attempting to select or use a
constructor withheld by opacity is rejected with
`resolve.opaque-constructor`. An implementation item whose spelling is absent,
private, or names a public non-interface declaration is rejected with the
corresponding unavailable-export or interface-kind reason. The failed item does
not bind the interface spelling.

One stable implementation identity reached through several selected routes is
retained once. Each retained imported or re-exported fact carries an
authorization route whose first hop is the current module's exact import edge
and whose suffix is the dependency summary's authorization for that fact. A
local implementation has an empty route. A nonempty route preserves every
summary edge back to the defining module; it does not change declaration
ownership.

For one identity, the shortest route wins. Equal-length routes use dependency
order, then import source order, then selector source order. These ranks choose
the current winner but do not enter a public authorization route. If the ranks
are equal, the lexicographic sequence of graph-local `(from ModuleId, to
ModuleId, import byte range)` hop keys breaks the tie. `ModuleId` participates
only inside that final graph-local hop key; it does not replace dependency,
import, or selector rank. Process-global source allocation and hash-map
iteration do not choose a route.

Effective availability and public authorization choose routes independently.
Any explicit implementation item may supply the effective winner. Only a
public item may supply the public winner, so a shorter private route cannot
authorize a re-export. An empty public authorization denotes a public local
implementation. A private local implementation never enters the public
implementation closure.

Resolution uses each already checked dependency's immutable export summary.
The summary supplies public local and re-exported names under their selected
spellings, checked constrained rank-1 schemes with kinded binders, accessible
constructor and effect-operation facts, the public implementation closure with
authorization routes, and hidden kind, identity, interface-shape, or
effect-signature facts required to close those public facts. The compiler
produces this source-body-free summary only after
checking the complete module; Ash source does not declare it. It contains no
dependency source body, implementation source body, forwarding declaration,
or mutable dependency scope. Importing a scheme does not infer or generalize
it again.
Exported function values also retain compiler-inferred control summaries for
capture checking. These summaries describe possible calls, requests and handler
control; they do not import dependency source bodies. Admission authenticates
their defining function identity and retained type and effect identities.

Summary admission authenticates every retained type-variable identity against
one defining kinded binder record and derives each nominal constructor kind
from its ordered parameter records before the dependency facts enter local
resolution. Resolution preserves those identities and kinds. Qualification,
targeted renaming, opacity, re-export, and another path through a dependency
diamond cannot recompute a kind or replace a defining record with a local one.
For each public method scheme, admission also authenticates the complete
method-parameter set, written order, method owner, kinds, body scope, identity,
and provenance. A dependent checks from that body-free fact without importing
the interface or implementation body.

For each public effect, admission authenticates its defining module, ordered
parameters, `EffectId`, ordered operation signatures, and `OperationId` values.
A dependent preserves those facts without importing an effect body or creating
a local identity.

A public constrained global, public implementation, or re-exported fact may
refer to declarations defined by an earlier module. The summary retains the
foreign interface's checked ordered parameter records, optional determinant
positions, and method shape, plus any nominal or constructor identities needed
to authenticate and type those public facts.
This hidden closure creates no source binding, cannot be qualified or targeted
through the summary, and does not export a hidden spelling or constructor.
Privacy and opacity therefore remain properties of source access even when a
public scheme or implementation route carries the hidden identity.

For a `newtype`, that authenticated closure also retains the declaration kind,
owner, ordered parameter identities and kinds, sole same-spelled constructor,
canonical representation and provenance, and constructor access. A transparent
projection exposes the constructor and representation facts needed for source
wrapping and matching. An opaque projection exposes the nominal identity and
parameters but withholds the constructor and representation. A private
declaration exposes no name. The hidden canonical fact remains available to
linking for all three modes, but it creates no source name, constructor access,
coercion, or interface evidence. Alias and diamond routes must agree on the
same defining fact.

The following three sibling modules demonstrate a targeted public name
re-export. `arithmetic.ash` defines the original binder:

```ash
pub answer : Unit -> Int
answer () = 42
```

`facade.ash` re-exports it under a new public spelling:

```ash
pub import arithmetic (answer as facade_answer)
```

The entry selects that spelling without creating a facade definition:

```ash
import facade (facade_answer)

main : Unit -> Int
main () = facade_answer(())
```

The program observes `42 : Int`, and `facade_answer` resolves to the binder
defined by `arithmetic.ash`.

Name selection alone does not admit evidence. In this entry, both `Equal` and
`equal` resolve, but the method obligation is `constraint.unsatisfied` because
the import contains no `impl Equal` item:

```ash
import equality (Equal, equal)

main : Unit -> Bool
main () = equal(1, 1)
```

The sibling `equality.ash` does publish an implementation:

```ash
pub interface Equal<A> {
    equal : (A, A) -> Bool
}

pub impl Equal<Int> {
    equal (left, right) = left == right
}
```

The missing selector, not the implementation declaration, owns the absence
from the entry's effective environment. Adding `impl Equal` to the targeted
list makes that fact available without changing the two name bindings.

Imports are installed in source order. Nominal types, interfaces, effects,
implementations, and globals share one interleaved local declaration order.
Resolution allocates declaration identities before resolving bodies, and
allocates local type-variable identities in that declaration order as
described below.

## Interface, implementation, and requirement identities

Resolution allocates stable identities from canonical defining ownership and
declaration order:

- an `InterfaceId` combines the defining `ModuleId` with the interface
  declaration;
- a `MethodId` combines its `InterfaceId` with method declaration order;
- an `EffectId` combines the defining `ModuleId` with effect declaration order;
- an `OperationId` combines its `EffectId` with operation declaration order;
- an `ImplId` combines the defining `ModuleId` with the anonymous
  implementation declaration;
- an `ImplMethodId` combines its `ImplId` with the implemented `MethodId`;
- a `RequirementId` combines its owning global `BinderId` or `ImplId` with
  requirement declaration order;
- a `LexicalEvidenceId` combines the defining `ModuleId` with the local
  evidence declaration's source order; and
- each implementation method receives a hidden `BinderId` qualified by its
  defining module.

Aliases, targeted renames, imports, and re-exports preserve `EffectId` and
`OperationId`. An effect instance is the exact pair of one `EffectId` and its
ordered type arguments; equal source spellings or separately declared effects
do not make instances equal. Effect visibility is whole-API visibility: a
public effect exposes all of its operation signatures, while a private effect
exposes none. An operation cannot be imported or renamed independently of its
owner.

Aliases, targeted renames, and alternate routes never participate in these
identities. Every interface, method, effect, operation, implementation,
implementation method, requirement, and hidden implementation-method binder is
allocated before a global or implementation-method body is resolved. An
implementation method head resolves its spelling to the interface's `MethodId`;
it does not introduce a lexical term binding. The hidden binder names the
checked method body for later compiler phases, not for Ash source.

An interface application is valid in a constraint, implementation head, or
local evidence header.
It retains the complete ordered argument vector. Arity and positional kinds are
checked later; resolution does not discard a dependent argument.
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

A local effect conflicts with a nominal type, interface, effect, targeted
uppercase binding, or module alias of the same spelling. Two operations in one
effect cannot share a spelling. Operations do not conflict with module-level
lowercase terms because operation references resolve through their owning
effect.

## Type binder identity and scope

The defining resolved binder record owns the spelling, source origin, and
canonical kind of each `TypeVariableId`. A type occurrence retains that
identity instead of copying an independently authoritative kind. Resolution
allocates source-origin type-variable identities from one module-wide sequence
in declaration source order, then in binder encounter order within each
declaration. Interleaving a nominal type, interface, effect, implementation, or
global
therefore does not regroup its binders by declaration family. Free type-name
candidates later rejected by the interface method or implementation
prerequisite rules retain the same encounter order, but their allocation does
not make them valid binders.

A local `newtype` allocates its written type parameters in the same
module-wide sequence when resolution reaches the declaration. These parameters
scope only over its representation and retain their declared order and kinds.
The nominal itself is a rigid declaration identity, not a type-variable binder.

A resource acquisition allocates its identity binder in the same module-wide
type-variable sequence after resolving its initializer. The binder has kind
`Type` and scopes over the resource body only. It is distinct from enclosing
type parameters and other acquisition binders, regardless of spelling.

Nominal and ordinary effect parameters use their written set and order and may be
phantom. Effect parameters scope over all operation signatures in their
declaration and cannot have kind `EffectRow`. An interface has a nonempty
ordered written parameter vector. A kind annotation fixes its binder's kind;
an omitted annotation fixes it at `Type`.

Native symbol and source resource parameters retain their complete written
Type/Row vector, including parameters with no ABI operand. An owner state
family retains its own ordered nominal parameters; the current canonical owner
checkpoint admits only `Type` formals. These distinct inventories are not
collapsed into a Type-only vector for source effect identity.

For an interface declaration, binder encounter order starts with the interface
parameters in written order, then visits methods in declaration order and each
method's explicit parameters in written order. The interface parameters and
one method's local parameters scope over that method signature only. The
optional determination edge resolves only parameter names from that same interface declaration.
Its names do not introduce binders. An implementation equation does not inherit
the interface or method-parameter spellings from the interface it implements.

A local evidence method likewise does not inherit those spellings. Each
supplied method receives independent contextual rigid parameters in its
interface method's declared order and kinds. Their identities belong to that
supplied method, including when methods of the same interface nest. They do
not enter its body's source type namespace; an enclosing type name keeps its
meaning. The local evidence header introduces no type parameters.

An explicit global parameter list is an ordered bijection with the free type
variables of the global's value type and requirements. The written order is
the outer scheme order and scopes over the complete header, patterns, and body.
An explicit implementation parameter list is an ordered bijection with the
free variables across its complete head argument vector. Its written order is
the implementation head-parameter order and scopes over the head,
prerequisites, and method bodies. Every prerequisite variable must belong to
that complete head set; a variable
that is unlisted and occurs only in a prerequisite remains
`impl.prerequisite-variable`. Listing such a variable does not add it to the
head's free-variable set and instead makes that explicit binder unused.

A row tail resolves only to a global parameter or eligible generalized-local
parameter of kind `EffectRow`. Explicit global parameters state that kind;
omitted global parameters follow the existing first-occurrence policy across
the complete computation type and requirements. A row-tail occurrence does not
resolve as an ordinary value type, nominal argument, interface argument, or
pattern type.

An absent method parameter list binds no method-local parameter.
A present method parameter list is an ordered bijection with the method type's
free variables other than the interface parameters. Its binders must be
distinct from every interface parameter and one another, every listed binder
must occur in the method type, and written order becomes method-scheme order.

A duplicate explicit binder, including a method binder that repeats an
interface parameter, is `resolve.duplicate-type-parameter`; a listed binder
absent from the global's value type and requirements, the implementation head,
or its method type is `resolve.unused-type-parameter`; and an unlisted free
header or method name under an explicit list is `resolve.unknown-type`. With an
absent method list, another free type variable remains
`interface.method-parameter`. Requirement determination is a later static rule;
resolution retains requirement-only variables admitted by a total interface
edge.

When a global omits its parameter list, first occurrences in its value type
come first, followed by first occurrences found only in its requirements. When
an implementation omits its list, first occurrences across its complete head
argument vector become its parameters. A method list is never implicit. Every
omitted declaration kind annotation and every binder introduced by an omitted
implementation binder list is fixed to `Type`. An omitted global list
discovers ordinary free type variables and effect-row-tail variables in their
shared first-occurrence order. A name occurring only in ordinary type positions
has kind `Type`; one occurring only as an effect-row tail has kind `EffectRow`;
using the same name in both roles is invalid. Ash does not infer a function
kind from use. This is the current phase-dependent language constraint, not a
commitment against a later bounded declaration-local inference rule.

The executable test `resolution_binder_policies_are_executable_and_ordered`
checks written order, first-occurrence order, omitted kinds, phantom nominal
parameters, and both global presentations:

```ash
type Phantom<Unused, A> = Phantom(A)
type Pair<Left, Right> = Pair(Left, Right)

interface Witness<Value> {
    witness : Value -> Bool
}

ordered<B, A> : A -> B -> A
ordered left right = left

fn operational<D, C>(left : C, right : D) -> C {
    left
}

legacy : Y -> X -> Y
legacy left right = left

impl<F, E> Witness<Pair<E, F>> {
    witness value = true
}

impl Witness<(S, R)> {
    witness value = true
}

main : Unit -> Int
main () = 42
```

## Type and constructor scope

All module-level nominal data and `newtype` declarations in one module are mutually visible,
including in their own and earlier constructor payloads or representations.
Resolution allocates each nominal identity in cross-declaration source order
before resolving any payload or representation type. Two module-level nominal
declarations cannot share a spelling.

A module-level `newtype` receives the same module-owned nominal and constructor identity forms
as ordinary data. It has exactly one constructor under its owner. Resolution
requires that constructor's spelling to equal the nominal spelling; a mismatch
is `resolve.newtype-constructor-name` at the constructor spelling. Imports,
renames, re-exports, and facade diamonds preserve both defining identities.
Equal spellings or equal representations from separate declarations do not
make their identities equal.

Every constructor receives a stable identity under its owning nominal type.
Module-level constructors form one module-wide term namespace and must have distinct
spellings across those declarations. Constructor names do not conflict
with ordinary lowercase term names unless an import rename gives them the same
spelling. A type occurrence must name a local or imported nominal type, an
in-scope type parameter, or one of `Int`, `Bool`, and `Unit`. An uppercase term
or pattern occurrence must name an accessible local or imported constructor.

A parameterized nominal declaration makes its distinct kinded parameters
visible throughout that declaration's constructor payloads or representation
and nowhere else. A declaration cannot repeat a parameter spelling. A
parameter shadows a same-spelled unqualified nominal type inside its
declaration.

The source tree retains a named type application with its argument vector and
spans. Resolution admits a nominal constructor or in-scope type parameter as
the head, then folds the arguments left into repeated unary applications. For
example, `F<A, B>` resolves as
`Application(Application(F, A), B)`, with one provenance step and argument span
per fold. A bare nominal constructor or type parameter remains its resolved
identity; resolution does not require saturation and does not reject a
parameter merely because it occurs in function position. [Static
semantics](static-semantics.md) derives the kind of the bare, partial, or
saturated result and owns any application-kind failure.

A block `newtype` instead receives
one stable, module-qualified lexical nominal identity per source declaration.
Lexical and module ownership are distinct. Equal names, parameter lists, or
representations do not equate declarations. Repeated execution of a block,
function, generalized binding, or recursive member reuses that declaration's
identity; it does not allocate a runtime identity. The constructor keeps the
same owner-and-ordinal relationship and same-spelling requirement as a module
`newtype`. Lexical facts are not module declarations or importable names.

## Public, private, and opaque declarations

Declaration visibility affects access from other modules, not scope inside the
defining module. The three ordinary-data visibility modes are:

- `type` exports neither the nominal name nor any constructor;
- `pub opaque type` exports the nominal name, identity, arity, and parameters,
  but no constructor; and
- `pub type` exports the nominal name and its complete constructor set.

All three modes leave the type name and constructors available inside the
defining module. Individual constructors cannot have separate visibility.

The corresponding `newtype` modes are:

- `newtype` exports neither the nominal name nor its constructor;
- `pub opaque newtype` exports the nominal name, identity, arity, and
  parameters but withholds the constructor; and
- `pub newtype` exports the nominal name and its sole constructor.

All three leave the constructor available in the defining module. Its
visibility is not independent of the declaration.

An `interface` declaration without `pub` is private. Its interface spelling and
method spellings remain local to the defining module. `pub interface` exports
the interface identity, ordered parameter records, optional determinant
positions, ordered methods, ordered method-parameter records, checked method
signatures, and their spellings as one declaration unit. A method cannot have visibility
separate from its interface. Public implementation facts are anonymous: `impl`
keeps the fact local, while `pub impl` places the checked fact in its module's
public implementation closure without creating an exported source name. A
dependent obtains that fact only through an explicit implementation item. A
targeted public implementation item may authorize later dependents to select
the same fact transitively.

A public opaque nominal can appear by name in an importing module's annotations
and global signatures. Its constructors cannot occur there as values or
patterns, whether targeted or qualified. Importers may define new functions
over the named type and obtain values from exported operations without
inspecting its data or newtype representation.

A public transparent data type makes its constructors available as values and
patterns. A public transparent `newtype` likewise makes its sole constructor
available for explicit wrapping and matching. Constructor identities and
payload or representation types remain those of the defining module. Renaming
or reaching the same declaration through another route preserves those
identities. Equal spellings or representations from different declarations do
not make their nominal or constructor identities equal.

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

A complete import in `main.ash` exposes `Carrier.transform`; the separate
implementation item selects the public fact. The result of `Carrier.make`
carries the same hidden nominal identity used by that fact, even though the
importer has no spelling for it:

```ash
import carrier as Carrier
import carrier (impl Transform)

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

Its sibling `main.ash` can name `Token.Token`, call the public method, and
select the public implementation fact without gaining constructor access:

```ash
import token as Token
import token (impl Equal)

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

Each global uses either the complete explicit parameter list or the omitted
list's first-occurrence rule defined in [Type binder identity and
scope](#type-binder-identity-and-scope). Its type parameters do not enter
another global signature. Thus `identity : A -> A` declares one rank-1
kind-`Type` parameter without adding source type-parameter punctuation to the
function name, while `identity<A> : A -> A` states the same binder explicitly.

Two local globals cannot have the same name. In an equational definition, the
name in the global signature must equal the name at every equation head.

## Local scope

A block resolves its bindings from left to right. A local initializer uses the
scope before its binder, so the binding is nonrecursive. The binder is visible
in later bindings and in the block result. A local may shadow an earlier local,
global, or targeted import. The stable identities keep the definitions
distinct.

A local `newtype` installs its nominal name and constructor together for the
following declarations and block result.
The representation sees the preceding lexical type scope and its own parameters.
It may use an enclosing type parameter or preceding nominal. It cannot refer to
itself or a later local declaration. If it shadows an earlier nominal, the
earlier identity remains the meaning of that spelling in its representation.
Later local declarations may shadow earlier local or module nominal and
constructor bindings. Both preceding name bindings are restored when the block ends.

A local `newtype` cannot be a member of a `let rec` group. A following recursive
term group may use its nominal name and constructor. Local nominal declarations
do not form recursive groups.

A resource initializer resolves in the preceding term and type scopes. The
acquisition's identity and handle binders then enter scope together for its
body block and may shadow earlier names. Neither binder is visible in its own
initializer or after the resource expression. Closing the body restores the
preceding scopes. The handle is an ordinary term binder, not a release owner.
For a source family, resolution checks the complete written argument vector
against the retained header and identifies the fresh binder at the explicit
owned position. Every other Type or Row actual resolves in the preceding type
scope. The fresh identity cannot occur in those actuals or in its initializer.

The target of `hook` or `register` resolves as an exact effect instance in the
preceding type scope. A registration's transformer resolves in the preceding
term and type scopes, before its body. Resolution retains the generated
handler's compiler-owned identity and the lexical registration-owner relation;
neither form introduces a source-visible term or type binder. Their body blocks retain
the surrounding clause's resume scope. A transformer function is an ordinary
function and cannot capture that clause's resume capability.

A cleanup action resolves in the preceding term and type scopes, before its
body block. Resolution retains its hidden callback binding and lexical cleanup
owner relation; neither introduces a source-visible binder or namespace. The
body retains the surrounding clause's resume scope. An action function remains
an ordinary function and cannot capture the enclosing clause's resume capability.

Each local `with` declaration receives its own `LexicalEvidenceId` and hidden
method binders when resolution reaches it. It creates no source-visible term
binding. Its method heads identify interface methods; method bodies resolve
under the preceding term and type scopes. They may capture preceding ordinary
values or recursive functions, but gain no self or sibling binding from the
declaration. Checking admits the source only for the following block remainder.
Local evidence identities and their methods are not exported or imported.

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

Each handler clause receives one hidden `ResumeId` owned by that clause. The
clause's operation pattern and resume capability scope only over its body;
`resume` or `discard` outside such a scope is
`effect.resume-outside-clause`. Both forms name that same hidden capability.
A nested handler's handled expression remains in the outer clause scope.
Each nested handler clause receives its own resume scope and cannot use the
outer capability. Nested functions, recursive members, and supplied local
evidence methods cannot capture a
resume capability; static semantics owns the non-escape and exactly-once
checks.

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
name routes reach one identity. It does not participate in semantic identity,
implementation availability, or evidence selection.

Selected implementation facts separately retain the chosen authorization
route. Overlap and selected-prerequisite diagnostics use its import hops in
order. The route authenticates availability and supplies causal labels; it does
not become part of the implementation identity.
