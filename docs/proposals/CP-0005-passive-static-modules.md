# CP-0005: Passive Static Modules

- ID: `CP-0005`
- Status: accepted
- Related: [DN-0022: Passive Static Modules](../design/DN-0022-passive-static-modules.md), [DN-0020: Ash Dialect Milestones](../design/DN-0020-ash-dialect-milestones.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), and [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md)

> This proposal is not current Ash.

## Current behavior

Ash currently implements the Mini-Ash language defined by the
[specification](../../spec/README.md). The `ash` executable reads one UTF-8
source file. That file contains zero or more mutually visible nominal type
declarations, zero or more mutually visible global function definitions, and
one required result expression.

A source file cannot import another file, declare public or opaque definitions,
or use qualified names. Every nominal type and constructor is visible
throughout its file. Resolution creates one file-local global term scope and
one immutable nominal and constructor registry. Typed elaboration lowers the
globals and result into one pure Core program. The executable evaluates the
file result and prints its value and type.

The completed implementation, tests, specification, and evidence are retained
historically at the `mini-ash` Git tag. This proposal evolves the current source
tree; it does not add a second selectable compiler dialect.

## Proposed behavior

### Module source form

Each `.ash` source file defines one unnamed passive static module. A module
contains zero or more imports followed by zero or more nominal type declarations
and global function definitions. It has no module header, source-level module
signature, or file result expression.

The proposed module root is:

```ebnf
module ::= { import_declaration line_end } { module_declaration line_end } ;
module_declaration ::= type_declaration | global_definition ;
```

An import is compile-time composition. It does not run initialization, evaluate
a file result, register behavior, or create a runtime module value.

### Import paths and local visibility

The proposal adds the reserved words `import`, `as`, `pub`, and `opaque`, plus
the punctuation `@` and `.`. Module path segments use ordinary lowercase
identifiers. A module alias uses an uppercase identifier.

```ebnf
import_declaration ::=
    "import" module_path
    ( "as" upper_identifier | "(" import_item { "," import_item } ")" ) ;
module_path ::= relative_module_path | absolute_module_path ;
relative_module_path ::= identifier { "." identifier } ;
absolute_module_path ::= "@" identifier "." identifier { "." identifier } ;
import_item ::= import_name [ "as" import_name ] ;
import_name ::= identifier | upper_identifier ;
```

A relative path begins in the importing source's directory. Its segments map to
child directories and a final `.ash` file. Thus `import math as Math` resolves
`./math.ash`, while `import helpers.math as Math` resolves
`./helpers/math.ash`.

An absolute path begins at a configured named module root. For example,
`import @std.collections.list as List` resolves
`collections/list.ash` beneath the configured `std` root. The tool accepts
repeatable `--root name=path` arguments. The entry file's containing directory
is its implicit root for relative imports. A module reached through a named root
retains that root for its relative descendants.

Paths contain no extension syntax, empty segment, current-directory segment, or
parent segment. The loader canonicalizes each configured root and target,
rejects a target outside its owning root, and admits one canonical source once.
Overlapping named roots and alternate paths to one canonical source do not
create distinct module identities.

A complete import binds the dependency's public namespace under its alias:

```ash
import @std.collections.list as List
```

Public terms, types, and constructors are then available through qualified
names such as `List.map`, `List.Option`, and `List.Some`. Qualification does not
open private declarations.

A targeted import binds only selected public spellings as unqualified names:

```ash
import @std.collections.list (map, Option as ListOption, Some)
```

One selector imports every public identity with that spelling into its existing
namespace. If a type and constructor intentionally share one uppercase
spelling, the selector imports both; syntactic context continues to distinguish
them. A rename changes that spelling in every imported namespace selected by
the item.

Module aliases and targeted imports occupy file-wide namespaces. A duplicate
alias, duplicate targeted binding, conflict with another import, or conflict
with a local declaration is rejected. Imports do not silently shadow file-wide
bindings. Imports cannot be re-exported in this proposal.

The complete import graph must be acyclic. A module can use only dependencies
reachable through its own imports. Mutual visibility and recursion remain
available among globals declared within one module, but not across an import
cycle.

### Public, private, and opaque declarations

An unmodified declaration is private to its defining module.

```ash
type Hidden = Hidden(Int)

hidden_step : Hidden -> Hidden
hidden_step value = value
```

The proposal extends declaration syntax as follows:

```ebnf
type_declaration ::=
  [ "pub" [ "opaque" ] ]
  "type" upper_identifier [ type_parameters ] "=" [ line_end ]
  constructor_declaration { line_end "|" constructor_declaration } ;
equational_global ::=
  [ "pub" ] external_interface line_end equation { line_end equation } ;
inline_operational_global ::=
  [ "pub" ] "fn" identifier "(" typed_pattern { "," typed_pattern } ")"
  "->" type block ;
```

`opaque` is valid only in `pub opaque type`. The three nominal visibility modes
are:

- `type` exports neither the nominal name nor its constructors;
- `pub opaque type` exports the nominal name, identity, kind, and parameters,
  but no constructor;
- `pub type` exports the nominal name and its complete constructor set.

Individual constructor visibility is not configurable. Inside the defining
module, all constructors remain available regardless of the type's public
mode.

An equational function is public when `pub` precedes its external interface.
Its equation heads do not repeat `pub`. An inline operational function is
public when declared with `pub fn`.

A public function scheme may contain a private nominal identity. Importers do
not receive a source name or constructor for that type, but every occurrence of
the same hidden identity remains equal across the defining module's public
schemes. An importer may therefore obtain, retain in inferred local bindings,
and pass such values among compatible imported functions. It cannot mention
the type in an annotation or declare a global whose interface requires that
name.

A public opaque type is nameable in downstream type annotations and global
interfaces. Its constructors remain unavailable in terms and patterns. This
supports downstream functions over values created through public smart
constructors without exposing representation.

A public transparent type contributes its complete constructor set to term
resolution, pattern checking, irrefutability, and coverage in an importer.
Opaque and hidden types contribute no constructor patterns outside the defining
module. Binder and wildcard patterns remain available because they do not
inspect representation.

### Generated export summaries and checking

The compiler derives an immutable export summary after one complete module
resolves and type-checks. This summary is compiler data, not Ash source and not
a separately declared module signature.

The summary contains public global identities and fully zonked rank-1 schemes,
public nominal identities and parameters, transparent constructor metadata,
opaque access facts, hidden nominal identities referenced by public schemes,
and causal provenance. It may retain withheld spellings solely to distinguish
an unavailable private export in diagnostics; those spellings never enter an
importer's name environment.

Modules are checked in dependency order. Resolution and elaboration consume
dependency summaries rather than dependency private scopes or bodies. Imported
polymorphic globals and constructors instantiate according to the existing
rank-1 rules. Importing does not re-infer or re-generalize an exported scheme.

Term binders, nominal types, and constructors are qualified by their defining
module identity. Module identity follows the uniquely admitted canonical source
within one compilation, not an import alias or display path spelling.

### Entry and execution

The source path passed to `ash` is the entry module. The entry module must
declare exactly one local global named `main`. An imported or qualified `main`
does not satisfy this requirement.

The scheme for `main` must be monomorphic and have the form `Unit -> R`, where
`R` is closed after elaboration. `R` may be any current closed Ash type. `main`
need not be public.

After all modules check, the compiler assembles their global definition groups
and a generated application of the entry `main` to unit into one pure Core
program. Dependency groups surround dependent groups. The linked program uses
one combined internal nominal and constructor registry and retains provenance
from every admitted source.

Module visibility and opacity are source access rules. They erase after
resolution and typed elaboration authenticate every reference. Core receives no
module, import, export, opacity, initialization, or runtime-loading node. The
existing independent Core validator checks the linked program before the
existing evaluator evaluates `main ()`. The tool prints the resulting value and
closed type through the existing observation format.

The first implementation links every loaded definition. Reachability-based
linking and dead-code elimination are not observable language semantics and are
outside this proposal's evidence boundary.

### Failures

The implementation must retain structured stage ownership for module failures.
Stable reason families include:

- `module.unknown-root`, `module.not-found`, `module.path-escape`, and
  `module.import-cycle` for source-caused graph loading failures;
- parser-owned expected-token or expected-form reasons for malformed imports,
  modifiers, paths, and qualified names;
- `resolve.duplicate-module-alias`, `resolve.unavailable-export`,
  `resolve.import-conflict`, and `resolve.opaque-constructor` for name and access
  failures;
- existing type mismatch and instantiation reasons for cross-module typing;
- `entry.missing-main`, `entry.main-polymorphic`, `entry.main-domain`, and
  `entry.main-open-result` for the entry contract.

Duplicate or malformed `--root` configuration is an invocation failure rather
than an Ash source rejection. A missing file, unknown root, escape, or cycle
caused by an import is a source rejection with the import occurrence as its
primary location. Cross-module diagnostics relate an importing occurrence to
the exported declaration that supplied its type.

A diagnostic may display a hidden identity as `Math.<private T>` to distinguish
it from another hidden type. Diagnostic display does not make the private
spelling resolvable.

The compiler reports the first deterministic failure in dependency and source
order after retaining the existing independent lexical and parser diagnostics
for the affected source. Graph-wide semantic recovery is not proposed.

## Semantic delta

The source unit changes from one complete program with a result expression to
one passive declarations-only module. A complete program becomes the acyclic
transitive closure of one entry module's imports plus a generated call to its
local `main`.

Name resolution gains module-qualified identities, qualified and targeted
imports, public export boundaries, hidden private identities, and opaque
constructor access. Type checking gains dependency summaries but retains the
existing rank-1 schemes, instantiation, unification, pattern, and coverage
rules. Dynamic expression evaluation is unchanged; only the program root is
constructed from `main ()` instead of a file result expression.

The current source tree stops accepting Mini-Ash file roots when this complete
proposal lands. The historical `mini-ash` tag remains the retained runnable
Mini-Ash dialect.

## Affected specification areas

- [Lexical structure](../../spec/lexical-structure.md) changes reserved words,
  punctuation, qualified names, and module path tokens.
- [Syntax](../../spec/syntax.md) replaces the program root, adds imports and
  declaration modifiers, and admits qualified occurrences.
- [Name resolution](../../spec/name-resolution.md) adds module identity,
  import scopes, export access, opacity, and cross-module diagnostics.
- [Static semantics](../../spec/static-semantics.md) replaces file-global
  program checking with dependency-ordered module checking, export summaries,
  and the `main` contract.
- [Elaboration](../../spec/elaboration.md) defines module erasure, linked global
  groups, hidden and opaque registry facts, and generated `main ()`.
- [Dynamic semantics](../../spec/dynamic-semantics.md) replaces the initial file
  result with the generated entry application while retaining expression
  reduction.
- [The `ash` executable](../tools/ash.md) changes invocation, module roots,
  input loading, failures, and entry observation.

## Resulting specification truth

After implementation, tests, and specification changes merge together, Ash is
a pure, rank-1, modular language. One executable program is an acyclic graph of
passive source modules. Imports expose only declarations made public by their
defining module. Public opaque types are nameable without constructor access,
while private identities may flow through public schemes without becoming
nameable. Every module is checked from immutable dependency summaries, module
structure erases into validated pure Core, and execution observes `main ()` from
the entry module.

## Interactions

The proposal preserves Mini-Ash expression, pattern, function, recursion,
nominal data, coverage, rank-1, Core, validation, transform, and evaluation
semantics inside each module. Existing nominal equality by declaration identity
extends across module-qualified identities rather than comparing exported
spellings or representations.

Public hidden and opaque types exercise the access distinctions anticipated by
[DN-0007](../design/DN-0007-data-and-pattern-typing.md). Constructors remain
ordinary polymorphic values when access permits them.

This proposal deliberately precedes Ash interfaces and `impl`. A later proposal
may package interface declarations and implementations in these passive modules
and may use generated export summaries for separate constraint checking. It
must not reinterpret module export summaries as source module signatures.

The later core-versus-library audit may change current source or Core behavior
without keeping a compatibility path for Mini-Ash. Historical comparison builds
the `mini-ash` tag separately.

## Non-goals

This proposal does not add:

- interfaces, `impl`, associated types, constraints, or dictionary evidence;
- individual constructor exports or import re-exports;
- parent traversal, import cycles, or cross-module recursive groups;
- source module signatures, module declarations, or module values;
- package manifests, versions, root search order, or dependency acquisition;
- persistent compiled-module artifacts, incremental caching, or separate object
  linking;
- initialization, dynamic loading, unloading, runtime discovery, providers,
  registration, or effects;
- dead-code elimination or a core-versus-library migration; or
- a current-tree Mini-Ash compatibility dialect.

## Required evidence

Implementation must provide:

- exact lexer, parser, concrete-tree, projection, and recovery cases for every
  import, modifier, path, qualified-name, and declarations-only root form;
- sibling, nested, named-root, full qualified, targeted, and renamed import
  cases;
- canonical duplicate admission and a diamond graph that shares one module
  identity;
- direct and indirect cycle rejection, unknown root, missing file, root escape,
  malformed configuration, alias collision, unavailable export, and targeted
  binding conflict cases;
- private, opaque, and transparent nominal cases, including smart constructors,
  downstream functions over a named opaque type, hidden-type composition,
  hidden-identity mismatch, opaque construction and pattern rejection, and
  transparent exhaustive matching;
- cross-module rank-1 instantiation without exported inference variables or
  re-generalization;
- evidence that dependent resolution and typing consume immutable export
  summaries rather than dependency bodies;
- exact valid and invalid `main` cases and exact CLI observation of `main ()`;
- module-qualified binder, combined registry, multi-source provenance,
  transformed Core, independent validation, and evaluation cases;
- graph-wide source, edge, path, syntax, coverage, type, Core, and validation
  resource boundaries with explicit worklists and small-stack tests;
- implementation-locality evidence at the accepted parser, resolver,
  elaborator, and Core assembly boundaries;
- a complete specification replacement, executable examples, tool
  documentation, reason-code review, relative-link review, and authority review;
- `cargo xtask verify` with no failure; and
- a bounded milestone comparison that builds the `mini-ash` tag separately for
  representative unchanged expression semantics without adding the historical
  compiler to current verification.
