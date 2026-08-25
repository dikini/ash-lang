# DN-0022: Passive Static Modules

- ID: `DN-0022`
- Status: exploring
- Related: [DN-0020: Ash Dialect Milestones](DN-0020-ash-dialect-milestones.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md), [DN-0007: Data and Pattern Typing](DN-0007-data-and-pattern-typing.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), the [Mini-Ash closure report](mini-ash/closure.md), and the [passive-module evidence](modular-ash/evidence.md)

> This design note is informative. It records the exploration that led to the
> implemented passive-module increment, but it does not define current Ash.
> The [specification](../../spec/README.md) is the source of current language
> behavior.

## Question

Can Ash add passive static modules, explicit public and opaque declarations,
deterministic imports, and per-module checking while elaborating the complete
program into the existing pure Core dialect?

## Result

Yes. Modular Ash implements the recommended model: declarations-only source
modules, acyclic rooted imports, defining-file exports, generated immutable
export summaries, separate dependency-ordered checking, and assembly into one
validated pure Core program. Module syntax and access rules erase before Core;
there is no runtime module value or module Core node.

The [passive-module evidence](modular-ash/evidence.md) records the required
positive and negative cases, resource boundaries, implementation-locality
inspection, compiler verification checkpoints, and comparison with the
historical Mini-Ash tag at commit `d62d3ba`. Current semantic details belong to
the [specification](../../spec/README.md), not this retained design account.

## Context

When this note was written, Ash was the Mini-Ash dialect. One source file
contained mutually visible nominal declarations and global functions followed
by one result expression. The file could not import another source. Nominal,
constructor, term, and type-parameter identities were allocated within that
file, and resolution published one immutable registry to elaboration and Core.

The `mini-ash` Git tag retains the completed Mini-Ash implementation, tests,
specification, and evidence. The selected plan evolved current source into
Modular Ash rather than keeping Mini-Ash and Modular Ash as selectable dialects
in one compiler. Historical or differential evidence can build the tag
separately.

The closure report supplied the transferable boundary facts. Resolved and Core
registries were immutable. Nominal identities already distinguished
declarations by source. Global schemes were fully zonked before they left
elaboration. Explicit Core type abstractions and applications preserved rank-1
scope until runtime erasure. Independent Core validation already accepted
provenance from a set of source files even though the Mini-Ash driver supplied
one.

[DN-0007](DN-0007-data-and-pattern-typing.md) separates the ability to name a
nominal type from the ability to construct or deconstruct its values. Static
modules are the first source boundary that can exercise that separation.
[DN-0011](DN-0011-modules-providers-and-resolution.md) supplies later dynamic
pressure but does not require loading, providers, registration, or unloading in
this increment.

At the passive-module increment, Ash `interface` and `impl` still denoted a
future Rust-trait- or Haskell-type-class-like relationship. They were not module
signatures. That increment added modules only; interfaces and implementations
were the next candidate Modular Ash increment. They are now implemented.

## Constraints

### Keep modules passive

A module packages declarations and compile-time metadata. Importing a module
does not evaluate a file result, run initialization, register behavior, or
create a runtime module value. Modular Ash files contain declarations only.

The executable selects a local function named `main` from the entry module,
requires a monomorphic type `Unit -> R` with closed `R`, applies it to unit, and
observes the result. Imported definitions named `main` do not satisfy the entry
contract. The local `main` need not be public.

### Declare exports in the defining file

There are no source-level module signatures. A declaration's modifier controls
its public surface:

- `type` keeps the type name and constructors private;
- `pub opaque type` exports the type name and parameters but no constructors;
- `pub type` exports the type name, parameters, and complete constructor set;
- `pub` on an equational interface or `pub fn` exports a global function.

Individual constructor exports are outside the first increment. A private
nominal identity may occur in a public function type. Importers can pass values
of that hidden type among compatible imported functions, but cannot name,
construct, or deconstruct it. A public opaque type adds nameability without
revealing representation, allowing downstream modules to declare new functions
over values created through smart constructors.

### Resolve deterministic rooted paths

Each source file defines one unnamed module. It has no module header. Module
identity comes from the uniquely resolved source, not a local import alias.

A relative module path begins in the importing file's directory. For example,
`import math as Math` resolves `./math.ash`, and
`import helpers.math as Math` resolves `./helpers/math.ash`. Relative paths may
descend into child directories but cannot traverse to a parent.

An absolute module path begins with a configured named root. For example,
`import @std.collections.list as List` resolves
`collections/list.ash` beneath the `std` root. Root configuration belongs to
the tool boundary. Resolution appends the `.ash` extension, admits a canonical
source once, and rejects a path whose canonical target escapes its selected
root.

The import graph is acyclic. Cross-module recursion and strongly connected
module checking are outside the first increment.

### Keep imported names explicit

A complete import binds one qualified module alias:

```ash
import @std.collections.list as List
```

An importing module refers to public definitions through qualified names such
as `List.map` and `List.Option`.

A targeted import introduces selected exports as unqualified local names:

```ash
import @std.collections.list (map, Option as ListOption)
```

Target selection changes source visibility, not which dependency is checked or
linked. Unknown, private, duplicate, or conflicting selections are rejected.
Re-exporting an import is outside the first increment.

## Candidate directions considered

### Check modules separately and assemble one Core program

This was the recommended and selected direction. The driver builds the import
graph and processes modules in dependency order. Each checked module produces a
compiler-generated immutable export summary. Dependents resolve and type-check
against that summary rather than the dependency's private scope or body.

After every module checks, a graph-owned Core builder assembles all loaded
definitions and the generated `main ()` root in one arena. The existing pure
Core validator and evaluator consume the linked program. Module boundaries
erase after they have established source visibility and typed references.

This direction adds no persistent compiled-module format and no runtime module
node. It preserves the current Core validation and execution boundary while
making module checking real rather than a preprocessing convention.

### Compile validated Core fragments and link them

Each module could emit a persistent validated Core fragment and export summary.
A linker would combine fragments and construct the entry call. This direction
prepares for caching and separate compilation, but immediately requires an
external binder representation, fragment validation, relocation or globally
qualified handles, an object format, and linker diagnostics. No current
consumer justifies that machinery.

### Flatten sources before resolution

The loader could rename declarations and construct one synthetic source
program for the existing pipeline. This is smaller as a prototype, but privacy,
opacity, targeted imports, hidden identities, and cross-file diagnostics would
be preprocessing conventions instead of front-end invariants. It would not
provide the evidence required for module semantics.

## Selected model

### Graph loading and source admission

The tool receives an entry file and zero or more named-root mappings. Loading
resolves imports recursively, admits each canonical source once, records import
edges, and rejects cycles. Missing roots, missing files, invalid path segments,
root escapes, and duplicate root names retain the importing source as their
causal location.

Loading, cycle detection, and graph destruction must use explicit worklists
rather than host recursion at admitted graph depth.

### Module-qualified identity

Term binders, nominal types, and constructors receive identities qualified by
their defining module. Local aliases and alternate import paths cannot create a
second semantic identity for one admitted source. Existing scheme parameters
remain scoped binders and may be alpha-renamed at an import boundary.

One module's own declarations retain Mini-Ash's simultaneous global scope.
`pub` changes only what dependents can see; it does not change recursion or
visibility inside the defining module.

### Generated export summaries

The compiler publishes a module's export summary only after that complete
module resolves, type-checks, and elaborates successfully. The summary contains:

- exported global spellings, module-qualified identities, fully zonked rank-1
  schemes, and provenance;
- transparent nominal names, parameters, identities, and complete constructor
  metadata;
- opaque nominal names, parameters, and identities without constructor access;
- hidden nominal identities referenced by public schemes without a resolvable
  source name or constructor access.

Repeated occurrences of one private type across public functions retain the
same hidden identity. Imported global schemes instantiate normally and are not
re-inferred or re-generalized.

Qualified imports install one module namespace. Targeted imports install the
selected identities in their existing term, type, or constructor namespaces.
They never silently shadow another file-level binding.

Transparent imported types contribute their complete constructor set to
pattern checking and coverage. Outside its defining module, an opaque or
hidden type admits no constructor pattern. Binder and wildcard patterns remain
valid because they do not inspect representation.

### Elaboration and Core assembly

Modules elaborate in dependency order through the existing bidirectional rule
interfaces. An imported name can reach elaboration only after resolution has
authenticated it against an export summary.

A graph-owned Core builder reserves every module-qualified global binder. Each
module contributes one simultaneous group for its own globals. Dependency
groups surround dependent groups, and the linked root applies the entry
module's local `main` to unit:

```text
dependency globals
  -> dependent globals
    -> entry globals
      -> main ()
```

The linked program carries one combined internal nominal and constructor
registry and provenance from every participating source. The first increment
links all loaded definitions and performs no dead-code elimination.

Privacy and opacity are source access rules. Once resolution and elaboration
authenticate references, whole-program Core transforms may inspect private
implementations. Core gains no import, export, opacity, initialization, or
runtime module node.

### Failure behavior and resource accounting

Failures remain owned by the first stage that can establish them:

- loading owns root, path, file, canonicalization, and cycle failures;
- parsing owns import, modifier, qualified-name, and module-root grammar;
- resolution owns unknown or private exports, alias and selection conflicts,
  unavailable constructors, and binder relationships;
- elaboration owns cross-module type mismatches and imported instantiation;
- entry validation owns missing or malformed `main`;
- Core validation owns linked registry, scope, type, provenance, and dialect
  invariants.

Diagnostics relate an importing use to the exported declaration that supplied
its type. A diagnostic may render a private type as `Math.<private T>` to
distinguish identities without making the spelling resolvable in source.

The compiler reports failures deterministically in dependency and source order.
Graph-wide recovery is outside the first increment. Existing syntax, coverage,
type, Core-construction, and validation work accounting extends across the
complete module graph. Loading also bounds cumulative sources, import edges,
and path segments before retaining proportional graph state. Exact limits are
implementation resource policy, not language semantics. The implementation
supplies boundary evidence for those limits.

## Requested evidence

The note requested positive cases for:

- sibling, nested, and named-root imports;
- complete qualified and targeted renamed imports;
- a diamond graph that admits one shared module identity once;
- private, opaque, and transparent nominal types;
- a private type shared among public smart-constructor operations;
- downstream global functions over a public opaque type;
- cross-module rank-1 instantiation;
- transparent constructor construction, deconstruction, and exhaustive
  matching;
- mutually recursive globals within one module; and
- exact execution and observation of `main ()`.

It requested negative cases for:

- unknown roots, missing files, invalid segments, canonical root escapes, and
  duplicate root configuration;
- direct and indirect import cycles;
- duplicate aliases, unknown or private targeted exports, and local binding
  conflicts;
- naming a private type, constructing or matching an opaque type, and mixing
  distinct hidden nominal identities;
- missing `main`, imported-only `main`, a non-`Unit` domain, a polymorphic
  scheme, and a non-closed codomain; and
- malformed combined registries, module-qualified binder collisions, foreign
  provenance, and transformed linked Core.

The architecture evidence had to show that a dependent module resolves and
types from an immutable export summary rather than a dependency body, while the
linked Core validator still authenticates every implementation. Resource tests
had to exercise graph width, graph depth, source count, import edges, combined
registry size, and cumulative type work on a small host stack. The retained
[evidence report](modular-ash/evidence.md) records these results.

The milestone comparison built the `mini-ash` tag in an isolated worktree and
compared representative unchanged semantics. That comparison did not add the
historical dialect to current source or routine current-tree verification.

## Intentional exclusions

This increment does not add:

- Ash interfaces, `impl`, associated types, or dictionary evidence;
- individual constructor exports or import re-exports;
- parent traversal or cyclic module graphs;
- source module signatures or module headers;
- persistent compiled-module artifacts, caching, package manifests, version
  resolution, or root search order;
- module initialization, dynamic loading, unloading, runtime resolution, or
  runtime module values; or
- dead-code elimination or a core-versus-library migration.

At the passive-module checkpoint, interfaces remained the next candidate
Modular Ash increment. They are now implemented. The resulting module and
interface boundary can support the core-versus-library audit without requiring
the current source tree to keep the Mini-Ash implementation dialect.

## Resolved implementation choices

The implementation assigned structured stage-owned reason families to module,
resolution, type, entry, Core, runtime, and resource failures. It uses
compilation-local module-qualified numeric identities, graph-wide cumulative
resource budgets, and one combined internal registry assembled before Core
validation. The tool accepts named roots through repeated
`--root name=path` options. These are observed results, not design-note
authority; the specification and tool guide define the current behavior.
