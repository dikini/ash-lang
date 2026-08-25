# CP-0008: Explicit Implementation Imports and Re-exports

- ID: `CP-0008`
- Status: accepted
- Related: [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [DN-0022: Passive Static Modules](../design/DN-0022-passive-static-modules.md), [DN-0023: Interfaces and Implementations](../design/DN-0023-interfaces-and-implementations.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), and [TASK-0015: Implement Explicit Implementation Imports and Re-exports](../tasks/TASK-0015-implement-explicit-implementation-imports-and-reexports.md)

> This proposal is not current Ash until the complete change is integrated into
> `main`.

## Current behavior

The [current specification](../../spec/README.md) defines Modular Ash. A
complete import binds one dependency's public namespaces under a local module
alias. A targeted import binds selected public spellings, with optional local
renaming. Either form creates a direct dependency and makes every public
implementation declared by that dependency available in the importing module.
Name selectors do not filter implementation availability.

Imported names and implementations are not re-exported. A generated body-free
summary publishes only public declarations owned by its module, plus hidden
identity and interface facts needed to close those declarations. Imported
implementation facts remain available only across their direct edge.

Interface evidence is selected during checking, retained on its source
occurrence, authenticated after module linking, and lowered to ordinary Core
type and term applications. The linked validator authenticates an imported
implementation against its defining direct dependency.

## Proposed behavior

### Surface forms

Imports remain a prefix of each passive module. Private imports retain complete
and targeted forms. A public import must be targeted:

```ebnf
import_declaration ::=
    "import" module_path
      ( "as" upper_identifier | targeted_import )
  | "pub" "import" module_path targeted_import ;
targeted_import ::=
  "(" import_item { "," import_item } ")" ;
import_item ::=
    import_name [ "as" import_name ]
  | "impl" upper_identifier ;
```

A name item retains the current namespace selection and optional local alias.
An implementation item cannot be renamed. Its uppercase spelling must select a
public interface in that dependency's summary.

Names and implementation availability are independent channels:

```ash
import equality (Equal, equal)
```

This import binds the interface and method but imports no implementation.

```ash
import equality (impl Equal)
```

This import makes the dependency's public `Equal` implementations available
without binding `Equal` or its methods as source names.

A qualified import acquires no implementations. Source that needs qualified
names and evidence uses a second targeted import:

```ash
import equality as Equality
import equality (impl Equal)
```

A public targeted import also adds each selected channel to its module's public
summary:

```ash
pub import equality (Equal, equal, impl Equal)
```

The public name entries use their selected local spellings. The declarations
retain their original binder, nominal, constructor, interface, and method
identities. Every public implementation fact exported for the selected
`InterfaceId` becomes locally available and enters the re-exporting module's
public implementation closure. It retains its original `ImplId` and method
binders. The re-exporting module adds an authorization route rather than a new
declaration.

### Selection, closure, and summaries

A module's effective implementation environment contains all local
implementations and only explicitly selected imported implementations. Neither
a complete import nor a targeted name item implies implementation selection.

An implementation selector operates on the dependency's public implementation
closure. Re-export closures therefore compose transitively. Reaching one
`ImplId` through more than one selected route retains one fact. Distinct
implementations for the same interface continue to undergo the current
full-head overlap check. The first module whose effective environment combines
overlapping implementations owns the failure and publishes no summary.

A checked public summary may contain public names and implementations owned by
an earlier module. It retains the hidden nominal and interface facts needed to
authenticate those exports without creating another source binding. Existing
privacy and opacity rules continue to govern name access. A public
implementation whose head contains a private nominal identity may carry that
identity as hidden metadata without exporting its spelling or constructors.

Each imported or re-exported fact records an authorization route from the
current module through its immediate dependency. A route preserves the original
declaration identity and every summary edge that authorized it. Multiple routes
to one identity select a shortest route; equal-length routes use dependency
order, then import and selector source order. Dependency order is the explicit
ordinal in the resolver's dependency-summary input; import and selector order
use their source ordinals within that input. These transient ranks choose the
current module's winner and do not enter public authorization data. When the
ranks converge on alternate suffixes, stable route identity is the
lexicographic sequence of graph-local `(from ModuleId, to ModuleId, import byte
range)` hop keys. Neither `ModuleId` nor process-global source allocation acts
as an order rank, and hash-map iteration does not participate.

Effective availability and public authorization choose routes independently.
The effective winner may come from any explicit selector. The public winner may
come only from a public selector, so a shorter private import cannot authorize a
re-export. An empty public authorization denotes only a public implementation
declared by the publishing module; a private local implementation never enters
a public summary.

### Checking, validation, and lowering

Resolution owns source bindings, interface-selector identity, availability of
the selected public export, and staged re-export candidates. Interface checking
owns the effective implementation closure and overlap. Summary construction
publishes no re-export until the module has checked completely.

Linked-evidence validation authenticates an imported implementation against
the complete recorded route through the immediate dependency's checked
summary. A valid `ImplId` without that authorization is an internal
`evidence.validation.*` failure. Validation does not select another candidate.
It authenticates every module's local implementation inventory and public
authorization table before validating occurrence availability through those
tables.

After validation, existing evidence lowering erases interface,
implementation, and authorization-route metadata. The result uses the original
ordinary Core binders, type applications, and term applications. This proposal
adds no Core node, runtime module, dictionary value, registry, or lookup rule.

The existing graph-wide type and interface-constraint budgets span selector
processing, imported-closure construction, summary closure, evidence
selection, and linked authorization validation. Re-export traversal uses the
acyclic source-module graph and does not introduce an independent recursion or
resource boundary.

## Semantic delta

Public implementation availability becomes explicit and transitive instead of
automatic and direct-only. Every existing cross-module use of a public
implementation must add an `impl Interface` selector on an authorizing import
route.

Targeted public imports add source-visible name re-exports and public
implementation re-exports. Re-exported facts preserve defining identities;
the facade contributes only selected spelling and authorization provenance.

Local implementations remain available in their defining module. Import
aliases, selected name aliases, and alternate routes still do not participate
in semantic declaration identity.

## Affected specification areas

- [Syntax grammar](../../spec/syntax.md#grammar)
- [Name-resolution imports and namespaces](../../spec/name-resolution.md#imports-and-namespaces)
- [Name-resolution public and private declarations](../../spec/name-resolution.md#public-private-and-opaque-declarations)
- [Interfaces and constrained schemes](../../spec/static-semantics.md#interfaces-and-constrained-schemes)
- [Implementations](../../spec/static-semantics.md#implementations)
- [Constraint satisfaction and checked evidence](../../spec/static-semantics.md#constraint-satisfaction-and-checked-evidence)
- [Globals and modules](../../spec/static-semantics.md#globals-and-modules)
- [Failure ownership and constraint resources](../../spec/static-semantics.md#failure-ownership-and-constraint-resources)
- [Module linking and entry generation](../../spec/elaboration.md#module-linking-and-entry-generation)
- [Interface-evidence lowering](../../spec/elaboration.md#interface-evidence-lowering)
- [Specification overview](../../spec/README.md)

## Resulting specification truth

An import makes implementation facts available only through explicit
implementation selectors. A targeted public import re-exports selected names
and implementation facts through separate channels. Transitive routes preserve
the defining identities and authorize use through checked summaries.

One module checks the deduplicated union of its local and explicitly selected
implementations. Evidence selection remains deterministic under scoped
coherence. Linked validation authenticates every retained selection through
its exact local or import/re-export route before unchanged Core lowering.

## Interactions

This change establishes the implementation-visibility closure that later
multi-parameter interfaces, determination rules, associated outputs, and
defaults will use. Those later features may add coherence rules, but they do
not need to replace this route or identity model.

Targeted name re-exports preserve the current namespace distinctions. A name
alias changes only the facade's public spelling. An implementation selector
still resolves the dependency's interface spelling and does not create a term
or type binding.

The change intentionally breaks current source that relies on automatic
implementation availability. The migration is mechanical when the required
interface is already known: add `impl Interface` to a targeted import, or add a
second targeted import beside a qualified import. An omitted selector owns an
ordinary unsatisfied-constraint diagnostic at the source occurrence.

Public summary closure may carry a private nominal identity or hidden interface
shape already permitted by current Ash. It does not weaken opacity, grant
constructor access, turn interfaces into module signatures, or recheck an
imported scheme.

## Non-goals

This proposal does not add:

- public module aliases, wildcard re-exports, or whole-module re-exports;
- individual implementation names, implementation-head selectors, or selector
  renaming;
- higher-kinded parameters, method-local type parameters, multi-parameter
  interfaces, associated outputs, functional dependencies, or defaults;
- fallback implementations or specialization;
- packages, version resolution, caches, persistent artifacts, or separate
  linking;
- module signatures, parent traversal, module cycles, dynamic loading, or
  runtime interface lookup; or
- a new Core node, runtime dictionary, or interface registry.

## Required evidence

- Parser and projection tests cover private and public targeted imports, mixed
  name and implementation items, malformed selectors, forbidden selector
  renaming, forbidden public qualified imports, recovery, spans, and import
  ordering.
- Resolution tests prove name-only, implementation-only, combined,
  private-only, and public re-export behavior as independent channels.
- A three-module definition, facade, and application program passes the public
  driver. Removing the application's implementation selector retains the name
  binding and produces the existing structured unsatisfied-constraint reason.
- Transitive and diamond source cases preserve original declaration
  identities, deduplicate one `ImplId`, and choose deterministic shortest
  provenance. The orphan rule and acyclic module graph make valid
  distinct-module overlapping public implementations unreachable in source;
  a structurally assembled checked-closure fixture therefore proves that the
  first combined effective closure rejects distinct overlapping facts.
- Alias, alternate-route, hidden-carrier, opaque-type, private-export, orphan,
  and conflict cases preserve current visibility, ownership, and failure
  boundaries.
- Exact-budget and deep-graph cases cover selector expansion, closure
  construction, summary retention, evidence selection, linked route
  validation, and small-stack destruction.
- Tampering tests reject a valid implementation identity carried through an
  unauthorized or inconsistent route before Core synthesis.
- Core inspection proves that direct and facade selection use the original
  method binders and existing type and term applications. Evaluation agrees and
  adds no runtime lookup or registry behavior.
- The migration corpus adds explicit selectors to every existing
  cross-module implementation use and retains a negative witness that ordinary
  imports no longer make implementations available.
- The implementation, specification, tool documentation, retained evidence,
  diagnostics, and development trajectory agree. Focused verification and
  `cargo xtask verify` pass before the increment closes.
