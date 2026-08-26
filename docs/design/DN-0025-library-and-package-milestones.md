# DN-0025: Library and Package Milestones

- ID: `DN-0025`
- Status: exploring
- Related: [DN-0020: Ash Dialect Milestones](DN-0020-ash-dialect-milestones.md), [DN-0022: Passive Static Modules](DN-0022-passive-static-modules.md), [DN-0023: Interfaces and Implementations](DN-0023-interfaces-and-implementations.md), [DN-0019: Primitive Feature Composition](DN-0019-primitive-feature-composition.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [CP-0008: Explicit Implementation Imports and Re-exports](../proposals/CP-0008-explicit-implementation-imports-and-reexports.md), the [explicit-import evidence](lib-ash/imports-evidence.md), the [core-and-library audit](modular-ash/core-library-evidence.md), and the [Modular Ash closure report](modular-ash/closure.md)

> This design note is informative. It does not define current Ash, accept
> language semantics, or accept a package or artifact architecture.

## Question

Which work should close Modular Ash, which language and library capabilities
belong in its first descendant, and which package and compiled-artifact
capabilities require a later milestone?

## Current boundary

The [current specification](../../spec/README.md) defines the first `lib-ash`
increment on the completed Modular Ash base. It has passive acyclic source
modules, public and private declarations, opaque type exports, qualified and
targeted imports, targeted public name and implementation re-exports,
compiler-generated body-free export summaries, method-only single-parameter
interfaces, explicit implementation selection, authenticated transitive
authorization routes, explicit evidence lowering, and one linked typed Core
program. Interfaces are not module signatures. Persistent compiled modules,
package resolution, and separate object linking remain outside current Ash.

The `mini-ash` Git tag retains Mini-Ash as a historical runnable dialect.
Current source does not carry a second grammar or compiler path for it.
[DN-0020](DN-0020-ash-dialect-milestones.md) records the completed separately
authorized core-versus-library audit and simplification analysis. The paired
[audit](modular-ash/core-library-evidence.md) and
[closure report](modular-ash/closure.md) retain that final milestone
checkpoint. Task and plan cleanup, repeated root verification, independent
reviews, and the closure commit completed the lifecycle mechanics. The
annotated `modular-ash` tag retains that commit. None of those mechanics added
language work.

The proposed type-system additions cross parsing, name resolution, kind and
type checking, implementation selection, export summaries, linked-evidence
validation, and Core elaboration. Package and artifact work crosses module
identity, graph loading, compiler inputs, persistence, linker validation,
diagnostics, and resource limits. Combining both sets in one milestone would
make failures harder to attribute.

## Leading milestone sequence

The leading sequence has three stages:

```text
modular-ash -> lib-ash -> pack-ash
```

### `modular-ash`

Modular Ash is complete at its final milestone checkpoint. The retained
core-versus-library audit, simplification analysis, module and interface
evidence, and closure report establish the boundary. The annotated
`modular-ash` tag retains the final verified closure commit.
No proposed type-system, re-export, package, cache, or linker mechanism entered
that closure.

### `lib-ash`

The first bounded `lib-ash` increment is complete: implementation
availability is explicit, and targeted imports can re-export selected names and
implementation authorizations. The retained
[evidence report](lib-ash/imports-evidence.md) records its reviewed boundary.
The complete milestone remains open. Later proposals may add the language
mechanisms needed to define stronger libraries: higher-kinded parameters,
method-local type parameters, multi-parameter interfaces, associated outputs
or relational determination, and method and associated-type defaults.

### `pack-ash`

After `lib-ash` stabilizes its summaries and identities, explore and, through
later decisions and tasks, add package manifests, exact version resolution, a
compiler-private cache, separate compiled-module linking, and a distributable
artifact format pinned to the `pack-ash` milestone.

This sequence avoids extending `modular-ash` indefinitely. It also avoids
freezing a package artifact around public-summary semantics that `lib-ash`
would immediately change.

## Prepared `lib-ash` sequence

Planning detail decreases after the first increment. Each later semantic
increment requires its own accepted proposal and task, and evidence may split,
narrow, reorder, or remove it.

1. Replace automatic direct-import implementation availability with explicit
   implementation selectors. Add targeted name and implementation re-exports,
   transitive authorization routes, and a migration corpus. This completed
   first increment was accepted by
   [CP-0008](../proposals/CP-0008-explicit-implementation-imports-and-reexports.md)
   and is retained by the
   [explicit-import evidence report](lib-ash/imports-evidence.md).
2. Add explicit `Type` and function kinds and higher-kinded parameters without
   kind inference or kind polymorphism. Make checking, summaries,
   substitution, and independent Core validation kind-aware.
3. Add method-local type parameters. Keep ordinary source rank-1 and admit
   polymorphic term slots only as authenticated compiler-generated interface
   evidence.
4. Compare multi-parameter interfaces, associated outputs, and functional
   dependencies on one corpus. Retain only source forms that improve
   expressiveness or diagnostics, and make equivalent relationships converge
   on one canonical determination model and Core shape.
5. Add method defaults after method evidence is stable. Add associated-output
   defaults only if the comparison retains associated outputs. Lower defaults
   through generated adapters rather than runtime dictionaries.
6. Close `lib-ash` with its combined library corpus, summary and identity
   audit, Core-versus-library simplification analysis, resource verification,
   specification review, migration verification, and one retained linked Core
   program.

The first increment establishes the visibility and coherence closure used by
later multi-parameter and determination work. `pack-ash` remains separate
until the complete `lib-ash` milestone stabilizes those summaries and
identities.

## `lib-ash` type and interface model

### Kinds and higher-kinded parameters

The initial kind language contains `Type` and function kinds. Ordinary type
parameters default to `Type`; a parameter used as a constructor requires an
explicit kind such as `Type -> Type`. The design does not initially infer kinds
or support kind polymorphism.

Nominal constructors receive derived kinds. An unsaturated constructor is
valid only where the expected kind admits it. Every value-level expression
still has a type of kind `Type`.

Core must retain enough information to check this boundary independently.
Type binders carry kinds, and type abstraction, application, substitution, and
validation are kind-aware. A value binder's type must still have kind `Type`.

Methods may bind explicit rank-1 type parameters. For example, this
illustrative declaration requires both a higher-kinded interface parameter and
method-local parameters:

```ash
interface Functor<F : Type -> Type> {
    map<A, B> : (A -> B, F<A>) -> F<B>
}
```

This does not add source syntax for higher-rank values. A polymorphic interface
method does, however, require compiler-generated higher-rank evidence. For
`Functor<F>`, the method slot has a type shaped like
`forall A B. (A -> B, F<A>) -> F<B>`. A constrained function receives that
polymorphic slot, and a default adapter passes it to the default binder.

Core therefore admits polymorphic term parameters only in authenticated
compiler-generated evidence positions during this increment. Independent Core
validation checks that the nested scheme agrees with its `MethodId`; ordinary
Ash annotations cannot introduce, accept, or return such a value. This keeps
the source language rank-1 without pretending that polymorphic dictionaries
are ordinary monomorphic functions.

### Canonical determination model

Associated types and functional dependencies must not become independent
solvers. Every interface declaration produces one canonical checked model:

```text
explicit parameters
associated outputs
determination edges
methods and defaults
```

For example, the following schematic declaration has three explicit
parameters, one associated output, and one explicit determination edge:

```ash
interface Decode<Format, Source, Value>
    where (Format, Source) -> Value
{
    type Error
    decode : (Format, Source) -> Result<Value, Error>
}
```

The explicit edge determines `Value` from `(Format, Source)`. The complete
interface argument tuple determines `Error`, so transitive closure also
determines `Error` from `(Format, Source)`.

The initial source roles remain disjoint:

- functional dependencies relate explicit interface parameters;
- associated types introduce named outputs;
- each associated output is implicitly determined by the complete interface
  argument tuple plus any local associated-family parameters;
- one output cannot appear both as an explicit parameter and as an associated
  type; and
- functional-dependency clauses cannot name associated outputs.

A later design may add syntax for an associated output with a smaller
determinant set. It should not overload the initial functional-dependency
syntax before examples justify the interaction.

Method use must remain deterministic before evidence selection. The explicit
interface parameters that occur in a method's ordinary type form its syntactic
seed set. Associated projections do not reveal their own determinants. Closing
the seed set under the interface's determination edges must cover every
explicit interface argument needed for selection. Otherwise the interface
declaration is rejected. At a particular occurrence, ordinary checking may
still leave a seed parameter ambiguous; selection then waits and reports
ambiguity if the surrounding arguments or expected type do not resolve it. An
explicit interface-application syntax could relax this rule later; the initial
design does not add one.

Inference first performs ordinary kind-aware unification. When a determinant
tuple contains no unsolved inference variable, matching that tuple against
visible implementations may fill its dependent arguments; coherence guarantees
that every match agrees on those arguments. This improvement does not select
method evidence until the complete goal has one full-head candidate. Equal
visible constraints for the same interface and determinant tuple also equate
their dependent tuples. The solver never guesses a determinant, reverses an
edge, or uses a dependent output to choose among unknown inputs. Abstract
requirements already supply their complete explicit interface arguments.

Coverage and coherence use the same relation for generic and ground
implementations. For every determination edge `X -> Y`, the checker first makes
two independently alpha-freshened instances of one implementation head,
normalizes their terminating projections, and unifies their `X` tuples. Their
`Y` tuples must then be definitionally equal under the resulting substitution.
This self-comparison rejects a head such as `C<Int, B>` when the interface says
its first parameter determines `B`.

The checker then applies the same comparison to every pair of distinct visible
implementations. Ordinary full-head overlap remains a separate error. This
rejects, for example, separate `Convert<Int, Bool>` and
`Convert<Int, String>` implementations when the interface declares its first
parameter determines its second.

A public multi-parameter implementation satisfies the orphan rule when its
interface is local or a local outer nominal constructor occurs in a determinant
set whose closure determines the complete explicit interface head. Without a
smaller declared determinant, the complete head is that set. Scoped import and
re-export closures determine which pairs undergo overlap and determination
checks; unrelated branches do not acquire global coherence.

Determination metadata uses declaration-position sets sorted lexicographically
and removes duplicate edges. Closure may contain redundant or cyclic edges, but
those edges do not add evidence binders or change declaration order.

The associated and relational source forms should be compared on the same
programs before both are retained. Equivalent relationships should lower to
the same explicit Core type parameters and evidence shape, up to alpha-renaming
of generated binders. If one source form adds no useful expressive or
diagnostic power, `lib-ash` should omit it.

### Associated outputs and Core

Concrete associated projections may normalize during checking. Abstract
projections in constrained public declarations cannot always normalize to a
nominal type before Core. Elaboration therefore makes the determined output an
explicit Core type parameter.

Schematically:

```ash
forall I. Iterator<I> => I -> Option<Iterator<I>.Item>
```

lowers to a Core shape equivalent to:

```text
forall I Item. (I -> Option<Item>) -> I -> Option<Item>
```

Concrete selection supplies the output type arguments and then the method
evidence. Associated-type and functional-dependency forms therefore need no
distinct runtime representation.

### Termination and canonical goals

Projection normalization uses canonical goals consisting of the associated
output identity and normalized argument tuple. Merely detecting an identical
active projection is insufficient because an equation can grow its arguments.

The checker builds the dependency graph induced by associated equations and
defaults in the current visible closure. Each checked summary retains its
dependency transitions so an importer can recheck a larger combined closure.
An edge between different acyclic components may preserve argument size. Every
edge within a recursive component must make a syntactically checkable
strict-subterm decrease in the ordered argument tuple for every substitution.
The checker rejects an equation when it cannot establish that decrease. This
conservative size-change condition permits acyclic aliases and structurally
recursive families but rejects growing projection chains.

Implementation prerequisites use the same normalized argument order. A
generic prerequisite must be strictly smaller than its implementation head
under the fixed structural multiset order. A ground prerequisite may rely on
canonical active-goal cycle detection. An unresolved projection cannot
participate in the measure. One driver-owned constraint budget spans
normalization, improvement, candidate matching, prerequisite traversal, and
evidence construction; exhaustion does not stand in for a termination rule.

## Defaults and implementation completion

Resolution allocates all method and associated-output identities before it
checks defaults. Declaration order determines identity but not source
visibility among interface members.

A default associated equation is kind-checked. It may refer to interface
parameters, its own family parameters, and other associated projections.
It must satisfy the projection dependency and decrease rule. Normalization also
tracks canonical active projections and rejects concrete cycles. A public
interface summary retains the checked equation and its verified dependency
facts.

A default method body is checked once in the interface-owning module under:

- the interface parameters and their kinds;
- method-local type parameters;
- abstract associated outputs; and
- abstract evidence for the interface methods.

The export summary retains the checked scheme and binder identity, not the
method body. The defining module's compiled fragment retains the body.

Each implementation member is either explicit or supplied by one default.
Missing, duplicate, and extra members are errors. Defaults do not create
implementation candidates, fallback implementations, or specialization.

An implementation using a method default receives a generated adapter. The
adapter applies the interface arguments, associated-output arguments, and final
method functions to the interface-owned default binder. Explicit methods and
generated adapters form the implementation's recursive Core group. This lets a
default call required, defaulted, or overridden methods without a runtime
interface object.

Implementation completion proceeds in this order:

1. admit explicit associated equations;
2. fill missing equations from defaults;
3. kind-check completed outputs;
4. verify projection dependencies, decrease, and cycle freedom;
5. check canonical determination consistency; and
6. check implementation method bodies.

Checked evidence carries every explicit interface argument once in declaration
order, every associated output once in declaration order, and every method slot
once in declaration order. A polymorphic method occupies one slot with its
complete checked scheme. Determination edges are metadata and add no duplicate
type binder. A failure in any member, default, equation, determination, or
evidence fact makes the implementation summary unavailable as a whole.

## Name and implementation re-exports

Names and implementation availability remain separate semantic channels. One
import or re-export declaration may select both, but selecting one does not
imply the other. The prepared first increment uses a targeted public import:

```ash
pub import equality (Equal, equal, impl Equal)
```

`Equal` imports and re-exports the interface name, `equal` imports and
re-exports the method name, and `impl Equal` imports and re-exports every
public implementation fact exported for that `InterfaceId`. Without `pub`,
the same selectors affect only the importing module. `impl Equal` alone does
not bind or export `Equal` as a source name.

Only targeted imports may be public in this increment. A qualified import
keeps its current local module alias and acquires no implementation facts. A
module that needs qualified names and implementations may use two imports:

```ash
import equality as Equality
import equality (impl Equal)
```

A name selector may retain its existing `as` alias. An implementation selector
cannot be renamed and names the dependency's public interface spelling. A
public name re-export uses the selected local spelling while retaining the
original declaration identity. A public implementation re-export retains the
original implementation identity and records another authorization route; it
does not copy the declaration.

The initial design imports all public implementations for a selected interface
name. It does not name individual implementations or select implementation-head
patterns.

This selector replaces Modular Ash's rule that every direct import
automatically admits every public implementation from that dependency. Names
keep their existing complete or targeted import behavior; implementations
become opt-in per interface. This is an intentional source-compatibility change
that requires proposal and migration evidence rather than an accidental parser
or resolver consequence.

An explicit implementation re-export adds those facts to the re-exporting
module's public closure. Re-export closures compose transitively. Reaching one
implementation identity through multiple paths retains one fact; distinct
declarations still undergo overlap and determination checks. Dead-code
elimination may remove unused evidence only after the full imported closure has
passed validation.

The first increment retains current single-parameter interfaces, so its
coherence check remains ordinary full-head overlap. A module checks the
deduplicated union of its selected imported and local implementations. The
first module that combines two distinct overlapping implementations owns the
failure. A public summary is available only after that closure succeeds.

The primary witness has three modules: a definition module publishes an
interface, method, and implementation; a facade re-exports all three channels;
and an application explicitly imports all three from the facade. Removing the
application's implementation selector leaves the method name available but
produces the existing unsatisfied-constraint failure.

## `lib-ash` error ownership

An error belongs to the first judgment with enough information to establish it.
Parsing owns malformed declarations and selectors. Resolution owns identities,
visibility, and unavailable exports. Kind and interface checking own invalid
kinds, method determinacy, contradictory determination, nonterminating
projection dependencies, and invalid defaults. Implementation checking owns
completion, equations, orphan status, prerequisites, and conflicts already
visible to the defining module.

Import-closure construction owns a conflict or nonterminating projection graph
first created by combining imported implementation sets. If that module also
re-exports the facts, it does not report the failure again during summary
construction. Summary construction instead owns invalid public closure or
privacy. Linked-evidence validation owns forged or inconsistent retained
selections. Constraint improvement and selection at a source occurrence own
ambiguous or unsatisfied goals and concrete active-goal cycles. Exhaustion of
the shared constraint budget belongs to whichever declaration, import-closure,
selection, linking, or validation judgment consumes its final unit. Core
validation owns Core kind, scope, type, dialect, registry, and provenance
failures.

Diagnostics identify the normalized interface arguments, relevant
determination edge, original implementation locations, and import or re-export
paths that made the facts visible. When several routes carry one identity, the
compiler chooses a shortest provenance path, breaking equal-length ties by
dependency order, import source order, and then stable route identity.

## `lib-ash` evidence and closure

The first increment's
[retained evidence](lib-ash/imports-evidence.md) covers the complete
name-versus-implementation and private-versus-public selector matrix; the
three-module facade; transitive and diamond identity; aliases; hidden and opaque
nominal facts; private exports; overlap at the first combined closure;
deterministic shortest authorization routes; graph-wide selector, closure,
summary, and validation budgets; rejection of forged routes; unchanged Core
node inventory; and explicit migration of every imported implementation
dependency. Neither complete nor ordinary targeted name imports make
implementations available implicitly.

The comparison corpus should cover kind-aware Core, authenticated polymorphic
evidence slots, higher-kinded partial application, method-local parameters,
method determinacy, multi-parameter improvement and selection, generic
determination conflicts, multi-parameter orphan ownership, direct and
transitive determination, growing and cyclic projection rejection,
prerequisite termination, default completion, overrides, mutually recursive
method defaults, explicit implementation imports, re-exports, diamond
identity, privacy, opacity, conflicts, and deterministic diagnostics.

The associated and relational forms should be compared for expressiveness,
annotation burden, inference, ambiguity diagnostics, summary complexity, and
Core output. Existing Modular Ash programs should remain valid except for an
intentional change accepted by a proposal. Explicit implementation imports are
the expected compatibility change in this design and require a migration
corpus.

`lib-ash` closes only after retained semantics are specified, positive and
negative evidence passes, summaries support separate dependent-module checking,
linked validation authenticates generated evidence and default adapters, and
the associated-versus-relational comparison has a recorded outcome. It retains
one linked Core program and adds no package resolver, persistent object format,
runtime registry, or dynamic interface lookup.

## `pack-ash` exact graph and identity

A package tool owns manifests, constraints, acquisition, lock data, and version
selection. The compiler receives an exact graph and does not choose versions.
The `ash` executable may act as a facade over a separate package executable or
library.

The package tool supplies semantic identities and the compiler derives revision
and artifact keys:

```text
PackageId     = resolver-owned locked package identity
ModuleId      = PackageId + canonical logical module path
SourceRevision = hash of the admitted source content
ArtifactKey   = ModuleId + SourceRevision + complete compilation context
```

`PackageId` distinguishes resolved package instances. Registry and immutable
version-control packages can derive it from their locked source coordinates,
name, and exact version or revision. A workspace form must provide the same
relocation property without using its installation path or current content;
its exact encoding remains an open, gating package-design question.

The exact graph assigns each packaged source one canonical logical module path.
It also records route aliases and named-root ownership. During source admission,
the compiler maintains a bijection between `ModuleId` and canonical physical
source: different routes to one source must name the graph's same logical
module, and two sources cannot claim one logical path. An undeclared alternate
logical path is a malformed exact graph rather than a second module identity.

This mapping keeps `ModuleId` stable across import aliases, declared symlink
routes, installation paths, cache locations, and graph routes without deriving
identity from the first route discovered. `SourceRevision` changes when source
content changes. `ArtifactKey` governs cache reuse and includes every semantic
compilation input. The encoded forms remain private during the initial cache
stage.

A lock graph records exact versions, immutable source or workspace identities,
checksums or revisions, dependency edges and local aliases, and required Ash
milestones. Two routes to one locked node share a `PackageId`; two resolved
versions remain distinct.

Current module-path rules remain: an unqualified path is relative to the
importing module, a named root comes from the supplied exact graph, targets
remain inside every owning root, and parent traversal remains forbidden. A
dependency alias chooses an exact edge but does not participate in module
identity. The admitted module and its artifact retain the complete owning-root
set and exact module-map fingerprint. Warm and source-free paths authenticate
those facts against the locked graph instead of reconstructing them from a
cache path.

## Compiled artifacts and linking

A module artifact joins a checked body-free export summary with a validated
typed Core fragment. The fragment contains definitions, private binders,
implementation methods, default adapters, and diagnostic provenance.
Cross-module references use a `ModuleId` plus declaration identity and the
dependency or re-export summary route that authorized the occurrence. Local
intermediate binders may use fragment-local indices.

An artifact records its module identity, source revision, artifact key, module
map and owning-root fingerprint, Ash milestone, private format version,
dependency-summary fingerprints, external identities and authorization routes,
exported and hidden linker closure, typed Core, retained evidence, and source
provenance. A default binder is a hidden linker capability in its interface
summary; it is not thereby a source-visible export.

The linker:

1. authenticates headers and content hashes;
2. verifies the exact graph, module map, owning roots, dependency identities,
   and summary fingerprints;
3. authenticates every external occurrence against its exact direct-dependency
   or re-export summary route before resolving the identity;
4. combines nominal, interface, implementation, and binder registries;
5. validates each module's imported implementation closure and retained
   evidence without imposing coherence on unrelated graph branches;
6. constructs `main ()`;
7. independently validates the complete linked Core program;
8. optionally eliminates dead code; and
9. independently validates the transformed Core program.

External authorization, visible coherence, evidence validation, and ordinary
Core validation precede dead-code elimination. An invalid unreachable fragment
cannot become valid because optimization removes it.

Artifact work proceeds through three internal stages:

1. a compiler-private cache whose format may change at any time;
2. a separate linker that consumes compiler-private artifacts; and
3. a distributable format frozen for a named Ash milestone and documented
   format revision.

The stable format promises compatibility only within its stated milestone.
Later Ash versions may require recompilation. The artifacts are Ash typed-Core
objects, not necessarily native operating-system object files.

The complete initial `ArtifactKey` contains the `ModuleId`, source revision,
exact module-map and owning-root fingerprint, exact dependency-summary
fingerprints, Ash milestone, semantic compiler options, and target
configuration. Two identical source files in different modules cannot share an
identity-bearing artifact. Finer front-end and backend caches may follow only
after this model has correctness evidence.

## `pack-ash` failure ownership

The package tool reports version, acquisition, checksum, dependency-cycle,
milestone, and manifest-versus-lock failures. The compiler reports source and
module-checking failures. The linker reports unauthorized or unresolved
external identities, two incompatible artifact keys for one exact-graph module,
summary or module-map mismatch, missing hidden closure, forged evidence, and
artifact or target incompatibility.

A missing or stale private cache entry triggers recompilation and is not a
source error. A corrupt private entry is discarded or quarantined before
recompilation. A corrupt or incompatible distributable artifact without source
is a normal user-facing error and names the expected and observed identity,
milestone, format, and checksum facts.

Serialized artifacts are untrusted input. One driver-owned graph budget spans
artifact bytes and tables, module maps and owning-root sets, external-reference
authentication, combined registries, evidence validation, both Core
validations, and optimization. Decoding charges declared sizes before
allocation, rejects invalid indices and duplicate table entries, and uses
explicit graph worklists. Cache publication is atomic so readers cannot observe
partial output. The package tool owns acquisition and lock-graph resource
failures; the compiler or linker owns exhaustion after handing off the exact
graph.

## `pack-ash` evidence and closure

The primary equivalence compares one-shot source compilation with separate
artifact production and linking before optional dead-code elimination. Their
Core graphs must be isomorphic while preserving package, module, declaration,
type, evidence, and provenance identities; only fragment-local and generated
binders may be alpha-renamed. With the same optimization configuration, their
post-optimization Core and evaluation must also agree. Diagnostic equivalence
means equal structured reason, causal identity, spans, and related provenance;
stable rendering is compared exactly.

Evidence must cover deterministic lock resolution, simultaneous package
versions, alternate routes, workspace relocation, forbidden traversal,
cold-versus-warm builds, precise summary invalidation, diamond linking,
separately compiled defaults and evidence, validation before dead-code
elimination, corruption recovery, source-free incompatibility, tampering,
deterministic output, and the cumulative resource boundary across decoding,
linking, validation, and optimization.

The private cache closes when cold and warm routes agree and invalidation and
recovery work. Separate linking closes when it agrees with one-shot compilation
on positive and negative cases. The distributable format closes when a clean
environment can build from locked source-free dependencies and an independent
reader, such as the separate linker process, enforces compatibility. Each stage
must also pass every applicable item in the preceding evidence inventory;
workspace relocation cannot pass until the package design selects a portable
workspace identity.

The leading recommendation requires that final distributable stage before the
`pack-ash` tag. Otherwise the milestone would not complete the source-free
package workflow that justifies separate objects.

## Alternatives considered

### Extend `modular-ash` with all features

This avoids new milestone names but leaves no stable boundary after the
completed module and interface work. It also combines language inference,
summary evolution, package identity, persistence, and linking in one failure
surface.

### Close `modular-ash`, then combine library and package work

This preserves the current milestone but freezes artifacts while the same
increment changes kinds, interface evidence, defaults, and re-export summaries.
Cache and linker failures could conceal language-model failures.

### Use three stages

Closing `modular-ash`, stabilizing language and library semantics in `lib-ash`,
and then building `pack-ash` around those summaries gives each milestone a
testable boundary. This is the leading direction.

## Intentional exclusions

The design does not currently include:

- module signatures;
- source-level higher-rank values, kind inference, or kind polymorphism;
- fallback implementations or specialization;
- implementation-head import patterns or individual implementation names;
- parent-directory module traversal;
- dynamic module loading or runtime interface lookup;
- a permanent cross-version artifact ABI; or
- a required native object-file ABI.

Module signatures require separate design because Ash interfaces describe
type-class-like constraints rather than module APIs.

## Required authority transitions

This note can guide comparison and proposal work but cannot authorize product
implementation. CP-0008 and TASK-0015 authorized the implemented first
increment; the current specification and retained evidence record its result.
Further language changes for `lib-ash` require one or more change proposals and
tasks. Package, cache, and linker architecture that does not alter language
semantics requires accepted architectural decisions and tasks. Any
source-visible package or import semantic change also requires a change
proposal. Current specification text changes only with retained implementation
evidence.

## Open questions

- Does the comparison retain associated types, functional dependencies, or a
  narrower combination of both?
- What syntax, if any, lets an associated output declare a smaller determinant
  set?
- Which implementation-head import patterns are justified after the initial
  all-for-interface form has evidence?
- How does a portable lock graph encode unpublished workspace identity?
- Which manifest syntax and source namespaces are sufficient for the first
  resolver?
- Which artifact encoding and linker process boundary should become public at
  the end of `pack-ash`?
- When does a native backend justify a separate target object format?
- What independent design, if any, should introduce module signatures?
