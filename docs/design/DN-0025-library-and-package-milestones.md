# DN-0025: Library and Package Milestones

- ID: `DN-0025`
- Status: exploring
- Related: [DN-0020: Ash Dialect Milestones](DN-0020-ash-dialect-milestones.md), [DN-0022: Passive Static Modules](DN-0022-passive-static-modules.md), [DN-0023: Interfaces and Implementations](DN-0023-interfaces-and-implementations.md), [DN-0019: Primitive Feature Composition](DN-0019-primitive-feature-composition.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), the [explicit-import evidence](lib-ash/imports-evidence.md), the [explicit-kind evidence](lib-ash/kinds-evidence.md), the [method-parameter evidence](lib-ash/method-parameters-evidence.md), the [relational-interface evidence](lib-ash/relational-interfaces-evidence.md), the [core-and-library audit](modular-ash/core-library-evidence.md), and the [Modular Ash closure report](modular-ash/closure.md)

> This design note is informative. It does not define current Ash, accept
> language semantics, or accept a package or artifact architecture.

## Question

Which work should close Modular Ash, which language and library capabilities
belong in its first descendant, and which package and compiled-artifact
capabilities require a later milestone?

## Current boundary

The [current specification](../../spec/README.md) defines four bounded
`lib-ash` increments on the completed Modular Ash base. It has passive acyclic source
modules, public and private declarations, opaque type exports, qualified and
targeted imports, targeted public name and implementation re-exports,
compiler-generated body-free export summaries, method-only relational
interfaces, explicit implementation selection, authenticated transitive
authorization routes, explicit kinds, higher-kinded declaration parameters,
explicit fixed-kinded method-local parameters, authenticated polymorphic method
evidence, complete ordered interface applications, one optional total forward
determination edge, kind-preserving evidence lowering, and one linked typed
Core program.
Interfaces are not module signatures. Persistent compiled modules, package
resolution, and separate object linking remain outside current Ash.

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

The retained relational addition crosses parsing, name resolution, kind and
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

The first bounded `lib-ash` increment is complete. Implementation availability
is explicit, and targeted imports can re-export selected names and
implementation authorizations. The retained
[evidence report](lib-ash/imports-evidence.md) records its reviewed boundary.
The second increment is complete. Its reviewed explicit kinds and higher-kinded
declaration parameters across checking, summaries, evidence, and independent
Core validation are retained by the
[kind evidence](lib-ash/kinds-evidence.md). The third bounded increment is also
complete. Its explicit method-local type parameters, authenticated evidence
adapters, rank-1 source boundary, and runtime erasure are retained by the
[method-parameter evidence](lib-ash/method-parameters-evidence.md). The fourth
bounded increment is implemented and specified. Its complete relational
applications, total forward determination, one-pass improvement, linked
authentication, exact resources, and downstream exclusions are retained by the
[relational-interface evidence](lib-ash/relational-interfaces-evidence.md).
That product checkpoint defines the revised `lib-ash` goal; integration and
transition-artifact cleanup remain lifecycle work. Associated outputs, general
determination graphs, and defaults are separate future features rather than
requirements for this milestone.

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
   first increment is retained by the
   [explicit-import evidence report](lib-ash/imports-evidence.md).
2. Add explicit `Type` and function kinds and higher-kinded parameters without
   kind inference or kind polymorphism in this increment. Make checking,
   summaries, substitution, and independent Core validation kind-aware. The
   absence of kind inference is a phase-dependent semantic boundary, not a
   permanent language principle; later work may consider bounded
   declaration-local kind inference separately from kind polymorphism. The
   completed second increment is retained by the
   [explicit-kind evidence report](lib-ash/kinds-evidence.md).
3. Add method-local type parameters. Keep ordinary source rank-1 and admit
   polymorphic term slots only as authenticated compiler-generated interface
   evidence. The completed third increment is retained by the
   [method-parameter evidence report](lib-ash/method-parameters-evidence.md).
4. Add complete ordered multi-parameter interface applications and at most one
   total forward determination edge. Retain one isolated improvement pass and
   full-application evidence selection. The completed product increment is
   retained by the
   [relational-interface evidence report](lib-ash/relational-interfaces-evidence.md).
5. Close the revised `lib-ash` product boundary with the combined library
   corpus, summary and identity audit, downstream-pressure review, exact
   resource verification, normative reconciliation, migration guards, and one
   retained linked Core program. The fourth increment supplies these product
   facts; integration and transition cleanup complete the lifecycle.

The first increment establishes the visibility and coherence closure used by
later multi-parameter and determination work. The second establishes fixed
kinds, canonical applications, and authenticated polymorphic identities.
The third establishes canonical method schemes, occurrence-local
instantiation, authenticated generated evidence adapters, and the preserved
rank-1 source and erased-runtime boundaries.
The fourth establishes complete relational applications and an explicit
selection key without generalizing evidence authority or adding a Core or
runtime mechanism.
`pack-ash` remains separate until the complete `lib-ash` milestone stabilizes
those summaries and identities.

## `lib-ash` type and interface model

### Kinds and higher-kinded parameters

The initial kind language contains `Type` and function kinds. Ordinary type
parameters default to `Type`; a parameter used as a constructor requires an
explicit kind such as `Type -> Type`. This increment does not infer kinds or
support kind polymorphism. The first restriction is phase-dependent: later
work may consider bounded declaration-local kind inference without treating it
as kind polymorphism or as a prerequisite for this increment.

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
polymorphic slot, and a generated evidence adapter exposes the selected
implementation method at that scheme.

Core therefore admits polymorphic term parameters only in authenticated
compiler-generated evidence positions during this increment. Independent Core
validation checks that the nested scheme agrees with its `MethodId`; ordinary
Ash annotations cannot introduce, accept, or return such a value. This keeps
the source language rank-1 without pretending that polymorphic dictionaries
are ordinary monomorphic functions.

### Retained relational determination model

The revised milestone settles on the simplest complete lowered form: a
nonempty ordered interface parameter vector, a complete application vector,
and at most one total forward edge from a nonempty determinant slice to its
entire complement. Without an edge, every parameter remains part of the
selection key. With an edge, every method must mention each determinant while
dependents may occur anywhere or nowhere. One fixed pre-mutation snapshot
permits forward improvement from inference-free keys; evidence selection still
uses complete applications.

This form is sufficient for the revised `lib-ash` goals. It preserves stable
interface and implementation identities, complete relationships through body-
free summaries and linked validation, occurrence-owned opaque evidence,
simultaneous substitution, and ordinary Core method evidence. Determinant
metadata erases before Core and adds no runtime mechanism.

Associated-output declarations, projections, equations, normalization, and
their source elaboration are not current Ash. Multiple, partial, chained,
cyclic, reverse, or injective edges, neutral parameters, and alternative keys
are likewise deferred rather than encoded into this boundary.

The retained representation also answers three downward pressures without
prematurely implementing them. Effects may reuse stable typed identities and
ordered applications, but handler and provider authority must remain separate.
Proofs may reuse typed identities and complete arguments, but proof authority
must not be confused with implementation evidence. Existential packages may
hide any argument while preserving its equality relationships with payloads
and encapsulated evidence; because summaries and selections already carry the
complete application, that future work need not refactor interface heads.
Existentials still require their own binders, scope, generativity, Core forms,
and evidence authority.

Associated outputs and method or associated-output defaults are not current
Ash or unfinished `lib-ash` work. If later examples justify them, each requires
a separate proposal covering its source syntax, identity, checking,
elaboration, authentication, termination where applicable, and evidence.

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

The first increment retained predecessor single-parameter interfaces, so its
coherence evidence used ordinary full-head overlap. Current Ash generalizes
that case to complete selection keys. A module checks the
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
kinds, method determinacy, and contradictory determination. Implementation
checking owns completion, orphan status, prerequisites, and conflicts already
visible to the defining module.

Import-closure construction owns a conflict first created by combining imported
implementation sets. If that module also re-exports the facts, it does not
report the failure again during summary construction. Summary construction
instead owns invalid public closure or privacy. Linked-evidence validation owns
forged or inconsistent retained selections. Constraint improvement and
selection at a source occurrence own ambiguous or unsatisfied goals and
concrete active-goal cycles. Exhaustion of the shared constraint budget belongs
to whichever declaration, import-closure, selection, linking, or validation
judgment consumes its final unit. Core validation owns Core kind, scope, type,
dialect, registry, and provenance failures.

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

The second increment's current
[kind evidence](lib-ash/kinds-evidence.md) covers explicit and omitted
binder policies, fixed kinds through inference and first-order evidence,
canonical unary type application, authenticated body-free facts, resolved and
generated Core binder authority, exact resources, tampering, predecessor
migration, and runtime erasure. The absence of kind inference in that increment
is phase-dependent rather than a permanent library-language restriction.

The third increment's current
[method-parameter evidence](lib-ash/method-parameters-evidence.md) covers
fixed-kinded method schemes, rigid implementation checking, body-free and
linked authentication, generated Core adapters, transforms, diagnostics,
migration, exact resources, small-stack disposal, and runtime erasure.

The fourth increment's current
[relational-interface evidence](lib-ash/relational-interfaces-evidence.md)
covers complete ordered vectors, total partition admission, method
determinacy, requirement and implementation rules, coherence, forward-only
improvement, full-goal selection, body-free summaries, linked and independent
Core authentication, hidden and opaque dependents, deterministic diagnostics,
exact resources, predecessor migration, and runtime erasure.

Together the four reports supply the revised `lib-ash` product boundary:
specified retained semantics, positive and negative corpus evidence, separate
dependent-module checking, linked evidence authentication, Core validation and
transforms, one linked relational program, and no package resolver, persistent
object format, universal evidence family, runtime registry, or dynamic
interface lookup. The product checkpoint is complete on its branch. Integration,
final transition-artifact removal, and any milestone tag are lifecycle actions,
not additional language semantics.

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
implementation methods, generated evidence adapters, and diagnostic provenance.
Cross-module references use a `ModuleId` plus declaration identity and the
dependency or re-export summary route that authorized the occurrence. Local
intermediate binders may use fragment-local indices.

An artifact records its module identity, source revision, artifact key, module
map and owning-root fingerprint, Ash milestone, private format version,
dependency-summary fingerprints, external identities and authorization routes,
exported and hidden linker closure, typed Core, retained evidence, and source
provenance. Generated evidence adapters remain authenticated Core relationships;
they do not become source-visible exports.

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
separately compiled method evidence, validation before dead-code
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
increment changes kinds, method and relational evidence, and re-export
summaries. Cache and linker failures could conceal language-model failures.

### Use three stages

Closing `modular-ash`, stabilizing language and library semantics in `lib-ash`,
and then building `pack-ash` around those summaries gives each milestone a
testable boundary. This is the leading direction.

## Intentional exclusions

The design does not currently include:

- module signatures;
- source-level higher-rank values or kind polymorphism; the prepared kinds
  increment also excludes kind inference as a phase-dependent constraint, not
  a permanent language principle;
- fallback implementations or specialization;
- associated-output declarations or projections, general determination graphs,
  or method and associated-output defaults;
- effect handlers or providers, proof authority, a common universal evidence
  family, or existential pack and unpack forms;
- implementation-head import patterns or individual implementation names;
- parent-directory module traversal;
- dynamic module loading or runtime interface lookup;
- a permanent cross-version artifact ABI; or
- a required native object-file ABI.

Module signatures require separate design because Ash interfaces describe
type-class-like constraints rather than module APIs.

## Required authority transitions

This note can guide comparison and proposal work but cannot authorize product
implementation. All four completed bounded increments followed the change-
proposal and task workflow; the current specification and the retained
[import](lib-ash/imports-evidence.md), [kind](lib-ash/kinds-evidence.md), and
[method-parameter](lib-ash/method-parameters-evidence.md), and
[relational-interface](lib-ash/relational-interfaces-evidence.md) evidence
reports record their results. Further language changes for `lib-ash`
require one or more change proposals and tasks. Package, cache, and linker
architecture that does not alter language semantics requires accepted
architectural decisions and tasks. Any source-visible package or import
semantic change also requires a change proposal. Current specification text
changes only with retained implementation evidence.

## Open questions

- Which implementation-head import patterns are justified after the initial
  all-for-interface form has evidence?
- How does a portable lock graph encode unpublished workspace identity?
- Which manifest syntax and source namespaces are sufficient for the first
  resolver?
- Which artifact encoding and linker process boundary should become public at
  the end of `pack-ash`?
- When does a native backend justify a separate target object format?
- What independent design, if any, should introduce module signatures?
