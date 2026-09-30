# DN-0031: Resource Composition Concept Map

- ID: `DN-0031`
- Status: exploring
- Related: [DN-0009](DN-0009-effects-handlers-and-continuations.md), [DN-0010](DN-0010-identities-and-resource-lifetimes.md), [DN-0011](DN-0011-modules-providers-and-resolution.md), [DN-0017](DN-0017-resource-management-and-storage-policy.md), [DN-0026](DN-0026-effect-ash-resource-first-milestones.md)

> This design note is informative. It maps an exploratory algebra of resource
> composition to current Ash. It defines no current semantics, accepts no
> architecture, and authorizes no implementation or refactoring.

## Question

Which concepts needed for resource composition already have an Ash mechanism,
which remain missing, and which overlap enough to merit a shared abstraction?

## Context and proposed vocabulary

[DN-0032](DN-0032-algebra-of-scoped-resource-composition.md) develops a
literature-based candidate algebra and bounded derivations for the concepts
mapped here. [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md)
develops a direct operational candidate with one expression calculus, ordered
interpretation frames, and separately checked continuation capabilities.
Neither adds implemented coverage to this inventory.

The exploration separates resource parameters from the computations using them.
An effect describes typed requests; a provider supplies their interpretation;
a handler establishes the scope of that interpretation. A resource describes
typed provision of capabilities and participates in composition. State,
allocation, and release belong to particular provisions, not the general
definition of resource.

This vocabulary is provisional. In particular, the proposed provider is broader
than current sealed builtin `Provider<R>` evidence. Current source handlers
contain interpretation clauses themselves. Similar names do not establish
semantic equivalence.

The guiding composition equation is schematic:

```text
A[A'] · B[B'] = (A, B)[A'; B']
```

Here `A` and `B` are resource parameters; `A'` and `B'` are bodies. The second
body becomes the continuation of the first, with result binding made explicit
when needed. The right side provides the composed resources to the sequenced
body. Source binding and exact instance selection must remain coherent.

The composition has an interval enclosing its constituent lifetimes. This
does not require allocating every constituent at entry or retaining it until
the region ends. Laws and proofs must justify equivalent lifetime placements
while preserving observations. Whether the equation defines abstract
composition or also holds for existing sequential scope execution requires a
precise semantics; it is not an unconditional rewrite of current Ash.

## Reading the maps

Each row has a stable concept ID for discussion. These IDs are documentation
labels, not proposed language identities. **Implemented** means the cited
specification defines the bounded feature. **Partial** means related machinery
exists but does not implement the full exploratory concept. **Missing** means
the current language does not expose that abstraction. **Open** means the
design itself is unsettled.

Overlap is a separate axis: shared purpose or similar structures are not proof
of duplicated code. Specification links establish semantics; code and test
links identify evidence to inspect, not alternative semantic authority.

## Concepts to current features

| ID / concept | Current Ash feature and authority | Coverage / missing part |
| --- | --- | --- |
| C01: typed request API | Parameterized effects and operation identities: [effects](../../spec/static-semantics.md#effects). | Implemented for current operation signatures; user-declared effect equations remain missing. |
| C02: effect requirements | Exact effect instances and row tails: [computation types and rows](../../spec/static-semantics.md#computation-types-and-effect-rows). | Implemented. Rows do not establish ordering or commutativity of interpretations. |
| C03: scoped interpretation | Exhaustive `handle`, `perform`, `resume`, checked `discard`: [effects](../../spec/static-semantics.md#effects). | Partial: lexical handling exists; a general parameterized handler/provider installation abstraction is missing. |
| C04: provider | Ordinary interfaces and implementations, [scoped exact evidence](../../spec/static-semantics.md#scoped-exact-evidence), and sealed [builtin providers](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies). | Partial: builtin provider methods issue requests; source handlers interpret them. No general source resource-provider declaration. |
| C05: resource access | Opaque duplicable handles with inferred dependencies: [cells](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies), [native buffers](../../spec/static-semantics.md#scoped-native-buffers). | Implemented for two providers. Handles can pass through helpers and closures while their owner remains live; ownership is not transferable. |
| C06: data and parameterization | [Kinds, monotypes and schemes](../../spec/static-semantics.md#kinds-monotypes-and-schemes), constrained interfaces, ordinary data types. | Partial: payload and identity parameters have supporting machinery; a generic resource contract and the type of its supplied body remain open. |
| C07: binding and substitution | Resolved [type binder identities](../../spec/name-resolution.md#type-binder-identity-and-scope); linked evidence and lexical instantiation: [elaboration](../../spec/elaboration.md). | Partial: coherent names, types, rows and evidence exist across current features; named resource-composition substitution is missing. |
| C08: fresh identity | [Local nominal scope](../../spec/static-semantics.md#local-nominal-scope) and fresh acquisition identities in C05. | Partial: both distinguish identities, but a local nominal does not acquire runtime ownership or provider authority. |
| C09: scope dependency and lifetime | Escape checking, fresh runtime activation and continuation ownership: [cell execution](../../spec/dynamic-semantics.md#scoped-cell-execution). | Partial: current scopes are checked; a general interval algebra and proof-directed lifetime movement are missing. |
| C10: completion | [Scoped cleanup actions](../../spec/static-semantics.md#scoped-cleanup-actions) and resource release. | Implemented bounded guarantees for normal completion and owned abandonment. Neither establishes eventual completion of divergent computation. |
| C11: composition | Nested resource/handler syntax and [synchronous typed hooks](../../spec/static-semantics.md#synchronous-typed-hooks). | Partial: nesting and a fixed transformer chain exist; C11's resource/body composition operator is missing. Hook composition is comparison evidence, not that operator. |
| C12: laws and proofs | Compiler checking and validated evidence: [constraint satisfaction](../../spec/static-semantics.md#constraint-satisfaction-and-checked-evidence); [current exclusions](../../spec/README.md). | Missing as a general source proposition/proof and provider-law facility. Interface evidence must not be relabeled as proof of arbitrary semantic equations. |
| C13: observations and cost | [Dynamic semantics](../../spec/dynamic-semantics.md) and bounded compiler/runtime accounting. | Partial: current behavior has a specification; the proposed algebra lacks a defined observational equivalence and cost model. Compiler work budgets are not source resource identities. |
| C14: continuation use and extension | Nonduplicable, nonescaping resume/discard capability: [effects](../../spec/static-semantics.md#effects). | Partial: current ownership checking exists; multi-shot, escape, suspension and concurrent resumption require distinct proof obligations. [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md#continuation-extensions-and-sequencing-laws) records those boundaries and explores [sequencing relative to a continuation model](DN-0032-algebra-of-scoped-resource-composition.md#candidate-interpretation-sequencing-relative-to-a-continuation-model), including contract-dependent typing, laws and implementations. No model is selected. |
| C15: asynchronous effect hooks | Current [synchronous hooks](../../spec/static-semantics.md#synchronous-typed-hooks); deliberate later-extension boundary in [DN-0026](DN-0026-effect-ash-resource-first-milestones.md#leading-boundary). | Missing: asynchronous execution introduces concurrency and scheduling, even without parallel threads. [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md#asynchronous-effect-hooks-require-scheduling-semantics) records ordering, fan-out, retained context, completion and scheduler proof obligations. |

## Identity map

| Identity role | Existing representation or relationship | Boundary to preserve |
| --- | --- | --- |
| Source spelling | Names resolve to binders and defining declarations. | Renaming a binder must not change meaning; equal spelling must not merge instances. |
| Effect API / operation | Module-owned effect and operation identities, with exact effect arguments. | The same API can have different instances and interpretations. |
| Formal resource identity | Acquisition's kind-`Type` binder, allocated in the shared type-binder sequence. | A formal binder is not a payload type or a runtime allocation address. |
| Runtime resource instance | Fresh activation, carried through lexical instantiation. | Re-executing one acquisition site creates a new instance; aliases retain the original one. |
| Provider selection | Interface identity, exact arguments, and selected evidence. | General provider instance identity remains open; sealed evidence is not the interpretation itself. |
| Handler / continuation owner | Core handler and resume-owner identities. | An interpretation boundary and the resource it accesses are related, not interchangeable identities. |
| Region | No general current source representation. | Decide composition binding before adding a new global identity or registry. |

These relationships derive from [name resolution](../../spec/name-resolution.md),
[surface elaboration](../../spec/elaboration.md#surface-erasure), and
[resource execution](../../spec/dynamic-semantics.md#scoped-cell-execution).

## Overlap and implementation evidence

| Area | Evidence already available | Assessment and next audit question |
| --- | --- | --- |
| Resource operations / ordinary effects | [Elaboration](../../spec/elaboration.md#surface-erasure) explicitly generates ordinary provider methods requesting `Ops<R>`; [Core effects](../../src/core/effect.rs) includes request, handler and resource nodes. | Shared mechanism confirmed. Determine whether a general provision can elaborate to existing operations while retaining authentication. |
| Type parameters / resource identity binders | [Shared binder sequence](../../spec/name-resolution.md#type-binder-identity-and-scope). | Sharing is already specified. Do not invent a parallel naming system for composition. |
| Local nominal / resource escape | [Local nominal scope](../../spec/static-semantics.md#local-nominal-scope), C05 dependency rules, [newtype tests](../../tests/newtype_resources.rs), [resource typing tests](../../tests/resource_scope_typing.rs). | Semantic overlap, different guarantees. Audit reusable boundary checks without equating nominal escape with retained access. |
| Scoped evidence / builtin provider evidence | [Evidence implementation](../../src/evidence.rs), [evidence validation](../../src/evidence_validation.rs), [scoped evidence tests](../../tests/scoped_evidence_interactions.rs). | Related evidence transport; builtin authority remains sealed. Whether more implementation can be shared is unverified. |
| Handlers / resources / cleanup / registrations | Distinct nodes in [Core effects](../../src/core/effect.rs), control handling in [capture control](../../src/core/capture/control.rs), [cleanup interaction tests](../../tests/cleanup_interactions.rs). | Common ownership/control problem with distinct completion behavior. No redundant implementation established by this map. |
| Composition / hooks | [Hook runtime tests](../../tests/hooks_runtime.rs), [retained hook evidence](effect-ash/synchronous-hooks-evidence.md). | Transfer ordering, registration and capture cases; do not import hook-specific endomorphism restrictions into general resources. |

## Constraints and candidate directions

Preserve exact binding, effect-row relationships, access dependencies,
continuation ownership, provider authority and observable completion. Review
current tests as obligations within their scope, not as proof of the new laws.

Compare three directions: composition that elaborates to existing nested forms;
a general typed provider/handler installation abstraction; or a new primitive
region representation. Prefer the first as a comparison baseline. Introduce
new machinery only where a named typing or semantic example defeats reuse.
No direction is selected here.

## Evidence and experiments

The first study should formalize resource composition, computation sequencing,
binding substitution and observation separately. State candidate identity,
associativity, substitution-coherence and interpretation laws, with typed
premises. Exchange, duplication, elimination and lifetime movement need their
own provider-law evidence; they do not follow from effect rows.

Compare immutable configuration, cells, observable logging and locks. Include
two instances of one API, aliases, repeated acquisition at one site, provider
dependencies, result-dependent sequencing, capture/resume/discard and failed
acquisition. Record both positive examples and counterexamples. These cases
are design obligations, not claims that all are expressible in current Ash.

Measure type/row preservation, observations, access validity and completion
first; measure allocation counts, peak retention and dispatch costs separately.
Prove transformations against an operational or denotational model rather than
assuming every desired optimization as an axiom. A future prototype needs a
bounded question and explicit disposal/retention conditions before code work.

## Maintenance

Update affected rows when this exploration changes or a retained implementation
changes its coverage. Preserve concept IDs when wording changes. For every
coverage change, update its specification link and relevant evidence together.
Split a row when one label hides different obligations.

Mark duplication confirmed only after locating both implementations and showing
that they enforce the same invariant. Record intentional distinctions and
contrary evidence alongside any proposed consolidation. Do not turn a gap into
a roadmap commitment; proposals and tasks retain their own authority.

Verify relative links and anchors, table structure, Markdown style and authority
boundaries after updates. Runtime tests are needed for changed executable claims
or examples; maintaining this inventory alone does not require a full build.

## Open questions

- What type relates supplied access, exact effects and the body's result?
- Which identities are substituted, and where must freshness be introduced?
- Which compositions need dependent parameters rather than a product?
- What observation model makes the composition and interval laws precise?
- Which provider laws can be expressed and checked using the future proof system?
- Which apparent overlaps are reusable abstractions, and which protect distinct
  semantic boundaries?
