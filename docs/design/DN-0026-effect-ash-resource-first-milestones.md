# DN-0026: Effect Ash Resource-First Milestones

- ID: `DN-0026`
- Status: exploring
- Related: [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md), [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md), [DN-0012: Coeffects and Hooks](DN-0012-coeffects-and-hooks.md), [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md), [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md), [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md), [DN-0023: Interfaces and Implementations](DN-0023-interfaces-and-implementations.md), [DN-0025: Library and Package Milestones](DN-0025-library-and-package-milestones.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), and [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md)

> This design note is informative. It outlines possible `effect-ash`
> milestones; it does not define current Ash, accept effect or resource
> semantics, or authorize implementation. All syntax and types are
> illustrative.

## Question

Which missing language and runtime capabilities should `effect-ash` add after
`lib-ash`, and how can they be split into bounded increments that reach useful
resource and hook behavior without making dynamic loading, existentials,
asynchrony, or concurrency initial dependencies?

## Current boundary

The [current specification](../../spec/README.md) defines a pure, rank-1
language with passive, statically linked modules. Nominal declarations,
imports, re-exports, interface constraints, and selected implementation
evidence preserve checked identities. Static module and interface machinery
erases: evaluation has no runtime module value, interface registry, or dynamic
implementation lookup.

`lib-ash` has four completed bounded increments, and its revised milestone is
complete. [DN-0025](DN-0025-library-and-package-milestones.md) separates later
library-type work from `pack-ash`. The trajectory gives `effect-ash` no ordering
dependency on `pack-ash`. Dynamic loading is therefore future composition
pressure, not part of the boundary outlined here.

[AD-0007](../decisions/AD-0007-typed-core-dialects.md) provides a typed Core
operation-family seam while requiring the pure dialect to contain no inhabited
effect machinery. [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)
provides explicit first-order evaluator state while leaving surface and Core
continuations unchosen. These boundaries make later effect work localizable,
but they do not supply effect semantics.

After `lib-ash`, the following capabilities would still be absent:

- effect API declarations, effect rows, handlers, and typed continuation
  contracts;
- representation-preserving `newtype` declarations, local type declarations,
  or runtime-established fresh identities;
- resource acquisition scopes, identity-indexed resource values, ownership or
  usage checking, and deterministic cleanup;
- runtime provider relationships and a checked foreign-provider boundary;
- runtime hook registration, publication, and registration lifetimes;
- suspension, asynchronous hook execution, concurrency, cancellation, and
  replay-safe multi-shot continuations; and
- dynamic module loading, runtime package resolution, and unloading.

The last item does not become an `effect-ash` dependency merely because future
dynamic composition may reuse identities, provider relationships, or
continuations.

## Leading boundary

The leading direction is resource-first. Resources exercise effect
interpretation, identity, evidence, lifetime, cleanup, and foreign boundaries
without requiring a scheduler. Synchronous hooks follow the first resource
scope because they expose useful reactive machinery and test runtime
registration and ordered handler flow. Asynchronous hooks and concurrency
remain later extensions, but the synchronous representation must not rule them
out.

The ordering is partial rather than total:

```text
module newtype
      |
      v
local newtype ---> scoped exact evidence ---+
                                             |
effect kernel ------------------------------+
                                             v
                                      resource scope
                                        |       |
                                        v       v
                               synchronous     reliable
                                  hooks        cleanup
                                        |       |
                                        +---+---+
                                            v
                                  foreign providers
                                            |
                                            v
                                  suspension and async
                                            |
                                            v
                                       concurrency
```

Only causal edges constrain the order. Among ready increments, planning should
prefer the least work that produces the most transferable evidence or useful
behavior. In particular, pure `newtype` work and the effect kernel may proceed
independently before their first integration at resource scope.

## Common generative identity substrate

### Serve pure and effectful consumers

Generative identity is not a resource-only feature. Pure code needs fresh
nominal distinctions, and later existential packages and ML-like signatures
will pressure the same type and scope machinery. `effect-ash` may be the first
consumer that requires the implementation, but it should not encode identity
as an effect-specific or resource-specific facility.

The initial `effect-ash` boundary should implement two consumers:

1. pure generative nominal types; and
2. effect or resource scopes that bind a fresh identity and relationships
   indexed by it.

This is enough to test common identity representation, scope, substitution,
equality, evidence, Core validation, and erasure. It does not require general
existential packaging.

### Use a representation type as the template

A small `newtype` form is the leading pure source mechanism. Illustratively:

```ash
newtype UserId = UserId(Int)
```

The declaration introduces one fresh nominal identity and one representation
field. The constructor and pattern expose the representation where visibility
permits. Wrapping and matching may erase after typed Core has validated the
representation boundary; `newtype` should not imply a wrapper allocation.

The representation type is a template, not a source of constraint facts. A
`newtype` does not automatically inherit interfaces implemented by its
representation, and no representation-based coercion satisfies a constraint.
Explicit operations or an explicit implementation must establish each wanted
relationship.

### Reuse ordinary declaration scope and visibility

`newtype` should be a declaration form rather than a resource-specific scope
form. A local declaration follows ordinary lexical binding scope. A module
declaration reuses current visibility and summary machinery:

- private `newtype` exposes neither its name nor constructor to dependents;
- public opaque `newtype` exposes its stable nominal identity but withholds its
  constructor; and
- public transparent `newtype` exposes the identity and representation
  constructor.

The exact grammar remains proposal work. It should follow the existing nominal
declaration shape and existing sequential or recursive binding structure
rather than introduce a separate `scope` syntax solely for types.

With static modules, one module-level declaration introduces one identity in
the linked program. Imports and re-exports preserve it instead of regenerating
it. Local declarations introduce identities distinct from every other
declaration, including declarations with the same spelling and representation.

This model must not permanently define an identity as a source path. Dynamic
loading, repeated module instantiation, or future module parameterization may
later change when one declaration is instantiated. Those cases are excluded
from the first milestone, but the internal identity representation should not
make them impossible.

### Keep type identity separate from resource lifetime

A fresh type prevents values from unrelated identities from being confused. It
does not by itself prove ownership, non-escape, non-duplication, release, or
destruction.

For a resource scope, the fresh identity is an index or brand. The resource
value carries the handle:

```text
fresh identity r
File<r>                 resource value
Provider<File, r>       exact provider relationship
```

The raw native handle remains provider-owned. A user should not need to wrap a
native handle in a zero-field type to obtain its identity. Usage and lifetime
analysis must separately govern whether `File<r>`, closures that capture it, or
continuations that retain it may escape, duplicate, or be discarded.

The acquisition form must surface the identity binder enough for source tests
to relate annotations and operations to that exact scope and to demonstrate
that another acquisition does not match. Its exact syntax remains proposal
work.

Pure declaration generativity and runtime resource generativity may differ in
when they instantiate a fresh identity. The first proposals must state that
generation boundary explicitly while keeping both forms on the same identity,
binder, and equality substrate.

## Constraint elaboration

### Preserve current improvement and evidence selection

Current Ash applies ordinary unification before relational improvement. For
eligible pending determined roots, it freezes one snapshot and performs one
source-ordered improvement pass from an abstract requirement, exact current-
implementation evidence, or one matching concrete implementation. Improvement
cannot refine a determinant key, inspect prerequisites, repeat to saturation, or
construct evidence. After a complete root passes that gate, evidence selection
uses the same source order. Recursively selected prerequisites use complete-
application selection without snapshot membership. Selected evidence lowers to
authenticated ordinary Core type abstractions, functions, and applications.
Evaluation performs no interface lookup.

The initial generativity work should extend that flow rather than add a second
constraint solver or a runtime interface registry.

### Add scoped exact evidence, not local implementation search

An acquisition or other trusted identity-introduction construct may introduce
exact evidence indexed by its fresh identity. The evidence is lexical and
matches only an identity-equal complete goal. In complete-goal selection, it
must take precedence over general concrete implementation search so a global
implementation cannot capture a relationship established for a fresh resource.

This is authenticated evidence introduction, not a locally searchable `impl`.
The initial boundary therefore has these rules:

- module-level `newtype` declarations may use ordinary module-level
  implementations;
- local `newtype` declarations do not add local implementations or change
  overlap and orphan rules;
- the representation type contributes no implicit implementation evidence;
- acquisition may bind exact provider or capability evidence for its fresh
  identity;
- pure local code passes operations or evidence through ordinary functions and
  constrained abstractions; and
- evidence may escape only through an independently valid abstraction. The
  initial boundary adds no existential package merely to permit escape.

A later proposal must make two placements explicit: whether scoped evidence can
supply relational improvement for an eligible known determinant key, and where
it enters complete-goal selection relative to abstract requirements and exact
current-implementation evidence. It must preserve the fixed root snapshot,
single forward pass, mandatory consistency check, and separate complete-
application selection of recursive prerequisites. Scoped evidence cannot refine
a key, unlock a root outside the snapshot, or become a competing global
candidate. It uses identity equality and is validated before Core construction.

### Keep effect requirements separate

Provider evidence does not discharge an effect row, choose a handler, or define
handler order. An effect row records outstanding interpretation requirements.
A handler performs semantic discharge. Exact evidence supplies a typed
relationship that the handler may consume.

This separation lets the compiler reuse binders, substitutions, constraints,
and Core evidence without turning ordinary interface selection into effect
handling.

## Milestone slices

### 1. Module `newtype`

Add one-field nominal representation declarations at module scope. Reuse current
private, public transparent, and public opaque identity channels, summaries,
imports, and re-exports. Establish distinctness, constructor access, kind
checking, and representation erasure without effects or runtime witnesses.

### 2. Local `newtype`

Permit the same nominal mechanism in ordinary local binding scope. Establish
lexical type scope, shadowing, identity equality, interaction with local
generalization and recursive groups, and type-escape diagnostics. This is the
pure generativity corpus; it does not add existentials or local `impl` search.

### 3. Scoped exact evidence

Extend constraint elaboration with authenticated, lexically scoped evidence for
one complete identity-indexed relationship. Specify separately whether that
evidence participates in relational improvement and where it enters complete-
goal selection, while preserving the fixed-snapshot and recursive-prerequisite
boundaries. Reuse current evidence binders, application order, Core validation,
and erasure. Test the mechanism first with a pure relation before a resource
acquisition depends on it.

### 4. Effect kernel

Add effect API identity, effect-row checking, ordered handler composition, and
an explicitly typed non-escaping one-shot continuation boundary. Begin with
one resumption, then checked discard. Keep row equality separate from handler
order and effect identity separate from API shape.

The effect Core dialect must use AD-0007's operation-family boundary. The
runtime may build on AD-0008's explicit machine, but an evaluator frame does
not become a language continuation until the new dialect and validator assign
it that meaning.

### 5. Resource scope

Combine local generative identity, scoped provider evidence, and the effect
kernel in one safe, non-foreign provider. Acquisition binds a fresh resource
identity, a value such as `File<r>`, and only the exact relationships the
provider establishes. The handler interprets the identity-local requirement
before the scope closes.

This slice must distinguish static name escape, value or closure escape,
continuation escape, usage, and runtime lifetime. Rejecting a hidden type name
is not a substitute for accounting for a live resource.

### 6. Synchronous hooks

Add runtime registration, deregistration, and sequential inline publication at
named typed hook identities. A registration has its own resource identity and
captures the identities required by its subscriber. Handler placement defines
when publication occurs. Subscriber effects remain visible in effect rows.

The first slice excludes parallel fan-out and suspension. Its chain
representation and failure boundary must nevertheless permit later subscribers
to suspend without replacing the hook API or creating a second effect runtime.

### 7. Reliable cleanup and foreign providers

Define cleanup across normal return, abort, handler unwinding, and partial
acquisition. Establish ordering and failure ownership before a foreign provider
can expose a native handle. Then add a narrow checked foreign-provider boundary
that translates native failure into ordinary typed failure and retains every
identity, authority, and cleanup obligation.

This slice creates FFI pressure; it does not choose a general native ABI,
dynamic library loader, or package format.

### 8. Suspension and asynchronous hooks

Permit a one-shot continuation to escape its immediate handler call. The
suspended value must retain its handler context, resources, registrations, and
cleanup obligations. Asynchronous hook execution then defines ordering,
completion, cancellation, and failure without changing the synchronous
contract retroactively.

### 9. Concurrency

Add scheduler and transfer semantics only after suspension and ownership
boundaries are explicit. Concurrency must account for moving resources through
mailboxes or tasks, hook fan-out, cancellation, and cleanup. A scheduler may be
a library, but that remains a claim to test rather than an initial premise.

### 10. Optional replay and multi-shot continuations

Repeated resumption is later optional work. It requires both a duplicable
captured environment and an interpretation whose effects have meaningful
replay semantics. Effect API identity alone proves neither property.

## Evidence and failure ownership

Each slice should have a positive and negative corpus before a change proposal
selects semantics:

| Slice | Required evidence | Failure owned by |
| --- | --- | --- |
| Module `newtype` | Distinct declarations over one representation remain unequal; transparent and opaque imports preserve the defining identity; wrapping erases without allocation. | Resolution, kind checking, type checking, summary validation, or Core validation. |
| Local `newtype` | Nested identities do not mix; scope and shadowing are deterministic; generalization and recursive binding do not leak an unnameable type accidentally. | Resolution or type checking at the introducing or escaping construct. |
| Scoped evidence | Exact evidence solves only its identity-equal goal; representation evidence is not inherited; a concrete global implementation cannot hijack selection; generated Core evidence validates independently. | Constraint elaboration before Core construction, or Core evidence validation for malformed compiler output. |
| Effect kernel | Rows track outstanding requirements; nested handlers preserve order; one-shot resume and discard satisfy their contracts; unrelated effect identities do not collapse. | Effect typing, handler typing, continuation-use checking, or the validated runtime boundary. |
| Resource scope | Separate acquisitions do not mix; normal, rejected, and nested scopes account for values and identity-local requirements; closures and continuations cannot hide an unaccounted resource. | Type, usage, effect, or lifetime checking at the construct that loses the obligation. |
| Synchronous hooks | Registration changes runtime behavior only while live; sequential order is observable and specified; subscriber effects and failures remain visible. | Registration, publication, subscriber, or owning handler according to the typed hook contract. |
| Cleanup and FFI | Cleanup occurs exactly as specified on every admitted exit; foreign failure creates no forged evidence or leaked partial resource. | The acquisition, cleanup, provider, or foreign boundary named by the failing transition. |
| Async and concurrency | Suspension and transfer preserve identities, ownership, handler context, cancellation, and cleanup; restricted values are not broadcast or replayed. | The suspension, transfer, scheduler, handler, or hook boundary that violates its declared contract. |

Resource measurements should include evaluator frame growth, retained capture
size, evidence and identity counts, hook-chain update and publication cost,
cleanup order, and linked runtime components. A program that uses only pure
`newtype` should acquire no effect, hook, scheduler, provider, or runtime
identity machinery.

Disposable prototypes may test one named slice and comparison corpus. Retain
only their design evidence unless a later accepted change proposal and task
adopt the behavior as product work.

## Intentional exclusions

This leading boundary does not include:

- dynamic loading, unloading, runtime package resolution, or runtime interface
  lookup;
- general existential types or ML-like module signatures;
- general local implementations, implementation shadowing, or automatic
  constraint lifting through a `newtype` representation;
- general dependent or refinement types;
- a complete ownership, borrow, region, or storage-policy system in the first
  resource slice;
- asynchronous hooks, a scheduler, or concurrency in the synchronous hook
  slice;
- multi-shot continuation semantics in the one-shot kernel; or
- a general native ABI or dynamic foreign-library loader in the first foreign
  provider slice.

These exclusions remove non-causal work. They do not claim that later features
will need different identities, constraints, handlers, or runtime
representations.

## Authority transitions

This note can guide comparison and decomposition only. Each source-visible
increment requires a change proposal that states its semantic delta, affected
specification areas, diagnostics, limits, and evidence. Each retained product
increment also requires an authorized task, implementation, positive and
negative tests, specification changes, and review. A non-language runtime
choice that converges independently requires an architectural decision before
product work.

No `effect-ash` tag or completion claim follows from this outline. The revised
`lib-ash` milestone is complete independently; this dependency analysis neither
closed it nor authorizes a later language increment.

## Open questions

- What exact `newtype` grammar and constructor rules best reuse nominal type
  declarations?
- Does a local recursive declaration group admit `newtype`, and if so, what
  recursion is meaningful for representation checking and erasure?
- At what point does a local pure identity instantiate, and how does that
  relate to an identity freshly established on each resource acquisition?
- What Core form or validated metadata must retain a `newtype` representation
  boundary until its last checked use?
- Does scoped exact evidence participate in fixed-snapshot improvement for an
  eligible known determinant key, and where does it enter the abstract, exact-
  current, and concrete complete-goal selection order?
- Which first pure relation best tests scoped exact evidence without effects?
- Which row representation and inference boundary is sufficient for the first
  closed and open effect cases?
- What minimum usage or lifetime rule prevents a resource-bearing closure or
  continuation from escaping its scope?
- Which cleanup rule applies to checked discard, handler abort, subscriber
  failure, cancellation, and partial foreign acquisition?
- May synchronous registration mutate a hook chain during publication, and
  which invocation observes that change?
- Which suspension representation preserves typed handler boundaries without
  treating every evaluator frame as capturable control?
- After causal prerequisites are met, which ready slice offers the best ratio
  of implementation effort to transferable evidence and usable behavior?
