# DN-0010: Identities and Resource Lifetimes

- ID: `DN-0010`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md), [DN-0012: Coeffects and Hooks](DN-0012-coeffects-and-hooks.md)

> This design note is informative. It explores possible future identity and lifetime semantics; it does not define current Ash, accept an architecture, or authorize roadmap work. The syntax and type notation in this note are illustrative.

## Question

Can one typed identity model connect static equality, runtime resolution, resource ownership, staged removal, and captured continuations without requiring a monolithic runtime context or general dependent typing?

## Context and scope

Several possible future facilities need to say that values and runtime relationships refer to the same entity:

- two parts of a handler/provider binding;
- a provider and resources it creates;
- a hook and its registrations;
- a dynamically loaded module and exported objects;
- a continuation and the resources or code it retains.

This note explores identity as the common substrate. It does not define all effects as identity changes: reads, writes, sends, queries, logging, and other operations may create or remove no identity. Nor does every identity automatically become a security capability. Policy remains a possible library interpretation of typed relationships.

The source exploration was influenced by reversible acquisitions and delayed provider withdrawal. The candidate Ash model applies those lifecycle insights to independently represented identities and relationships instead of treating the runtime as one replaceable context.

## Suggested design rules

### Connect static and runtime identity

> Suggested rule: An identity has type-level meaning and a runtime representation that supports equality and resolution while preserving its identity through opaque or existential packaging.

Conceptually:

```text
type-level identity a
        ^
        |
runtime witness for a
```

An effect instance might therefore use `Database<a>` rather than a string key. A handler and provider parameterized by `a` can be known to agree, while a provider parameterized by fresh `b` does not match merely because it implements the same named API.

### Use one identity concept across introduction stages

> Suggested rule: Treat compile-time, link-time, load-time, and run-time introduction as stages at which an identity becomes known, not as distinct semantic kinds of identity, until a counterexample requires a distinction.

What changes by stage is the available evidence, naming scope, lifetime, and whether a witness can be erased. The identity's equality meaning need not change.

### Model runtime structure as local typed relationships

> Suggested rule: Describe runtime structure in terms of identities and typed relationships, without requiring one universal registry, state object, lock, or synchronization domain.

A semantic graph may include edges such as:

```text
implements
handles
owns
borrows
depends-on
subscribes-to
```

This graph is a reasoning model. An implementation can keep independent resources in separate data structures with separate synchronization.

### Separate ownership from provenance

> Suggested rule: The code or module that defines a constructor does not thereby own every resource later created through that constructor; acquisition establishes ownership and dependency explicitly.

If module `M` defines `makeConnection` and another scope calls it to create `Connection<c>`, `M` is the code provenance of the implementation. The owner could be an application, request, process, resource scope, or another subsystem. Module code may nevertheless need to remain loaded while the connection's operations or destructor depend on it.

### Separate withdrawal from destruction

> Suggested rule: Make an identity unavailable for new resolution before destroying it when existing dependents need time to unwind.

A candidate lifecycle is:

```text
available
    |
    v
withdrawn from new resolution
    |
    v
draining existing dependents
    |
    v
removed
```

The exact mechanism may involve leases, ownership, borrowing, reference edges, explicit drain protocols, or a combination. The semantic distinction matters even if the first runtime uses a simpler mechanism.

### Preserve stable bindings

> Suggested rule: Replacing an available provider changes candidates for new bindings; it does not silently retarget existing bindings to a fresh identity.

For:

```text
Database<a> replaced by Database<b>
```

the identities remain unequal:

```text
a != b
```

Existing consumers bound to `a` could finish, migrate explicitly, fail and reconstruct, or follow library-defined recovery. Transparent mutation underneath an ongoing computation would erase the provider identity guarantee.

### Distinguish acquisition cleanup from universal reversal

> Suggested rule: Use identity lifetime to model acquisitions with cleanup, but do not claim that every effect has an inverse.

These pairs naturally create and remove resources:

```text
open / close
register / deregister
allocate / free
spawn / terminate
```

These emissions generally do not have an inverse supplied by the core:

```text
send packet
charge card
print output
write to an uncontrolled service
```

Transactions, compensation, deferred emission, idempotency, or recovery may address particular cases.

## Candidate model

### Identity witnesses and packages

A difficult dynamic association could be packaged schematically as:

```text
exists a.
{
    identity : Identity<a>,
    provider : Provider<a>,
    handler  : Handler<a>
}
```

Outside code cannot name `a`, but opening the package preserves the equality shared by its members. The working hypothesis is that parametric polymorphism, associated types, opaque or existential types, and identity witnesses cover the important cases without allowing arbitrary runtime values in types.

The hypothesis must be tested. If it fails, the failure should identify the missing relationship before Ash considers stronger type machinery.

### Identity layers

One representation might support several semantic roles:

```text
effect API identity
operation identity
hook identity

handler instance identity
provider identity
resource identity
module instance identity
registration identity
```

Uniform machinery does not imply that the roles are interchangeable. A provider may create many connections; a module instance may export several handlers; a registration may depend on a hook and capture a connection. The model needs typed edges rather than accidental identity equality between these layers.

### Creation

Many operations can introduce a fresh identity:

```text
load module
open connection
spawn process
create provider
install handler
allocate resource
create subscription
```

Their common structural result is:

```text
operation
    |
    v
Create(a)
    |
    v
new values and relationships involving a
```

The type system must explain how fresh `a` enters a scope. The runtime must represent `a` long enough to compare, resolve, retain, and remove it.

### Removal and draining

For a provider `p`, staged removal might perform:

```text
1. reject new bindings to p
2. notify or invalidate dependent relationships
3. allow existing dependents to unwind
4. release references or leases
5. remove p
6. release resources owned by p
```

Sequential acquisition often produces LIFO cleanup:

```text
create a
create b
create c

remove c
remove b
remove a
```

Dependency edges can require a more general order. Cycles, transfer, shared ownership, and partial failure make this an open lifetime problem rather than a requirement to implement a stack.

### Ownership, references, and code reachability

The candidate graph needs to distinguish at least:

- ownership, which determines responsibility for cleanup;
- dependency, which prevents removal while another object needs the identity;
- borrowing or leases, if temporary access does not transfer ownership;
- provenance, which records which code implements operations or destruction.

These distinctions are especially important for module unloading. A module cannot be reclaimed while a live handler, callback, destructor, or suspended continuation still needs its code. [DN-0011](DN-0011-modules-providers-and-resolution.md) develops the unloading sequence.

## Interactions and failure cases

### Continuations retain a world

An escaping continuation may capture:

```text
Provider<a>
Handler<b>
Resource<c>
```

If one identity begins removal before resumption, plausible semantics include:

- the continuation retains it and delays removal;
- resumption fails because the capture was weak;
- the continuation migrates or rebinds explicitly;
- different identity roles use different capture modes.

Implicitly resolving a new provider at resumption would violate stable binding unless the program explicitly requested rebinding.

[DN-0009](DN-0009-effects-handlers-and-continuations.md) asks where continuation escape and multiplicity appear in the type system. This note asks what those contracts require of ownership and removal.

### Multi-shot duplication

If a continuation captures `Resource<a>` and resumes twice, both branches might share `a`, clone some state, or be rejected. The answer depends on the resource:

- immutable data may be shareable;
- mutable state may require synchronization;
- a linear resource may forbid duplication;
- transactional state may require one transaction per branch or no multi-shot use.

Continuation multiplicity therefore may need to interact with linearity, borrowing, ownership, and effect constraints. It cannot safely remain a lowering detail.

### Registrations

A hook registration is itself an acquired identity and may depend on a hook, provider, handler, and values captured by its subscriber. Removal of any dependency may require deregistration, invalidation, draining, or rejection of later calls. [DN-0012](DN-0012-coeffects-and-hooks.md) covers publication and composition; the same general lifetime machinery should cover the registration.

### Provider replacement

A failure case arises when resolution caches by API name or implementation type instead of identity. A replacement that looks structurally identical could then change the behavior of an existing computation without an explicit transition. Tests must bind by witness and demonstrate that only new resolution selects the replacement.

### Modules

Loading can introduce existential identities, but module provenance must not become a universal owner edge. Unloading needs to withdraw module-provided bindings, prevent new module-originated objects, drain live objects that require module code, and only then reclaim the module. A global "remove module and all things reached from it" operation would destroy resources owned elsewhere.

### Security capabilities

Creating `Connection<a>` may make operations involving `a` available, but it does not by itself decide who may exercise them. An authorization handler can interpret identity relationships as capabilities. The core identity model should support that library without assigning one security meaning to every identity.

## Evidence and experiments

### Existential-resolution prototype

Build a disposable type-model prototype that packages a fresh provider, opens it through a known interface, resolves a matching handler, and rejects a handler for a different hidden identity. Compare:

- existential packaging plus witnesses;
- associated-type equality evidence;
- a more dependent store encoding used only as a control.

Retain the simpler approach only if it can express the equality relationships without unsafe casts or name-based lookup. Discard the prototype code after recording the expressiveness and diagnostic results.

### Lifecycle state machine

Specify a small transition system for creation, availability, withdrawal, draining, and removal. Test:

- new resolution after withdrawal;
- existing use during draining;
- nested LIFO acquisition;
- non-stack dependency ordering;
- ownership transfer;
- shared dependents;
- a dependency cycle;
- failure during cleanup.

The comparison criteria are deterministic permitted transitions, no use after final removal, and an explanation of who may advance each state.

### Stable replacement test

Resolve one consumer to `Database<a>`, introduce `Database<b>`, withdraw `a`, and verify:

- the existing consumer does not silently rebind;
- a new consumer may select `b`;
- `a` remains usable or fails according to its declared drain policy;
- final removal waits for or invalidates every retained dependency according to explicit rules.

### Captured-continuation matrix

Cross continuation modes with immutable, synchronized mutable, linear, transactional, handler, registration, and module-code identities. Record whether each combination shares, retains, clones, rejects, or requires a runtime check. A useful type design should make common safe cases concise and unsafe cases visible.

### Runtime representation probe

Compare candidate runtime witnesses for equality, hashing, compact storage, and lifetime tracking. Verify that statically proven equalities can erase checks while dynamically introduced witnesses survive opaque packaging. This experiment selects representation evidence, not language semantics.

## Open questions

- What constitutes identity equality statically and dynamically?
- How is a fresh identity introduced into the type environment and delimited in scope?
- Can all identity roles share one witness representation without becoming interchangeable in types?
- Which identities are compile-time constants, which require runtime storage, and when may witnesses be erased?
- Are existential packages and associated types sufficient for dynamic handler/provider resolution?
- What does removal mean to code that still holds a value parameterized by the identity?
- Which relations are ownership, dependency, borrowing, leasing, or provenance, and which affect liveness?
- Can ownership transfer, and how is it checked?
- How are shared ownership and dependency cycles collected or broken?
- Who initiates and completes draining, and how are failures or cancellation handled?
- Can a weakly captured identity make continuation resumption fallible in a typed way?
- When may a suspended continuation keep provider or module code alive indefinitely?
- How do multi-shot continuations interact with linear and transaction-scoped resources?
- What migration protocol, if any, can replace a captured provider identity safely?
- How are resource destructors represented when the code implementing them belongs to an unloadable module?
- Which acquisitions require strict LIFO cleanup, and which require dependency-driven order?
