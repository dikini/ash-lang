# DN-0011: Modules, Providers, and Resolution

- ID: `DN-0011`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md), [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md), [DN-0012: Coeffects and Hooks](DN-0012-coeffects-and-hooks.md)

> This design note is informative. It explores possible future module and resolution semantics; it does not define current Ash, accept an architecture, or authorize roadmap work. The syntax and type notation in this note are illustrative.

## Question

Can static linking and dynamic loading use one typed resolution model while modules remain passive packages, loaded interiors may stay opaque, and unloading respects the lifetime of code and resources?

## Context and scope

A future Ash program may need to resolve interfaces, effect handlers, provider requirements, hook subscribers, and module exports. Some relationships will be known during compilation or linking. Others may become known only when a package, identity, or runtime parameter arrives.

This note explores the hypothesis that those cases differ primarily in resolution stage, not in composition semantics. It focuses on modules as packages and on the typed relationships among their contents. It does not define a general plugin marketplace, activation framework, component scheduler, dynamic type universe, or universal registry.

Providers appear here because they are resolution targets and module exports. Their semantic separation from handlers and effect APIs is developed in [DN-0009](DN-0009-effects-handlers-and-continuations.md); their stable identity and lifetime are developed in [DN-0010](DN-0010-identities-and-resource-lifetimes.md).

## Suggested design rules

### Keep modules passive

> Suggested rule: A module packages definitions and metadata; loading it makes those contents available but does not implicitly start an active component or register runtime behavior.

A module may package:

- code and types;
- effect APIs;
- interfaces and implementations;
- handler definitions;
- provider implementations;
- resource constructors;
- subscriber definitions;
- metadata needed for typed discovery and elaboration.

The loader or ordinary program code performs orchestration. A load handler may choose to construct resources or registrations, but that is an explicit loading policy rather than an intrinsic module lifecycle.

### Share static and dynamic composition semantics

> Suggested rule: Resolve the same typed relationships at compile time, link time, load time, or run time according to when the required information becomes available.

For example:

```text
required interface + available impl = resolved implementation
required effect    + available handler = resolved interpretation
handler need       + available provider = resolved provider
hook identity      + compatible subscriber = registration
```

When all evidence is static, the compiler can specialize and erase witnesses. When evidence arrives later, the runtime retains typed witnesses and indirection. The two paths should not assign different meanings to the resolved relationship.

### Treat loading as delayed elaboration

> Suggested rule: Model dynamic loading as ordinary module elaboration performed later with runtime-supplied parameters and identities.

The two stages can be compared as:

```text
module package + known parameters
    -> compile/link elaboration
    -> resolved identities and implementations

module package + runtime parameters or identities
    -> runtime elaboration
    -> resolved identities and implementations
```

Loading changes the controlled runtime world and is therefore a plausible future effect. A load handler might validate a package, map code, instantiate identities, resolve exports, construct selected resources, reject the load, or publish hooks. None of those possibilities gives loading an automatic relationship to coeffect registration.

### Resolve by typed identity

> Suggested rule: Static and dynamic discovery use typed identities and compatibility evidence rather than string names or untyped shape matching.

Tooling and loaders should eventually be able to answer:

- which known effect APIs are present;
- which handlers interpret them and what lower effects those handlers require;
- which providers satisfy handler constraints;
- which hook identities are exported;
- which subscribers are type-compatible;
- which types or identities are hidden existentially.

When all facts are already known, this discovery collapses into ordinary linking.

### Preserve a statically known boundary

> Suggested rule: Already compiled Ash code interacts with dynamically loaded contents through a statically meaningful outer contract, while arbitrary module-internal types and protocols may remain opaque.

One candidate package boundary might expose an existential contract:

```text
exists a.
    KnownModuleAPI<a>
```

A different candidate might expose only a statically known transport boundary while implementing TLS, HTTP, a proprietary protocol, or an interpreter internally. In either case, dynamic loading need not extend the set of APIs the existing program can name directly.

### Keep loading and registration orthogonal

> Suggested rule: Loading may make subscriber code and hook identities available, but registration and deregistration remain separate acquisitions that occur only when their required identities are valid.

This avoids an implicit module-activation lifecycle and lets an application, request, process, or resource scope own a registration independently of the module that supplied its code.

### Unload only after code dependencies drain

> Suggested rule: Withdraw module-provided bindings and stop creating module-originated objects before reclaiming code; keep the module resident while live handlers, callbacks, destructors, or suspended continuations still require it.

Ownership and code provenance are separate. Unloading cannot assume that every object created with module code is owned by the module, but it must account for each object's dependency on that code.

## Candidate model

### Package and contract

A module package could carry:

- a statically known outer contract;
- code and data for its implementation;
- export identities and requirements;
- existentially hidden identities or associated types;
- compatibility metadata or witnesses;
- constructors whose invocation is separate from package loading.

This model lets a loaded module contain an opaque sub-world. The surrounding program needs to understand only the boundary. A more ambitious future design might let one module expose a manifest or proof for an opaque API and request another compatible module. That should remain outside the initial experiment until ordinary existential boundaries prove insufficient.

### Elaboration and resolution

Resolution could be expressed as typed constraints over identities. The same engine might support:

```text
interface/impl
effect/handler
handler/provider
hook/subscriber
module import/export
```

It may share generic and associated-type resolution, witness or dictionary construction, existential opening, and specialization. Semantic rules still differ: a handler transforms effect rows and controls continuations, while an `impl` dictionary does not.

The result of runtime elaboration may resemble:

```text
exists module_id provider_id handler_id ... .
    LoadedModule<module_id, provider_id, handler_id, ...>
```

The package keeps hidden identities related while exposing only the operations permitted by its known contract.

### Modules in handler chains

A loaded module may provide, consume, or transform effects rather than acting only as a terminal provider:

```text
Application
    | Http
    v
Retry module
    | Http
    v
Http-over-Network module
    | Network
    v
runtime provider
```

The retry module consumes and provides `Http`. Another module might provide `Filesystem` by consuming `ObjectStore`. Dynamic composition therefore needs the same handler-transformation model as static composition.

### Provider discovery

A provider can realize several effect APIs or expose lower-level resources from which handlers build interpretations:

```text
PostgresRuntime
    +-- Database provider
    +-- Transaction provider
    +-- Notification provider
```

Resolution should use ordinary type constraints and identity equality rather than a fixed one-provider/one-effect registry entry. Replacing one provider identity affects new bindings; [DN-0010](DN-0010-identities-and-resource-lifetimes.md) explains why existing bindings remain stable unless explicitly migrated.

### Unloading

A candidate unload sequence is:

```text
request unload
      |
      v
prevent new module-originated objects
      |
      v
withdraw module-provided bindings
      |
      v
drain or remove live objects requiring module code
      |
      v
release module-level resources
      |
      v
unmap or reclaim module
```

The loader or library may select a policy: wait, reject unload, cancel dependents, or require explicit migration. The core identity/lifetime model must at least make outstanding dependencies observable and prevent use of reclaimed code.

## Interactions and failure cases

### The static type world

A dynamically loaded module can contain APIs unknown to already compiled code, but those APIs remain inside an opaque boundary. Treating load as permission to add arbitrary named types to the running type checker would create a second dynamic language and prevent ordinary static compatibility checks.

Conversely, requiring Ash to understand every internal protocol would make typed loading unnecessarily restrictive. A known byte-transport or interpreter interface can safely contain richer opaque machinery.

### Identity lifetime

Loading may introduce module, provider, handler, resource, and registration identities. They have distinct ownership and dependency edges. The module's provenance does not make it the owner of all later resources, but those resources can keep module code live. [DN-0010](DN-0010-identities-and-resource-lifetimes.md) explores withdrawal, draining, and captured identities.

### Coeffect registration

The sequence:

```text
load module M
    -> subscriber implementation S becomes available

register S with Hook<h>
    -> Registration<r>

deregister r
    -> M may remain loaded
```

must be possible. A loader may explicitly combine those operations, but automatic registration on load would blur discovery, acquisition, ownership, and policy. Hook publication and registration are explored in [DN-0012](DN-0012-coeffects-and-hooks.md).

### Loading as an effect

If load is effectful, a handler may reject it, validate signatures or policy, introduce identities, and publish phases. That does not make module loading the sole source of identities: opening a connection, spawning a process, installing a handler, or creating a subscription can introduce identities during ordinary execution.

### Name-based discovery

String names can support diagnostics or package metadata, but using them as semantic equality would permit unrelated providers or hooks with matching names to bind. The resolver must preserve typed identity witnesses through existential opening.

### Separate static and dynamic implementations

Two unrelated resolution engines risk drift: the same module graph could type-check statically and bind differently after runtime loading. A common semantic model does not require one code path, but both implementations should produce equivalent typed relationships when given equivalent evidence.

### Code reclamation

Immediate unload after withdrawing exports is unsafe if:

- a handler implemented by the module remains installed;
- a callback implemented by the module remains registered;
- a resource destructor points into module code;
- a suspended continuation can resume into module code.

A correct design must expose or retain these dependencies rather than depending on callers to remember them informally.

## Evidence and experiments

### Static/dynamic equivalence fixture

Construct one small module graph containing an interface implementation, a transforming effect handler, a provider, an exported hook, and a compatible subscriber. Elaborate it once with all identities known and once after loading an existential package. Compare:

- accepted and rejected bindings;
- associated-type equalities;
- handler order and row transformation;
- runtime witnesses retained;
- opportunities for specialization;
- diagnostic quality.

Equivalent evidence should produce equivalent behavior. Keep only design conclusions; discard any loader scaffolding that does not become independently justified architecture.

### Opaque sub-world case

Load a package exposing a known byte transport while internally interpreting an unknown protocol. Verify that the host can store, pass, invoke, and unload the package through the known contract without naming its hidden types. Add a second package requiring a compatible hidden identity to test the limit of existential opening.

### Discovery surface

Prototype a machine-readable and human-readable view that reports provided and required typed identities, effect transformations, hook compatibility, and hidden associated types. Test collision cases where display names match but identities differ. The goal is to validate the semantic information needed, not to select a final package format or tool UI.

### Loading and registration separation

Exercise these cases:

- load without constructing resources;
- construct a provider later;
- register and deregister a subscriber while the package stays loaded;
- let another scope own a resource built by module code;
- unload while no code dependencies remain.

The experiment should reveal any hidden activation assumption in the candidate API.

### Unload stress cases

Request unload while each of these remains live: a handler, callback, resource destructor, provider binding, and suspended continuation. Compare wait, rejection, cancellation, and explicit migration policies. The core criterion is that no policy permits reclaimed code to remain reachable.

## Open questions

- What exact outer contract and evidence must a loadable package carry?
- Which parts of elaboration can share implementation between compiler, linker, and runtime?
- How are package authenticity, ABI compatibility, and version compatibility represented without making them language semantics prematurely?
- How does dynamic resolution open existential identities and preserve associated-type equalities?
- Are opaque types, existentials, associated types, and witnesses sufficient for every important dynamic binding case?
- How are ambiguity, priority, and multiple compatible providers handled?
- Is provider selection deterministic, explicit, scoped, or policy-controlled?
- Which discovery facts are semantic and which are only metadata for tools?
- Can one loaded opaque sub-world request another package satisfying a contract it introduced, and what statically known bridge would make that safe?
- What is the result and lifetime type of a load operation?
- Who owns identities and resources created during load if elaboration fails partway through?
- How are partial construction and rollback handled for effects that are not reversible?
- What prevents new objects during unload without imposing a global lock?
- How are cycles among module-code dependencies detected or broken?
- May unload cancel or invalidate suspended continuations, and how is that visible in their types?
- Which resolved artifacts can be cached, and how are caches invalidated when identities withdraw?
