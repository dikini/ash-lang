# Ash Algebraic Effects — Initial Design Note

## Status and intent

This note records the current design direction for algebraic effects in the Ash reboot. It is an initial architectural note, not a language specification.

A major goal of the reboot is to keep the Ash language/runtime core relatively small while making it expressive enough that higher-level mechanisms can move into libraries. Previous Ash concepts such as capabilities, access-control policies, roles, and similar policy mechanisms should, where possible, be expressible using the general machinery described here rather than retained as privileged language concepts.

The discussion was prompted in part by work on reversible effects and reactive coeffects in dynamically changing component systems. That work exposes several important problems—dynamic introduction and withdrawal of services, dependencies, rollback, provider identity, and reactive composition—but Ash approaches them from a different starting point.

Ash expects to have:

- algebraic effects;
- polymorphic effect rows;
- parametric polymorphism;
- interfaces and `impl`;
- associated types;
- opaque/existential types;
- unique identities with runtime representations;
- static and dynamically loaded modules.

These facilities should allow much of what other systems express using universal dynamic contexts or dependently typed key/value stores to be expressed instead through ordinary type relationships and identity resolution.

The central emerging picture is:

> **Effects define typed APIs. Handlers interpret those APIs. Providers supply concrete realizations. Identities connect the static and runtime worlds. Coeffects provide typed extension points in handler control flow. Modules package code, while linking/loading determines when enough information becomes available to resolve the pieces.**

---

# 1. Effects specify APIs, not protocols

An Ash effect declaration defines a typed API for an interaction.

Conceptually:

```ash id="5f6d89"
effect Database {
    query : Query -> Result
    begin : () -> Transaction
}
```

An effect declaration may establish:

- an effect identity;
- operation identities;
- operation argument and result types;
- generic parameters;
- associated types;
- other static relationships;
- public coeffect hook identities.

It does **not** necessarily specify a protocol in the stronger sense of the legal temporal ordering of operations.

For example, an API containing:

```text id="b8a8f0"
begin
query
commit
rollback
```

does not itself say that:

```text id="16c7b7"
begin
query*
(commit | rollback)
```

is the legal protocol.

Such protocols may be expressible using typestate, session types, state-indexed APIs, or other abstractions constructed using Ash's type system.

They should remain a **library concern unless experience demonstrates that core language support is necessary**.

Thus:

```text id="73e97e"
effect
    = typed interaction API

protocol
    = constraints on interaction over time
```

---

# 2. Effect rows describe outstanding requirements

A computation may have a type such as:

```ash id="e81c36"
fn f(...) -> T ! { Database, Log | e }
```

The effect row describes effect APIs whose operations may escape the computation and therefore require interpretation.

Effect-row composition is structural. Row ordering does not imply execution or handler ordering.

Conceptually:

```text id="abcb51"
{ Database, Log | e }
=
{ Log, Database | e }
```

subject to the eventual precise row algebra.

This must not be confused with commutativity of effect operations.

Effect-row composition describes requirements, not execution order.

The exact algebra remains to be formalized, including multiplicity, identity-bearing instances, subtraction, forwarding, and open rows.

---

# 3. Effects, handlers, and providers are distinct

Three concepts should remain separate even though their implementations may share machinery.

## Effect

The effect defines the API.

## Handler

The handler defines an interpretation of the effect.

A handler may:

- implement the effect directly;
- use a provider;
- translate the effect into other effects;
- wrap another handler;
- alter continuation behavior;
- expose and publish coeffect hook points.

## Provider

A provider supplies a concrete implementation or resource used by an interpretation.

Conceptually:

```text id="ea6b17"
Database API
     |
     v
Database handler
     |
     v
Postgres provider
```

A handler might instead translate:

```text id="9f2d3a"
Http
  |
  v
Http handler
  |
  +-- Network
  +-- Clock
  +-- Entropy
```

A dynamically loaded module may therefore provide handlers, consume effects, provide resources, or combine all of these roles.

---

# 4. Relationship to interfaces and `impl`

The relation between an effect and its handler resembles the relation between an interface and an implementation.

| Interface machinery | Effect machinery |
| --- | --- |
| interface | effect API |
| method | effect operation |
| `impl` | handler |
| implementation dictionary | handler dictionary/binding |
| monomorphization | handler specialization |

This similarity should influence both surface syntax and implementation.

Both abstractions need similar parameterization mechanisms:

- generic parameters;
- associated types;
- identity parameters;
- constraints;
- witness/dictionary passing;
- static specialization.

The compiler may plausibly implement both using closely related machinery.

They remain distinct because handlers additionally participate in continuation control and coeffect execution.

---

# 5. Handler composition is ordered

Effect-row composition and handler composition are fundamentally different.

Handlers form ordered interpretations:

```text id="f17412"
H3 ∘ H2 ∘ H1
```

In general:

```text id="ebdf56"
H1 ∘ H2 != H2 ∘ H1
```

Strict handler ordering should therefore be the general rule.

If particular handlers can be proven independent or commuting, that may later permit optimization, but commutativity should not be assumed.

A formal handler calculus remains to be developed, including:

- composition;
- open rows;
- forwarding;
- partial interpretation;
- first-class handlers;
- handler identity;
- handler lifetime;
- effects introduced by handlers.

---

# 6. Continuation semantics are fundamental

An algebraic effect operation cannot be characterized completely as:

```text id="ab9ca4"
A -> B
```

because a handler also interacts with the continuation.

Important cases include at least:

### One-shot

The continuation may be resumed at most once.

### Multi-shot

The continuation may be resumed multiple times.

### Abortive / non-resumable

The continuation may be discarded.

### Suspensive / escaping

The continuation may escape the immediate handler invocation and resume later.

These distinctions affect transactions, resource safety, nondeterminism, async computation, workflows, and other libraries.

A transaction surrounding a one-shot continuation has an intuitive interpretation:

```text id="95a563"
begin
run continuation
commit or rollback
```

With a multi-shot continuation, the semantics are not obvious:

```text id="c6f58a"
clone transaction state?
one transaction per branch?
reject the composition?
```

Continuation semantics are therefore part of the semantic contract, not merely an implementation optimization.

A major open question is where and how the continuation contract is expressed: per effect, per operation, per handler, inferred, or some combination.

---

# 7. Identities connect static typing and runtime resolution

Ash needs a uniform concept of **identity** which is:

- unique at the type level;
- represented by a runtime value;
- usable for runtime comparison and resolution;
- preservable through opaque and existential types.

Conceptually:

```text id="ff46f6"
type-level identity α
        ↕
runtime witness/value for α
```

This is likely singleton-like, although the exact representation remains open.

An effect instance may conceptually involve:

```text id="c98775"
Database<α>
```

rather than a string such as `"Database"`.

The same identity can parameterize pieces that must agree:

```text id="eb34c9"
Handler<Database, α>
Provider<Database, α>
```

while a provider involving `β` does not accidentally match merely because it implements the same named API.

---

# 8. Identities should be uniform

There is currently no compelling reason to distinguish “generative” identities from “normal” identities.

An identity may become available:

- during compilation;
- during linking;
- during dynamic module loading;
- during ordinary execution.

These are different stages of introduction, not different kinds of identity.

What varies is:

- when the identity becomes known;
- which scope can name or carry it;
- how long it remains valid;
- whether it is exposed or hidden existentially.

---

# 9. Identity creation and removal are fundamental runtime events

Module loading is only one source of new capabilities.

Any operation that creates a new identity may introduce capabilities:

```text id="e32767"
load module
open connection
spawn process
create provider
install handler
allocate resource
create subscription
```

All have the general shape:

```text id="7241ad"
operation
    |
    v
Create(α)
    |
    v
new capabilities involving α
```

Removal is equally fundamental:

```text id="11c4b8"
Remove(α)
```

Examples include unloading a module, closing a connection, terminating a process, disposing a resource, removing a provider or handler, and deregistering a subscription.

Creation and removal of identities are therefore fundamental changes in the runtime capability world.

---

# 10. The runtime is conceptually an identity graph, not a giant context

A useful semantic model is a typed graph:

```text id="b77f36"
identities
    |
    +-- implements
    +-- handles
    +-- owns
    +-- depends-on
    +-- subscribes-to
```

Creation adds identities and relationships.

Removal invalidates identities and removes or transforms relationships.

This does **not** imply a literal global graph, universal registry, synchronization domain, or global lock.

Independent resources should remain independently represented and synchronized.

---

# 11. Existential packages may replace dependent runtime stores

Ash should first attempt to solve dynamic association using:

- opaque types;
- existential packages;
- associated types;
- generic constraints;
- identity witnesses.

Conceptually:

```text id="0bbdd6"
exists α.
{
    identity : Identity<α>,
    provider : Provider<α>,
    handler  : Handler<α>
}
```

Outside code need not know what `α` is. It needs only to preserve the fact that the members refer to the same identity.

This may provide much of the required dynamic safety without introducing full dependent types.

---

# 12. Coeffects are typed extension points in effect execution

The event-system vocabulary remains useful:

```text id="bdb8b5"
publish event
    ≈
perform effect operation

subscribe to event
    ≈
register coeffect handling
```

Ash does not need a generic event bus to implement this.

Coeffects attach typed reactions to explicitly exposed points in handler control flow.

This provides a connection to event systems, AOP join points, framework hooks, React-style lifecycle mechanisms, and reactive systems without requiring their usual implementation models.

Messaging, processes, streams, and similar abstractions remain separate concerns.

---

# 13. Hook points are part of the effect API

A public hook point has:

- a unique type identity;
- a runtime representation;
- a payload/type contract.

An effect API therefore contains:

```text id="c8f8a7"
Effect API
    |
    +-- effect identity
    +-- operation identities
    +-- public hook identities
```

This supports:

- static linking;
- dynamic registration;
- type resolution;
- discoverability;
- documentation;
- tooling;
- compatibility checking.

Possible designs include fixed `before`/`after` hooks, per-effect hooks, per-operation hooks, and explicit arbitrary named hooks. These approaches need not be mutually exclusive.

The important invariant is that public hook points are typed API identities, not string-named events.

---

# 14. Handlers give hook points their operational meaning

Although hook identities belong to the effect API, handlers determine their placement in control flow.

Conceptually:

```text id="6b23ef"
receive operation
      |
      v
publish hook A
      |
      v
perform handler work
      |
      v
publish hook B
      |
      v
resume continuation
```

Thus:

- the effect API defines hook identity and type;
- the handler determines where the hook occurs;
- registration associates subscribers with the hook identity;
- reaching the point publishes to the associated coeffect chain;
- execution continues according to the handler's continuation semantics.

Private handler control points remain implementation details unless exposed as public hook identities.

---

# 15. Coeffect registration is separate from module loading

Registering a coeffect is a runtime action distinct from module loading.

Registration may occur:

- during a module-load handler;
- during explicit initialization;
- during ordinary execution;
- temporarily within another scope;
- in reaction to another effect;
- at any point where the identities required by the registration remain valid.

Therefore:

```text id="efb078"
module load
    !=
coeffect registration
```

A module can make subscribers or registration mechanisms available without registering them.

---

# 16. Coeffect composition has at least two forms

## Sequential composition

```text id="cc1554"
C1 ; C2
```

`C2` observes the result/context produced by `C1`.

This maps naturally to continuation chains:

```text id="34aace"
C1 -> C2 -> C3 -> continue
```

## Parallel composition

```text id="bb1434"
C1 || C2
```

Both react to the same hook without sequential dependence being part of their meaning.

Parallel composition requires semantics for:

- failure aggregation;
- result aggregation;
- conflict;
- independence;
- deterministic ordering;
- possible actual concurrency.

“Parallel” describes the algebraic relationship and does not necessarily imply simultaneous machine execution.

---

# 17. Coeffects may alter control flow

Coeffects are richer than passive observers.

Depending on the hook and handler semantics, a coeffect may potentially:

- observe;
- transform;
- reject;
- abort;
- suspend;
- introduce additional effects.

Temporal placement matters.

A pre-operation hook can potentially reject before the underlying transition occurs.

A post-operation hook runs in a world in which the transition has already happened, so failure there has different semantics.

The types available at different hook points may also differ. An operation that creates a fresh identity illustrates this directly:

```text id="ba982f"
before:
    identity α does not exist

operation:
    Create(α)

after:
    α is valid and may appear in types/values
```

The handler's continuation semantics determine how such hook behavior composes with the surrounding computation.

---

# 18. Coeffect execution should exploit continuation structure

A conventional event implementation might perform dynamic lookup and callback enumeration on every publication.

Ash should instead exploit the fact that:

- hook identities are typed;
- registrations change relatively infrequently;
- handlers already define continuation flow.

Registration can construct or update a cached chain:

```text id="c0568f"
registration
    |
    v
update hook/continuation chain
```

The hot path becomes:

```text id="71bb17"
handler reaches hook
       |
       v
cached chain
       |
       v
continue
```

Sequential coeffects naturally map to continuation chains.

Parallel coeffects may map to preconstructed fan-out structures.

When everything is statically known, compilation/linking may inline or monomorphize the chain entirely.

Thus the flexibility of coeffects need not imply the usual performance characteristics of a general event bus.

---

# 19. Modules are passive code packages

A module is not an active component.

A module packages things such as:

- code;
- types;
- effect APIs;
- interfaces and implementations;
- handler definitions;
- provider implementations;
- resource constructors;
- metadata.

Loading a module makes such machinery available.

It does not imply that the module itself begins executing as an independently active entity.

The loader or other external code performs orchestration.

This distinction is fundamental.

---

# 20. Static linking and dynamic loading are the same composition at different stages

Static linking and dynamic loading should not be modeled as two different semantic worlds.

The primary distinction is:

> **When does the information necessary to perform resolution become available?**

At compile/link time:

```text id="38b7bf"
known information
      |
      v
resolve
      |
      v
specialize
```

At runtime:

```text id="19bc21"
new information becomes available
      |
      v
resolve
      |
      v
retain necessary runtime indirection
```

Anything that can be resolved dynamically can in principle be resolved statically if the required information is available earlier.

The implementation should therefore avoid two unrelated systems for static modules and dynamic plugins.

Dynamic loading is an elaboration of the ordinary module system at a later stage.

---

# 21. Module loading is an effect

Loading a module changes the controlled runtime world and is naturally effectful.

Conceptually:

```text id="d55028"
load : ModuleImage<P> -> Loaded<P> ! { ModuleLoad }
```

A load handler may:

- validate;
- map code;
- instantiate identities;
- create resources;
- resolve exports;
- select loading mechanisms;
- reject the load;
- publish coeffect hooks.

But module loading remains only one particularly visible operation that introduces identities and capabilities.

It has no privileged relationship to coeffect registration.

---

# 22. Dynamically loaded modules and the static type world

A running Ash program can directly use only APIs/types for which it has a statically meaningful representation.

A dynamically loaded module may introduce:

- values;
- implementations;
- providers;
- handlers;
- resources;
- fresh identities;
- opaque/existential packages.

It cannot make an entirely new API directly usable by already compiled code that has no static way to refer to that API.

This does not prevent a loaded module from implementing arbitrary opaque internal protocols.

For example:

```text id="655749"
Ash-visible API:
    TCP / byte transport

module interior:
    TLS
    HTTP
    proprietary RPC
```

Ash need not know what happens inside the opaque boundary.

A possible future extension could permit modules to carry opaque protocol universes, manifests, witnesses, or proofs and then request loading of other compatible modules. Such mechanisms may even fall naturally out of Ash's eventual type system.

They are explicitly beyond the initial effects design.

---

# 23. Resource acquisition and reversal

The motivating paper's reversible-effect idea remains useful, but Ash should not interpret it as restoration of one monolithic context.

An effect may acquire identities/resources:

```text id