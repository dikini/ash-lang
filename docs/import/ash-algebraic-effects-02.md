# 23. Resource acquisition and reversal

The motivating paper's reversible-effect idea remains useful, but Ash should not interpret it as restoration of one monolithic context.

An effect may acquire identities and resources:

```text id="g9eaz8"
create α
create β
establish relationship α -> β
```

Cleanup may later remove those identities and relationships:

```text id="z7a6gn"
remove β
remove α
```

The important unit of reversal is therefore not necessarily:

```text id="d86uqb"
Γ -> Γ'
```

followed by a function restoring all of `Γ`.

It is the lifetime of the identities and relationships introduced into the portion of the world controlled by Ash.

This has several advantages.

Resources can remain independently represented and synchronized. There is no implication that unrelated resources participate in one global state or one global lock.

Reversal can also be local. Acquiring a subscription, connection, handler, provider, or other resource can produce whatever information is necessary to remove that particular identity later.

The paper's LIFO observation remains useful for sequential acquisitions:

```text id="0xyt70"
create α
create β
create γ

remove γ
remove β
remove α
```

but dependency relationships may impose more general removal orderings.

---

# 24. Ownership is separate from module provenance

The code that defines a resource operation need not own the resources created by that operation.

This is particularly important for dynamically loaded modules.

Suppose module `M` provides a constructor:

```text id="5cbjmr"
makeConnection(...)
```

and unrelated code later calls it, producing:

```text id="05sw3b"
Connection<α>
```

The connection is not automatically owned by `M` merely because its implementation code came from `M`.

Likewise, a module may provide a coeffect subscriber, but a registration created later may belong to:

- an application scope;
- a request;
- a process;
- another dynamically loaded subsystem;
- an explicitly managed resource scope.

Thus:

> **Module provenance and runtime ownership are distinct relationships.**

The operation performing an acquisition must establish the appropriate ownership/lifetime relationship.

This becomes important during module unload because code belonging to a module cannot safely disappear while live objects still depend on that code.

---

# 25. Removal is potentially a staged operation

Identity removal should not necessarily mean instantaneous disappearance.

The motivating paper contains a valuable observation here: a provider being withdrawn may still be required by existing dependents while they perform their own cleanup.

A useful general lifecycle is:

```text id="eovjvf"
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

For a provider identity `α`:

```text id="c3lknr"
1. stop establishing new bindings to α
2. notify/invalidate dependent relationships
3. allow existing dependents to unwind
4. release dependent references/leases
5. remove α
6. release resources owned by α
```

This prevents a provider from disappearing before consumers have had an opportunity to tear down safely.

The precise mechanism may use:

- leases;
- ownership relations;
- reference relationships;
- explicit drain protocols;
- some combination.

The semantic point is more important than the initial implementation choice:

> **Unavailability for new use and final destruction are distinct moments.**

---

# 26. Provider replacement should preserve identity semantics

A new provider that implements the same API is not automatically the same provider.

Suppose:

```text id="y3zayh"
Database<α>
```

is replaced by:

```text id="44dg7d"
Database<β>
```

Even if both have identical implementation types or expose equal values:

```text id="5f2wgd"
α != β
```

Existing computations or resources bound to `α` should not silently begin using `β`.

This preserves an important property identified by the motivating paper's committed-provider view.

A binding should normally remain stable for its lifetime:

```text id="vv7f55"
consumer
    |
    v
Database<α>
```

Replacement changes what may be resolved for **new** bindings.

Existing bindings must instead:

- continue until completion;
- be explicitly migrated;
- be invalidated and reconstructed;
- or follow some other semantics defined by the relevant library/handler.

Transparent mutation of provider identity underneath an ongoing computation should not be the default.

---

# 27. Modules may provide or consume handlers

A dynamically loaded module should not be classified merely as a provider.

Because handlers can translate effects, a module may occupy arbitrary positions in an interpretation chain.

For example:

```text id="thp45h"
Application
    |
    | Http
    v
Retry module
    |
    | Http
    v
Http-over-Network module
    |
    | Network
    v
runtime provider
```

The retry module both consumes and provides `Http`.

Another module might provide:

```text id="80rwlu"
Filesystem
```

by consuming:

```text id="z8c1b6"
ObjectStore
```

Thus dynamically loaded modules can contribute typed transformations:

```text id="2f71rk"
{ E | r }
    |
    v
handler
    |
    v
{ F, G | r }
```

This is one of the reasons dynamic modules should be treated as ordinary modules whose resolution happens later, rather than as a separate plugin abstraction.

---

# 28. Module load and coeffect registration remain orthogonal

A module load may create identities that make later coeffect registrations possible, but the two operations remain independent.

For example:

```text id="gzw2g6"
load module M
    |
    v
subscriber implementation S becomes available
```

Later:

```text id="mowzq3"
register S with Hook<α>
```

and later still:

```text id="uqgh60"
deregister S
```

while `M` remains loaded.

Alternatively, a load handler may itself choose to register `S`.

That is merely one orchestration policy.

The general rule is:

> **Coeffect registration may occur whenever all identities required by the registration are valid.**

The same applies to deregistration.

This avoids introducing an implicit “module activation” lifecycle that Ash does not need.

---

# 29. Static linking and dynamic loading should share resolution machinery

The same conceptual relationships exist regardless of when they become known.

For interfaces:

```text id="j6hpb7"
required interface
      +
available impl
      =
resolved implementation
```

For effects:

```text id="86z68c"
required effect identity
      +
available handler
      =
resolved interpretation
```

For providers:

```text id="rly2if"
handler requirement
      +
provider identity
      =
resolved provider
```

For coeffects:

```text id="bpx99l"
hook identity
      +
subscriber
      =
registration
```

When all information is known during compilation/linking, these relationships can be resolved and aggressively specialized.

When some information becomes available only at runtime, equivalent resolution must happen dynamically.

This suggests that Ash should seek a common underlying resolution mechanism rather than separate static and dynamic implementations wherever practical.

---

# 30. Dynamic loading is delayed elaboration

This gives a useful conceptual interpretation of dynamic module loading:

> **Dynamic loading is ordinary module elaboration performed at a later stage because some of its inputs were unavailable earlier.**

Static case:

```text id="cwrhwi"
module package
    +
known parameters
    |
    v
elaboration/linking
    |
    v
resolved identities and implementations
```

Dynamic case:

```text id="fxs50b"
module package
    +
runtime parameters/identities
    |
    v
runtime elaboration
    |
    v
resolved identities and implementations
```

The resulting relationships should obey the same type rules.

The runtime case merely retains representations of identities and witnesses that the statically resolved case may be able to erase.

---

# 31. Dynamic modules do not imply a dynamically extensible Ash type universe

A dynamically loaded module may contain types and APIs unknown to the already compiled program.

Those remain opaque unless the existing program has some statically known abstraction through which to manipulate them.

For example:

```text id="bdw29v"
exists α.
    KnownModuleAPI<α>
```

allows the program to manipulate an unknown `α` through the known API.

Similarly, a module may internally implement an entirely unknown network or application protocol while exposing only:

```text id="dchcax"
Transport<α>
```

to Ash.

Thus dynamic modules can contain arbitrarily rich opaque worlds without requiring runtime extension of Ash's statically understood type universe.

A more sophisticated future system might permit one dynamically loaded module to expose a proof/manifest for a new opaque API and request another module satisfying that API.

That possibility is interesting, but is beyond the initial design.

---

# 32. Capabilities become a library interpretation

Previous Ash capability mechanisms may be subsumed by the effect system.

If a computation can perform:

```text id="2n3gp2"
Filesystem
```

only when an appropriate handler is available, then access to the handler/provider relationship is already capability-like.

A library can implement access control by inserting an interpretation:

```text id="r4u4lq"
Filesystem
      |
      v
AccessControlHandler
      |
      v
FilesystemProvider
```

The handler may consult:

- caller identity;
- resource identity;
- policy state;
- role information;
- other effects.

The Ash core does not need to define the policy.

It provides the mechanisms from which the policy can be constructed.

---

# 33. Roles and policies should likewise be library concepts

Roles can be represented as compositions or packages of capabilities and handlers.

Policies can be implemented through:

- handlers;
- coeffect hooks;
- identity relationships;
- ordinary data and interfaces.

For example:

```text id="g2f4tq"
Before<File.write>
    |
    v
policy subscriber
    |
    +-- permit
    +-- reject
```

or an authorization handler may wrap the entire effect.

These choices have different semantics and should remain available to library authors.

The core should not prescribe one universal access-control model.

This reflects a broader reboot principle:

> **The Ash core should provide mechanisms for interaction; libraries should define policies governing interaction.**

---

# 34. Transactions illustrate the boundary of library abstraction

Transactions are likely implementable as libraries, but only after Ash specifies the continuation semantics on which they depend.

A transaction abstraction may combine:

- effect handlers;
- resource acquisition;
- coeffect hooks;
- protocol/typestate libraries;
- provider-specific behavior.

But whether such a transaction is sound under:

```text id="zc0m5e"
one-shot
multi-shot
escaping
abortive
```

continuations is a property of the core effect semantics.

Thus “move to libraries” does not mean “the core has no semantic obligations.”

The core must expose sufficiently precise guarantees for libraries to prove or type-check their own abstractions.

---

# 35. Protocols remain a library concern

Effects define APIs, not interaction protocols.

Protocol mechanisms such as:

- session types;
- typestate;
- state machines;
- linear sequencing constraints;

should initially be built from Ash's type system and libraries.

For example, an effect may expose:

```text id="kcnjkr"
send
receive
close
```

while a library defines the legal interaction:

```text id="j6d6zh"
connect ;
(send | receive)* ;
close
```

Nothing in the initial algebraic-effect design should unnecessarily prevent such libraries.

Core protocol machinery should be added only if library-level expression proves insufficient or unacceptably awkward.

---

# 36. Processes, messaging, and streams are separate concerns

Coeffects have a useful event-system interpretation, but this should not cause Ash to conflate them with messaging.

Ash may separately have:

- processes;
- actors;
- channels;
- mailboxes;
- streams;
- messaging.

These abstractions will undoubtedly interact with:

- effects;
- identities;
- continuations;
- resource lifetimes.

For example, spawning a process introduces an identity and sending a message may be effectful.

Nevertheless:

```text id="mgbx9c"
coeffect hook
    !=
message
```

and:

```text id="yyx42h"
hook chain
    !=
mailbox/event queue
```

The concerns should remain separate until their interaction is understood.

---

# 37. Initial implementation direction

A plausible implementation strategy follows directly from the semantic structure.

## Effect/interface resolution

Share compiler machinery where practical:

- generic parameter resolution;
- associated-type resolution;
- witness/dictionary construction;
- monomorphization.

## Static handlers

When handler identity and composition are statically known:

- specialize;
- inline;
- erase unnecessary dictionaries;
- compile coeffect chains directly.

## Dynamic handlers

When identities become known only at runtime:

- retain runtime identity witnesses;
- resolve through typed tables or dictionaries;
- cache resolved chains aggressively.

## Coeffects

Treat registration as mutation of a hook-chain resource.

Execution should ideally require only:

```text id="mbd8ad"
load cached chain
execute chain
```

rather than general subscriber discovery.

## Identities

Use a runtime representation suitable for:

- equality;
- hashing where needed;
- compact storage;
- stable association with type-level witnesses.

The exact representation is deliberately unspecified at this stage.

---

# 38. Major unresolved design questions

The discussion has identified several genuinely foundational gaps. These should be treated as major design work rather than implementation details.

## 38.1 Continuation semantics

This is probably the highest-priority unresolved issue.

Ash must determine:

- which continuation modes exist;
- whether modes are declared per effect or operation;
- whether handlers may strengthen/weaken those constraints;
- how continuation modes appear in types;
- how escaping continuations interact with identity lifetime;
- how multi-shot continuations interact with resources.

Many important libraries depend directly on these answers.

---

## 38.2 Formal effect-row algebra

The intended row-polymorphic design needs a precise algebra.

Questions include:

- set versus multiset semantics;
- duplicate schemas with distinct identities;
- row unification;
- row subtraction;
- forwarding;
- open rows;
- effect aliases or grouping;
- interaction with generic and associated types.

In particular, handling:

```text id="6quk81"
Database<α>
```

must remove precisely that requirement, not every `Database`-shaped effect.

---

## 38.3 Formal handler calculus

Handler composition needs precise typing and operational rules.

Questions include:

- what is the exact type of a handler?
- how are ambient effects represented?
- how does forwarding work?
- can handlers themselves be effectful during construction?
- are handlers ordinary first-class values?
- how are handler identities represented?
- how do nested handlers interact with coeffect hooks?
- what guarantees permit handler specialization?

The distinction between handler composition and effect-row composition must remain explicit.

---

## 38.4 Identity semantics

Identity has become central enough that it needs its own formal design.

Questions include:

- what exactly constitutes an identity?
- what is its runtime representation?
- how is a fresh identity introduced into the type environment?
- how is identity equality expressed statically and dynamically?
- how are identities existentially hidden?
- what does removal mean to code retaining a value parameterized by that identity?

There is currently no reason to distinguish static and generative identities semantically, but this needs validation through a formal model.

---

## 38.5 Identity layers

Not every identity necessarily represents the same thing.

Potentially distinct identities include:

```text id="z4qjhz"
effect API identity
operation identity
hook identity

handler instance identity
provider identity
resource identity
module instance identity
```

The same identity machinery may represent all of these, but the relationships between them need clarification.

For example, one provider identity may create many connection identities.

The design must avoid accidentally identifying:

```text id="06btxl"
provider identity
```

with:

```text id="n9cvpi"
resource identity
```

merely because both participate in the same effect API.

---

## 38.6 Ownership and lifetime

Creation/removal semantics require a precise ownership model.

Questions include:

- who owns a newly created identity?
- can ownership transfer?
- can resources be borrowed?
- what keeps module code alive while values implemented by it remain live?
- what does unloading mean in the presence of outstanding handlers or callbacks?
- how are dependency cycles handled?
- what is the relationship between ownership and reference/lease relationships?

This is where the motivating paper's reversible effects and delayed withdrawal provide useful guidance, but Ash's model should be identity/resource based rather than context based.

---

## 38.7 Coeffect algebra

Sequential and parallel composition need formal semantics.

For sequential composition:

```text id="z6r6nc"
C1 ; C2
```

questions include:

- result passing;
- failure;
- rejection;
- effect accumulation;
- continuation interaction.

For parallel composition:

```text id="b2v4fi"
C1 || C2
```

questions include:

- independence;
- deterministic semantics;
- failure aggregation;
- conflict;
- result combination;
- actual concurrency.

This algebra should be sufficiently explicit that handlers can declare or implement hook behavior predictably.

---

## 38.8 Hook typing

Public hooks are API elements, but their precise typing model remains open.

Questions include:

- are hooks generic?
- can they introduce fresh identities into the post-hook type environment?
- can a pre-hook transform its operation arguments?
- can it reject?
- can an after-hook transform a result?
- are such transformations coeffects or should some be modeled as handlers?
- how are hook effects represented?

The implementation is mechanically straightforward once the semantic contract is known; defining that contract is the hard part.

---

## 38.9 Interaction between coeffects and continuations

Because handlers drive both continuations and coeffect publication, their interaction requires explicit semantics.

Questions include:

- if a continuation is resumed multiple times, do after-hooks run multiple times?
- are hook registrations captured by a continuation or resolved when resumed?
- what happens if registrations change while a continuation is suspended?
- can a coeffect subscriber itself capture or resume the surrounding continuation?
- what does parallel coeffect execution mean around a multi-shot continuation?

This is likely one of the more subtle parts of the eventual formal model.

---

## 38.10 Dynamic resolution and existential opening

The combination of runtime identities and existential packages needs validation.

The goal is to support patterns resembling:

```text id="w6g6yf"
exists α.
    Package<α>
```

and safely resolve handlers/providers using `α` without requiring general dependent typing.

The design needs to establish that this machinery is expressive enough for the important dynamic cases and identify where it is not.

---

# 39.