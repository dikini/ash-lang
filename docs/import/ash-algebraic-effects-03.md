# 39. Static and dynamic discovery

Typed identities should support both static and dynamic discovery.

At static compile/link time, tooling should be able to answer questions such as:

- which effect APIs are available?
- which handlers can interpret them?
- which providers satisfy handler requirements?
- which coeffect hooks are exposed?
- which subscribers are compatible with those hooks?

At runtime, the same relationships may need to be established later when identities are introduced dynamically.

The important point is that discovery should remain **typed identity resolution**, not name-based lookup.

This applies equally to:

- handlers;
- providers;
- resources;
- coeffect hook registrations;
- dynamically loaded module exports.

Where static information is sufficient, discovery should collapse into ordinary linking.

Where information becomes available later, the runtime should perform equivalent identity-based resolution.

---

# 40. API discoverability is part of the design

Because hook points are public API identities, discoverability matters.

For an effect API, tools should eventually be able to present something like:

```text id="0wp8fn"
Effect Database

Operations:
    query
    begin
    commit

Hooks:
    BeforeQuery
    AfterQuery
    BeforeCommit
    AfterCommit
```

This is important for both programmers and tooling.

The same applies to dynamically loaded modules. If a module exports a handler or subscriber through a known API, the loader and developer tools should be able to determine:

- what identity it provides;
- what identity it requires;
- what hook identities it can subscribe to;
- what associated types or identities are hidden existentially.

This strengthens the case for explicit typed hook identities rather than purely conventional `before`/`after` implementation points.

---

# 41. Effects may create capabilities indirectly

Identity creation and capability introduction are related but not identical.

Creating an identity may make new capabilities available:

```text id="p46q2f"
Create(α)
    |
    v
new operations involving α become possible
```

but not every identity automatically represents a capability in the security sense.

For example:

```text id="0i34gh"
Connection<α>
```

may permit:

```text id="7e3yvi"
send<α>
receive<α>
close<α>
```

while a separate policy layer decides who may exercise those operations.

Thus identities provide the substrate from which capability systems can be built, but the Ash core should not force every identity into one specific capability interpretation.

---

# 42. Effects and coeffects should remain distinct from policy

Coeffect hooks can support policy mechanisms, but coeffects are not themselves policies.

For example:

```text id="rxyfjw"
Before<FileWrite>
```

may host:

- an authorization policy;
- an audit subscriber;
- a transformation;
- a debugger;
- a metrics hook.

The hook is part of the effect API.

The registered coeffect subscriber provides behavior.

The policy meaning is a library-level interpretation.

This separation is important because the same coeffect machinery should remain useful outside security and access control.

---

# 43. Handlers define interpretation boundaries

A handler does more than choose an implementation. It establishes an interpretation boundary.

Conceptually:

```text id="hj37le"
outer computation
      |
      | performs E
      v
handler boundary
      |
      | may publish coeffects
      | may perform other effects
      | may manipulate continuation
      v
inner interpretation
```

This boundary is where several concerns meet:

- effect discharge;
- effect transformation;
- continuation behavior;
- coeffect publication;
- provider access;
- resource creation/removal.

The exact syntax should make this role clear without conflating the handler with any one of those mechanisms.

---

# 44. Providers need not be effect-specific objects

A provider may realize one effect API, several APIs, or supply lower-level resources from which handlers realize effects.

For example:

```text id="1ozc82"
PostgresRuntime
    |
    +-- Database provider
    +-- Transaction provider
    +-- Notification provider
```

or:

```text id="ksupcn"
Socket<α>
```

may be a resource used by:

```text id="85f76u"
HttpHandler<α>
```

without the socket itself being "an Http provider."

Thus provider relationships should be expressed through ordinary type constraints and identities rather than forcing a one-provider/one-effect model.

---

# 45. Effects may be layered without exposing lower layers

A handler can use lower-level effects while exposing only the higher-level API to its caller.

For example:

```text id="k3yog8"
Application
    |
    | Database
    v
DatabaseHandler
    |
    | Network + Filesystem
    v
lower-level handlers/providers
```

The caller's effect row may contain only:

```text id="20eajr"
{ Database }
```

while the handler implementation itself requires:

```text id="zu17nk"
{ Network, Filesystem }
```

Handler typing must therefore support effect-row transformation, not merely effect elimination.

Conceptually:

```text id="xnlaph"
Handler :
    { Database | r }
        ->
    { Network, Filesystem | r }
```

This is one of the major reasons a formal handler calculus is needed.

---

# 46. Coeffect hook publication is part of handler semantics, not a universal scheduler

The runtime should not impose one universal rule such as:

```text id="du2nla"
before hooks always run here
after hooks always run there
```

unless Ash deliberately chooses such a restricted model.

More generally, the effect API defines public hook identities, and the handler decides when those identities are published.

For example:

```text id="n5rel5"
handle Commit:
    publish Validate
    prepare
    publish Prepared
    commit
    publish Committed
    resume
```

This allows effect APIs to expose extension points that correspond to meaningful phases of the interpretation rather than forcing all APIs into one generic lifecycle.

---

# 47. Coeffects are potentially effectful

A subscriber attached to a hook may itself perform effects.

For example:

```text id="6hdfvv"
After<Query>
    ! { Metrics, Logging }
```

or:

```text id="aq39kx"
Before<ModuleLoad>
    ! { SignatureVerification, Policy }
```

Therefore the type of a coeffect subscriber should include its own effect row.

This raises composition questions:

```text id="377h3q"
C1 ! e1
C2 ! e2
```

For sequential composition:

```text id="3s6v7x"
C1 ; C2
```

the resulting effects should compose in the ordinary effect-row sense.

For parallel composition:

```text id="3uuh25"
C1 || C2
```

the semantic relationship between `e1` and `e2` may require additional constraints if the callbacks are intended to be independent.

This is another point where effect algebra and coeffect algebra interact but should not be conflated.

---

# 48. Coeffect registration itself is an acquisition

Registering a callback creates a runtime identity and relationship.

Conceptually:

```text id="vpze5a"
register Hook<H> callback
    |
    v
Create(Registration<ρ>)
```

The registration remains valid while:

- the registration identity `ρ` exists;
- the hook identity remains valid;
- any identities captured by the subscriber remain valid.

Deregistration removes that identity:

```text id="h2nd64"
Remove(ρ)
```

This allows coeffect registration to participate naturally in the same resource/lifetime machinery as other acquisitions.

No special event-subscription lifetime model is necessary.

---

# 49. Captured identities constrain coeffect lifetime

A subscriber may close over identities.

For example:

```text id="xq03ob"
subscribe After<Query<db_id>> with callback(connection_id)
```

The registration is only valid while the identities it depends on remain meaningful.

This suggests a dependency relationship:

```text id="s4gl69"
Registration<ρ>
    depends-on Hook<η>
    depends-on Database<α>
    depends-on Connection<β>
```

Removal of one of these identities may require:

- deregistration;
- invalidation;
- draining;
- rejection of future invocation.

This is another case where typed identity relationships can replace a monolithic runtime context.

---

# 50. Identity removal and suspended continuations interact

Escaping or suspended continuations create a major lifetime question.

Suppose a continuation captures:

```text id="i332ox"
Provider<α>
Handler<β>
Resource<γ>
```

and then suspends.

Before it resumes, one of those identities may be removed.

Ash must define whether:

- captured identities are retained by the continuation;
- removal waits for the continuation;
- resumption fails;
- the continuation can be migrated/rebound;
- some identities may be weakly captured.

This is a fundamental interaction between:

- continuation semantics;
- identity lifetime;
- dynamic loading/unloading;
- resource safety.

It should be treated as part of the core effects design, not deferred entirely to libraries.

---

# 51. Multi-shot continuations and identity duplication

Multi-shot continuations pose an even harder question.

If a continuation captures a resource identity:

```text id="q90alr"
Resource<α>
```

and is resumed twice, do both branches share `α`?

If `α` represents:

- immutable data, sharing may be harmless;
- a mutable resource, sharing may require synchronization;
- a linear resource, duplication may be invalid;
- transactional state, semantics may be ambiguous.

Thus continuation multiplicity may need to interact with:

- linearity;
- borrowing;
- ownership;
- effect constraints.

This is a major design gap and one of the strongest reasons not to treat multi-shot continuations as a transparent implementation option.

---

# 52. The type system should carry as much as possible

A recurring design principle is:

> **Prefer expressing relationships in the type system when Ash already has the machinery to do so.**

This applies to:

- effect requirements;
- handler compatibility;
- provider compatibility;
- associated types;
- identity relationships;
- existentially hidden identities;
- hook subscriber types.

The runtime should primarily handle facts that cannot be known earlier:

- which identity instances currently exist;
- which dynamic package was loaded;
- which registrations are currently installed;
- which runtime identities correspond;
- which resources remain alive.

This keeps dynamic machinery narrow and makes static specialization possible.

---

# 53. Avoid full dependent typing unless required

The motivating paper's dependent key/value store solves a real dynamic typing problem.

Ash may be able to avoid introducing full dependent types by combining:

```text id="1xk3l4"
parametric polymorphism
+
associated types
+
opaque/existential types
+
identity witnesses
```

The working hypothesis is that these are sufficient to express most required dynamic relationships.

For example:

```text id="6pv1r9"
exists α.
    {
        provider : Provider<α>,
        handler  : Handler<α>
    }
```

preserves the crucial equality without requiring arbitrary values to appear in types.

This hypothesis should be tested against difficult examples before adding more powerful type machinery.

---

# 54. The system should permit opaque sub-worlds

Although the Ash-visible API universe of a compiled program is closed, modules may internally create structures Ash does not understand.

A known outer API may carry:

- byte protocols;
- interpreters;
- dynamically defined schemas;
- application-specific state machines;
- other opaque abstractions.

The Ash program need only understand the boundary.

This is important because it prevents the typed module/effect system from becoming unnecessarily restrictive.

Future work may investigate whether opaque sub-worlds can exchange proof-carrying or manifest-described APIs through known outer interfaces.

This should not be required for the initial design.

---

# 55. Interaction with static modules

Everything described for runtime identities should have a natural static analogue.

A statically linked module may introduce identities that are fully known during linking.

The compiler can then:

- resolve handlers;
- resolve providers;
- bind hook subscribers;
- specialize generic code;
- erase runtime identity checks where equality is proven statically.

The semantic model should not distinguish these bindings from equivalent dynamically resolved bindings.

Only the amount of remaining runtime representation differs.

---

# 56. Interaction with dynamically loaded modules

A dynamically loaded module is a passive package whose exports are resolved through a statically known outer contract.

Loading may introduce fresh identities:

```text id="bu6phg"
exists α β ...
    LoadedModule<α, β, ...>
```

Those identities may then participate in:

- provider construction;
- handler construction;
- resource acquisition;
- coeffect registration;
- ordinary values.

The loader is responsible for orchestration.

The module itself is not implicitly activated, nor does loading automatically register its coeffects.

---

# 57. Unloading modules

Module unloading is more constrained than loading because code may remain reachable through runtime identities originating from the module.

A possible lifecycle is:

```text id="j61egh"
request unload
      |
      v
prevent creation of new module-originated objects
      |
      v
withdraw module-provided bindings
      |
      v
drain/remove live objects requiring module code
      |
      v
remove module-level resources
      |
      v
unmap/reclaim module
```

The exact policy belongs partly to the loader/library, but the core identity/lifetime machinery must make such reasoning possible.

In particular, module code must not disappear while:

- handlers implemented by it remain active;
- callbacks implemented by it remain registered;
- resources with destructors implemented by it remain live;
- suspended continuations refer to its code.

---

# 58. Reversible effects should be interpreted carefully

Not all effects are reversible.

There is an important distinction between acquisitions:

```text id="tyyhqs"
open / close
register / deregister
allocate / free
spawn / terminate
```

and emissions:

```text id="wddjzd"
send packet
charge card
print output
write to uncontrolled external system
```

Ash should not pretend every effect has a mathematical inverse.

Libraries may instead use:

- transactions;
- compensation;
- deferred emission;
- idempotency;
- explicit recovery.

The core identity/resource model fits acquisitions particularly well because creation/removal correspond naturally.

---

# 59. Identity creation/removal are not the only effects

Although identity creation and removal are fundamental runtime events, ordinary effects also include operations that do not create or remove identities.

Examples:

```text id="ffgn1y"
read
write
send
query
log
```

Thus:

> **Identity lifecycle is a fundamental part of the runtime model, not a definition of all effects.**

Effects remain the general interaction mechanism.

Identity creation/removal become especially important where runtime structure and capabilities change.

---

# 60. Effects, coeffects, and time

Effects describe operations occurring in control flow.

Coeffects attach reactions to typed points in that flow.

Time therefore enters the model through ordered execution rather than through a universal global time structure.

Important distinctions include:

```text id="6w9u3k"
before transition
after transition
during suspended interpretation
after resumption
during removal/draining
```

The handler determines the exact operational sequence.

This temporal structure is why coeffects cannot be reduced merely to polarity or a dual effect row.

---

# 61. Effects and coeffects are related but not symmetric in implementation

The effect/coeffect duality is useful conceptually:

```text id="xux9bu"
effect:
    computation acts outward

coeffect:
    computation/environment reacts inward
```

but operationally the two differ.

An effect operation enters a handler.

A coeffect subscriber is invoked by a handler at a particular hook point.

Thus:

```text id="wm5o8m"
effect dispatch
    and
coeffect dispatch
```

may share identity and call-chain machinery, but they play different roles.

The design should preserve this distinction even if compiler/runtime implementation code is heavily shared.

---

# 62. Likely common compiler machinery

Several seemingly separate Ash features may share implementation infrastructure.

Potentially common mechanisms include:

```text id="20wlq4"
type identity representation
constraint resolution
witness/dictionary passing
monomorphization
existential packaging
runtime witness comparison
```

These may support:

- interfaces/impl;
- effects/handlers;
- providers;
- dynamically loaded module exports;
- hook identities and subscribers.

This is desirable, but semantic distinctions should not be erased simply to maximize implementation reuse.

---

# 63. Library opportunities

If the core succeeds, a broad range of facilities should become libraries.

Examples include:

- capability security;
- access-control policy;
- roles;
- auditing;
- tracing;
- metrics;
- retries;
- caching;
- reactive dependencies;
- plugin orchestration;
- transactions where continuation semantics permit;
- protocol/session-type systems;
- workflow systems.

This is one of the major motivations for the reboot.

The test for adding a new core feature should therefore include:

> Can this instead be expressed cleanly and efficiently as a library using effects, handlers, identities, coeffects, and the type system?

---

# 64. Major gaps summary

The initial design is coherent enough to identify its major unresolved questions.

These are not minor syntax details.

## Continuation semantics

Need a precise account of:

- one-shot;
- multi-shot;
- abortive;
- suspensive/escaping continuations;
- interaction with resources and identities.

## Effect-row algebra

Need formal rules for:

- open rows;
- identity-bearing effects;
- unification;
- subtraction;
- forwarding;
- multiplicity.

## Handler calculus

Need formal typing and operational semantics for:

- handler composition;
- effect transformation;
- forwarding;
- first-class handlers;
- handler identity and lifetime.

## Identity semantics

Need to define:

- identity introduction;
- runtime representation;
- equality;
- existential hiding;
- removal/invalidation.

## Identity layers

Need to distinguish or relate:

- API identities;
- operation identities;
- hook identities;
- handler identities;
- provider identities;
- resource identities;
- module identities.

## Ownership and lifetime

Need a model for:

- ownership;
- borrowing/reference relationships;
- transfer;
- draining;
- unloading;
- captured identities.

## Coeffect algebra

Need formal semantics for:

```text id="zl6jzf"
sequential composition
parallel composition
failure
rejection
transformation
```

## Hook typing

Need to determine:

- generic hooks;
- payload typing;
- fresh identities introduced across hook points;
- pre/post transformation;
- subscriber effect rows.

## Coeffects and continuations

Need to resolve:

- repeated publication under multi-shot continuation;
- registration changes during suspension;
- capture of hook chains;
- parallel coeffects around resumed continuations.

## Dynamic resolution

Need to validate that:

```text id="84cmuc"
opaque types
+
existentials
+
identities
+
associated types
```

are sufficient for the intended dynamic module and provider-resolution cases without full dependent typing.

---

# 65. Initial design principles

The discussion suggests the following principles for the first Ash algebraic-effects design.

1. **Effects define typed APIs, not protocols.**

2. **Effect rows describe outstanding interpretation requirements.**

3. **Handlers, providers, and effects remain distinct concepts.**

4. **Effect/handler parameterization should resemble interface/impl parameterization where the semantics permit.**

5. **Handler composition is ordered by default.**

6. **Continuation semantics are part of the core effect contract.**

7. **Public coeffect hook points are typed identities in the effect API.**

8. **Handlers determine where hook points occur in interpretation flow.**

9. **Coeffect registration is independent of module loading.**

10. **Coeffects support at least sequential and parallel composition.**

11. **Coeffect invocation should compile to continuation-like chains rather than require a generic event-bus hot path.**

12. **Identities have both type-level meaning and runtime representation.**

13. **Do not distinguish normal and generative identities without a demonstrated need.**

14. **Identity creation and removal are fundamental runtime events.**

15. **The runtime should be modeled in terms of typed identities and relationships rather than a monolithic context.**

16. **Static linking and dynamic loading use the same composition semantics at different resolution stages.**

17. **Modules are passive code packages; orchestration is external.**

18. **Opaque/existential packaging and identity resolution should be tried before introducing full dependent typing.**

19. **Ownership and provenance are distinct.**

20. **Higher-level policies should preferentially be libraries built from the core mechanisms.**

---

# 66. Overall architecture

The current architecture can be summarized as:

```text id="qcp1wm"
                    TYPE / API WORLD

          interfaces        effect APIs
               \               /
                \             /
                 type resolution
                       |
                       v
               identities/witnesses
                       |
             +---------+---------+
             |                   |
             v                   v
          handlers            providers
             |
             | interpret effects
             | publish hooks
             v
        continuation flow
             |
             v
        coeffect chains
             |
             v
         subscribers


                    RUNTIME WORLD

         Create(identity)
               |
               v
       capabilities/resources
               |
               v
       typed relationships
               |
               v
         Remove(identity)
```

Modules package definitions participating in this system.

Static linking resolves the graph when the required information is already available.

Dynamic loading performs equivalent elaboration when information becomes available later.

---

# 67. Relationship to the motivating paper

The motivating work remains useful because it identifies real problems:

- dynamically changing dependencies;
- provider identity;
- safe removal;
- reversible acquisitions;
- reactive coeffects;
- delayed withdrawal.

Ash changes the solution because much of the structure can be carried by the type system.

Where the paper uses:

```text id="9kwm64"
unified context
dependent key/value store
runtime dependency descriptions
```

Ash should investigate:

```text id="m8bn33"
typed identities
effect rows
handlers
interfaces/impl
associated types
existential packages
runtime identity resolution
```

The paper's lifecycle insights remain highly relevant, especially:

- identity of providers matters;
- replacement should not silently mutate existing bindings;
- withdrawal should often drain before destruction;
- acquisitions need explicit cleanup semantics.

The goal is therefore not to reproduce the paper's runtime context in Ash.

It is to absorb the useful lifecycle and reactive ideas into Ash's existing typed architecture.

---

# 68. Closing perspective

The discussion began with algebraic effects and dynamic plugins, but the more general architecture that emerged is broader.

The core concepts are:

```text id="h1qkcc"
effects
handlers
continuations
identities
coeffect hooks
resource lifetimes
type resolution
```

From these, Ash should be able to build richer abstractions as libraries.

The most significant insight is perhaps that **dynamic composition need not require a second, weaker dynamic type world**.

Static and dynamic composition can use the same typed relationships.

The runtime needs only enough representation to preserve identities and resolve relationships that could not be established earlier.

Likewise, coeffects need not become a separate event subsystem.

They can be understood as typed extension points exposed by effect APIs and driven mechanically by handler control flow.

The remaining hard work lies not in adding more concepts, but in precisely defining the few foundational ones that now carry a large part of the architecture:

> **continuations, identities, handler composition, coeffect composition, and lifetime.**