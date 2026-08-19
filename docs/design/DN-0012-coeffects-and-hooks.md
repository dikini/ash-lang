# DN-0012: Coeffects and Hooks

- ID: `DN-0012`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md), [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md)

> This design note is informative. It explores possible future coeffect and hook semantics; it does not define current Ash, accept an architecture, or authorize roadmap work. The syntax and type notation in this note are illustrative.

## Question

Can future Ash handlers expose typed extension points whose subscribers compose predictably, may perform effects or alter control flow, and obey identity and continuation lifetimes without introducing a universal event bus or scheduler?

## Context and scope

The event-system analogy is useful:

```text
perform effect operation ~ publish event
register coeffect       ~ subscribe to event
```

The candidate semantics are narrower and more structured. A coeffect subscriber reacts at a typed point deliberately exposed in handler control flow. The hook has an API identity; the handler gives it operational placement; registration associates a subscriber with it; reaching the hook executes the resolved chain.

This note uses *coeffect* for that reaction mechanism. It does not equate coeffects with messages, process mailboxes, streams, security policy, environmental requirements in other effect systems, or a polarity-reversed effect row. Those concepts may interact with hooks but need independent semantics.

## Suggested design rules

### Make public hooks typed API identities

> Suggested rule: A public hook has a unique type identity, runtime witness, and payload contract and is declared as part of the effect API rather than addressed by an untyped event name.

An effect's discoverable surface could contain:

```text
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

Fixed `before`/`after` hooks, per-effect hooks, per-operation hooks, and explicitly named phases are possible surface families. They need not be mutually exclusive. The important distinction is between a public typed identity and a handler's private control point.

### Let handlers define publication semantics

> Suggested rule: The effect API defines a hook's identity and type, while each compatible handler defines where and under what continuation contract that hook is published.

A handler might interpret an operation as:

```text
receive operation
      |
      v
publish Validate
      |
      v
prepare
      |
      v
publish Prepared
      |
      v
commit
      |
      v
publish Committed
      |
      v
resume continuation
```

Ash need not impose one universal scheduler or assume that every API has the same before/after lifecycle.

### Keep registration separate from availability

> Suggested rule: Loading or linking may make a subscriber definition available, but registration and deregistration are explicit runtime acquisitions whenever the required identities are valid.

A module can export subscriber code without activating it. A loader may explicitly register the subscriber as one policy, but registration can also occur during ordinary execution or within a temporary scope. [DN-0011](DN-0011-modules-providers-and-resolution.md) explores module availability and discovery.

### Support distinct sequential and parallel composition

> Suggested rule: Coeffect composition has at least a sequential form and an independence-oriented parallel form; "parallel" does not by itself require simultaneous machine execution.

Sequential composition:

```text
C1 ; C2
```

lets `C2` observe the result or context produced by `C1`. Parallel composition:

```text
C1 || C2
```

gives both subscribers the same input without making their mutual ordering part of the meaning. The parallel form still needs deterministic rules for result combination, failure, conflict, and whether actual concurrency is permitted.

### Include subscriber effects in types

> Suggested rule: A subscriber's type records effects it may perform, and composition combines those requirements without conflating effect-row algebra with coeffect-composition algebra.

For example, using the named-hook-identity style above:

```text
AfterQuery ! { Metrics, Logging }
BeforeModuleLoad ! { SignatureVerification, Policy }
```

Sequential subscribers accumulate their effect requirements through ordinary row rules. Parallel subscribers may need additional independence constraints beyond row union.

### Treat registration as a resource

> Suggested rule: Registering a subscriber creates a typed registration identity whose lifetime depends on the hook and on identities captured by the subscriber.

Conceptually:

```text
register Hook<h> subscriber
    |
    v
Create(Registration<r>)
```

Deregistration removes `r`. This lets registration use the general ownership, dependency, draining, and removal model explored in [DN-0010](DN-0010-identities-and-resource-lifetimes.md).

### Compile resolved chains off the hot path

> Suggested rule: Treat registration as construction or update of a typed hook chain so publication can invoke a cached continuation-like structure instead of discovering callbacks through a general event bus each time.

When everything is statically known, linking may inline or specialize the chain. Runtime registration can rebuild or patch a cached sequential chain or fan-out structure. This is an implementation direction to test, not a promise that all registration changes are cheap.

### Keep mechanism separate from policy and messaging

> Suggested rule: Hooks provide typed control-flow extension points; libraries assign meanings such as authorization, auditing, metrics, retries, or debugging, while messaging and process communication remain separate abstractions.

The same `BeforeFileWrite` hook might host a policy subscriber, audit subscriber, transformation, or debugger. No one use should become the core definition of coeffects.

## Candidate model

### Hook declarations

A hook declaration needs to relate:

- a hook identity `h`;
- input payload and possibly output or transformed payload;
- effect API and operation identities, where relevant;
- generic and associated types;
- the effects subscribers may perform;
- control actions the hook contract permits;
- identities introduced or removed across the hook.

A public hook could be documented and discovered by identity. A handler can also use private phases that do not become public API.

### Publication and handler flow

The handler owns temporal placement. This matters because pre- and post-transition worlds can have different types and failure meanings:

```text
before:
    identity a does not exist

operation:
    Create(a)

after:
    a is valid and may occur in values and types
```

A pre-hook may reject before any transition. A post-hook runs after some state change and may require rollback, compensation, or an explicit rule if it fails. The hook type may need to express these different environments rather than reuse one callback signature.

### Subscriber control

Depending on the hook contract, a subscriber might:

- observe;
- transform input, output, or context;
- reject;
- abort;
- suspend;
- perform additional effects.

Not every hook must permit every action. Some transformations may be better modeled as effect handlers rather than subscribers. The formal boundary should depend on who controls operation interpretation and continuation resumption, not on naming convention.

### Sequential chains

A sequential chain maps naturally to explicit continuation structure:

```text
C1 -> C2 -> C3 -> handler continuation
```

The coeffect algebra must define:

- which value or context passes to the next subscriber;
- how transformed payloads are typed;
- whether rejection skips later subscribers;
- how failure unwinds;
- how subscriber effects accumulate;
- whether registration order determines chain order or order is explicit.

### Parallel fan-out

A parallel group could be a preconstructed fan-out:

```text
          +-> C1 -+
hook input        +-> combine -> continue
          +-> C2 -+
```

Its contract must define:

- whether subscribers are independent by proof, declaration, or convention;
- deterministic result and failure aggregation;
- conflicts between transformations;
- cancellation and partial completion;
- whether effects from different branches may interfere;
- whether the runtime may execute branches concurrently.

Without these rules, `C1 || C2` is only suggestive notation.

### Registrations and captured identities

A registration might establish dependencies such as:

```text
Registration<r>
    depends-on Hook<h>
    depends-on Database<db>
    depends-on Connection<c>
    depends-on subscriber code
```

Withdrawal of one dependency could trigger deregistration, invalidate future invocation, enter a drain state, or make publication fail. The chosen behavior may vary by strength of capture, but it must not leave a cached chain pointing to removed identities or reclaimed code.

### Resolution and discovery

Static tools and runtime loaders should resolve a subscriber through typed hook identity and payload compatibility. Where identities are known early, the compiler can bind and specialize the chain. Where they arrive later, runtime resolution retains witnesses. Display names remain useful for documentation but do not establish equality.

## Interactions and failure cases

### Continuation capture and resumption

Handlers drive both publication and continuation flow, so the model must answer whether a continuation captures:

- the hook chain present when it suspends;
- only the hook identity, resolving the current chain when it resumes;
- a mixture based on registration lifetime or capture mode.

Suppose registrations change while an operation's continuation is suspended. Snapshot semantics preserve the old chain and its dependencies; live semantics observe the new chain; invalidation may reject resumption. Each choice affects determinism and resource retention.

With a multi-shot continuation, post-hooks might run once per resumption, once around the original operation, or be rejected if their effects cannot repeat safely. A subscriber might itself capture or resume the surrounding continuation. These behaviors need explicit contracts shared with [DN-0009](DN-0009-effects-handlers-and-continuations.md).

### Effectful subscribers

Two subscribers can have unordered hook semantics while their effects conflict. For example, both may write the same resource or one may depend on the other's output. Effect-row union alone does not prove independence. A parallel composition must either require evidence, define a deterministic serialization/merge, or reject the ambiguous case.

### Failure after a transition

If an after-hook rejects after an external write or resource creation, ordinary unwinding cannot pretend the transition never happened. The handler or library may need compensation, staged publication, transaction support, or an error that reports partial completion. Universal reversal is not available.

### Fresh identities

A hook before identity creation cannot safely receive values parameterized by the not-yet-created identity. An after-hook may. A hook type system that ignores this distinction either leaks an invalid witness early or prevents useful post-creation registration.

### Lifetime and cached chains

Caching moves discovery off the hot path but makes invalidation central. Removing a hook, subscriber, captured resource, or module code must update, drain, or invalidate every cached chain that depends on it. A cache keyed only by display name or callback address would lose typed lifetime information.

### Policy

An authorization subscriber at `BeforeFileWrite` can reject, but an authorization handler around the entire effect may establish different guarantees. Both should remain possible library choices. Calling the hook itself a policy would obscure audit and instrumentation uses.

### Messaging

A hook chain is invoked synchronously or according to its handler contract at a point in interpretation. A mailbox or stream has delivery, buffering, ordering, and backpressure semantics of its own. Reusing identity or continuation machinery does not make the abstractions equivalent.

### Time

The relevant temporal distinctions arise from ordered control flow:

```text
before transition
after transition
during suspended interpretation
after resumption
during withdrawal or draining
```

No universal global-time structure follows from this sequence. The handler defines the operational order for its hooks.

## Evidence and experiments

### Hook typing matrix

Define representative hooks for observation, input transformation, rejection, result transformation, and fresh-identity creation. For each, record:

- input and output payload types;
- allowed control actions;
- subscriber effect rows;
- identities available before and after publication;
- handler obligations after failure.

Compare fixed before/after templates with arbitrary named typed phases. Retain a design only if tools can discover the public contract and handlers can implement it without exposing private control points.

### Composition calculus

Give small operational and typing rules for `C1 ; C2` and `C1 || C2`. Test:

- transformed result passing;
- first and multiple failures;
- rejection;
- effect accumulation;
- conflicting writes;
- deterministic aggregation;
- cancellation;
- actual serial and concurrent execution.

The experiment should distinguish algebraic independence from scheduling. Discard syntax or runtime structures after recording which rules make the cases unambiguous.

### Continuation interaction matrix

Cross one-shot, multi-shot, abortive, and suspended handler behavior with before- and after-hooks. Change registrations during suspension and compare snapshot, live, and invalidating semantics. Include a subscriber that captures the surrounding continuation. Measure not performance first, but whether each behavior can be stated, typed, and cleaned up consistently.

### Registration lifetime cases

Create a registration that captures provider, resource, and module-code identities. Then withdraw each dependency in turn while publication is idle, executing, and suspended. Verify that no subsequent invocation observes a removed identity and that draining does not reclaim code still on a chain.

### Static and dynamic chain construction

Build the same hook chain through static linking and runtime registration. Compare semantics, effect requirements, order, and diagnostics. Benchmark direct specialization, cached sequential chains, and cached fan-out only after semantic equivalence is established.

### Boundary comparison

Implement the same authorization or retry concern once as a hook subscriber and once as a handler. The comparison should reveal which operations each can intercept, whether it can control resumption, and what failure guarantees it can offer. Use the result to define the semantic boundary rather than privileging one mechanism.

## Open questions

- Are hook identities generic, and how are associated types or identity parameters represented?
- Which hooks are implicit, if any, and which must be declared explicitly?
- Can a pre-hook transform operation arguments, and can an after-hook transform a result?
- Which control actions are available per hook: observe, reject, abort, suspend, or resume?
- When does a transformation belong in a subscriber rather than a handler?
- How are subscriber effect rows reflected in the enclosing handler's type?
- What value or context flows through sequential composition?
- How are order and priority established for sequential registrations?
- What evidence establishes independence for parallel composition?
- How are parallel failures, conflicts, results, cancellation, and partial completion combined deterministically?
- Does parallel composition permit or require concurrent execution?
- Does a suspended continuation capture a hook-chain snapshot or resolve registrations at resumption?
- Do post-hooks run once per multi-shot resumption, once per handled operation, or according to a declared mode?
- Can subscribers capture or invoke the surrounding continuation?
- How do deregistration and draining behave while a subscriber is executing?
- Can registrations be weak, scoped, transferred, or borrowed?
- How are fresh identities introduced across a hook boundary?
- What happens when an after-hook fails after an irreversible operation?
- Which discovery and compatibility information must tools expose for hooks?
- How are cached chains invalidated without imposing a universal registry or synchronization domain?
