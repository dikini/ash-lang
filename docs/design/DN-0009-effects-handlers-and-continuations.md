# DN-0009: Effects, Handlers, and Continuations

- ID: `DN-0009`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0002: Core Representation](DN-0002-core-representation.md), [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md), [DN-0012: Coeffects and Hooks](DN-0012-coeffects-and-hooks.md), [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md), [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md)

> This design note is informative. It explores possible future effect semantics; it does not define current Ash, accept an architecture, or authorize roadmap work. The syntax and type notation in this note are illustrative.

## Question

What contracts would let a future Ash effect system describe typed interaction requirements, compose ordered interpretations, and expose continuation behavior precisely enough for resource-safe libraries and checked compiler transformations?

## Context and scope

Current Ash does not have the effect system described here. [DN-0002](DN-0002-core-representation.md) treats effects and handlers only as architectural probes for a typed Core representation. This note carries that pressure forward without requiring effects in the initial language.

The exploration separates five concerns that are easy to collapse:

- an effect names a typed interaction API;
- an effect row records interactions a computation still requires someone to interpret;
- a handler interprets, forwards, or transforms those requirements;
- a provider supplies an implementation or resource used by an interpretation;
- a continuation contract constrains what the handler may do with the rest of the computation.

Protocols, access-control policy, transactions, processes, messaging, and streams are relevant consumers of these mechanisms. They are not defined here as built-in effect-system features.

## Suggested design rules

### Keep APIs separate from protocols

> Suggested rule: An effect declaration describes a typed interaction API, while temporal protocols remain library abstractions unless evidence shows that the core type system cannot express them adequately.

An API may contain operations such as:

```ash
effect Database {
    query : Query -> Result
    begin : () -> Transaction
    commit : Transaction -> ()
    rollback : Transaction -> ()
}
```

That declaration alone would not establish the protocol:

```text
begin
query*
(commit | rollback)
```

Typestate, session types, state-indexed interfaces, or another library abstraction might express the ordering. Adding protocol rules to every effect would prematurely commit the core to one temporal model.

### Treat rows as requirements, not schedules

> Suggested rule: An effect row records outstanding interpretation requirements; its structural order does not determine handler or operation order.

A candidate type could resemble:

```ash
fn fetch(...) -> T ! { Database<db>, Log | e }
```

If rows are structurally unordered, then:

```text
{ Database<db>, Log | e }
=
{ Log, Database<db> | e }
```

This equality would say nothing about whether database and log operations commute. It also would not decide whether rows use set or multiset semantics. In particular, handling `Database<db>` must not accidentally discharge every effect with the same API shape.

### Keep effects, handlers, and providers distinct

> Suggested rule: Effects define APIs, handlers define interpretation boundaries, and providers supply implementations or resources; shared compiler machinery must not erase these semantic distinctions.

A direct interpretation might have this shape:

```text
Database API
     |
     v
Database handler
     |
     v
Postgres provider
```

A transforming interpretation might instead expose one API while requiring lower layers:

```text
Application
    |
    | Http
    v
Http handler
    |
    +-- Network
    +-- Clock
    +-- Entropy
```

A provider need not correspond to exactly one effect. One runtime may support several APIs, while a lower-level resource such as `Socket<s>` may be used by an HTTP handler without being an HTTP-specific provider.

### Order handler composition by default

> Suggested rule: Handler composition is ordered unless a checked fact establishes that a particular reordering preserves behavior.

In general:

```text
H3 ∘ H2 ∘ H1
```

does not imply:

```text
H1 ∘ H2 = H2 ∘ H1
```

Rows can remain structurally unordered while handlers form an ordered interpretation stack. A future optimizer could use proven independence or commutativity, but neither property follows from row membership.

### Make continuation behavior contractual

> Suggested rule: Continuation multiplicity and escape behavior are semantic contracts, not hidden implementation choices.

At least these modes merit comparison:

- one-shot: resume at most once;
- multi-shot: resume more than once;
- abortive: discard without resumption;
- suspensive or escaping: retain and resume after the immediate handler call.

The eventual design may combine axes rather than encode four exclusive labels. It must still make enough information available to type-check libraries whose safety changes across those cases.

A conservative candidate would make one-shot use the ordinary continuation
contract and admit repeated resumption only when two independent obligations are
met:

- duplicating the captured environment preserves every usage and authority rule;
- the installed interpretation gives the outstanding interactions a meaningful
  replay semantics.

Pure computation with an unrestricted capture is one sufficient test case, not
a complete definition of replay safety. An effect API alone cannot establish the
second obligation because different handlers may interpret the same API by
sharing state, cloning state, or rejecting replay.

### Prefer checked relationships over dynamic convention

> Suggested rule: Express effect compatibility, handler transformations, provider requirements, and continuation restrictions through Ash types and witnesses where practical; retain runtime machinery for facts learned only at runtime.

This direction could share parameterization infrastructure with interfaces and `impl`: generic parameters, associated types, constraints, identity witnesses, dictionaries, and specialization. Handlers remain distinct because they also control continuations and publish the hooks explored in [DN-0012](DN-0012-coeffects-and-hooks.md).

## Candidate model

### Effect APIs

An effect declaration could introduce:

- an effect API identity;
- operation identities and their argument/result types;
- generic parameters and associated types;
- identity parameters distinguishing instances of the same API;
- public hook identities, if the API exposes them.

The declaration would not choose an implementation, provider, temporal protocol, or policy.

### Effect rows

Rows would describe which operations may escape a computation. A useful formalization must cover:

- closed and open rows;
- row unification;
- identity-bearing instances;
- multiplicity or an explicit reason to exclude it;
- subtraction when one handler discharges one requirement;
- forwarding of requirements a handler does not interpret;
- effects introduced by handler construction and execution;
- aliases or groupings without hiding identity distinctions.

Row algebra and handler composition need separate judgments. Conflating them would make an unordered collection of requirements accidentally dictate ordered control flow.

### Identity-local requirements

A generative resource scope pressures the row model to distinguish a hidden
implementation interaction from a requirement that remains outstanding at the
scope boundary. A candidate may remove an identity-indexed requirement only
when the responsible scope or handler has interpreted it and proves that the
identity, its authority, and any suspended computation that retains them do not
escape.

This is semantic discharge, not display-only row hiding. It must not erase
external I/O merely because an internal resource identity is fresh, and it must
remain sound when a continuation suspends past the apparent lexical scope.

### Handler boundaries

A handler is a boundary at which an operation may be discharged, forwarded, or translated:

```text
outer computation
      |
      | performs E
      v
handler boundary
      |
      +-- consult provider
      +-- publish typed hooks
      +-- perform other effects
      +-- resume, retain, duplicate, or discard continuation
      v
inner interpretation
```

A transformation type might be presented schematically as:

```text
Handler : { Database<db> | r } -> { Network, Filesystem | r }
```

This is not ordinary function syntax. It states the effect-row transformation that a future handler calculus must make precise. A caller can require only `Database<db>` even when its chosen interpretation requires `Network` and `Filesystem` below the boundary.

Handlers might be ordinary first-class values, separately classified values, or elaborated dictionaries. The choice affects lifetime, inference, specialization, and whether handler construction itself can be effectful.

### Provider relationships

A provider relationship could be an ordinary typed constraint rather than a privileged one-provider/one-effect object. For example, a handler parameterized by identity `p` could require a resource or implementation associated with `p`. [DN-0010](DN-0010-identities-and-resource-lifetimes.md) explores why replacing `p` with a fresh identity cannot silently retarget existing bindings; [DN-0011](DN-0011-modules-providers-and-resolution.md) explores when such relationships are resolved.

### Continuation contracts

The contract might live:

- on each operation;
- on an entire effect API;
- on the handler;
- in an inferred effect or usage property;
- across more than one of these layers, with explicit compatibility rules.

Handler rules would need to say whether an implementation may strengthen or weaken the requested contract. For example, a handler that never resumes is compatible with some callers but may violate a caller that relies on completion. A handler that resumes twice is unsafe when the captured computation owns a linear resource.

Transactions expose the pressure clearly. Around a one-shot continuation, a handler can plausibly:

```text
begin
run continuation
commit or rollback
```

For a multi-shot continuation, at least three incompatible interpretations appear plausible:

```text
clone transaction state
one transaction per branch
reject the composition
```

The core need not build transactions in, but it must publish enough continuation semantics for a transaction library to state which interpretation is sound.

## Interactions and failure cases

### Identities and resources

Identity-bearing effects let two instances of one API remain distinct. Provider lifetime, captured resource identities, draining, and multi-shot duplication belong to [DN-0010](DN-0010-identities-and-resource-lifetimes.md). The handler calculus must expose enough continuation information for those rules to be enforced.

### Modules and dynamic resolution

A module can contribute a handler anywhere in a transformation chain. For example:

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

The retry layer both consumes and provides `Http`. Treating every dynamically loaded module as a terminal provider would reject this composition. [DN-0011](DN-0011-modules-providers-and-resolution.md) considers a common static and dynamic resolution model.

### Coeffects

Handlers determine where typed hooks occur and what continuation surrounds them. Coeffect subscribers may themselves perform effects or alter control flow. Their algebra and the question of whether hook chains are captured or re-resolved on continuation resumption are explored in [DN-0012](DN-0012-coeffects-and-hooks.md).

### Library mechanisms and policy

Capabilities, roles, authorization, auditing, retry, caching, and protocol enforcement are candidate libraries built from handlers, identities, hooks, and ordinary types. Moving them to libraries does not remove core obligations: the core must make handler ordering and continuation behavior precise enough for those libraries to justify their guarantees.

Processes, messages, channels, mailboxes, and streams may use effects, but they should not be equated with effect dispatch or hook chains before their independent semantics are understood.

### Reversal

Not every effect has an inverse. Acquisition pairs such as open/close or register/deregister fit resource-lifetime machinery. Emissions such as sending a packet, charging a card, or writing to an uncontrolled system may need transactions, compensation, deferred emission, idempotency, or recovery. A handler calculus must not imply universal reversibility.

### Likely implementation sharing

Interfaces/`impl` and effects/handlers may share constraint solving, associated-type resolution, witness construction, dictionary passing, and monomorphization. Static handler chains may be specialized and inlined; dynamic chains may retain typed witnesses and cached dispatch. Such sharing is an implementation hypothesis, not evidence that interfaces and handlers have identical semantics.

## Evidence and experiments

### Minimal row and handler calculus

Define a small typed calculus with pure terms, identity-bearing effect operations, open rows, forwarding, and ordered handlers. Use it to compare candidate answers to these questions:

- Does handling `Database<a>` remove only that instance?
- Can a handler translate `{ Database<a> | r }` into `{ Network, Filesystem | r }` without leaking the lower requirements to the caller?
- Can nested handlers forward unknown row tails without losing identity information?
- Which facts are needed to justify specialization or handler reordering?

Retain a model only if its typing and operational rules agree on these cases. Discard prototype syntax and implementation scaffolding after the comparison; only the resulting design evidence should survive.

### Continuation stress cases

Exercise each continuation contract with:

- a transaction that commits or rolls back;
- a linear resource captured by a possible multi-shot continuation;
- an abortive authorization or validation handler;
- a suspended computation whose provider begins draining;
- a handler that publishes pre- and post-operation hooks;
- a nondeterministic handler that resumes more than once.

The matrix should separately vary capture duplicability and handler replay
semantics. It should include an unrestricted capture under a non-replayable
handler and a restricted capture under an otherwise replayable handler; neither
case should gain multi-shot use from the other property alone.

Compare rejection points, required type annotations, runtime checks, and whether cleanup can be proved to occur once.

### Representation probes

Extend the [DN-0002](DN-0002-core-representation.md) Core experiments with one operation, one ordered handler stack, forwarding, one effect transformation, and each continuation mode. Check that continuations remain explicit compiler data, transformations can traverse them, and Core remains typed after rewriting and Core/CPS conversion.

### Static and dynamic equivalence

Resolve the same handler/provider graph once with all identities known and once with one package introduced at runtime. Compare resulting behavior and typing. Dynamic resolution may retain witnesses and indirection; it should not invent different composition semantics.

### Local-requirement elimination

Compare a handled identity-local state operation, an unhandled external write,
and a local operation captured by an escaping continuation. Record the inferred
row at each boundary and the evidence used to remove a requirement. Reject a
model that hides the external write or eliminates the local operation while a
continuation can still resume it outside the scope.

## Open questions

- What is the exact algebra of open, identity-bearing effect rows?
- Are rows sets, multisets, or another structure, and how are duplicate API shapes represented?
- What is the formal type of a handler, including ambient effects and effects introduced by construction?
- How do partial interpretation and forwarding compose?
- Are handlers first-class values, and if so, how are their identity and lifetime tracked?
- Where are continuation multiplicity, abortiveness, and escape behavior declared or inferred?
- May a handler strengthen or weaken a continuation contract, and under what subtyping or compatibility relation?
- Does a non-resuming handler need a distinct result type?
- Which resource properties constrain multi-shot resumption: linearity, ownership, borrowing, synchronization, or effect restrictions?
- Is one-shot use the conservative default, and which checked facts are
  sufficient to admit multi-shot use without making purity its definition?
- What exact non-escape and interpretation evidence permits an identity-local
  requirement to leave a public row?
- How do exceptions, cancellation, and ordinary failure interact with handler unwinding and continuation contracts?
- When can handler reordering or fusion be proved safe?
- How do nested handlers determine which public hook identities they publish?
- Can protocol libraries express useful session and typestate disciplines without privileged core support?
- Which propositions must eventually be statically established before a compiler transform may rely on handler independence or commutation?
