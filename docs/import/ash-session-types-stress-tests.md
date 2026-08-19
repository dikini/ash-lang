# Ash Session Types — Stress Tests

## Status and intent

This note records a proposed set of stress tests for the future Ash type and effect systems.

It does not propose that session types become a built-in Ash language feature. The purpose is to use session-typed protocols as a demanding expressivity test for the more general machinery Ash expects to develop: richer type expressions, effects and handlers, associated types, identities, existential abstraction, continuation contracts, and potentially resource multiplicity.

The central question is:

> **Can Ash express and statically verify useful temporal protocols using general type-system machinery rather than a privileged protocol subsystem?**

A particularly important application is verification of private workflows inside effect handlers.

---

# 1. Effects and protocols remain distinct

An effect defines a typed interaction API.

For example:

```ash
effect Transaction {
    begin    : () -> Tx
    query    : (Tx, Query) -> Result
    commit   : Tx -> ()
    rollback : Tx -> ()
}
```

These operation signatures do not themselves establish the temporal protocol:

```text
begin
query*
(commit | rollback)
```

The protocol describes legal interaction over time.

The current Ash direction should therefore preserve:

```text
effect
    = typed interaction API

protocol
    = temporal constraints on interaction
```

Session types, typestate, state-indexed APIs, or related abstractions may provide ways to express the second using the ordinary type system.

The initial assumption should remain that protocols are library-level abstractions unless experiments demonstrate that irreducible language support is required.

---

# 2. State-indexed protocols are the easy part

A protocol can be represented conceptually as transitions between static states:

```text
Txn<Idle>
    begin
        -> Txn<Open>

Txn<Open>
    query
        -> Txn<Open>

Txn<Open>
    commit
        -> Txn<Closed>

Txn<Open>
    rollback
        -> Txn<Closed>
```

Associated types or equivalent static relations could describe generic transitions:

```text
Step<P, State, Operation> -> NextState
```

Conceptually:

```ash
interface Step<P, S, Op> {
    type Next
}
```

with implementations such as:

```text
Step<Transaction, Open, Query>
    Next = Open

Step<Transaction, Open, Commit>
    Next = Closed
```

An illegal transition has no corresponding evidence.

This suggests that much of the ordinary state-machine structure of session types may be expressible using:

```text
static state domains
type indices
associated types
constraints / evidence
ADTs for branching
```

without introducing a dedicated session-type calculus.

---

# 3. Choice can use ordinary ADTs

Protocol branching need not require a special session construct.

For example:

```text
authenticate :
    Session<Auth, Unauthenticated>
    -> AuthResult
```

where:

```ash
type AuthResult =
    Accepted(Session<Auth, Authenticated>)
    | Rejected(Session<Auth, Closed>)
```

allows ordinary pattern matching to reveal the resulting protocol state:

```ash
match authenticate(session, credentials) {
    Accepted(next) => ...
    Rejected(done) => ...
}
```

This should be tested before introducing special static machinery for internal or external choice.

---

# 4. Nominal states can avoid general recursive session types

A recursive protocol such as:

```text
Open =
    query ; Open
  | commit ; End
  | rollback ; End
```

does not necessarily require recursive structural types.

Nominal states can represent the nodes:

```text
Idle
Open
Closed
```

while transition evidence represents the graph.

This may allow useful recursive protocols without immediately requiring type-level fixed points such as:

```text
μX. ...
```

The stress tests should determine whether nominal state graphs are sufficient for practical protocols.

---

# 5. Resource multiplicity is the critical problem

State indexing alone does not guarantee protocol fidelity.

Suppose:

```text
r : Resource<Open>

r2 = close(r)
```

If `r` remains an ordinary reusable value, the program may still attempt:

```text
use(r)
```

after the transition.

Likewise:

```text
r : Resource<Open>

a = r
b = r

close(a)
use(b)
```

may violate the intended protocol even though every local transition is well typed.

The central difficulty is therefore not merely:

> Which transitions are legal?

It is also:

> What happens to the authority represented by the old state when a transition occurs?

This introduces resource multiplicity.

---

# 6. Multiplicity properties should be separated

The experiments should avoid using “linear” as an umbrella term for several distinct properties.

At minimum, distinguish:

```text
duplicable?
discardable?
```

giving the familiar combinations:

```text
duplicable   discardable

yes          yes          unrestricted
no           yes          affine
no           no           linear
```

The fourth combination should not be assumed impossible merely because it is unusual.

The important design question is where such properties belong.

Candidates include:

```text
values
bindings
types
type constructors
function arrows
closure captures
continuations
effect computations
resource obligations
```

The stress tests should distinguish these alternatives.

---

# 7. Minimal multiplicity stress test

A deliberately small diagnostic program is:

```text
r : Resource<Open>

f = fn() {
    use(r)
}

f()
f()
```

If `r` is single-use, the second call must not be permitted.

Possible explanations include:

```text
r is linear
f becomes linear because it captures r
f has a multiplicity-bearing arrow
the capture set appears in f's type
Resource itself determines usage
the enclosing computation carries an obligation
```

Candidate designs should be required to explain this example without special treatment of `Resource`.

---

# 8. Generalization must interact with resources

A related test is local polymorphism.

For example:

```text
let f = fn(...) {
    use(resource)
}
```

must not be generalized in a way that duplicates or otherwise loses the resource obligation.

The existing generalization architecture is intentionally designed so later resource facts may participate in generalization eligibility.

Session/resource experiments should therefore test whether resource-sensitive generalization can enter through that existing policy seam rather than changing the semantics of `let`.

---

# 9. Handler implementations may have private protocols

A handler need not interpret an operation atomically.

Conceptually:

```text
effect operation arrives
        |
        v
private handler workflow
        |
        +-- private transition
        +-- invoke effect X
        +-- private transition
        +-- invoke effect Y
        +-- provider action
        +-- private transition
        |
        v
resume / abort / suspend continuation
```

These intermediate states need not be part of the effect API.

They may remain entirely private implementation details.

This creates an important application for session typing:

> **Use a private protocol to statically verify the implementation of an effect operation.**

---

# 10. Public hooks are projections of private workflow

A handler workflow might be:

```text
Received
    ↓
Validated
    ↓
Executing
    ↓
Committed
    ↓
Returning
```

Only selected points may be exposed:

```text
before_execute
after_commit
```

This suggests the model:

```text
effect operation
    request being interpreted

handler workflow
    private protocol used to interpret it

coeffect hook
    selected workflow point exposed to composition
```

A public hook can therefore be understood as an explicitly exposed point in an otherwise private protocol.

For example:

```text
BeforeCommit
    occurs at Prepared

AfterCommit
    occurs at Committed
```

This could eventually allow the compiler to verify both the private workflow and the placement of public hooks within it.

Private protocol states themselves need not become public API.

---

# 11. Handler workflows may invoke other effects

A private handler protocol may contain ordinary Ash effect operations.

For example:

```text
Http.request
    ↓
ResolveDns
    ↓
Network.connect
    ↓
Tls.handshake
    ↓
Network.write
    ↓
Network.read*
    ↓
Network.close
```

This gives the checker two different static questions:

```text
effect typing
    Which effects may escape?

protocol typing
    In which states may operations occur?
```

A useful stress case is therefore:

```text
connect
write
close
write
```

where every operation may have a valid ordinary type but the final operation violates the protocol.

---

# 12. Client and implementation protocols are different

Session-like protocols can occur at multiple abstraction boundaries.

A transaction API might expose:

```text
client protocol:

begin
→ query*
→ commit | rollback
```

while its handler follows:

```text
implementation protocol:

checkout connection
→ execute*
→ release connection
```

A handler may therefore translate between protocols just as it may translate one effect into other effects.

This suggests viewing some handlers as protocol transducers:

```text
client protocol
       |
       v
    handler
       |
       v
provider protocol
```

The protocols need not be identical or publicly visible.

---

# 13. Continuations introduce another protocol

Handler workflows also manipulate continuations.

A workflow may contain:

```text
Prepare
→ Resume
→ Finalize
```

For a one-shot continuation:

```text
Resume
→ Resume
```

must be illegal.

For a multi-shot continuation it may be legal, but resources captured by the continuation may then be duplicated.

For an abortive handler, the continuation may instead be discarded.

For a suspensive handler, the continuation may escape and be resumed later.

This suggests that continuation usage itself can be viewed as a protocol:

```text
one-shot:

Available
    → Resumed

or

Available
    → Discarded
```

and potentially:

```text
suspensive:

Available
    → Suspended
    → Resumed
```

Continuation multiplicity and session/resource multiplicity may therefore be manifestations of the same deeper static property.

---

# 14. Composition is more important than local checking

A critical test is:

```text
handler H interprets EffectA
    acquires affine resource r
    performs EffectB
        whose handler is multi-shot
    then releases r
```

Even if `H` itself resumes its continuation once, the handler for `EffectB` may duplicate a continuation containing `r`.

A resource system that validates each handler independently but permits this composition is insufficient.

The stronger requirement is:

> **Multiplicity safety must compose across ordinary functions, effect operations, handler boundaries, and continuation capture.**

This should be one of the primary acceptance criteria for candidate designs.

---

# 15. Stress-test suite

Candidate designs should be tested against at least the following cases.

### Transition reuse

Advance a protocol endpoint and then reuse the old state.

### Aliasing

Duplicate an endpoint before advancing one alias.

### Discard

Acquire something whose protocol requires completion or cleanup and abandon it.

### Branching

Carry one resource into alternatives and determine the obligations at the join.

### Recursion

Thread a resource through a recursive protocol such as `query*`.

### Closure capture

Capture a restricted resource and invoke the resulting closure zero, one, or multiple times.

### Polymorphic binding

Attempt to generalize a binding containing or capturing a restricted resource.

### One-shot continuation

Advance resource state, resume once, then finalize.

### Multi-shot continuation

Resume a resource-bearing continuation more than once.

### Abort

Advance a resource and then discard the continuation.

### Suspension

Allow a continuation and its resource state to escape for later resumption.

### Parallel coeffects

Publish a hook carrying a restricted capability to parallel subscribers.

### Nested handler composition

Carry a restricted resource through an operation interpreted by a handler with different continuation multiplicity.

---

# 16. Candidate mechanisms to compare

The stress-test corpus should be reusable across competing designs.

Candidates may include:

```text
affine types
linear types
uniqueness typing
multiplicity-bearing arrows
multiplicity polymorphism
capture typing
resource/effect obligations
generative identities
state-token approaches
combinations of these
```

No candidate should be selected merely because it naturally describes session types.

The desired mechanism should explain the broader Ash problems exposed by the same tests.

---

# 17. Three concentric protocols

The investigation currently suggests at least three distinct but potentially related protocol layers:

```text
1. Client protocol

   Legal sequence of effect operations.

2. Handler protocol

   Legal private workflow used to interpret an operation.

3. Continuation protocol

   Legal use of captured control.
```

Session typing may be useful at all three layers.

Only selected states or transitions of a private handler protocol need become public coeffect hooks.

---

# 18. Main design hypothesis

The current hypothesis is that useful session typing may not require a privileged `Session` type or dedicated protocol calculus.

Much of the required expressivity may emerge from:

```text
static finite state domains
type indexing
associated types / transition evidence
existential and generative identity
effect typing
continuation typing
resource multiplicity
```

The likely irreducible pressure is not state-machine representation.

It is **usage discipline**.

The experiments should therefore answer:

> **Can Ash describe a stateful handler protocol using ordinary typed relationships such that illegal operation order, stale-state reuse, invalid resource duplication, invalid continuation use, and unsafe handler composition become static failures?**

A successful design should do so compositionally and without session-specific compiler rules.