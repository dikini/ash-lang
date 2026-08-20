# DN-0013: Session and Resource Protocol Stress Tests

- ID: `DN-0013`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md), [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md), [DN-0012: Coeffects and Hooks](DN-0012-coeffects-and-hooks.md), [DN-0014: Finite Kinds and Promotion](DN-0014-finite-kinds-and-promotion.md), [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md), [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md)

> This design note is informative. It does not define current Ash, accept an architecture, or propose privileged session types. Its protocols and examples are an evaluation corpus for general Ash mechanisms.

## Question

Can general Ash mechanisms describe and statically check useful temporal protocols, including private handler workflows, so that illegal operation order, stale-state reuse, invalid resource duplication, invalid continuation use, and unsafe handler composition fail statically?

## Context and scope

An effect signature describes a typed interaction API. It does not by itself describe the legal order of interactions. For example, signatures for `begin`, `query`, `commit`, and `rollback` do not establish the sequence `begin; query*; (commit | rollback)`.

This note uses session-like protocols to stress possible future facilities such as finite static domains, type indices, associated types or other transition evidence, existential and generative identity, effect typing, continuation typing, and resource multiplicity. It asks whether those general facilities suffice. It does not select a dedicated protocol calculus, a privileged `Session` type, or any particular resource system.

All examples below are illustrative. They are not current Ash syntax or semantics.

The easy part appears to be representing a state graph. The harder part is preserving the authority carried by a state-indexed value when that value can be duplicated, discarded, captured, generalized, or carried through effect handlers and continuations.

## Suggested design rules

### Separate interaction APIs from temporal protocols

> Suggested rule: Treat effect typing and protocol typing as separate judgments: an effect says which typed interactions are available, while a protocol says when those interactions are legal.

A candidate should first try to express protocols with general type-system machinery. Irreducible language support becomes a candidate only if the experiments identify a requirement those mechanisms cannot express.

### Represent state machines with ordinary static relationships

> Suggested rule: Prefer finite nominal states, type indices, transition evidence, and ordinary algebraic data types before adding recursive or choice-specific session constructs.

A transaction may be modeled conceptually as:

```text
Txn<Idle> --begin--> Txn<Open>
Txn<Open> --query--> Txn<Open>
Txn<Open> --commit | rollback--> Txn<Closed>
```

A relation such as `Step<Protocol, State, Operation> -> NextState` can make a transition legal only when corresponding evidence exists. An algebraic result can expose branch-specific successor states. Nominal state nodes plus transition evidence may encode cycles such as `query*` without structural recursive types or type-level fixed points.

This approach succeeds if legal transitions, choice, and cyclic state graphs can be checked without protocol-specific rules. It fails if ordinary relations cannot retain the branch or recursion information needed by realistic protocols.

### Keep usage properties independent

> Suggested rule: Model duplication and discard as separate properties, and require each candidate to say where those properties live.

At minimum, the investigation must distinguish unrestricted, affine, and linear behavior, while not assuming that the unusual fourth combination—duplicable but not discardable—is meaningless. Candidate locations include values, bindings, types, type constructors, function arrows, closure captures, continuations, effect computations, and resource obligations.

The diagnostic example is a closure that captures a restricted resource and is called twice. A successful design explains, without special treatment of the resource type, whether the captured value makes the closure restricted, changes its arrow, appears in a capture set, or creates an enclosing obligation. A design fails if the second call is accepted despite duplicating single-use authority, or if it rejects safe uses without identifying the relevant obligation.

Usage and alias authority are separate axes. A unique mutable value may be
non-duplicable, but uniqueness states that incompatible aliases do not exist;
affinity states that a particular value may be discarded but not duplicated.
One property must not stand in for the other.

The first useful static distinction may be qualitative—whether duplication and
discard are permitted—without tracking exact use counts. A candidate should add
quantitative multiplicities only when the corpus contains a soundness or
expressiveness case that runtime state or separate analysis cannot cover.

### Keep handler workflows private by default

> Suggested rule: Permit a handler implementation to use a private protocol, and expose only explicitly selected workflow points as public hooks.

An effect operation may initiate a private workflow containing validation, provider actions, other effect operations, state transitions, and a final resume, abort, or suspension. A public coeffect hook can be understood as a projection of a named point in that workflow; private states need not become public API.

The client protocol and the handler's implementation protocol may differ. A handler may therefore act as a protocol transducer, translating a public transaction sequence into a private connection or provider sequence.

### Treat continuation use as a protocol

> Suggested rule: Make continuation availability, resumption, discard, and suspension visible to the same usage analysis that protects other restricted resources.

A one-shot continuation may move from `Available` to `Resumed` or `Discarded`; a suspensive continuation may move through `Suspended` before later resumption. Multi-shot resumption is only safe when duplicating the continuation also safely duplicates everything it captures. Continuation multiplicity and resource multiplicity may be instances of one deeper usage property rather than unrelated features.

### Require compositional safety

> Suggested rule: Multiplicity safety must compose across function calls, effect operations, handler boundaries, continuation capture, and public hooks.

Local handler checking is insufficient. Consider a handler that acquires an affine resource, performs another effect whose handler is multi-shot, and then releases the resource. The outer handler may resume only once while the inner handler duplicates a continuation containing the resource.

A candidate succeeds only if it rejects the unsafe composition or proves that the captured authority can be duplicated. It fails if each handler passes in isolation while their composition duplicates or loses an obligation.

## Candidate directions

The corpus should compare at least these mechanism families, alone and in combinations:

- affine types;
- linear types;
- uniqueness typing;
- multiplicity-bearing arrows;
- multiplicity polymorphism;
- capture typing;
- resource or effect obligations;
- generative identities;
- state-token approaches.
- structural inference from the restrictions of fields and captures;
- runtime counters or [certificates](DN-0018-runtime-established-static-evidence.md)
  for exact-use policies that do not affect qualitative soundness.

No mechanism should win because its vocabulary resembles session types. The useful candidate is the one that also explains closure capture, generalization, continuation use, effect handling, and composition with the fewest special cases.

## Interactions

### Three protocol layers

The investigation must keep three concentric layers distinct:

1. The client protocol constrains the legal sequence of public effect operations.
2. The handler protocol constrains the private workflow used to interpret an operation.
3. The continuation protocol constrains the use of captured control.

The layers may share machinery, but they have different boundaries and visibility. Only selected handler states or transitions need appear as public hooks.

### Effects inside handler protocols

A private workflow may invoke ordinary effects. The checker must then answer both which effects escape and which operations are legal in the current protocol state. A sequence such as `connect; write; close; write` can be well typed as individual operations yet invalid as a protocol.

### Resource-sensitive generalization

Local polymorphic generalization must not duplicate or erase obligations held or captured by a binding. A candidate should integrate resource facts through the generalization eligibility policy rather than silently treating resource-bearing bindings as ordinary reusable values.

### Branches, recursion, and identity

Branches must reconcile obligations at their join; recursion must thread the current state through each iteration; and generative or existential identity may be needed to prevent resources or endpoints from unrelated sessions from being mixed.

### Parallel hooks and nested handlers

Publishing a restricted capability to multiple hook subscribers can duplicate it. Nested handlers can change continuation multiplicity around a captured resource. Both cases test whether public composition preserves private protocol guarantees.

### Destruction and cancellation

Affine discard does not by itself define deterministic destruction. A candidate
must state whether discarding an owned value elaborates to a destructor, which
effects that destructor may perform, how destruction is ordered, and what
happens during abort, cancellation, or partial failure. Linear completion
obligations and affine values with implicit cleanup may produce different
answers and should not be conflated.

## Evidence and experiments

The following corpus is a minimum, not a feature checklist. Each experiment should record the accepted and rejected program, the inferred usage or transition facts, the mechanism responsible for the result, and any special rule required.

| Stress category | Success observation | Failure observation |
| --- | --- | --- |
| Transition reuse | Advancing an endpoint invalidates the old-state authority. | The old endpoint remains usable after a transition. |
| Aliasing | Advancing one alias either rejects prior duplication or updates the single shared authority soundly. | One alias advances while another retains stale authority. |
| Discard | An obligation that requires completion or cleanup cannot disappear silently. | A required resource can be abandoned without discharge or an explicit permitted discard. |
| Branching | Each branch accounts for the resource and the join accepts only compatible resulting obligations. | One branch loses, duplicates, or advances an obligation incompatibly. |
| Recursion | A loop such as `query*` threads exactly the successor state into the next iteration and exit. | Recursion recreates an old state or drops its completion obligation. |
| Closure capture | Calling a closure zero, once, or many times is checked against the captured resource's discard and duplication properties. | Closure invocation count is unrelated to captured authority. |
| Polymorphic binding | Generalization is restricted or annotated when a binding contains or captures a restricted resource. | Instantiation duplicates or erases a resource obligation. |
| One-shot continuation | At most one resume is accepted, followed by valid finalization. | A second resume is accepted or finalization uses pre-resume authority. |
| Multi-shot continuation | Repeated resume is accepted only when the captured environment is safely duplicable. | A multi-shot handler duplicates a restricted capture. |
| Abort | Discarding the continuation checks every captured discard obligation. | Abort silently abandons a non-discardable resource. |
| Suspension | Escaping control carries its resource state and resumes with that same authority later. | Suspension loses, duplicates, or reconstructs the captured resource state. |
| Parallel coeffects | Parallel subscribers receive only duplicable data or a soundly mediated capability. | A hook broadcasts a restricted capability as though it were unrestricted. |
| Nested handler composition | Continuation and resource multiplicities remain safe across handlers with different policies. | Independently accepted handlers compose into duplication or loss. |
| Composite propagation | A product or closure is no more duplicable or discardable than its restricted contents. | Wrapping a restricted value restores unrestricted use. |
| Deterministic cleanup | Every accepted exit path runs or transfers the required cleanup exactly as its contract states. | Return, abort, cancellation, or destructor failure silently leaks or repeats cleanup. |
| Dynamic exact bound | A runtime counter enforces an exact-use policy without weakening static non-duplication. | Encoding the count dynamically permits duplication of the underlying authority. |

Additional comparison cases should establish whether:

- finite nominal states and transition evidence express legal order without a privileged session construct;
- ordinary ADTs retain different successor states across protocol choice;
- nominal state graphs express useful recursive protocols without static fixed points;
- private handler transitions can contain effect operations while keeping their state private;
- public hooks can be verified as projections of actual private workflow points;
- a handler can translate a client protocol into a distinct provider protocol;
- calls to the minimal captured-resource closure are accepted zero times only when its capture is discardable, once when the single call accounts for the capture, and many times only when its capture is duplicable, with every disallowed call count rejected;
- the affine-resource/multi-shot-handler example is rejected compositionally.

A prototype, if needed, is disposable. Retain it only as design evidence if it compares multiple mechanism families against the same corpus and records both false acceptances and false rejections. It must not become product architecture without a later decision or semantic proposal and an authorized task.

## Open questions

- Are finite nominal state graphs sufficient for practical recursive protocols, or does some case require structural recursion or type-level fixed points?
- Which transition relation mechanism gives useful inference and diagnostics without making protocol states privileged?
- Where should duplication and discard properties live, and can one placement cover values, closures, continuations, and computations?
- Does the unusual duplicable-but-not-discardable combination reveal a real obligation model?
- Can resource-sensitive generalization reuse the candidate seam explored in [DN-0006: Initial Type System](DN-0006-initial-type-system.md) without changing ordinary `let` semantics?
- What identity mechanism prevents endpoints from distinct protocol instances from being mixed?
- How are branch joins, abort, exceptions, and cleanup obligations reconciled?
- Does affine elimination invoke implicit destruction, require explicit cleanup,
  or vary by resource type, and how are destructor effects ordered?
- Which real program requires static exact-use arithmetic rather than a runtime
  counter or separate bounded-resource analysis?
- How should hook publication describe sequencing, concurrency, and the multiplicity of payloads?
- Can one continuation/resource analysis cover one-shot, multi-shot, abortive, and suspensive handlers?
- Which experiment, if any, demonstrates irreducible need for language support specific to protocols?

The main hypothesis remains that state-machine representation will emerge from ordinary static relationships, while usage discipline will supply the decisive evidence. The hypothesis survives only if the same general machinery rejects invalid state order, stale reuse, duplication, continuation misuse, and unsafe handler composition without protocol-specific escape hatches.
