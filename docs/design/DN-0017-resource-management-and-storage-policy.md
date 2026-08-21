# DN-0017: Resource Management and Storage Policy

- ID: `DN-0017`
- Status: exploring
- Related: [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md), [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md), [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md), [DN-0014: Finite Kinds and Promotion](DN-0014-finite-kinds-and-promotion.md), [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md)

> This design note is informative. It explores possible resource-management and
> storage policies; it does not define current Ash, accept an ownership system,
> require optional garbage collection, or authorize runtime work. All types and
> operations are illustrative.

## Question

Could one future Ash resource discipline support deterministic cleanup, more
than one memory-management policy, and transfer of large values while keeping
allocation, copying, suspension, and destruction visible enough to reason about?

## Context and scope

Current Ash has the pure language and runtime semantics defined by the
[Mini-Ash specification](../../spec/README.md), but it has no resource-sensitive
semantics or storage policy. Existing notes explore the pieces that would
constrain this question:

- [DN-0009](DN-0009-effects-handlers-and-continuations.md) owns effect rows,
  handlers, and continuation contracts;
- [DN-0010](DN-0010-identities-and-resource-lifetimes.md) owns identity,
  ownership relationships, and staged removal;
- [DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md) owns usage
  discipline and its compositional stress cases;
- [DN-0014](DN-0014-finite-kinds-and-promotion.md) explores finite static names
  for states without selecting a resource model.

This note asks what runtime policies those mechanisms might permit. It does not
choose where usage properties live, define a borrow checker, make processes a
language primitive, or require general-purpose systems programming.

The source pressure is broader than avoiding tracing collection. Files, sockets,
locks, transactions, mappings, continuations, and registrations also require an
account of authority, transfer, release, and failure.

## Constraints

A candidate should preserve these boundaries:

- effects describe interactions; resource-sensitive types establish authority;
- resource identity, protocol state, usage, alias authority, and storage policy
  remain distinguishable even when one type relates them;
- persistent and immutable data retain efficient structural sharing;
- omitting a scheduler, collector, or allocator from a program should make it
  possible to omit the corresponding runtime machinery;
- source and tooling should expose unbounded copying, allocation, suspension,
  and effectful destruction at the boundary where they matter;
- low-level lowering may consume checked facts but must not become the authority
  for Ash resource safety.

These are comparison constraints, not accepted language requirements.

## Suggested design rules

### Permit plural storage policies

> Suggested rule: Do not make one reclamation strategy the semantic definition
> of every resource.

A future program might combine stack or value storage, unique ownership,
regions, immutable shared storage, reference counting, traced regions, and
foreign storage. A common resource contract may govern their safe use while
libraries or runtime components choose representation and reclamation.

This hypothesis fails if combining policies requires unsound casts, hidden
global tracing, or incompatible meanings for ordinary type and control rules.

### Separate transfer from copying

> Suggested rule: Transferring unique authority need not copy the represented
> payload, but the sender must lose the authority transferred.

For a large array, a send operation could move an allocation descriptor and its
ownership into a mailbox while leaving the bytes in place. The semantic
isolation claim would be that two processes cannot exercise incompatible mutable
authority, not that their data must occupy distinct address spaces.

A type system that accepts both sender and receiver mutation after transfer has
failed. An implementation that silently deep-copies may remain safe but violates
the intended cost contract unless that copy is visible.

### Treat immutable sharing as a separate transition

A unique mutable value might become a frozen shared value. That transition ends
unique mutation authority; it does not by itself choose reference counting,
arena ownership, tracing, or another reclamation policy.

The useful pattern is:

```text
construct with unique authority
    -> freeze
    -> share immutable access
```

The comparison must include persistent structures so that resource discipline
does not turn ordinary functional sharing into repeated copying.

### Make cleanup semantics explicit

If unused affine ownership triggers cleanup at scope exit, the language must
define that as an elimination rule rather than infer it from the word
“affine.” The rule must account for destructor effects, ordering, cancellation,
partial initialization, and failure during cleanup.

Explicit cleanup, implicit deterministic cleanup, and region-wide cleanup are
distinct candidates. [DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md)
owns the usage and control-flow cases that each candidate must pass.

### Keep optional runtimes honest

Delimited continuations may permit a process scheduler to be a library, with a
process represented by a suspended continuation and a mailbox. That is a
hypothesis, not an established architecture. A library candidate must still
state who owns suspended state, queued messages, scheduler data, and unreceived
resources when a process terminates.

A mailbox carrying restricted values is an owning container. Sending transfers
ownership into it; receiving transfers ownership out; destroying the mailbox
must account for every queued value. Scheduler-specific tracing should not be
assumed necessary until this ordinary ownership model fails a named case.

### Preserve checked facts through lowering

Typed Core may need to retain established uniqueness, locality, transfer, and
cleanup facts until the transformations that consume them. It may then lower to
ordinary control flow, allocation, reference operations, and backend aliasing
attributes. [DN-0008](DN-0008-typed-core-and-elaboration.md) owns the
representation and validation question.

Backend metadata may improve optimization. Program soundness must not depend on
a backend assigning Ash-specific meaning to unchecked metadata.

## Candidate directions

### Common discipline with policy-specific libraries

General identity, usage, authority, control, and cleanup rules would establish
safety. Allocators, regions, collectors, shared-storage policies, and schedulers
would implement different policies under those rules. This direction best
matches the goal of paying only for imported machinery, but it demands evidence
that the rules compose across policies.

### Managed-memory baseline with explicit external resources

Ordinary memory would use a required tracing or reference-counted runtime while
files and other resources use separate cleanup rules. This may simplify common
allocation and sharing, but it weakens the claim that memory and external
resources share one discipline and may impose runtime costs on programs that do
not need them.

### Exclusive ownership baseline with managed regions

Ordinary data would follow one ownership regime, while graph-shaped or cyclic
data enters explicit managed regions. This may make costs and destruction
predictable, but boundary friction and persistent-data ergonomics could force
resource policy into otherwise ordinary interfaces.

No direction should be selected from examples alone. The same corpus must
measure rejected safe programs, accepted unsafe programs, surface annotations,
runtime support, and observable costs.

## Evidence and experiments

A disposable experiment should compare the candidates against these cases:

| Case | Required observation | Failure observation |
| --- | --- | --- |
| Unique array transfer | The receiver gains mutation authority and the sender loses it without a payload copy. | Both retain authority or an unreported deep copy occurs. |
| Freeze and share | Many readers share one immutable representation after unique construction. | Sharing restores mutation or requires copying per reader. |
| Persistent structure | Expected asymptotic sharing and update costs remain intact. | Resource rules introduce hidden linear traversal or copying. |
| Deterministic cleanup | Normal return, abort, cancellation, and partial initialization account for cleanup once. | A path leaks, repeats, or silently reorders effectful cleanup. |
| Mixed policies | Owned, region, shared, and foreign values cross typed boundaries without one policy becoming global. | Safety depends on hidden global tracing or unchecked conversion. |
| Mailbox ownership | Queued restricted values have one owner before send, while queued, and after receive. | Process termination or mailbox destruction loses the obligation. |
| Suspended process | Under a one-shot candidate, the scheduler owns the suspended computation and every captured resource remains live. | Suspension duplicates authority or reclamation ignores the capture. |
| Runtime omission | A program that does not select a collector or scheduler links neither facility. | Language semantics require the unused runtime component. |
| Lowering | Checked facts justify transformations before erasure and ordinary backend IR remains sufficient. | Erasure precedes a fact's last use or backend metadata becomes trusted semantics. |

Measure allocation count, bytes copied, maximum live storage, cleanup order,
required annotations, and runtime components. Performance evidence should focus
on hidden cost cliffs and asymptotic regressions, not only peak throughput.

Retain prototype code only if it compares at least two policies under the same
semantic model and records both static and runtime observations. It remains
design evidence until a later decision or proposal and an authorized task adopt
any part of it.

## Open questions

- Which minimum usage and authority rules let storage policies compose?
- Does implicit cleanup apply to every affine owner or only to types with an
  explicit destruction contract?
- How are destructor effects ordered relative to handler unwinding,
  cancellation, and other pending cleanup?
- Can cyclic ownership be confined to explicit managed regions without making
  ordinary abstractions policy-specific?
- Which sharing policies preserve persistent-data ergonomics and predictable
  reclamation?
- What does process isolation require beyond absence of incompatible mutable
  authority?
- Can schedulers remain libraries once parallel execution, cancellation, and
  foreign calls are included?
- Which allocation, copy, suspension, and destruction costs belong in types,
  effects, diagnostics, or optional analysis?
- Which bounded-resource properties belong in a separate build analysis rather
  than expression typing?
- What evidence would show that allocation-level uniqueness is too coarse and
  resource-place decomposition is needed?

The central hypothesis survives only if ordinary functional programs remain
ordinary to write, resource-sensitive boundaries expose their authority and
costs, and selecting one runtime policy does not silently impose it on the rest
of the program.
