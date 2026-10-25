# DN-0053: Scoped Generic Cells Without Native Owners

- ID: `DN-0053`
- Status: exploring
- Related: [generic cell checkpoint evidence](generic-cell/evidence.md),
  [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0043](DN-0043-shorter-surface-alternatives.md),
  [DN-0054](DN-0054-base-lexical-region-memory-contracts.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This note records the agreed candidate contract for a generic cell following
> the ash-ffi checkpoint. It defines no current Ash semantics, accepts no
> implementation architecture, and authorizes no product implementation or
> prototype. Resource-scope lifetime and rejection of resource dependency
> cycles are explicit initial restrictions.

The [product checkpoint integrated into local Main](generic-cell/evidence.md)
retains the accepted transition's implementation, specification, tests and
verification, together
with commands for retrieving its proposal and task history from local Git.
Its verified local Main integration is recorded there. This note retains the
candidate's rationale, alternatives and future questions; the current
specification supplies language
rules. Broader region contracts remain in
[DN-0054](DN-0054-base-lexical-region-memory-contracts.md).

## Question

Can `Cell<R,T>` provide reusable typed mutation through effects and scoped
ownership without acquiring a foreign owner, while preserving lexical scope,
payload dependencies, closure capture, and required completion?

## Context

The target baseline is the ash-ffi checkpoint `ffi-base`, commit
`354c76b391fe4af665cf6a03479a9874a57cb3e3`. Its implemented
[cell rules](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/static-semantics.md#scoped-cells-and-resource-dependencies)
separate a duplicable access handle from scope-owned release. Cells store only
`Int`. The baseline's
[source resource rules](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/static-semantics.md#source-resource-declarations)
support private Ash data, but require an authenticated foreign owner.
`Foreign.data_of` and `Foreign.replace_data` are restricted to that admitted
State/data relationship; they are not general cell operations.

[DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md) compares
shared mediated access, linear successors, and uniqueness. This note selects
shared access for the candidate, without selecting the other disciplines.
[DN-0035](DN-0035-region-memory-management-and-verified-providers.md) separates
name scope, storage lifetime, access authority, and completion.
[DN-0054](DN-0054-base-lexical-region-memory-contracts.md) proposes the explicit
region contracts that compose with this cell; generic cells do not require
region-backed ordinary construction first.

## Constraints

- Tie each cell's logical lifetime to its resource scope. A longer-lived
  backing allocation does not extend its access authority.
- Reject self-dependency and cycles between resource owners, including cycles
  hidden through payload closures or other cells. Preserve ordinary immutable
  cyclic data that introduces no prohibited resource dependency.
- Use ordinary reusable, discardable source values as payloads, subject to
  their dependencies. Do not introduce linear payloads or implicit disposal.
- Preserve current integer-cell behavior, exact handler precedence, lexical
  instantiation, and structural completion. Existing API compatibility is a
  delivery requirement; changing a type constructor's arity is not an alias.
- Preserve rank-1 source typing. A cell stores one monotype, not a scheme.
- Keep generic cell state independent of native State, ABI layout, foreign
  allocation, and native teardown.
- Retain independent Core validation and finite, charged dependency analysis.
  An implementation side table alone is not authority.

## Candidate directions

### Selected semantic approach

Generalize the existing cell primitive to hold one ordinary Ash value, with
ordinary effect requests for access. This is the smallest extension of the
current scoped-cell model.

A general declaration form for resources with arbitrary Ash state could later
reuse this contract, but is a broader language change. Linear state threading
would require additional use-accounting rules. Neither is a prerequisite.
The concrete Core representation and any shared implementation with existing
integer cells remain open.

### Types and operations

These are schematic roles and signatures, not selected source spellings:

```text
Cell<R,T>          opaque reusable access
CellProvider<R,T>  sealed evidence introduced by acquisition
CellOps<R,T>       exact effect instance

read  : Cell<R,T> -> T         ! {CellOps<R,T>}
write : (Cell<R,T>, T) -> Unit ! {CellOps<R,T>}
```

`R` and `T` have kind `Type`. Both methods require the exact
`CellProvider<R,T>`. An ordinary implementation, local evidence block, matching
name, or compatible representation cannot create a handle or provider authority.

`T` is fixed for one activation. It can be an ordinary data or function type;
there is no cell of an uninstantiated polymorphic scheme. No new `Copy` or
`Drop` interface is implied. Restricted payloads would need a separate proposal
covering copy, replacement, take, disposal, and completion. The initial API has
no empty state, manual release, or exclusive-borrow operation.

A read returns the stored ordinary value without consuming access. This
duplicates a value reference where ordinary Ash shares represented data; it
does not perform a deep copy or erase storage dependencies. A write replaces
the stored value and returns `Unit`. Discarding the previous value invokes no
source destructor and does not complete owners referenced by non-owning handles.

### Acquisition and scope

The following is illustrative acquisition syntax:

```text
resource Cell<R,T> c = initial {
    body
}
```

The initializer checks as monomorphic `T` and evaluates once in the preceding
scope. Neither `R` nor `c` is available there. Successful preparation introduces
a fresh rigid lexical identity, a non-owning handle, exact provider evidence,
and the cell interpreter for the body. Each execution creates a fresh runtime
activation, including repeated execution of the same source site.

The expression returns the body's answer directly. Its outward row combines
the initializer row with the body row after removing exactly `CellOps<R,T>`.
Normal typing of nested source handlers already accounts for their direct
outward requests. Other cell instances remain outward. Acquisition does not
introduce a native-resource outcome wrapper.

The result type, outward row, escaping schemes, evidence, and retained value
dependencies cannot expose the closing identity. Nested lexical blocks can
return access to a point still inside this resource scope. They cannot extend
the resource scope by returning a handle or a closure outside it.

### Retained payload dependencies

Every initializer and replacement must satisfy this invariant:

> Every resource owner required by the retained payload is proved to outlive
> the cell owner. The payload cannot require this cell's own owner.

The relation is strict for distinct resource owners. Checking follows actual
handles, selected fields, closures, selected evidence, and indexed operation
metadata, including dependencies reached through another cell. An unused
implementation environment entry is not by itself a capture.

An inner cell can retain access to an enclosing resource. An outer cell cannot
retain a value dependent on an inner resource, even if the program later clears
the cell before that resource closes. Proving temporary retention safe is
outside this initial contract.

A stored closure that captures its own cell rejects even when its exposed type
contains no `R`. An indirect cycle is also forbidden. This is an intentional
restriction on resource dependencies, not a claim that every such cycle is
intrinsically unsafe or a prohibition on ordinary cyclic immutable graphs.

The baseline's request-payload checking provides one reusable boundary: a
write reaching an outer cell interpreter cannot carry a younger dependency
across that dependency's owner. Inference must also preserve dependencies
through stored contents, aliases, imported helpers, and later reads.

### Reads, snapshots, and closures

A closure that reads a cell when called retains access to that cell. It can
be called repeatedly while the owner is live but cannot escape that owner.
A closure capturing a value read earlier retains that value's dependencies.
The distinction follows capture and call behavior, not the exposed arrow alone.

For example, these are scenario descriptions:

```text
live_reader  = closure that reads c when called
snapshot     = read c
saved_reader = closure that returns snapshot
```

An independent integer snapshot and `saved_reader` can escape the cell.
If the snapshot is access to outer region A, it still requires A. If it is a
closure requiring A, the captured dependency remains even in an identity-free
function type. Returning a locally acquired counter's `live_reader` beyond its
cell scope rejects; choosing heap storage does not repair that escape.

Later writes do not change earlier snapshots or invalidate their independent
value relationships. Inference must distinguish an earlier known independent
read from a later stored value capturing an outer owner. Branches and recursive
calls require sound joins and a finite analysis; unknown relevant behavior can
reject when safety cannot be established. The contract does not require a
particular flow-analysis algorithm or promise exact analysis for all programs.

### Effect interpretation and execution

The owner retains a payload root and activation. The builtin read and write
transitions authenticate their exact operation, instantiated types, and handle
before access. Preparation and checking precede mutation; refusal cannot publish
a partial cell or partially perform a write.

Ordinary source handlers retain precedence over the cell interpreter. An
intercepted read has the checked dependencies of that handler's reply; it must
not be assumed independent merely because the builtin cell's stored value would
be independent. A locally intercepted write that never reaches the slot does
not change it. Interception grants no acquisition or completion authority.

Primitive reads and writes invoke no user callback. A helper that reads, calls
an effectful function, then writes has no additional atomicity guarantee.

Capture/resume moves the same owner and payload without reacquisition.
Checked discard releases owned cells in structural order after required
dependent cleanup. Cleanup inside a cell scope may use its still-live cell.
Normal close removes the payload root once; ordinary values retained elsewhere
remain governed by their own storage and dependencies. Releasing a cell does
not promise immediate reclamation of all represented payload data.

Capacity or work exhaustion retains the existing internal-failure boundary;
it is not a new recoverable allocation effect. Internal termination promises
no source cleanup, and divergence promises no eventual release.

### Composition with regions and mutable syntax

`R` identifies the cell owner, not an allocator. If a later implementation
places its slot in region A, A must remain valid for the slot, but closing the
cell still revokes access at R. A region-backed payload retains its original
region dependencies. Assignment neither relocates it nor extends its region.

Regions provide placement and allocation. An ownership scheme determines who
owns A and its allocated objects and determines A's lifetime; lexical scope is
the first scheme explored in
[DN-0054](DN-0054-base-lexical-region-memory-contracts.md). Each region type may
specify an earlier object reclamation policy, including region-specific
collection. That policy must preserve valid object use; reclaiming A reclaims
all remaining objects allocated there together. A slot backed by A is subject
to this storage lifetime while R still bounds its logical access and completion.
None of these choices changes this cell candidate's resource-scope lifetime or
retained payload restrictions.

Under [DN-0054](DN-0054-base-lexical-region-memory-contracts.md), allocating
helpers initially receive explicit region access. That choice does not extend
cell lifetimes or introduce implicit allocation-polymorphic closures.

Mutable-variable syntax can later elaborate a declaration to a resource scope
over its lexical remainder. Bare reads, explicit access sharing, assignment
order, and snapshots must remain distinct as described by
[DN-0043](DN-0043-shorter-surface-alternatives.md#resource-access-and-mutable-payloads).
The cell contract selects no mutable-variable grammar.

## Evidence and experiments

The following observations motivated the accepted transition. The
[checkpoint evidence](generic-cell/evidence.md) records their implemented and
verified product results; this informative table supplies no additional rules.

| Case | Positive evidence | Required rejection or failure observation |
| --- | --- | --- |
| Typed payload | Int, data, and admitted function values support repeated reads and writes with sharing preserved. | Payload type changes or polymorphic cells reject. |
| Activation | Repeated and nested acquisitions retain distinct activations and exact operations. | A donor or stale key grants no access. |
| Aliases and helpers | Aliases, imported helpers, branches, and recursion preserve the same slot. | Helpers cannot erase stored dependencies or manufacture evidence. |
| Snapshot | An earlier independent read remains independent after a later outer-dependent replacement. | A live-reader closure cannot escape its owner. |
| Outer dependencies | An inner cell stores and returns access to an outer owner while it lives. | A younger dependency cannot enter an older cell. |
| Cycles | Ordinary immutable cycles with no prohibited owner dependency remain usable. | Direct and indirect resource dependency cycles reject, including hidden captures. |
| Handlers | Exact overrides preserve reply dependencies and request order. | An override cannot create slot or completion authority. |
| Control | Resume preserves the same payload; discard closes once after dependent cleanup. | Required outside or running completion cannot be skipped. |
| Validation | Construction, copying, transforms, and restored Core preserve all retained facts. | Changed owner, payload type, operation, or dependency facts reject independently. |
| Failure and cost | Exact, insufficient, and retry budgets preserve publication and mutation boundaries. | No partial authority or silent increase of work, stack, or capacity limits. |

This note authorizes no prototype or product change. Any later experiment
must isolate a remaining question and preserve the checkpoint's snapshot,
helper, hidden-capture, scope-completion and dependency boundaries.

## Open questions

The checkpoint retains the selected immutable contents-flow graph, shared
runtime kernel with distinct generic and legacy APIs, and authenticated Core
encoding. Its [evidence](generic-cell/evidence.md) records their measured costs
and boundaries. Further changes require separate design and authorization.

- Which concrete cases later justify temporary younger dependencies, resource
  cycles, restricted payloads, or finer borrow endpoints?
- How should future mutable syntax expose read, access sharing, and replacement
  without changing evaluation multiplicity or local generalization?
