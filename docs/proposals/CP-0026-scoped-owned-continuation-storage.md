# CP-0026: Scoped owned continuation storage

- ID: `CP-0026`
- Status: accepted
- Related: [DN-0056](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md),
  [TASK-0057](../tasks/TASK-0057-local-retained-control.md)

> This accepted proposal describes a prospective transition, not current Ash.
> C2 product work starts after the C1 proof result is retained and verified.

## Current behavior

[Effects](../../spec/static-semantics.md#effects) give a selected handler clause
one nonescaping continuation owner. A normal clause path consumes that owner
through `resume` or checked `discard`. [Dynamic execution](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
moves the selected segment into that owner; `resume` restores it above the
original clause continuation and runs the clause suffix when the segment
returns. Neither operation stores the owner as an ordinary value.

[Resources](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
own release independently of duplicable access and track stored dependencies
and completion. [Cleanup](../../spec/static-semantics.md#scoped-cleanup-actions)
owns an invocation and its unfinished completion. A running cleanup can be
captured and resumed but cannot be abandoned. Region placement supplies backing
and validity under its own owner; it does not transfer completion or resource
authority. Generic cells hold reusable discardable values, not owned control.

## Proposed behavior

### Store and admission

Introduce an authenticated scoped store activation `N` for one local executor.
It fixes a reply port `Unit`, an answer type `A`, the resumed computation's row
`rho`, and an exact required external interpretation `I`. The private
checkpoint operation has reply `Unit`. An answer may be library data such as
`Finished(value) | Suspended(key, reason)`; this proposal does not require
these constructor names. `A` may depend on the fresh `N` inside its scope, so
it can contain `Key<N>`; ordinary escape checks still apply at scope exit.
Fixed ports are per activation, not arbitrary
first-class continuation types. A library needing another reply port requires a
separate contract.

Fresh branches start by ordinary calls under admitted private handler roots.
Admission checks the actual function captures, dependencies and effects as
well as later retained control. A private root surrounds all branch-local
handlers, their suffixes after `resume`, and cleanup that must survive a yield.
Its selected checkpoint clause consumes its owner only by retaining it or by
resuming it; discarding that capture would abandon the root's outstanding
completion and is rejected. Inner user handlers keep their existing checked
discard behavior when outside completion remains protected.
The store owner and its driver, including a running drain cleanup, lie outside
that root. The private association from a checkpoint handler to `N` is
administrative and non-owning; it grants no general aliasing or dependency-cycle
exception.

Existing ordinary access remains duplicable: branches and the executor may
interleave access to a still-live outer cell or region under its existing
contract. Their single scope and completion owner is not duplicated. A
branch-local owner moves with its capture and its dependencies cannot escape
to another branch or the executor. Admission checks actual function, callable
and evidence captures and their current access and completion relationships.
Retention and locators grant no additional resource access. One executor
controls `N`, with no parallel store access. Fresh-root admission, continue and
probe occur only in the driver's control outside every active branch root for
`N`. Branches may checkpoint through their private root but cannot drive the
same store, even through a helper. This structural boundary needs no
first-class authority token. The administrative checkpoint clause remains part
of the branch invocation until it actually returns to the driver; removal of
its selected handler during clause execution does not grant driver authority.
This choice gives no concurrent thread-safety or isolated branch-state guarantee.

Each capture's recursively owned closure includes nested live clause captures,
resource owners and armed or running cleanup completions at their structural
positions. Admission rejects moving `N`'s own boundary into `N`, or returning
from the transferring clause while required outside completion is skipped.
External dependencies, region backing, providers and interpreters must remain
valid until their last admitted use and required completion. For this first
local contract, support outside a branch's owned capture must structurally
enclose `N`; support inside the capture moves with it. Other completion orders
need a separate contract. Existing value and operation-payload escape checks
still apply.

`I` describes the actual surviving interpreter requirements of retained control,
including selected handler identity and activation, lexical instantiation,
precedence and relevant provider context. At every restoration the actual
current consumer must satisfy these requirements. A matching type, row, effect
name or same-instance outer handler alone does not establish equivalence. If a
requirement or selected interpretation cannot be established, admission fails.
Handlers captured inside the segment return in their existing order; this does
not make a removed outside handler available. In this fragment an external
interpreter's actual enclosing frame remains live around `N`; checking the
current consumer must also exclude a nearer conflicting interpreter. The
contract does not require assigning a new runtime identity to that frame.

### Transfer and restoration

The authenticated retain carrier is a clause-scoped structural completion
operation, like `resume` or `discard`, available only for the selected
checkpoint clause's live hidden owner. Its source spelling and lowering are not
selected here. It is not an ordinary overridable effect request: an arbitrary
source handler cannot return a same-typed value while claiming to consume the
owner. It checks the store contract and capture
admission, prepares a slot and all fallible transfer resources, then commits a
single move from the clause owner to that slot. Its immediate effects are those
of the store operation; it does not execute the captured computation. Only the
selected owner is consumed; nested owners keep their actual live or consumed
state. On preparation failure, no slot or locator is published and the original
owner and its completion remain intact. The carrier must authenticate the
actual `N` activation and provider; a matching declaration is insufficient.

The resulting opaque `Key<N>` is an ordinary non-owning locator for this
activation and slot generation. It can be copied but cannot extend `N`'s
lifetime or escape its existing identity and dependency checks. Generation
reuse must not make a stale key name new control; representational exhaustion
fails instead of wrapping into an old live identity.

The authenticated continue operation requires executor authority, a key for
`N`, unit input and an admitted current consumer satisfying `I`. On a live
generation, it prepares the move, spends the slot and restores the captured
segment above a `Some` answer adapter and that current consumer. The restored
computation includes its selected handler and nested clause and cleanup state.
Its return, including an answer from a later checkpoint, flows to the current
consumer. It does not return to the clause that transferred the earlier
capture. An absent or spent generation returns `None` without executing control;
copying a key cannot restore a generation twice. The continue row includes
the store operation and `rho`. If it is presented through an ordinary effect
request, a source handler retains its existing precedence: only the admitted
store interpreter performs the store move. An intercepted result alone grants
no ownership or completion fact.

A checkpoint in a nested clause before its `resume` retains that clause's live
owner; one after `resume` retains its consumed state and the remaining suffix.
A checkpoint in running cleanup retains its saved body result and unfinished
cleanup, without making the action eligible for a second invocation. A later
checkpoint during drain returns to the drain's current continue consumer; the
drain's own completion remains outside the stored capture.

After committed transfer, the store owns the capture and its completion until
restoration; after committed restoration, active control owns them. Internal
failure teardown traverses the actual owned-control edges iteratively and must
not release any owner twice. If teardown itself cannot obtain required working
storage, it reports incomplete teardown; residual objects may remain
unreleased. As with current failure teardown, it promises neither source cleanup
nor rollback of already performed effects. Preparation failure before either
move must not duplicate, lose or partially publish an owner. Source cancellation,
arbitrary discard of retained work and a dummy answer are not added.

### Abstract transitions

These transitions specify the proposed ownership moves independently of their
eventual representation. A configuration has a current control context, the
store activation `N` with slots, and its still-live external support. A
selected checkpoint clause has a structural owner `c` in state `live(C)` or
`consumed`, where `C` is the complete owned captured segment. A slot is empty,
reserved, or `live(g, C)` for generation `g`; it can become spent. `D` is the
actual current consumer of a continue operation, not the clause that earlier
transferred `C`.

1. **Prepare retain.** From `live(C)` and an available slot, check admission
   and reserve all required resources. A failed preparation publishes no key,
   restores the unreserved slot state and leaves `c = live(C)`. No source-level
   recovery result is implied by this internal failure rule.
2. **Commit retain.** After successful preparation, change `c` to `consumed`
   and the reserved slot to `live(g, C)` as one ownership move. Return the
   non-owning key `(N, slot, g)` to the transferring clause. The clause may
   produce its `A` answer only when its remaining control does not skip an
   outside required completion. All nested owners remain in `C` unchanged.
3. **Prepare continue.** Check the key's activation and generation, executor
   authority and `D`'s actual interpretation. For a live slot, prepare the
   restoration before consuming it. Failure leaves `live(g, C)` unchanged.
   An absent or spent generation returns `None` to `D` without a move.
4. **Commit continue.** Change `live(g, C)` to spent and install `C` above an
   ordinary `Some` adapter above `D`. The resulting active control uniquely
   owns `C`. When `C` produces `a : A`, the adapter delivers `Some(a)` to `D`.
   No transition re-enters the earlier transfer-clause suffix. Subsequent
   checkpoints can transfer a new live capture to a fresh generation.
5. **Failure disposal.** At an internal failure, the host takes responsibility
   for teardown of actual active control and live slots, including recursively
   owned captures. It traverses these ownership edges iteratively and never
   releases an owner twice. If teardown completes, the represented owners have
   been released; a further resource failure reports incomplete teardown and
   may leave residual objects unreleased. It does not resume suspended source
   control or promise source cleanup.

Slot reuse assigns a generation that cannot alias a previous key during the
activation. At every committed point each capture and its required completion
have exactly one location: a live clause, one live slot, or active restored
control. Consuming a slot transfers that responsibility; it is not evidence
that the branch has finished. Probe and release consult the owning state, not
the library's ready-key collection.

### Normal release and drain

For this local fragment, `W(N)` contains retained captures, active admitted
branch control, and unfinished branch cleanup or close work. Fresh-root
admission begins a branch completion obligation; actual root completion retires
it only after its required cleanup and close work finish. A restored branch
that yields again transfers its obligation to the new capture instead. These
are ownership and analysis facts, not necessarily runtime token objects.
Constructing `Finished` or `Suspended` data, or losing a ready-queue key, does
not register or retire an obligation. `W(N)` excludes the store owner and the
drain's own running cleanup. The authenticated store probe
returns `Quiescent` exactly when `W(N)` is empty; an empty ready queue is not
enough. Normal release requires emptiness on every reachable normal predecessor
of release, after actual handler and cleanup suffixes. Existing cleanup may
invoke a library drain, but its `Unit -> Unit` type alone proves nothing about
that postcondition. An outer discard that owns `N` must establish the same empty
state at the actual structural close predecessor, after its armed drain action
and remaining closing control. It must also preserve required interpreter and
outside completion; otherwise it is rejected. Discard cannot drop live slots
or abandon stored running cleanup. A running drain itself cannot be abandoned.
These source rules are separate from internal failure disposal.

Infer finite normal-return relations for relevant store identities, correlating
input empty/nonempty state, observable result case and output state. A recursive
call group uses an ascending least fixed point over finite possible normal
returns. No returned tuple means no discovered finite normal return, not a
termination claim. Unknown external calls conservatively include possible
returns and state changes; they do not use the empty recursive seed. An
all-empty output check is valid only after the complete relation converges;
the initially empty relation cannot grant a release permission. Exhaustion
discards the unfinished result.

Only a probe whose actual selected interpreter supplies the authenticated store
contract establishes the result/state relationship. A source handler may
intercept the same operation and must be analysed through its real control.
Aliases may preserve a genuine observation while intervening control provably
preserves the same store; a possible change, alias change or loss of exclusive
control invalidates the old fact. Imported summaries retain interpretation and
identity requirements. Joins include all possible paths, including work after
`resume` and cleanup, and actual release is checked after those paths. On
analysis exhaustion no partial permission is published.

Independent linked Effect Core validation reconstructs the actual transfer,
interpretation, authority, completion, probe, freshness and return relationships
after transformations. It does not trust a source summary, a same-typed
substituted callback or a claimed producer annotation in place of that proof.

## Semantic delta

The selected checkpoint clause may consume its otherwise nonescaping owner by
transferring its exact owned capture to the store, and a later admitted
consumer may restore it at most once. Scoped ownership and checked release
extend to retained and restored control. New finite normal-return analysis can
establish a release fact from authenticated observations and actual control.
Other handlers retain their current completion behavior.

## Affected specification areas

- [Syntax](../../spec/syntax.md) and [name resolution](../../spec/name-resolution.md),
  if the selected store API requires source forms or identities.
- [Static effects](../../spec/static-semantics.md#effects),
  [cleanup](../../spec/static-semantics.md#scoped-cleanup-actions),
  [resource dependencies](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies),
  and region ownership.
- [Effect execution](../../spec/dynamic-semantics.md#effect-handlers-and-completion),
  resource and cleanup execution, and failure disposal.
- [Effect Core lowering](../../spec/elaboration.md#effect-core-lowering) and its
  [validation boundary](../../spec/elaboration.md#validation-boundary).

## Resulting specification truth

Once the complete product is integrated, accepted programs may transfer a
selected owned capture into its scoped store and restore a live generation
once at an admitted current consumer. Their store, branch and support owners
remain valid through required completion; a normal store release follows a
checked empty-work state. Runtime failure keeps the stated ownership accounting
without promising source cleanup. Scheduling remains library control.

## Interactions

The existing resource, region, exact-handler, dependency and cleanup rules
remain in force. A region that supplies backing does not become the store's
logical completion owner. Recursive or imported helpers and generic instance
coincidence must preserve actual identity and interpretation. Checkpoint
helpers use ordinary effects, so nearest-handler selection still applies.
Normal-return analysis proves only partial correctness: an infinite yielding
drain can fail to return while preserving ownership.

## Non-goals

No task or scheduler Core node, generic continuation value, arbitrary foreign
stack suspension, migration, shared-store parallelism, cancellation, wait or
channel protocol, compiler-inserted checkpoints, fairness, termination or
bounded latency is introduced. No new general resource declaration or
unrestricted exception to dependency cycles follows from this store. A
ready-only queue is not the authoritative completion state.

## Required evidence

- The [bounded C1 proof assignment](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md#c1-bounded-ownership-and-completion-proof-assignment),
  including correspondence and frozen AD-0012 integration, plus a separately
  mechanized C3 analysis before relying on its release facts.
- Source, Core and evaluator correspondence for exact ports, admission,
  ownership moves, generation, capacity and failure; independent revalidation
  after transformed Core.
- Positive cases for current-consumer return, nested clause states, suspended
  and repeated cleanup, a safe armed-drain outer discard, interleaved access to
  an outer cell and region support. Negative cases for self-capture, skipped
  completion, removed interpreters or abandonment of a running drain,
  branch-local dependency escape, stale/copied keys and failed transfer
  preparation.
- Genuine, intercepted, fabricated and stale probe cases; recursive and imported
  control, including a later-discovered nonempty return; handler and cleanup
  suffixes; callback substitution; conservative unknowns and bounded-work
  exhaustion.
- Executable coroutine, cooperative and explicitly gas-guarded library
  examples, including R waiting for P while Q remains retained and the final
  drain completes Q. False and true guards and lost ready-queue entries must be
  covered. These show no fairness or termination guarantee.
- Updated specification, focused checks and independent review for each
  delivery; the connected C2/C3 workspace checkpoint and final integrated gate;
  retained-result verification and the separate Main gate recorded in
  [TASK-0057](../tasks/TASK-0057-local-retained-control.md).
