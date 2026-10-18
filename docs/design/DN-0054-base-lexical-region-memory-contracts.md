# DN-0054: Base Lexical Region Memory Contracts

- ID: `DN-0054`
- Status: exploring
- Related: [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md),
  [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0044](DN-0044-no-default-runtime.md),
  [DN-0053](DN-0053-scoped-generic-cells-without-native-owners.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md)

> This note proposes a base region contract compatible with the agreed scoped
> Cell candidate. Explicit region access is the agreed initial call boundary;
> the remaining refinements are proposed design rules. This note defines no
> current Ash semantics, selects no source grammar or implementation
> architecture, and authorizes no product implementation or prototype.

## Question

What minimum region rules settle allocation, value validity, sharing, closure
capture, publication, and completion without changing the resource-scope
lifetime or cycle restrictions of `Cell<R,T>`?

## Context

The target is a possible extension after the ash-ffi checkpoint `ffi-base`,
commit `354c76b391fe4af665cf6a03479a9874a57cb3e3`. Its implemented
[resource dependencies](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/static-semantics.md#scoped-cells-and-resource-dependencies)
and [execution rules](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/dynamic-semantics.md#scoped-cell-execution)
provide scoped access and completion, but no selectable storage policy for
ordinary construction. The current ordinary heap, mathematical integers,
immutable sharing, recursive data, and lexical closures remain the baseline.

[DN-0035](DN-0035-region-memory-management-and-verified-providers.md) proposes
regions as storage-providing resources, with nearest applicable allocation as
a future default and separate policies for reclamation.
[DN-0044](DN-0044-no-default-runtime.md) separates application policy selection,
state acquisition, construction lowering, and service requirements.
[DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) distinguishes
foreign ABI facts from checked storage and access authority. None implements
this base.

The [scalar Arena evidence](provider-experiments/arena-results.md) transfers
capacity, publication, activation, and completion cases. It establishes neither
general graph layouts nor borrowing. Partial wider experiments are not accepted
capabilities. The generic Cell candidate in
[DN-0053](DN-0053-scoped-generic-cells-without-native-owners.md) needs only valid
payload dependencies, not successful completion of all this region work.

## Constraints

- Keep lexical name scope, physical storage lifetime, value validity, access
  permission, and completion authority distinct.
- Keep region owners scoped and nontransportable. No owner-plus-dependent
  package or reference count extends a whole region beyond its resource scope.
- Reject cycles of resource ownership dependencies. Preserve ordinary sharing
  and cyclic immutable graphs within their checked validity.
- Keep `Cell<R,T>` access tied to R's resource scope. Its retained payload
  dependencies must strictly outlive R; longer backing lifetime or quarantine
  cannot admit self-dependency, an owner cycle, or access after R closes.
- Preserve ash-ffi's request-payload boundary, including hidden captures and
  indexed operation metadata. Allocation introduces no exception for a request
  interpreted outside a required owner.
- Distinguish source scope completion from physical owner consumption. Retained
  owners and their transitive dependencies remain protected with ordinary access
  revoked; source completion alone does not authorize backing release.
- Require explicit region access at allocation-capable helper boundaries first.
  Keep existing rank-1 source restrictions; do not introduce implicit
  allocation-polymorphic returned closures.
- Preserve existing ordinary construction until a separate proposal specifies
  its region lowering, effects, failure, and entry-result contract.
- Keep checked operations and provider assumptions explicit. An interface
  implementation, numeric offset, or compatible type grants no memory authority.
- Begin sequentially with immutable region objects and a fixed-arena comparison.
  Generic Cell supplies mediated mutable state; exclusive views, moving
  collection, owner transport, and concurrency are separate extensions.

## Candidate directions

### Roles and initial boundary

The base logical model distinguishes the following roles. Names such as
`Region<A>` describe roles, not selected source declarations:

| Role | Proposed responsibility |
| --- | --- |
| Region identity A | Relate one owner's storage, access, effects, and completion. Each successful execution has its own activation. |
| Region access | Reusable non-owning permission to request the admitted allocation operations while A is live. |
| Region owner | Retain backing storage and required completion; aliases cannot close it. |
| Provider contract | State admitted representations, capacity units, acquisition and allocation outcomes, and reclamation guarantees. |
| Allocation record | Identify an initialized object and its extent, representation, and access provenance. It is not ownership of A. |
| Value dependency facts | Retain the storage and capability owners required to use the particular value. |
| Completion obligations | Identify cleanup that must run before backing storage is released. |

Start by exposing explicit region allocation without rewriting all existing
ordinary values. The first provider comparison uses fixed storage and bulk
release. Static selection fixes the discipline; capacity and success can still
depend on execution. Storage can come from foreign allocation, caller backing,
or another admitted primitive. No native owner is intrinsic to the logical
region contract.

Acquisition evaluates its configuration in the preceding scope, then creates
fresh A and its access only on success. Refusal enters no body and publishes no
partial owner. A provider must state its acquisition and body-result report
contract; there is no universal implicit outcome flattening. Required backing
release is established before successful access is published.

This is a staged refinement of DN-0035, not a replacement default heap policy.
Its proposed nearest-region convenience remains a later elaboration question.
One managed ordinary heap and individually owned storage remain comparison
alternatives with the tradeoffs recorded there.

### Explicit allocation and call boundaries

An allocation-capable helper receives region access explicitly. Its public
contract retains the exact region parameter, effects, result storage
relationships, and dependencies on its input values. Generic globals can
quantify that parameter using ordinary rank-1 rules. Monomorphic callables keep
their fixed region relationships.

Entering a helper, binding an alias, or entering an ordinary block acquires no
new region. Passing region B to a helper selects B for the constructions it
explicitly directs there. Existing values retain their storage. Calling a
closure inside B does not retarget access to A captured by that closure.

Creating a closure and allocating when it is later called are separate events.
A closure may receive region access as an ordinary parameter or retain access
lexically, subject to its monomorphic type and actual captures. It cannot
silently become universally allocation-polymorphic when stored or returned.

Later implicit construction must lower to an equivalent checked allocation
relationship. A future nearest-region form must specify the context at each
construction and call, including callbacks and returned closures. It cannot
select another region at runtime merely because a similarly named provider is
nearer. This note adds no implicit caller-context rule.

### Checked construction

A new region allocation requires live exact region access, an admitted
representation and construction, checked size and alignment, sufficient
capacity, and initialized contents before readable access is published. Public
operations expose typed access, not forgeable addresses or arbitrary object
indices. Native layout and Ash representation are separate contracts.

### Reservation and local initialization

Construction with younger dependencies uses two separate boundaries. Consider
outer region A and inner cell R. Sending an R-dependent closure as an ordinary
allocation request to A's outer interpreter is forbidden by the
[baseline request-payload rule](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/static-semantics.md#scoped-cells-and-resource-dependencies),
even when the eventual object would remain confined to R.

The proposed route reserves storage using independent requirements, then
initializes it locally while R remains live. This is a scenario description,
not executable source or a new ordinary function API:

```text
inside R, with access to outer region A:
    prepare the closure and its checked representation locally
    reserve storage from A using independent size and alignment requirements
    initialize the reserved storage locally with the closure
    publish access requiring both A and R
```

The reservation request's operands and exact type/effect metadata must be
independent of R. An R-indexed layout descriptor stays local; omitting the
closure term while exporting its dependency through metadata is not sufficient.
A reservation publishes no readable typed object or ownership of A.

Local initialization requires a separately checked construction primitive or
compiler lowering. It authenticates the exact reservation, extent, layout,
initializer, and retained dependencies before publication. It executes in the
constructing computation under R, invokes no source callback, and issues no
outward request carrying the payload. Ordinary access types or compatible
descriptors cannot manufacture this permission. This boundary is proposed work,
not permission already supplied by ash-ffi or its native byte primitives.

Any pending reservation belongs to that construction's completion obligation
before fallible reply handling. Capture/resume preserves the same obligation;
abandonment must cancel or account for it without publishing readable access,
corrupting other allocations, or bypassing retained-owner protection. Independent
Core validation must check the reservation, local initialization, and publication
relationship. A provider without this checked boundary rejects construction
with younger dependencies; it cannot forward the payload to A instead.

### Aliases and projection

Constructing a new object in A gives access to that object's storage a
dependency on A. Its retained fields can add dependencies. Aliasing an existing
value preserves its allocation and dependency facts without relocation.
Projecting a field follows the actual representation: returning an existing
outer reference can lose the inner container's dependency, while a view into
an inline field still requires the container's storage.

No implicit deep copy, promotion, or ownership transfer repairs an escape.
An explicit copy needs a separately admitted payload contract and recipient
storage. Shallow reference copying preserves dependencies. A base provider need
not support arbitrary deep copying of graphs, sharing, closures, or cycles.

Representation support must be declared. Refusing an unsupported explicit
region construction does not change existing ordinary construction. A later
claim of full ordinary-Ash compatibility must cover closures and recursive
data, rather than silently removing them or falling back to an unbounded heap.
Mathematical `Int` does not become a wrapping fixed-width value. Any selected
bounded encoding needs checked conversion and its own refusal behavior.

### Storage lifetime and value validity

The owners required by a value include the owner of storage needed to observe
it and every capability or stored reference actually needed by its use.
Access requires all those owners to remain valid. The fact that A's bytes are
live proves only A's storage contribution, not every captured dependency.

The reservation and local-initialization route can place a local immutable
closure in longer-lived storage A while it captures scoped cell R. Its usable
value remains confined to R; an ordinary outer allocation request carrying
the closure still rejects.
The closure requires both A and R. It cannot escape R merely because its own
record is in A. When R closes, no surviving source-accessible root may retain
that closure's R-dependent access. Inaccessible arena bytes are not an
additional access capability and do not keep R alive.

This permission requires the provider to preserve exact access provenance.
Region access alone cannot enumerate old object indices and republish a value
whose hidden dependencies have expired. Provider bookkeeping is not permission
to invoke stored closures or access expired fields. A provider unable to
establish these facts must reject this construction profile. Scanning arbitrary
objects for source destructors is not part of the base contract.

By contrast, putting that closure in an outer mutable cell is a retained-state
operation. The cell's payload is available for its owner's entire scope, so
every payload dependency must strictly outlive that owner under DN-0053.
Temporary younger storage followed by clearing the cell still rejects.
This separates a local immutable value's checked validity from publication into
a longer-lived mutable root.

### Owner dependencies and ordinary cycles

An owner dependency records authority or backing that must remain protected
until the dependent owner's consumption is established. Ending its source scope
alone does not discharge an outstanding edge. The initial model admits such
edges only to already established
enclosing owners. Edges point from dependent to longer-lived owner;
self-dependency and owner cycles reject. Capture/resume preserves this relation
through inactive periods rather than recomputing it from the currently visible
textual block. A retained disposition keeps the same edges after ordinary
source access has been revoked; it creates no new lifetime or cycle permission.

Consumption means the admitted disposition of the resource owner, not immediate
reclamation of every byte it used. Ordinary Cell close consumes its slot's
completion authority and drops the payload root even if an enclosing arena
retains the storage. For a foreign owner, only the recorded native disposition
establishes consumption; returning from source finish does not.

An allocation owned by A referring to another ordinary allocation in A is not
an owner-dependency edge from A to itself. Cyclic immutable graphs can therefore
remain valid. References and captured access add value dependencies; retaining
them in another owner's operational state requires that owner's stricter
outlives check. This distinction preserves DN-0035's ordinary cyclic data while
keeping the Cell restriction explicit.

A cell's logical owner R also remains distinct from a region A backing its
slot. Choosing A does not change R's closing point. A region object's pointer
to that slot cannot restore access after R closes.

### Initialization, failure, and accounting

Capacity, layout arithmetic, initialization, and complete reply preparation
precede publication. Partial construction remains privately owned, with no
readable access to uninitialized fields. Failure releases or accounts for
unpublished state without fabricating a new owner or damaging earlier objects.
Recursive construction may use checked uninitialized slots, but no unfinished
field may be observed and failure must revoke all unpublished access.

For a fixed arena, allocation refusal is a declared ordinary outcome. The
contract defines usable bytes, alignment padding, metadata and object limits;
refusal preserves previous references and published usage. Unsupported
representation, invalid construction, and internal checker/runtime exhaustion
remain distinguishable from that declared capacity outcome. This does not
change the terminal internal-capacity boundary retained by the Cell candidate.

Explicit allocation requests and exposed usage/failure observations constrain
optimization. Hoisting, eliminating, or fusing them requires preservation of
the selected observations. DN-0032's conditional scope laws do not authorize
unconditional scope movement.

Provider setup and failure delivery need an established storage foundation:
preallocated metadata, caller backing, or an already live enclosing provider.
They cannot recursively require the unestablished region without a base case.
Bounds must include backing, metadata, initialization scratch, closure records,
captured control, and cleanup state where promised. A payload bound alone is
not a bound on execution memory or reclamation work.

### Completion, control, and reclamation

Normal scope completion checks the body result and outward dependencies and
performs required inner completion and scheduled cleanup. Backing release is
permitted only when dependent consumption and the backing owner's disposition
authorize it. Successful consumption releases once; a completed source scope
does not by itself establish that consumption. Cleanup using A's storage runs
while A is live. Ordinary unreachable-data reclamation invokes no arbitrary
effectful source cleanup.

Composition with foreign owners preserves the existing
[ash-ffi retained-owner rules](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/dynamic-semantics.md#source-resource-execution-with-native-owners):

- A consumed dependent removes its existing edges once, including when source
  finish reports a consumed failure. That failure does not permit a second
  release or become successful completion.
- `RetainedError` preserves the same physical owner and dependency edges.
  The owner and transitive dependency closure remain quarantined, with ordinary
  source access revoked. Merely returning a completion report releases no edge.
- A retained dependent blocks a consuming enclosing call before native entry.
  `BlockedDependent` grants neither a fabricated disposition nor permission to
  free an enclosing region through another path. Only the already admitted
  completing operations may use protected dependencies under their exact rules.
- Separately admitted host destruction attempts dependents before enclosing
  owners. Successful consumption removes the same edges; retained destruction
  keeps them and blocks enclosing destruction. An incomplete attempt is terminal,
  is not retried, and protects unresolved objects until process termination.
  Host destruction runs no source finish or handler and cannot turn earlier
  failed source completion into success.

Physical protection beyond source scope exit grants no usable owner package,
region access, or extension of Cell R's scope. It cannot justify retaining
younger access in an outer cell or admitting resource dependency cycles. A
provider unable to preserve retained backing and dependency protection must
exclude retaining foreign composition from its admitted profile.

Capture moves the same owner, storage, and obligations into owned control;
resume restores them without acquisition or reinitialization. A textual boundary
crossed during capture is not a release event. Checked discard initiates closing
exactly its owned abandoned obligations in structural order and cannot skip
required outside or running completion. A witnessed retained foreign finish
keeps ash-ffi's terminal `runtime.resource-completion` behavior: no abandoned
body report is published and the discarding clause does not continue. Its
physical protection remains in force.
Consumed failures during owned discard keep their existing terminal behavior
as well; a failure report is not permission to repeat physical consumption.

The fixed arena supplies no individual free, compaction, resize invalidation,
or earlier reclamation guarantee. Repeated aliases do not duplicate release.
Region-local counting, tracing, and moving providers require additional root,
update, overflow, cycle, and failure contracts. They do not extend the owner
beyond its lexical resource lifetime. Internal termination and divergence keep
their existing limits on source cleanup and eventual release.

### Preservation of earlier boundaries

| Earlier rule | How this base proposal preserves it |
| --- | --- |
| Bindings do not relocate values. | Allocation is explicit; aliases preserve original storage. |
| Nearest applicable region is a proposed future default. | Initial explicit access settles the base call contract without selecting implicit elaboration. |
| Cell lifetime is its resource scope. | Backing-region lifetime and closure record placement grant no extension. |
| Cell resource dependency cycles reject. | Retained cell payloads require strictly older owners; ordinary graph cycles remain distinct. |
| Hidden captures cannot evade escape checking. | Values retain storage, access, evidence, and operation dependencies through calls and imports. |
| Younger-dependent operands cannot reach outer interpreters. | Reservation carries only independent requirements; checked local initialization keeps the payload under its required owners. |
| Source completion does not imply physical consumption. | Retained edges and quarantine block enclosing release until actual consumption; they grant no source lifetime extension. |
| One-shot control moves ownership. | Capture/resume preserves activations and ordered completion; it creates no exclusive borrow proof. |
| Ordinary values remain reusable. | Aliases share valid immutable data; resource owners remain separate obligations. |
| Native signatures do not establish memory safety. | Admitted representation, initialization, provenance, and access are separate checked obligations. |
| Current pure construction has no selectable allocation effect. | Its migration and observable failure contract require a separate proposal and lowering account. |

## Evidence and experiments

These are proposed requirements, not completed experiments or proofs:

| Case | Required positive observation | Nearby rejection or failure |
| --- | --- | --- |
| Explicit helper | A rank-1 helper allocates into its supplied region; aliases retain their original allocation. | A call silently changes the captured allocator or acquires a hidden region. |
| Nested construction | Inner storage can retain outer data; a projected outer reference can survive inner completion. | An inner aggregate or inline view escapes after its storage closes. |
| Local closure | Independent reservation followed by checked local initialization creates an A-backed closure requiring A and younger R, usable only inside R. | Sending the closure or R-dependent metadata to A's outer interpreter, escaping it, or restoring expired access rejects. |
| Pending construction | Capture/resume retains the exact reservation; abandonment accounts for unpublished storage before permitted backing release. | A forged reservation, mismatched initializer, partial readable object, or lost construction obligation is admitted. |
| Snapshot | A closure retaining an independent copied result can escape a cell. | A shallow copy of a region reference loses its backing dependency. |
| Graphs | Admitted immutable sharing and cycles preserve reference relationships. | A graph is accepted without its required initialization or representation support. |
| Owner ordering | A region, nested cell, and dependent cleanup complete in valid order. | Direct or indirect owner cycles, double release, or release before cleanup. |
| Retained dependent | A child returning `RetainedError` preserves its edges and quarantines transitive backing; enclosing teardown is blocked before native entry. | Source completion or `BlockedDependent` is treated as consumption and backing is freed. |
| Consumed failure and host destruction | Consumed failure removes edges once; host destruction follows dependency order without changing the source outcome. | Duplicate release, retry of incomplete destruction, source cleanup during host destruction, or lost protection after retention. |
| Fixed capacity | Exact fit succeeds; refused construction preserves earlier objects and accounting. | Partial readable publication, overflow, hidden backing fallback, or corruption. |
| Captured control | Resume preserves allocation identity; discard closes owned storage once. | Premature release or skipped outside/running completion. |
| Independent validation | Source summaries, Core copying/transforms, and runtime agree on regions and dependencies. | Same-shaped types, copied claims, or changed provenance grant storage authority. |

A later bounded study should compare explicit fixed-region allocation with the
ordinary managed-heap baseline on these cases, using the same results,
dependencies, failure and completion observations. The local-closure case must
exercise actual access provenance, not only a scalar result. Record payload and
metadata storage, copies, peak retention, work, and rejected useful programs.
Keep the existing scalar Arena receipt separate from new graph/closure evidence.

This note authorizes no prototype. A later assignment must select an admitted
representation fragment, trusted primitive boundary, exact comparisons, and
retention conditions. Retain coherent contracts and reproducible counterexamples;
discard machinery that weakens lifetime checks, hides fallback storage, or needs
per-library unchecked authority. Product adoption requires the proposal and task
workflow plus matching surface/Core semantics and evidence.

## Open questions

- Which retained construction and representation facts implement the reservation
  and local-initialization boundary with the least new machinery?
- How should independent validation retain value validity that can be shorter
  than its physical allocation, including through opaque public results?
- What explicit region API and effect-row spelling preserve useful inference
  without adding nested schemes or public capture annotations prematurely?
- Which initialization protocol supports the admitted recursive graph fragment
  with deterministic failure and bounded private construction work?
- Which application/entry ownership contract and construction lowering should
  later implement DN-0035's nearest-region default and DN-0044's supplied policy?
- Which concrete workloads justify temporary younger mutable dependencies,
  loans, earlier reclamation, or moving storage beyond this base?
