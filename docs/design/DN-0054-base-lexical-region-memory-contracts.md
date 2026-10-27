# DN-0054: Region Allocation and Lexical Ownership Contracts

- ID: `DN-0054`
- Status: exploring
- Related: [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md),
  [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0044](DN-0044-no-default-runtime.md),
  [DN-0053](DN-0053-scoped-generic-cells-without-native-owners.md),
  [DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md)

> This informative note separates placement/allocation from ownership,
> lifetimes and reclamation, and retains questions about broader compositions.
> The lexical base is described by the [specification](../../spec/README.md).
> Earlier candidate descriptions below explain the design boundary; they do not
> override current syntax/semantics or authorize another implementation,
> architecture or prototype. Nonlexical ownership, collection and transport
> remain exploratory.

## Question

What minimum placement and allocation contract can compose first with lexical
ownership, and later with other ownership schemes and reclamation policies?
How do those compositions establish value validity, sharing, closure capture,
publication, and completion without changing the resource-scope lifetime or
cycle restrictions of `Cell<R,T>`?

## Context

The completed slim FFI M1 was
[integrated into Main by PR #143](https://github.com/dikini/ash-lang/pull/143).
The lexical-region product adds selectable construction to the existing
[resource dependencies](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
and [execution rules](../../spec/dynamic-semantics.md#region-construction-and-close-steps).
Its [construction rules](../../spec/static-semantics.md#lexical-regions-and-construction-dependencies)
are the implemented baseline for the broader composition questions here;
mathematical integers, immutable sharing, recursive data and lexical closures
retain their specified contracts.
The [FFI boundary](../../spec/static-semantics.md#source-foreign-declarations)
aligns Bytes and opaque pointers; ordinary Ash binding modules express lifetime
interpretation and cleanup, while native behavior remains an assumption.

[DN-0035](DN-0035-region-memory-management-and-verified-providers.md) assigns
placement and allocation to regions, with ownership, lifetimes, and reclamation
as separate concepts composed with them. Lexical ownership comes first. M2
must supply default placement as well as explicit selection under the agreed
closest-live-context rule below.
[DN-0044](DN-0044-no-default-runtime.md) separates application policy selection,
state acquisition, construction lowering, and service requirements.
[DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) distinguishes
foreign ABI facts from library policy. Neither the slim FFI nor earlier
experiments implement this region base.

The [scalar Arena evidence](provider-experiments/arena-results.md) transfers
capacity, publication, activation, and completion cases. It establishes neither
general graph layouts nor borrowing. Partial wider experiments are not accepted
capabilities. The generic Cell candidate in
[DN-0053](DN-0053-scoped-generic-cells-without-native-owners.md) needs only valid
payload dependencies, not successful completion of all this region work.

[DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md) develops the
candidate algebra and proof obligations behind the placement, ownership,
lifetime, and reclamation relationships explored here.

## Agreed M2 delivery scope

[M2 #53](https://github.com/dikini/ash-lang/issues/53) includes default placement
for ordinary construction alongside explicit region selection, lexical
ownership, bulk reclamation, closures, and recursive immutable graphs. A
data-only or explicit-allocation-only product does not complete that scope.
Usage- or lifetime-based automatic placement inference is deferred as an
optimization; default placement itself is required.

The [specification](../../spec/README.md) defines the implemented lexical base;
the [bounded model evidence](lexical-regions/evidence.md) records the separate
matched R1/R2 proof scope. The earlier candidate requirements in this note are
informative design context, not pending M2 assignments or current language
rules. The broader algebra in DN-0055 remains separate exploration.

Construction, actual closure captures, ordinary graph cycles, projection,
failure, suspension, escape and refusal remain required cases. No new numeric
family, FFI policy framework, general allocator API or backend matrix is required.

### Approved allocator and storage direction

The complete conceptual interface is:

```text
RegionAllocator<R> {
    allocate : Request -> Storage<R>
    release : Unit -> Unit
}
```

Both members belong to the same implementation/state association fixed when R
is initialized. R's type and allocation/reclamation discipline remain fixed for
its lifetime; the owner controls release. An allocation-only effect may project
from this pair but is not the complete interface.

The default implementation uses host-backed storage. Fixed-capacity storage
uses the same ordinary effect interface, not a separate compiler policy.
One allocator may serve and outlive several regions: closing one logical region
does not destroy shared backing or invalidate another region. Rust heap storage
or an ordinary slim-FFI binding module can provide physical backing. Native
validity and cleanup guarantees remain assumptions of that module's contract,
not consequences of the region model or a restored quarantine protocol.

Allocation supplies actual storage for typed objects, owned buffers and closure
records. Merely charging a region while retaining those payloads on an unrelated
heap is insufficient. Reuse current typed representations and recursive slots
through a narrow internal construction boundary. Request carries independent
size/alignment requirements, not younger-dependent operands or captures; Ash
initializes the supplied storage locally and publishes readable access only
when initialization permits it. Address alone is not initialization or lifetime
proof.

A small private, nonrecursive Request representation and established host
startup/control machinery under existing limits supply the specified lexical
bootstrap. The [Core contract](../../spec/elaboration.md) defines its concrete
Request/Storage and supplied-storage boundary. Ordinary tuples or error constructors cannot be assumed
allocation-free; setup, refusal delivery and root observation need an established
storage foundation, without an untracked fallback destination.

## Constraints

- Keep region placement and allocation, ownership, lifetimes, reclamation,
  mutation, and completion authority distinct, with checked composition rules.
  Region ownership includes its allocated objects; their lifetimes cannot
  exceed the region's, and region reclamation reclaims all remaining objects
  together.
- Preserve the relation between region lifetime and object ownership: the
  region must remain valid for every permitted use of its objects. Neither
  earlier object reclamation nor whole-region reclamation may invalidate
  objects still required by admitted ownership or access. The first lexical
  scheme rejects escapes beyond the owning scope.
- Use lexical scope as the first ownership scheme: the enclosing scope owns
  the region and determines its lifetime. Keep owners nontransportable within
  this scheme; no package or reference count extends that lexical lifetime.
  Other ownership schemes need separate contracts rather than this restriction
  becoming part of the region definition.
- Reject cycles of resource ownership dependencies. Preserve ordinary sharing
  and cyclic immutable graphs within their checked validity.
- Keep `Cell<R,T>` access tied to R's resource scope. Its retained payload
  dependencies must strictly outlive R; longer backing lifetime alone
  cannot admit self-dependency, an owner cycle, or access after R closes.
- Preserve ash-ffi's request-payload boundary, including hidden captures and
  indexed operation metadata. Allocation introduces no exception for a request
  interpreted outside a required owner.
- Distinguish source scope completion from permitted backing release. Required
  ordinary dependencies and cleanup remain accounted for by the specified
  failure/completion rules, without a foreign-owner status protocol.
- Cover default placement and explicit selection at allocation-capable helper
  boundaries. Use the agreed caller-context contract below while preserving
  current rank-1
  restrictions and actual closure dependencies.
- Preserve the specified construction, effects, failure and entry-result
  contract; changing that base requires the proposal workflow.
- Keep checked operations and provider assumptions explicit. An interface
  implementation, numeric offset, or compatible type grants no memory authority.
- Begin sequentially with lexical ownership, immutable region objects,
  host-backed storage and bulk reclamation; fixed capacity is a model instance.
  Generic Cell supplies mediated mutable
  state. Region-specific collection is a separate reclamation composition;
  exclusive views, moving collection, other ownership schemes, and concurrency
  remain later comparisons.

## Candidate directions

### Roles and initial boundary

The base logical model distinguishes the following roles. Names such as
`Region<A>` describe roles, not selected source declarations:

| Role | Proposed responsibility |
| --- | --- |
| Region identity A | Relate allocation placement, storage, and dependencies, independently of the ownership scheme. |
| Region access | Reusable permission to request admitted allocations under the selected ownership and lifetime contract. |
| Ownership scheme | Determine who owns A and its objects, the region's lifetime, and associated completion authority. |
| Lifetime and validity rules | Preserve A for every permitted object use, bound object lifetimes by A's lifetime, and retain their other dependencies. |
| Region type and reclamation policy | A region type may specify earlier object reclamation through counting, tracing, or another policy. Region reclamation reclaims every remaining object together, after required completion. |
| Provider contract | State admitted representations, capacity units, initialization and allocation outcomes, and obligations required by the selected composition. |
| Allocation record | Identify an initialized object and its extent, representation, and access provenance; allocation access alone grants no ownership of A. |
| Value dependency facts | Retain required storage validity and capability owners for the particular value. |
| Completion obligations | Identify cleanup that must run before backing storage is released. |

M2 covers default placement of ordinary construction and explicit region
selection under the [specified lowering](../../spec/elaboration.md). Storage can
come from foreign allocation, caller backing,
static backing, or another admitted primitive. No native owner, resource
declaration, or runtime acquisition is intrinsic to the region contract.

This is a staged refinement of DN-0035 under the agreed default-selection
direction below. The specification owns the exact source and Core presentation.
One managed ordinary heap and individually owned storage remain comparison
alternatives with the tradeoffs recorded there.

### First ownership scheme: lexical scope

In the first composition, the enclosing scope owns region A and its allocated
objects and determines the region's lifetime. Resource machinery can establish
the associated ownership and completion obligations. This scope may manage
many allocations; allocating a value does not automatically create another
resource owner. Immutable objects
and mutable cells retain their own access and dependency rules.

The bounded model covers host/module-backed storage with bulk reclamation
at owner completion; fixed capacity is a concrete instance. Static selection fixes these policies; capacity and
success can still depend on execution. The scope's acquisition evaluates its
configuration in the preceding scope, then publishes a fresh activation and
region access only on success. Refusal enters no body and publishes no partial
owner. Required backing release is established before access is published.
The composition states its acquisition and body-result report contract; there
is no universal implicit outcome flattening.

The lexical scheme governs the owner dependencies and completion cases below.
Their nontransportable ownership rules do not define every possible region.
Using caller or static backing still requires the scheme to establish who owns
the region and its lifetime; it need not allocate or free that backing at each
scope entry and exit.

### Separate reclamation compositions

Each region type may specify its own object reclamation policy. The initial
arena type retains allocations until bulk release. Counted or traced region
types could offer earlier reclamation under their own contracts. Keeping
reclamation separate from placement, allocation, ownership, and lifetimes does
not require it to be selected independently of the region type.

All of these policies leave object lifetimes bounded by the region's lifetime.
Reclaiming the region reclaims every remaining object en masse, including
objects not reclaimed earlier. References to objects in another region do not
transfer their ownership or include them in this reclamation.

Earlier reclamation must preserve objects still required by valid ownership or
access. A collection policy must establish their liveness; an enclosing lexical
scope alone is not a substitute for tracing or reference accounting. Region
reclamation must also wait until admitted object uses and required completion
no longer need the storage. The lexical ownership scheme enforces this through
escape and dependency checks, rather than silently extending the region or
shortening a required object lifetime.

A region-specific collector could reclaim unreachable objects while the region
remains live and accepts allocations. Its reclamation contract must account
for roots, references from other regions, closures, and captured control; moving
collection also needs an update contract for every retained reference. Merely
remaining inside the owning scope does not establish that every allocation is
live or that a reference is a registered root.

Lexical ownership could still determine that region's owner and lifetime while
collection determines individual object reclamation. Other ownership schemes
need their own rules for region lifetime and completion. Neither collection nor
physical retention silently extends the scoped Cell candidate's access.
These are future compositions, not capabilities established by the fixed-arena
comparison or current scalar Arena evidence.

### Agreed placement, calls and effects

New ordinary construction uses the closest declared live allocation context.
The entry wrapper establishes a configured host-backed root, using default
parameters when none are supplied, and retains it through result observation
and required completion. Ordinary blocks and calls acquire no region. Calls
pass the caller's selected context for fresh construction. Explicit selection
of admitted live or captured region access scopes that computation and its
helpers, then restores the preceding context; it does not acquire another owner.
Existing values and aliases never move or promote implicitly.

Closure creation places its record in the creation context and retains actual
dependencies. Invocation receives the caller's context for fresh allocations;
explicit requests to a captured R still target that exact R. This does not make
stored callables higher-rank or change existing rank-1 restrictions. Capture and
resume preserve the selected context and owners rather than selecting the
resumer's current default.

Allocation is an ordinary effect tied to the selected region through existing
parametricity and handlers. Purity-compatible defaults, including allocation,
may be omitted in surface rows: `Int -> Pair ! {}` includes those defaults;
`Int -> Pair ! {Console}` includes them plus Console. Additional observable
allocator effects remain visible in source contracts and expanded rows. The
complete implicit-default expansion is specified; this note selects no additional
implicit effects. Broader inference of omitted definition rows remains outside
the lexical base, apart from the specified default expansion.

Core contains no implicits: elaboration retains expanded effect rows, selected
region/allocator arguments or bindings, request targets and handler/cleanup
relationships explicitly. The [specified realization](../../spec/elaboration.md)
uses explicit monomorphic default forwarding and the complete allocator pair;
it is not an ambient object. `StorageView` retains actual residency/lifetime
dependencies, rather than erasing them as an Address cast. The
[source grammar](../../spec/syntax.md) owns the region/provider and selection
forms; this note selects no alternative current syntax, layout or bootstrap.

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
[current request-payload rule](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies),
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
descriptors cannot manufacture this permission. The specified construction
boundary is distinct from permission supplied by the pointer/Bytes FFI mapping.

Any pending reservation belongs to that construction's completion obligation
before fallible reply handling. Capture/resume preserves the same obligation;
abandonment must cancel or account for it without publishing readable access,
corrupting other allocations, or bypassing required ordinary dependencies. Independent
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

Representation support must be declared. M2's ordinary-construction coverage
includes closures and recursive immutable graphs, subject to valid captures,
initialization and dependencies. That product scope is not a later fragment
and permits no hidden unbounded heap fallback.
Mathematical `Int` does not become a wrapping fixed-width value. Any selected
bounded encoding needs checked conversion and its own refusal behavior.

### Storage lifetime and value validity

Value validity combines the region's storage and reclamation guarantees with
every capability or stored reference actually needed by use. Under the initial
lexical scheme, required owners must remain valid. A collector would also need
to preserve the allocation through its rooting contract. The fact that
A's backing bytes are live proves only its storage contribution, not every
captured dependency or an individual allocation's continued validity.

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

Under the lexical ownership scheme, an owner dependency records authority or
backing that must remain protected until the dependent owner's consumption is
established. Ending its source scope alone does not discharge an outstanding
edge. The initial model admits such edges only to already established enclosing
owners. Edges point from dependent to longer-lived owner;
self-dependency and owner cycles reject. Capture/resume preserves this relation
through inactive periods rather than recomputing it from the currently visible
textual block. Pending ordinary completion must retain required dependencies;
it creates no new lifetime or cycle permission.

Consumption means the admitted disposition of the resource owner, not immediate
reclamation of every byte it used. Ordinary Cell close consumes its slot's
completion authority and drops the payload root even if an enclosing arena
retains the storage. An opaque Address or native reply proves no ownership,
validity or completion. Foreign cleanup and lifetime interpretation belong to
ordinary Ash binding contracts, with native behavior assumed rather than
proved by the region model.

An ordinary allocation in region A referring to another ordinary allocation in
A is not a resource-owner dependency on itself. Cyclic immutable graphs can
therefore remain valid. References and captured access add value dependencies;
retaining them in another owner's operational state requires that owner's
stricter outlives check. This distinction preserves DN-0035's ordinary cyclic
data while keeping the Cell restriction explicit.

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

Allocation success and refusal use the same ordinary effect contract. A request
captures evaluated operands and pending construction once. Success resumes
that state once with valid selected storage; there is no operand replay.
Refusal uses checked discard and the handler's ordinary result only where
current rules admit discard. It does not resume refusal as Storage, add a
per-constructor result wrapper, roll back earlier effects, retry, or fall back
to another destination. Internal checker/runtime exhaustion remains the
existing terminal boundary, distinct from declared allocation refusal.

Recursive construction preserves current guarded slots, function templates,
member aliases and source-order initializers. Suspension retains completed
members, pending slots and the next initializer. Unfinished access cannot be
forced or transported. Checked abandonment accounts for or revokes unpublished
state without a new whole-group transaction or same-region-only restriction.

During running cleanup, an inner safe handler may discard only a local
computation and let the action finish; an outer handler cannot abandon that
running action or an unfinished close. Closing preserves the captured
allocation context and restoration frames. After inner frames unwind, cleanup
uses the closing computation's context; successful discard restores the clause
context. A saved release action captures provider function/state, not handlers:
it must use surviving or action-local interpretations, never replace a removed
nearest interpreter with an outer same-instance one. Preserve the current
`effect.cleanup-context` boundary.

For fixed capacity, the contract states usable bytes, padding, metadata and
object limits. Refusal preserves previous references and published usage.

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

### Lexical completion, control, and bulk reclamation

In the first ownership scheme, the owning scope determines the region's
lifetime. Before ending source access, normal completion checks the body result
and outward dependencies and performs required inner completion and scheduled
cleanup while A is live. Backing release must respect
required ordinary dependencies and completion. Reclaiming the region releases
all remaining objects together, once permitted; the
[execution rules](../../spec/dynamic-semantics.md#region-construction-and-close-steps)
define normal, failure and partial-construction transitions. Ordinary unreachable-data
reclamation invokes no arbitrary effectful source cleanup.

Composition with native calls uses the current slim FFI boundary and ordinary
Ash handlers and scoped cleanup. It does not restore compiler-owned foreign
quarantine, retained/consumed status reports, blocked-dependent native entry
or host-destruction rules. A region proof cannot establish native memory
validity or a library's cleanup behavior from its signature. The contract keeps
those assumptions explicit while preserving required Ash-owned dependencies.

Capture moves the same owner, storage, and obligations into owned control;
resume restores them without acquisition or reinitialization. A textual boundary
crossed during capture is not a release event. Checked discard completes its
owned abandoned obligations in structural order and cannot skip required
outside or running completion. The specified construction and cleanup failure
rules preserve that boundary; no retired foreign completion codec is required.

The fixed-arena composition supplies no individual free, compaction, resize
invalidation, or earlier reclamation guarantee. Repeated aliases do not
duplicate release. Region-specific counting, tracing, and moving collection
require separate root, update, overflow, cycle, and failure contracts. Composing
them with lexical ownership preserves its region lifetime; choosing another
ownership scheme needs a separate account. Internal termination and divergence
keep their existing limits on source cleanup and eventual release.

### Preservation of earlier boundaries

| Earlier rule | How this base proposal preserves it |
| --- | --- |
| Regions provide placement and allocation. | Ownership determines the region owner and lifetime; reclamation and access rules compose separately. |
| Lexical scope is the first ownership scheme. | Its resource and completion rules govern the initial arena comparison without defining all regions. |
| Bindings do not relocate values. | Default placement and explicit selection concern construction; aliases preserve original storage. |
| M2 includes default placement and explicit selection. | Closest declared live context and caller selection govern new construction; usage/lifetime inference remains a later optimization. |
| Cell lifetime is its resource scope. | Backing-region lifetime and closure record placement grant no extension. |
| Cell resource dependency cycles reject. | Retained cell payloads require strictly older owners; ordinary graph cycles remain distinct. |
| Hidden captures cannot evade escape checking. | Values retain storage, access, evidence, and operation dependencies through calls and imports. |
| Younger-dependent operands cannot reach outer interpreters. | Reservation carries only independent requirements; checked local initialization keeps the payload under its required owners. |
| Completion and backing release are distinct obligations. | Required ordinary dependencies and cleanup remain accounted for; no source lifetime extension or foreign quarantine protocol follows. |
| One-shot control moves ownership. | Capture/resume preserves activations and ordered completion; it creates no exclusive borrow proof. |
| Ordinary values remain reusable. | Aliases share valid immutable data; resource owners remain separate obligations. |
| Native signatures do not establish memory safety. | Admitted representation, initialization, provenance, and access are separate checked obligations. |
| Source construction carries explicit allocation requirements in Core. | The current specification governs default expansion, placement, failure and entry observation; further variations need their own transition contract. |

## Evidence and experiments

This table records comparison requirements and nearby failure modes. The
specification and [R5 evidence](https://github.com/dikini/ash-lang/issues/70) own
the implemented lexical cases; wider composition cases remain exploratory and
are not completed proofs merely because the lexical product is retained:

| Case | Required positive observation | Nearby rejection or failure |
| --- | --- | --- |
| Default placement | Ordinary construction, including closures and recursive immutable graphs, receives placement under the agreed default direction and accepted R2 contract. | Validity changes silently, a data-only subset is substituted, or placement inference is required to obtain a default. |
| Explicit helper | A rank-1 helper allocates into its supplied region; aliases retain their original allocation. | A call silently changes the captured allocator or acquires a hidden region. |
| Nested construction | Inner storage can retain outer data; a projected outer reference can survive inner completion. | An inner aggregate or inline view escapes after its storage closes. |
| Local closure | Independent reservation followed by checked local initialization creates an A-backed closure requiring A and younger R, usable only inside R. | Sending the closure or R-dependent metadata to A's outer interpreter, escaping it, or restoring expired access rejects. |
| Pending construction | Capture/resume retains the exact reservation; abandonment accounts for unpublished storage before permitted backing release. | A forged reservation, mismatched initializer, partial readable object, or lost construction obligation is admitted. |
| Snapshot | A closure retaining an independent copied result can escape a cell. | A shallow copy of a region reference loses its backing dependency. |
| Graphs | Admitted immutable sharing and cycles preserve reference relationships. | A graph is accepted without its required initialization or representation support. |
| Owner ordering | A region, nested cell, and dependent cleanup complete in valid order. | Direct or indirect owner cycles, double release, or release before cleanup. |
| Failure and completion | The accepted R2 failure rules account for unpublished construction, required dependencies and cleanup before permitted bulk release. | Partial publication, duplicate release, lost cleanup, or backing release invalidates admitted uses. |
| Ordinary native binding | Ash handlers and cleanup express the library contract under explicit native assumptions. | An Address or native reply is treated as ownership, memory-validity or completion proof. |
| Fixed capacity | Exact fit succeeds; refused construction preserves earlier objects and accounting. | Partial readable publication, overflow, hidden backing fallback, or corruption. |
| Captured control | Resume preserves allocation identity; discard closes owned storage once. | Premature release or skipped outside/running completion. |
| Independent validation | Source summaries, Core copying/transforms, and runtime agree on regions and dependencies. | Same-shaped types, copied claims, or changed provenance grant storage authority. |
| Separate placement and management | One region holds immutable objects and mutable cells under lexical ownership without changing their access rules. | Placement alone grants mutation, owner completion, or a longer cell lifetime. |
| Region type policy | Each compared region type states its object reclamation policy separately from the lexical scheme that determines its owner and lifetime. | Type selection silently changes ownership or a collector's guarantees are attributed to the fixed arena. |
| Whole-region reclamation | The region owner owns the allocated objects; permitted region reclamation releases all remaining objects together. | Object access survives region reclamation, required completion is skipped, or a referenced object from another region is reclaimed. |
| Ownership and lifetime preservation | The region remains valid for every owned object's admitted uses; lexical escape checks and reclamation rules preserve this relation. | Region or object reclamation invalidates a use still permitted by ownership or access. |

The bounded M2 comparison must cover default placement and explicit fixed-region
selection against the ordinary managed-heap baseline on these cases, stating each one's ownership,
lifetime, and reclamation contract and using the same results,
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

- Which minimum region allocation facts can be reused by other ownership and
  reclamation schemes after the first lexical composition?
- How should a region-specific collector expose rooting and cross-region
  references while keeping region lifetime distinct from object reclamation?
- Which retained construction and representation facts implement the reservation
  and local-initialization boundary with the least new machinery?
- How should independent validation retain value validity that can be shorter
  than its physical allocation, including through opaque public results?
- Which concrete workloads justify temporary younger mutable dependencies,
  loans, earlier reclamation, or moving storage beyond this base?
