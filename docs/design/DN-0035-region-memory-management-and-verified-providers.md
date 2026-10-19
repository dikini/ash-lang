# DN-0035: Region Memory Management and Verified Providers

- ID: `DN-0035`
- Status: exploring
- Related: [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md), [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md), [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md), [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md), [DN-0031: Resource Composition Concept Map](DN-0031-resource-composition-concept-map.md), [DN-0032: Algebra of Scoped Resource Composition](DN-0032-algebra-of-scoped-resource-composition.md), [DN-0033: Direct Effects and Continuation Capabilities](DN-0033-direct-effects-and-continuation-capabilities.md), [DN-0034: Verification Foundation for Ash Semantics and Implementation](DN-0034-one-shot-kernel-soundness-and-practicality.md), [DN-0054](DN-0054-base-lexical-region-memory-contracts.md)

> This design note is informative. It consolidates a proposed memory-management
> direction and its reference cases. It does not define current Ash, accept an
> architecture, select a default allocator, or authorize implementation. Region
> interfaces, provider verification, borrowing, and processes remain design work.

## Question

Can regions provide placement and allocation while composing with separate
ownership, lifetime, and reclamation contracts? Can verified library providers
support static storage, arenas, reference counting, tracing, and individually
released objects while preserving ordinary immutable sharing and making each
composition's guarantees and costs explicit?

The design direction assigns placement and allocation to regions. Ownership,
lifetimes, reclamation, and mutation remain separate concepts whose contracts
must compose with the selected storage. Lexical scope is the first ownership
scheme to explore, among other possible schemes. In that scheme the enclosing
scope owns the region and determines its lifetime; resource machinery can
enforce the associated backing and completion obligations.

Ownership of a region includes ownership of the objects allocated in it.
Reclaiming the region reclaims all remaining objects together; their lifetimes
cannot exceed the region's lifetime. The ownership scheme must preserve each
object's required lifetime: its region
must remain live for every valid use. Reclamation cannot invalidate objects
still required by admitted ownership or access.

Each region type may specify its own object reclamation policy. Region-specific
garbage collection is one such policy, requiring its own liveness and
reclamation rules. This policy can reclaim individual objects earlier; it does
not determine the region's owner or extend its lifetime. Nearest applicable
region selection remains a possible future default for ordinary construction.

[DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md) develops a
candidate algebra for these relationships, with lifetime containment,
ownership contexts, reclamation obligations, and a bounded preservation target.

This note concerns memory management. Compiler backends, intermediate
representations, and code generation are outside its scope.

## Context

### Current semantic foundation

The [dynamic semantics](../../spec/dynamic-semantics.md) define one evaluation
heap containing ordinary tuples, constructors, recursive slots, and aliases.
Successful observation retains that heap with the result. Ordinary values are
duplicable subject to existing resource dependency rules. Cyclic immutable data
and lexical closures are supported; a storage policy must not silently remove
those behaviors from ordinary code.

[Bindings](../../spec/dynamic-semantics.md#bindings) evaluate an initializer and
extend the lexical environment. [Construction](../../spec/dynamic-semantics.md#tuples-constructors-and-matches)
allocates ordinary data. Binding an existing value is not specified as copying
or relocating its represented data. A binding scope and a storage lifetime are
therefore already distinct concepts. The ordinary lambda-calculus discipline
of binding and application does not require physical stack allocation.

[Scoped resources](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
separate duplicable, non-owning access handles from scope-owned release
obligations. Inferred dependencies follow handles, aggregate contents, closure
captures, selected methods, and operation metadata. A result cannot retain a
dependency on a closing owner merely because its exposed type omits the identity.
Requests cannot export that dependency to an interpreter outside the owner.

[Resource execution](../../spec/dynamic-semantics.md#scoped-cell-execution)
creates a fresh activation on each successful acquisition. Capture and resume
move ownership; they do not duplicate it. Checked discard closes the owned
abandoned scopes. [Cleanup](../../spec/dynamic-semantics.md#scoped-cleanup-actions)
preserves required invocation and structural completion order. Internal
termination does not promise source cleanup, and divergence does not promise
eventual release.

The current providers are sealed builtin relations for cells and native buffers.
They do not establish general region storage, library-defined acquisition,
individual ownership transfer, or borrowing. Ordinary allocation is not a
source-selectable region effect. These gaps are semantic work, not facilities
already supplied by an interface declaration.

### Transferable exploration

[DN-0017](DN-0017-resource-management-and-storage-policy.md) motivates plural
storage policies, efficient persistent sharing, optional runtime services, and
explicit transfer and copying. This note separates placement and allocation
from the policies composed with them. The initial comparison uses lexical
ownership and statically selected policies.

[DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md) separates usage,
alias authority, and completion. [DN-0018](DN-0018-runtime-established-static-evidence.md)
explores checked relationships such as disjoint mutable views. Neither accepts
a general borrow system.

[DN-0031](DN-0031-resource-composition-concept-map.md) distinguishes proposed
providers and resource provisions from current sealed evidence. [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md)
separates reusable bindings from restricted obligations and gives conditional
scope-composition laws. Its bounded derivations do not prove a general memory
model; observable allocation failure and cleanup constrain scope movement.

[DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md) supplies
pressure from captured control and owned completion. [DN-0034](DN-0034-one-shot-kernel-soundness-and-practicality.md)
distinguishes semantic safety, implementation correspondence, and intended
observations. Existing proofs do not verify the memory providers proposed here.
Older notes' descriptions of their then-current language are not current
authority; the specification supplies that boundary.

## Constraints

- Keep region placement and allocation separate from ownership, lifetimes,
  reclamation, and mutation. A composition must state how their contracts fit:
  region ownership covers its objects, and region reclamation reclaims every
  remaining object together.
- Select and check the initial composition's policies statically. A runtime
  activation supplies fresh state, not a new policy. Dynamic policy replacement
  is outside the initial comparison.
- Begin with lexical scope as the ownership scheme. Its nontransportable owners
  and nested lifetimes constrain that composition, not every possible region.
- Explore explicit nested allocation contexts. Nearest-region selection for
  ordinary construction remains a proposed convenience; aliasing an existing
  value preserves its allocation and dependencies.
- Preserve ordinary immutable sharing, persistent structures, and closure use.
  Restrictions follow storage dependencies and authority, not allocation alone.
- Keep lexical name scope, storage lifetime, access authority, and resource
  completion distinct. Heap storage does not imply mutation or individual release.
- Use existing identity, dependency, effect, and completion mechanisms where
  their established guarantees suffice. Identify additional rules explicitly.
- Require memory safety from every admitted provider. State stronger guarantees
  separately, including reclamation timing, capacity, failure, and operation cost.
- Permit programs to select only the memory services they need. A fixed-storage
  policy must not depend silently on an unbounded auxiliary heap or collector.
- Begin with sequential execution. Later processes initially share no storage;
  parallel sharing, owner transport, and cancellation are outside the initial
  lexical ownership comparison.
- Do not equate safe access with eventual release, termination, or bounded work.

## Candidate directions

### Working direction: regions for placement and allocation

A region determines where new storage is placed and how allocations obtain
space. Its allocation contract states admitted representations, size and
alignment requirements, capacity, initialization, and failure behavior. A region
may use several blocks, pools, or individually managed allocations; its identity
is not a physical address or one contiguous block.

An ownership scheme determines who owns a region and thereby its allocated
objects, and sets the region's lifetime. Object lifetimes are bounded by that
lifetime. Value validity also accounts for earlier object reclamation and any
other dependencies needed by access. Reclamation determines when storage
becomes reusable. These concepts can
overlap in a selected composition, but placement alone establishes none of their
policies. Immutable values and mutable cells can use the same region without
acquiring the same access rules.

Reclaiming the region reclaims its remaining objects en masse after required
completion. This covers objects allocated there, not objects in another region
merely referenced by them. Such references preserve their original placement
and dependencies.

This lifetime bound is also a preservation obligation. The region must remain
valid for every use permitted by an object's ownership and access contracts.
Neither earlier collection nor whole-region reclamation may invalidate an
object still required by those contracts. Under the first lexical scheme,
objects cannot retain valid access beyond the owning scope; escape checking
rejects that use. Other ownership schemes must establish the same storage
validity relationship under their own region lifetime rules. Selecting a
placement or reclamation policy cannot silently shorten an owned object's
required lifetime.

The proposed roles are:

| Role | Responsibility |
| --- | --- |
| Region identity | Relate allocation placement, storage, and dependencies without itself conferring ownership. |
| Region allocation access | Permit allocation into the selected storage under its checked contract. |
| Region type and provider | State and realize placement, allocation, initialization, and failure guarantees, with an object reclamation policy where specified. |
| Ownership scheme | Determine who owns the region and its objects, the region's lifetime, and associated completion authority; lexical scope is the first scheme. |
| Lifetime rules | Keep the region live for every permitted object use, bound object lifetimes by its lifetime, and preserve other dependencies. |
| Reclamation policy | Determine earlier object reclamation; reclaiming the region reclaims all remaining objects together. |
| Resource scope and handler | Supply ownership, completion, and request interpretation where the chosen composition uses them. |
| Client checking | Establish valid access, usage, dependencies, and completion. |

An owned arena initially composes a region with a lexical scope that owns it
and sets its lifetime, plus bulk reclamation. Caller-supplied backing can depend
on an existing owner; static backing may require no runtime acquisition or
deallocation. Other ownership schemes remain open. Region-specific counting or
tracing adds reclamation contracts, including how roots preserve live
allocations while the region continues accepting allocations.

Reuse resource rules for the ownership and completion they actually establish.
Placement, construction, and memory access still need their own checked
contracts. The experiment must identify those boundaries rather than assume
that a resource declaration supplies a complete memory model.

A handler's signatures do not prove its implementation safe. Intercepting a
request does not grant authority to manufacture references, reclaim storage, or
close an owner. The relation between source overrides and verified storage
interpretations needs a contract, preserving the current distinction between
interpretation and resource authority.

### Default allocation and nested lifetimes

One proposed convenience lets ordinary code use a default region without
naming an allocator at every construction. An explicit allocation context could
select another region. This selects placement; the composed ownership and
lifetime contracts determine how long its values remain usable. The default
policy and the validity of entry results remain open.

An ordinary binding or function call does not automatically acquire a region.
The following scoped-arena scenario uses lexical ownership and bulk release;
it is not proposed Ash syntax or a universal region lifecycle:

```text
acquire arena backing for region A
    construct x                  -- storage defaults to A
    acquire arena backing for region B
        bind y to x              -- no relocation of x
        construct tuple (x, y)   -- new tuple storage defaults to B
    complete B's backing owner
complete A's backing owner
```

Region B may contain references to A. In this composition, surviving state must
not retain access to B's reclaimed storage. Returning an outer value projected
from an inner aggregate can be safe even when returning the aggregate itself
is unsafe.
Dependencies follow retained contents and actual use, including hidden captures.

Reference copying preserves the original dependency. Construction or explicit
data copying into another region can produce an independent result. No implicit
deep-copy or promotion rule is assumed. Temporary references from longer-lived
mutable storage into a shorter-lived region require proof that they are removed
before completion; whether initial checking admits them remains open.

The allocation context across function calls needs a specified rule: a caller
may supply the applicable region, or a callable may retain a lexical allocation
context. Either choice must account for its dependencies. The nearest-region
default alone does not settle this boundary, especially for callbacks and
returned closures. Existing values retain their original storage in either case.

Allocation-dependent failure and accounting may be observable. The design must
specify how implicit construction relates to effect rows and generic provider
requirements without silently changing current pure-program behavior.

### Reusable values, heap storage, and restricted authority

Immutable region-backed values can have many aliases within a valid lifetime.
They need not each carry a unique release obligation. A binding can disappear
while another binding or closure retains the same allocation. The composed
ownership, lifetime, and reclamation contracts determine whether that allocation
remains until bulk release or becomes reclaimable earlier.

This separates the ordinary discipline of reusable values from resource owners.
A handle may be reusable without being an owner. A tuple or closure containing
authority does not erase its restrictions; an immutable outer representation
does not establish immutable reachable state.

Rust-like ownership is a candidate access discipline, not the definition of
region storage. It would add moves, shared borrows, exclusive mutable borrows,
and restrictions inherited through fields and captures. A move transfers
authority; a shared borrow excludes incompatible mutation; an exclusive borrow
restricts other access for its duration. The first comparison can use lexical
borrow scopes before introducing more precise endpoints or field-level places.

Freezing ends unique mutation authority and enables immutable sharing. It does
not choose between arena, counted, or traced storage. Current duplicable mutable
cell access remains current semantics, not an example of verified exclusivity.

### Ownership and reclamation compositions

Different region types may specify different object reclamation policies as
part of their contracts. An arena type can retain objects until bulk release;
a counted type can reclaim objects as counts permit; a traced type can reclaim
unreachable objects while the region remains live. Reclamation is a separate
concept even when its policy is fixed by the selected region type. The type's
contract must state that policy's guarantees and obligations without making it
the region's ownership scheme or lifetime. Every such type still reclaims its
remaining objects together when the region is reclaimed.

Policy selection is fixed statically, while capacity, allocation success,
reference counts, and reachability may depend on execution. Static selection
does not require every runtime outcome to be known in advance.

| Composition | Candidate contract |
| --- | --- |
| Static storage | Known storage layout and bounded initialization; no subsequent allocation where promised. |
| Fixed arena | Allocation within a fixed budget; bulk reclamation when the selected backing owner releases it. |
| Growable arena | Allocation from acquired blocks; bulk reclamation and stated acquisition failure. |
| Region-local reference counting | Accounted sharing and earlier reclamation where counts permit. |
| Region-local tracing | Retain reachable objects and reclaim unreachable storage within the region. |
| Individual early release | Per-object release authority remains bounded by region ownership; region reclamation releases every remaining object. |

Distinguish releasing a reference, reclaiming an allocation, and completing an
owner. An arena need not offer individual release. Under the initial lexical
scheme, completing the resource owner can authorize backing release; allocation
access alone grants no such authority. A static region need not have a runtime
completion operation. Composing a collector with a region can reclaim individual
allocations while its backing remains available.

Counted storage must define duplication and release accounting, count overflow,
and cycle behavior. Cycles may remain until region completion or use a declared
cycle policy. Counting references does not extend a lexical owner's scope.
Any different ownership scheme needs its own lifetime and completion contract.

Tracing requires a complete account of roots and references, including closures,
captured control, and references held by nested regions. A moving provider also
needs a valid reference-update contract. Neither follows merely from lexical
lifetime checking. The initial model need not require moving collection.

An arena's safety contract can permit cyclic ordinary data without tracing:
bulk reclamation does not depend on discovering unreachable objects. Long-lived
regions may select earlier reclamation to bound retention during execution.

### Effects and required completion

In the initial lexical composition, a request may capture the resource owner
backing a region without completing it. Resume preserves that activation and
storage; checked discard closes the owned abandoned obligations after required
dependent completion. A textual block boundary is not a release event during
capture. Other ownership schemes must specify their control relationships.

Borrowing must account for authority retained in captured control. A handler
must not exercise conflicting access while a suspended computation owns an
exclusive borrow. One-shot resumption prevents continuation duplication, not
all alias conflicts.

Bulk release must follow cleanup that uses the region's storage. Ordinary
unreachable-data reclamation does not implicitly invoke arbitrary effectful
source cleanup. Owned values with individual destruction require explicit
completion contracts, including order and effects. Resource completion does not
promise success under divergence, internal exhaustion, or external termination.

Fallible acquisition must publish neither partial values nor unearned owners.
The provider must distinguish its declared allocation failure from internal
execution failure. Current native-buffer behavior is a bounded precedent, not
an automatically inherited failure protocol for every future provider.

### Verified provider contracts

The proposed verification obligation is compositional:

> Given a region composed with stated ownership, lifetime, and reclamation
> contracts, and clients satisfying their premises, allocation and management
> operations preserve valid storage, admitted authority, and required
> completion.

Client checking establishes those premises. Provider verification establishes
their preservation by allocation, access, reclamation, and closing. Composition
must establish that nested providers and handlers preserve the same obligations.

All admitted providers require memory safety. Additional verified claims can
include bounded bytes, bounded operation work, no collection pauses, early
reclamation, explicit copying costs, and recoverable allocation failure. Safe
reclamation, prompt reclamation, and bounded reclamation work are separate claims.

Generic clients request capabilities and guarantees rather than implementation
details. Ordinary immutable sharing should not require knowledge of whether
storage is counted or traced. Individual release and exclusive access may require
additional capabilities. Providers need not pretend to offer identical costs.

A proof of an abstract algorithm must connect to the actual implementation and
its storage primitives. Assumed foreign behavior, tested behavior, and proved
correspondence must remain distinguishable. Source proof syntax, evidence
admission, and the trusted primitive boundary remain open; current interface
evidence is not proof of arbitrary provider laws.

### Alternatives for comparison

Compare the working direction with two simpler baselines:

- One managed discipline for ordinary values, with explicit regions only for
  specialized library values. This reduces changes to ordinary construction but
  may prevent programs from omitting unwanted memory services.
- Per-object ownership as the baseline, with explicit regions for shared or
  cyclic data. This alternative allocation model grants no permission for an
  object allocated in a region to outlive that region.

Compare the same programs, rejection behavior, annotations, and costs. Do not
select the working direction solely because the resource vocabulary fits it.

### Later process ownership

One later composition could give processes ownership of backing storage for
their regions. The initial process comparison shares no storage. Message
transport must establish receiver-owned data; ordinary cross-process references
are not admitted. Copying and any later ownership transfer require explicit
contracts and costs.

Process suspension would retain its region, and process completion would close
its obligations before release. Scheduler ownership, mailbox destruction, and
termination require further semantics. This note does not claim current Ash
supports escaping suspension or processes, and does not require parallel sharing
to settle the sequential model.

## Evidence and experiments

### Reference corpus

Every case needs positive and contrary variants, declared provider assumptions,
and observations of safety, admission, retained storage, and cost. Static and
fixed-capacity cases pressure constrained-system use; they do not by themselves
establish support for an embedded target.

| ID | Reference case | Required observation | Contrary observation |
| --- | --- | --- | --- |
| MM-01 | Static immutable configuration graph | Known placement and initialization; no mandatory runtime backing acquisition or release. | Access silently needs a general heap, collector, or unnecessary resource acquisition. |
| MM-02 | Fixed-capacity region | Capacity and alignment respected; completion permits backing-storage reuse. | Silent fallback, overlapping live allocations, or invalid reuse. |
| MM-03 | Repeated scratch regions | Peak storage bounded across repeated iterations. | Retention grows with completed iterations. |
| MM-04 | Exact-capacity failure | Sufficient capacity succeeds; failure preserves live values and follows the declared contract. | Partial value or authority publication, corruption, or hidden retry. |
| MM-05 | Nearest allocation and aliases | Construction uses the nearest region; binding outer data in an inner scope does not relocate it. | Hidden copying or lost storage dependencies. |
| MM-06 | Nested-region return | Outer-value projection and independent copied results escape safely. | Inner storage escapes through aggregates, closures, or evidence. |
| MM-07 | Persistent immutable tree | Updates and readers preserve sharing and expected costs. | Deep copies per version or reader. |
| MM-08 | Helper and closure allocation context | Direct calls, helpers, callbacks, and factories obey one specified placement rule. | Ambiguous placement or hidden dangling captures. |
| MM-09 | Move and scoped borrowing | Old-owner use rejects; shared reads and exclusive mutation compose safely. | Conflicting alias use or release during borrowing. |
| MM-10 | Disjoint mutable views | Checked split permits independent mutation without copying. | Overlap gains exclusive authority or safe splits always reject. |
| MM-11 | Counted shared graph | Bindings, projections, and captures maintain accounting and valid access. | Premature reclamation or unexplained retention. |
| MM-12 | Counted cycle and deep release | Cycle behavior matches the contract; deep release has stated auxiliary storage and work. | Unpromised cycle retention, invalid release, or unbounded hidden work. |
| MM-13 | Region-specific collection and hidden roots | Dead objects are reclaimed while the region remains available; closures, captures, and cross-region references remain roots when required. | Missed roots, premature reclamation, or treating the region's availability as proof every object remains live. |
| MM-14 | Captured region | Resume preserves values; discard closes owned obligations in order. | Duplicated ownership, premature release, or skipped cleanup. |
| MM-15 | Borrow across a request | Unrelated handler work succeeds; conflicting access rejects. | Suspended exclusive authority coexists with handler mutation. |
| MM-16 | Cleanup and partial acquisition | Cleanup uses live storage; failed acquisition creates no unearned obligation. | Release before cleanup, double invocation, or leaked partial ownership. |
| MM-17 | Mixed region providers | Counted, arena, or traced nesting preserves both contracts. | Hidden global policy, implicit promotion, or invalid dependencies. |
| MM-18 | Faulty provider variants | Verification rejects live reclamation, omitted roots, count overflow errors, incomplete initialization, and double release. | Application examples pass while invalid provider claims are admitted. |
| MM-19 | Placement with separate access and ownership | Immutable objects and mutable cells use one region while retaining their own access and completion rules. | Allocating in the region silently changes cell lifetime or grants mutation or backing-release authority. |
| MM-20 | Region types with different reclamation policies | Arena, counted, and traced region types expose their distinct object reclamation contracts while stating ownership and region lifetime separately. | Selecting a region type silently changes the owner, extends region lifetime, or promises another type's reclamation behavior. |
| MM-21 | Whole-region reclamation | The region owner owns its allocated objects; reclamation releases all remaining objects together after required completion, including cycles left by an earlier-reclamation policy. | A resident object survives region reclamation, a reference extends its lifetime without the region, or a referenced object in another region is incorrectly reclaimed. |
| MM-22 | Ownership and lifetime preservation | Region lifetime covers every valid use required by owned objects; the lexical scheme rejects escaping access and collection preserves required objects. | A policy reclaims an object still required by valid ownership or access, or backing is reclaimed while an admitted use remains. |

MM-13 includes collection of an outer region while an inner region retains the
only reference to an outer object. The selected contract must preserve that
reference or explicitly exclude the configuration. MM-06 includes a temporary
reference stored in an outer mutable container and removed before inner completion,
to measure conservative rejection rather than assume it is supported.

Bounds must include provider metadata, roots, closure storage, captured control,
cleanup records, and integer representation. A bounded payload arena does not
establish bounded execution if required auxiliary storage remains unbounded.
Existing mathematical integers cannot silently acquire wrapping semantics to
satisfy a static-memory case.

Measure allocation count, peak live bytes, metadata, payload copying, retained
unreachable storage, reclamation work, cleanup order, and failure observations.
Record surface annotations and rejected safe cases alongside invalid admissions.
Where a guarantee is absent, report that absence rather than infer it from timing.

### Bounded prototype and retention

A prototype should answer whether the region placement and allocation contract
composes with lexical ownership and at least two reclamation policies without
hidden copying, global memory services, or incompatible authority rules. This
is the first ownership comparison, not a definition excluding other schemes.

Begin with static storage, a fixed arena, nested immutable data, and captured
completion. Compare the arena with a region-local reclamation provider over the
same relevant cases. Extend with scoped borrowing and counting; tracing supplies
a further comparison. Keep process cases separate until scheduling and retained
ownership have a stated model.

The prototype must name its admitted fragment, assumptions, intended observations,
and provider proof obligations. Preserve the existing distinction between
ordinary allocation and acquired resource completion. Tests supplement proofs;
neither a proof of an unrelated calculus nor matching sample results establishes
provider implementation correctness.

Retain code only as design evidence if it records both policies, positive and
contrary cases, costs, and unresolved obligations. Discard candidate-specific
machinery that does not transfer. No prototype becomes product semantics or
architecture without the appropriate proposal or decision and authorized task.

## Open questions

- What is the minimum region interface, and which properties are common versus
  optional capabilities with additional obligations?
- Which ownership, lifetime, and reclamation obligations belong to each
  composition, and how do alternatives reuse the region allocation contract
  after the initial lexical ownership scheme?
- Which default discipline preserves current sharing, cyclic data, and returned
  values while remaining suitable for ordinary programs?
- How is the surrounding allocation lifetime of entry results established?
- Is a function's allocation context caller-supplied or lexically retained, and
  how do callbacks and generic functions express the relationship?
- How do implicit constructions relate to effect rows, provider constraints,
  failure, and allocation accounting?
- What dependency abstraction covers ordinary heap graphs without prohibiting
  safe projections or making every value explicitly region-annotated?
- When can temporary references in outer mutable storage be proved absent at
  inner completion?
- What minimum usage rules support scoped borrowing and captured authority?
  Which examples justify field-level places or more precise borrow endpoints?
- How are implicit reference duplication, release, roots, and cyclic structures
  described in provider contracts while keeping immutable code ordinary?
- What contracts govern source handlers intercepting storage requests?
- Which primitive storage operations are trusted, and how are provider proofs
  connected to actual implementations and admitted at a specific revision?
- How are optional capacity, reclamation, and latency guarantees verified without
  confusing them with memory safety or termination?
- What additional ownership and message rules are needed for later isolated
  processes, without adding shared-memory concurrency to the initial model?
