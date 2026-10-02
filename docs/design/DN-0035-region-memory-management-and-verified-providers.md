# DN-0035: Region Memory Management and Verified Providers

- ID: `DN-0035`
- Status: exploring
- Related: [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md), [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md), [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md), [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md), [DN-0031: Resource Composition Concept Map](DN-0031-resource-composition-concept-map.md), [DN-0032: Algebra of Scoped Resource Composition](DN-0032-algebra-of-scoped-resource-composition.md), [DN-0033: Direct Effects and Continuation Capabilities](DN-0033-direct-effects-and-continuation-capabilities.md), [DN-0034: Verification Foundation for Ash Semantics and Implementation](DN-0034-one-shot-kernel-soundness-and-practicality.md)

> This design note is informative. It consolidates a proposed memory-management
> direction and its reference cases. It does not define current Ash, accept an
> architecture, select a default allocator, or authorize implementation. Region
> interfaces, provider verification, borrowing, and processes remain design work.

## Question

Can lexically nested regions and verified library providers support static
storage, arenas, reference counting, tracing, and individually owned storage
under one lifetime and resource discipline, while preserving ordinary immutable
sharing and making each policy's guarantees and costs explicit?

The working direction is that regions provide storage through resource
capabilities and effect interpretations. Provider contracts are selected and
checked statically. The provider determines allocation and reclamation policy;
language rules establish valid access, dependencies, and completion authority.
Ordinary construction defaults to the nearest applicable region.

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
explicit transfer and copying. This note narrows that exploration to lexical
regions with statically fixed disciplines.

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

- Select and check each region's discipline statically. A runtime activation
  supplies fresh state, not a new policy. Dynamic policy replacement is excluded.
- Let explicit regions nest. Newly constructed values requiring storage default
  to the nearest applicable region; aliasing an existing value preserves its
  allocation and dependencies.
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
  parallel sharing, escaping region ownership, and cancellation are excluded.
- Do not equate safe access with eventual release, termination, or bounded work.

## Candidate directions

### Working direction: regions as storage-providing resources

A region is a resource provision that supplies storage capabilities under a
lexical lifetime. Its provider implements a statically selected storage
discipline, and associated handlers interpret the supported requests. Its scope
owns completion. A region may use several blocks, pools, or individually managed
allocations; its identity is not a physical address or one contiguous block.

The proposed roles are:

| Role | Responsibility |
| --- | --- |
| Region identity | Relate storage, values, operations, and dependencies. |
| Provider contract | State capabilities, invariants, failure behavior, and guarantees. |
| Provider implementation | Realize the selected discipline under those contracts. |
| Handler | Interpret requests for the associated provision. |
| Resource scope | Hold authority and the obligation to complete the region. |
| Client checking | Establish valid access, usage, dependencies, and completion. |

Regions may require a specific connection to ordinary construction, but should
otherwise reuse general resource rules. The experiment must identify any
irreducible region-specific rule rather than assume either complete uniformity
or a privileged allocator subsystem.

A handler's signatures do not prove its implementation safe. Intercepting a
request does not grant authority to manufacture references, reclaim storage, or
close an owner. The relation between source overrides and verified storage
interpretations needs a contract, preserving the current distinction between
interpretation and resource authority.

### Default allocation and nested lifetimes

Ordinary code uses a default discipline without naming an allocator at every
construction. An explicit region selects a provider for its scope. The default
policy and the surrounding lifetime for entry results remain open; ordinary
results must remain usable by their recipient.

An ordinary binding or function call does not automatically acquire a region.
The following is a scenario description, not proposed Ash syntax:

```text
enter region A
    construct x                  -- storage defaults to A
    enter region B
        bind y to x              -- no relocation of x
        construct tuple (x, y)   -- new tuple storage defaults to B
    complete B
complete A
```

Region B may contain references to A. Surviving state must not retain a reference
to B after B completes. Returning an outer value projected from an inner
aggregate can be safe even when returning the aggregate itself is unsafe.
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
while another binding or closure retains the same allocation. The region's
discipline decides whether that allocation remains until completion or becomes
reclaimable earlier.

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

### Policies and disposal contracts

Policy selection is fixed statically, while capacity, allocation success,
reference counts, and reachability may depend on execution. Static selection
does not require every runtime outcome to be known in advance.

| Policy | Candidate contract |
| --- | --- |
| Static storage | Known storage layout and bounded initialization; no subsequent allocation where promised. |
| Fixed arena | Allocation within a fixed budget; bulk reclamation at region completion. |
| Growable arena | Allocation from acquired blocks; bulk reclamation and stated acquisition failure. |
| Region-local reference counting | Accounted sharing and earlier reclamation where counts permit. |
| Region-local tracing | Retain reachable objects and reclaim unreachable storage within the region. |
| Individually owned storage | Transfer and borrowing contracts with individual release authority. |

Distinguish releasing a reference, reclaiming an allocation, and completing a
region. A provider need not support all three as client operations. An arena
need not offer individual release. Region completion consumes its owner rather
than being an unrestricted request through any alias.

Counted storage must define duplication and release accounting, count overflow,
and cycle behavior. Cycles may remain until region completion or use a declared
cycle policy. Counting references that extend an entire region beyond its
lexical lifetime is a separate, excluded extension.

Tracing requires a complete account of roots and references, including closures,
captured control, and references held by nested regions. A moving provider also
needs a valid reference-update contract. Neither follows merely from lexical
lifetime checking. The initial model need not require moving collection.

An arena's safety contract can permit cyclic ordinary data without tracing:
bulk reclamation does not depend on discovering unreachable objects. Long-lived
regions may select earlier reclamation to bound retention during execution.

### Effects and required completion

A request may capture a region without completing it. Resume preserves its
activation and storage; checked discard closes the owned abandoned region after
required dependent completion. Lexical ownership remains meaningful while the
scope is inactive. A textual block boundary is not a release event during capture.

Borrowing must account for authority retained in captured control. A handler
must not exercise conflicting access while a suspended computation owns an
exclusive borrow. One-shot resumption prevents continuation duplication, not
all alias conflicts.

Bulk release must follow cleanup that uses the region's storage. Ordinary
unreachable-data reclamation does not implicitly invoke arbitrary effectful
source cleanup. Owned values with individual destruction require explicit
completion contracts, including order and effects. Region completion does not
promise success under divergence, internal exhaustion, or external termination.

Fallible acquisition must publish neither partial values nor unearned owners.
The provider must distinguish its declared allocation failure from internal
execution failure. Current native-buffer behavior is a bounded precedent, not
an automatically inherited failure protocol for every future provider.

### Verified provider contracts

The proposed verification obligation is compositional:

> Given a well-formed region and clients satisfying its access, dependency, and
> usage rules, provider operations preserve valid storage, admitted authority,
> and required completion obligations.

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
- Individually owned storage as the baseline, with explicit regions for shared
  or cyclic data. This makes release authority prominent but may burden ordinary
  persistent structures and closure use.

Compare the same programs, rejection behavior, annotations, and costs. Do not
select the working direction solely because the resource vocabulary fits it.

### Later process ownership

Processes would own regions under this same memory model. Initially, processes
share no storage. Message transport must establish receiver-owned data; ordinary
cross-process references are not admitted. Copying and any later ownership
transfer require explicit contracts and costs.

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
| MM-01 | Static immutable configuration graph | Known storage and initialization; repeated reads require no further allocation. | Access silently needs a general heap or collector. |
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
| MM-13 | Traced graph and hidden roots | Closures, captures, and nested-region references remain roots when required. | Missed roots or permanent retention of all allocations. |
| MM-14 | Captured region | Resume preserves values; discard closes owned obligations in order. | Duplicated ownership, premature release, or skipped cleanup. |
| MM-15 | Borrow across a request | Unrelated handler work succeeds; conflicting access rejects. | Suspended exclusive authority coexists with handler mutation. |
| MM-16 | Cleanup and partial acquisition | Cleanup uses live storage; failed acquisition creates no unearned obligation. | Release before cleanup, double invocation, or leaked partial ownership. |
| MM-17 | Mixed region providers | Counted, arena, or traced nesting preserves both contracts. | Hidden global policy, implicit promotion, or invalid dependencies. |
| MM-18 | Faulty provider variants | Verification rejects live reclamation, omitted roots, count overflow errors, incomplete initialization, and double release. | Application examples pass while invalid provider claims are admitted. |

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

A prototype should answer whether one lexical dependency and completion model
admits ordinary sharing under at least two provider policies without hidden
copying, global memory services, or incompatible authority rules.

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
