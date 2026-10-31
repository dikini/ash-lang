# DN-0049: Native Storage, Access, and Packed Data Shapes

- ID: `DN-0049`
- Status: exploring
- Related: [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0039](DN-0039-files-and-filesystem-resources.md),
  [DN-0041](DN-0041-typed-serialization-and-data-pipelines.md),
  [DN-0042](DN-0042-native-interaction-and-efficient-data.md),
  [DN-0044](DN-0044-no-default-runtime.md)

> This note records an agreed planning direction. It defines no current Ash
> semantics, accepts no implementation architecture, and authorizes no product
> implementation or prototype. Access rules, layout contracts, and the generic
> memory-operation boundary remain design questions.

## Question

Can Ash libraries use native allocation through FFI to implement heap-like
storage, packed collections, and shapes over memory, with usable sharing,
borrowing, and mutation? What common checked operations let new allocators and
data structures reuse those foundations without handwritten Rust support for
each library or representation?

## Context

The [current dynamic semantics](../../spec/dynamic-semantics.md) define an
evaluation heap, reusable ordinary values, closures, and guarded cyclic data.
The [lexical region rules](../../spec/static-semantics.md#lexical-regions-and-construction-dependencies)
provide selected construction storage and retain residency and field/capture
dependencies. The [resource rules](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
separate non-owning handles from scope-owned completion. These mechanisms do
not establish general borrowing or packed typed layouts. The current
[foreign boundary](../../spec/static-semantics.md#source-foreign-declarations)
does not expose general native-memory reads and writes.

[DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) explores access to
libc and other native libraries through Ash-authored declarations and generic
bridges. For the native-backed storage route considered here, that FFI is a
prerequisite: it supplies backing allocation and release. Ash libraries would
define storage and collection policy; generic checking and memory operations
would preserve the required authority and validity relationships.

[DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md) supplies
experimental packed bytes/text and scalar Arena evidence. Its
[wider Arena results](provider-experiments/arena-results.md#regression-only-scope-and-deferred-work-2026-10-09)
record incomplete layouts, references, and graph work. Those experiments do not
establish the general memory model proposed here. Their
[private aggregate encoding](provider-experiments/semantics.md#layout-and-publication)
also must not be assumed to be a C layout or array element stride.

## Constraints

- Keep region placement and allocation, ownership, lifetimes, reclamation,
  representation, access permissions, and shape distinct, while checking their
  relationships. Lexical scope is the first ownership scheme, not a region's
  defining property.
- Treat sharing, borrowing, and mutation as initial usability concerns for these
  libraries. Existing scope liveness alone does not establish valid views,
  exclusivity, or disjoint access.
- Preserve ordinary immutable sharing and resource dependencies through fields,
  closures, selected methods, requests, and captured control. An immutable outer
  value does not establish immutable reachable state.
- Publish readable typed access only after its representation is initialized
  and valid. Distinguish reserved capacity from initialized contents.
- Check size and offset arithmetic, allocation bounds, alignment, and native
  conversions before the corresponding memory access.
- Keep mathematical `Int` semantics. A selected bounded storage encoding needs
  explicit conversion and failure behavior.
- Account for allocation failure, partial initialization, growth failure, and
  completion without losing earlier values or duplicating release authority.
- Keep foreign allocator assumptions explicit. A signature, layout descriptor,
  ordinary interface implementation, or calculated offset alone grants no
  native memory authority.

## Candidate directions

### Agreed decomposition

The following layers describe responsibilities and dependencies. Concrete
collection and shape examples should pressure their contracts together and may
develop alongside them.

| Layer | Responsibility |
| --- | --- |
| Native allocation through FFI | Obtain and release backing storage under declared size, alignment, failure, and ownership contracts. |
| Region placement and allocation | Select storage and obtain initialized allocation extents under size, alignment, capacity, and failure contracts. |
| Ownership and lifetimes | Determine who owns the region and its objects and the region's lifetime; keep storage valid for every permitted object use. Lexical scope is the first ownership scheme. |
| Reclamation | A region type may specify earlier object reclamation that preserves required object lifetimes. Reclaiming the region reclaims all remaining objects together after required completion. |
| Representation and layout | Define encodings, occupied extents, alignment, element strides, and field offsets. |
| Access discipline | Establish compatible aliases, read and mutation permissions, borrowing intervals, and invalidation. |
| Collections and shapes | Build packed arrays, vectors, strings, records, and indexed views using the same foundations. |

Allocator and data-structure policy belongs in Ash libraries over a common
checked boundary, whose implementation may remain in the compiler and runtime.
The compiler implementation language and a future native backend remain separate
choices. Adding a shape should reuse the common memory operations.

An arena can compose region allocation with lexical ownership and bulk release.
A region-specific collector could reclaim dead objects while the region remains
available. Its roots, cross-region references, and possible relocation need
additional contracts. Allocating a mutable cell or immutable value in the same
region does not unify their access rules or extend a cell's logical lifetime.

### Packed collections and calculated positions

Packed arrays and vectors store element representations inline with a defined
stride and alignment. Occupied extent and element stride can differ because
successive elements must remain aligned. Contiguity alone supplies neither a
particular encoding nor permission to reinterpret bytes as an arbitrary Ash type.

A representation can be selected independently of its source type. For example,
a mathematical `Int` could use a checked signed-64 storage encoding that refuses
out-of-range values. A fixed-width source type is another possible design.
Reference-containing elements additionally need a validity and dependency
account; a numeric layout descriptor does not establish it.

A shape maps logical coordinates or fields onto offsets in backing storage.
The following equations illustrate byte offsets, not Ash syntax:

```text
array:   offset(i)       = origin + i * element_stride
matrix:  offset(row,col) = origin + row * row_stride + col * column_stride
record:  offset(field)   = origin + field_offset(field)
```

Dimensions, strides, field metadata, and position calculations can largely be
ordinary library code. Slicing can adjust origin and dimensions; transposition
can exchange dimensions and strides. A view can therefore be strided even when
its backing allocation is contiguous. Arrays of records and separate field
columns provide further comparisons without requiring a new owner model.

Variable-sized inline elements need another indexing contract, such as an offset
table; they do not automatically support constant-stride access. UTF-8 strings
also distinguish byte offsets from scalar traversal, and text views must
preserve valid encoding boundaries.

Checked memory operations must connect a shape's calculated range to a live
allocation, valid representation, initialized contents, and sufficient access
permission. Mutable views that overlap need an explicit mediation rule;
independent mutation cannot follow merely from distinct view values.

### Sharing, borrowing, and mutation

Compare mediated shared mutation with checked exclusive access using the models
in [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md).
Specify shared readers, mutable views, disjoint ranges, permission recovery,
freezing, and transfer where required. Returning a view retains its backing
dependencies. Growth, refill, reset, or release must account for outstanding
access, including access retained by captured control.

Freezing ends the relevant mutation authority before immutable sharing. It does
not itself choose arena ownership, counting, or tracing. Earlier reclamation,
cycle behavior, and retention of a large allocation by a small view need their
own policy and cost contracts.

### Generic checked boundary and library policy

Compare two starting points before selecting primitives:

- Checked byte-memory operations with library-defined encodings and shape
  calculations. This offers a small common access surface but needs an account
  of typed decoding, initialization, and reference-containing representations.
- Typed memory operations using independently validated layout and access facts.
  This may expose more information for checking and lowering, but needs an
  account of fact construction, composition, and preservation.

Either route must explain which operations remain trusted and how library
implementations establish their obligations. Ordinary interface evidence is not
proof of arbitrary allocator or layout laws. Preserve defining identities and
dependencies through imports, specialization, Core validation, and execution.

An explicit heap library first manages its own values. Current lexical regions
already select storage for ordinary construction; extending that mechanism to
new packed representations and native-backed access remains a separate question.
The broader runtime-service alternatives are explored in
[DN-0044](DN-0044-no-default-runtime.md). The first storage study need not solve
that whole transition, introduce concurrent sharing, or supply a native backend.
It adds no requirements to the implemented copying FFI boundary.

## Evidence and experiments

The first proposed connected study obtains native backing, constructs a packed
array, creates shared shaped views, performs mutation under the admitted access
rules, and releases the owner once. It should compare the generic memory-boundary
candidates on the same cases before selecting their mechanisms.

| Case | Required observation |
| --- | --- |
| Native storage | Actual native allocation backs the payload; construction and access do not depend on a hidden evaluator copy of that payload. Account separately for evaluator and metadata storage. |
| Packed array and padded elements | Values occupy the declared positions; every repeated element remains aligned, including where extent differs from stride. |
| Matrix and subview | Calculated positions read the intended elements; views share backing under declared retention and copy costs. |
| Shared access and mutation | Compatible readers work; conflicting mutation, stale access, and unsupported overlapping mutable views reject or refuse before access. |
| Growth and initialization | Failed allocation or initialization preserves established values; no readable view exposes uninitialized capacity. |
| Lifetime and control | Escape beyond a closing backing owner through aggregates, closures, or requests rejects; resume preserves authority and discard completes the owned storage correctly. |
| Completion | Normal completion and owned abandonment release once, after dependent cleanup; internal failure remains distinct from successful source completion. |

Record native calls, payload and metadata allocations, bytes copied, retained
backing storage, access-check work, and completion order. Include bounds,
misalignment, overflow, invalid encoding, and invalidation failures. Compare
useful accepted programs and required annotations as well as rejection behavior.

Before any prototype, give it a bounded assignment with exact contracts and
comparison inputs. Retain successful source libraries and results as design
evidence; discard or revise mechanisms that require per-shape compiler support,
conceal payload copies, or fail the access and lifetime cases. Product adoption
requires the proposal or decision and task workflow.

## Open questions

- What minimum memory operations and admitted facts support both byte encodings
  and typed layouts without letting ordinary values forge authority?
- How do layout, initialization, and element dependencies compose for nested or
  reference-containing representations?
- Which alias rules support shared reads, mediated mutation, exclusive views,
  disjoint splits, and captured control with usable source annotations?
- Which offset and shape facts can be established statically, and which require
  checks at view construction or each access?
- How do growth, freezing, and transfer preserve values and outstanding access
  without hidden copies or lost completion obligations?
- Which reclamation and allocation-failure policies are needed by the first
  useful workloads before ordinary-construction lowering is considered?
