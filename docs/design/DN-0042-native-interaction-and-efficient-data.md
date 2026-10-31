# DN-0042: Native Interaction and Efficient Data

- ID: `DN-0042`
- Status: exploring
- Related: [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0039](DN-0039-files-and-filesystem-resources.md),
  [DN-0040](DN-0040-floating-point-semantics-and-representation.md),
  [DN-0041](DN-0041-typed-serialization-and-data-pipelines.md),
  [DN-0049](DN-0049-native-storage-access-and-packed-data-shapes.md),
  [DN-0024](DN-0024-executable-learning-and-evidence-stream.md)

> This note connects a development direction for planning, scheduling and
> feature tracking. It is informative: it defines no current Ash semantics,
> accepts no architecture and authorizes no implementation. Detailed questions
> and evidence remain in the linked notes.

## Question

How do native interfaces, resource and memory contracts, numeric representations
and data processing fit together as the next direction of Ash development?
Which concerns enable others, and which supply useful pressure without becoming
prerequisites for every delivery?

The intended capability is practical interaction with native systems and
efficient processing of data, with explicit contracts for representation,
access, ownership and conversion. The existing notes explore separate facets
of that capability. They are starting points, not a complete account of it.

## Context

The [current specification](../../spec/README.md) supplies modules, interfaces,
algebraic data, effects, handlers and scoped builtin resources. Its
[integer operations](../../spec/dynamic-semantics.md#primitive-operations)
use mathematical integers. Pointer/void FFI, lexical region storage, generic
cells, retained control and copied-byte pinned workers are implemented in
current `ffi-ash`. General native-memory access, borrowing and packed typed
collections are not implemented.

[DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md) supplies
experimental evidence from SQLite and arenas. The
[readiness review](foreign-authoring/dn-0036-readiness.md) distinguishes verified
mechanics from unfinished work and the remaining Ash-authoring boundary.
Those experimental foreign provider/owner routes are retired. Current native
calls and lexical-region construction are specified independently.

## Connected facets

| Facet | Motivation and relationship |
| --- | --- |
| [Ash-authored FFI, DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) | Express native declarations, behavioral contracts, conversions and linking without handwritten per-library host adapters. SQLite, native arenas and files are contrasting use cases for the same mechanisms. |
| [Regions, DN-0035](DN-0035-region-memory-management-and-verified-providers.md), and [resource properties, DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md) | Regions provide placement and allocation; region types may specify earlier object reclamation. Lexical scope is the first ownership scheme for the region and its objects. It determines region lifetime, preserving valid object use; reclaiming the region reclaims all remaining objects together. Mutation and access rules compose separately. |
| [Native storage and packed data shapes, DN-0049](DN-0049-native-storage-access-and-packed-data-shapes.md) | Treat FFI allocation as the prerequisite for the selected native-backed storage route. Connect Ash-library storage policy, checked layouts, sharing, borrowing, mutation, packed collections, and calculated positions over memory. |
| [Files, DN-0039](DN-0039-files-and-filesystem-resources.md) | Exercise buffers, partial progress, irreversible operations, native errors and fallible completion; supply input/output for data pipelines. |
| SQLite and [typed serialization, DN-0041](DN-0041-typed-serialization-and-data-pipelines.md) | Supply realistic programs combining types, interfaces, state, conversions and data movement. Their failures and costs test whether the foundations compose beyond isolated examples. |
| [Floating point, DN-0040](DN-0040-floating-point-semantics-and-representation.md) | Define numerical behavior for foreign calls and data processing. Optional machine integers are a separate, still undesigned concern; checked conversion from mathematical `Int` can serve bounded native calls first. |

These relationships run in both directions: foundations enable applications,
and applications reveal missing contracts or unnecessary machinery. For
example, copying SQLite columns exposes validity windows; file reads expose
initialized lengths and partial results; serialization exposes generic
composition and numerical precision choices.

## Constraints

Keep representation, access discipline and ownership distinct. A pointer's ABI
representation does not say whether it denotes an owned handle, borrowed buffer
or output slot. A native arena supplies storage; its interface alone does not
establish region validity. Logical sequences do not guarantee contiguous storage.

Base Ash-to-C mappings need position-sensitive treatment. A `void` result,
a `(void)` parameter list and `void *` have different roles. Array objects and
array parameters have different storage obligations; strings add length,
termination and encoding contracts. This note identifies that work without
selecting a mapping table or source syntax.

Preserve the boundaries of the individual notes. Connecting them adds no
requirements to completed DN-0036 deliveries and does not turn every future
concern into a prerequisite. Formal proofs remain a separate workstream;
compiler and independent Core validation remain implementation obligations.

## Candidate directions

### Copying first, explicit access choices later

The selected first DN-0037 direction is generated typed native bridges using
the existing evaluator, with a copying SQLite binding as the first complete
delivery and a minimal native arena acquisition, usage and release interface
as a second worked design case. This is a design direction, not an accepted
architecture. Unfinished wider Arena work does not block it.

Copying permits checked transforms such as narrowing, encoding conversion and
termination changes. It simplifies independence from native storage while
exposing the contracts needed to make calls and conversions correct. Its
allocations and data movement are costs to measure, not a permanent default
for all interfaces.

The longer-term aim includes zero-copy access. Authors and callers should be
able to choose tradeoffs through explicit contracts: independent copied data,
checked borrowed access, or access relying on declared foreign assumptions.
Zero-copy can be safe when its conditions are enforced; copying is not safe
merely by name. Representation compatibility, lifetime, aliasing and
invalidation still determine what each operation can promise.

### Concerns still needing design

- **Native storage, access, and packed collections:**
  [DN-0049](DN-0049-native-storage-access-and-packed-data-shapes.md) records the
  agreed planning direction from native backing through region placement and
  allocation, ownership and reclamation, representation, access permissions,
  and library-defined shapes. The intended arrays and vectors use inline
  representations with defined alignment and stride;
  sharing, borrowing, and mutation are initial usability questions. The generic
  memory-operation boundary and concrete collection contracts remain open.
- **Machine integers:** native widths and efficient element storage may
  motivate explicit bounded types. They require their own arithmetic and
  conversion choices; JSON does not itself require fixed-width Ash integers.
- **SIMD:** data-parallel algorithms depend on suitable collections and numeric
  behavior. Calling a native SIMD implementation through FFI and having Ash
  generate SIMD instructions are different routes; the latter needs additional
  execution and lowering design.

Link dedicated notes here as those questions become concrete. This summary
does not select their mechanisms.

### Planning and tracking use

Schedule bounded capabilities rather than complete subjects. General borrowing
need not precede copying FFI; selectable regions need not precede owned
in-memory serialization. For the native-backed heap-like storage direction,
FFI supplies allocation and release; sharing, borrowing, mutation, and layout
need design together to make that storage useful. File, serialization, and
memory design can develop alongside FFI, then connect when their required
contracts are ready. Explicit library-managed storage and later routing of
new packed representations through selected storage remain distinct scopes.
Ordinary construction already uses selected lexical-region storage. Broader
zero-copy and SIMD cases draw on additional storage and numeric decisions.

For a planned capability, distinguish an actual prerequisite from a useful
comparison workload. Link its governing note, any accepted proposal or decision,
its task and its evidence as they exist. Report design, experimental execution
and product integration separately. Update this note when relationships change;
keep detailed progress and acceptance criteria in their owning artifacts.

## Evidence and experiments

Use SQLite, arenas, files and data pipelines as implementation evidence for
common mechanisms. A second library should test transfer without adding
library-specific compiler policy. Compare copying and later borrowed paths
on observable values, errors, completion and actual data movement. Measure
compiler preparation and validation costs as well as runtime allocation and
copying; a richer contract should not hide repeated work.

Reuse existing examples and regression coverage where they establish the same
obligation. Add focused cases for new boundaries or demonstrated defects rather
than executing duplicate documentation corpora in every development run.

[DN-0024](DN-0024-executable-learning-and-evidence-stream.md) supplies another
source of realistic pressure. ash-doc deliberately targets a relatively stable
Ash release and ports forward to the next stable target. Future automated
forward-migration against ash-lang commits could discover omissions, bugs and
regressions while publication stays stable. That workflow is not set up or
designed here; confirmed defects can yield focused upstream regressions.

## Open questions

- Which bounded workloads best reveal the next missing contracts after the
  first copying binding and arena lifecycle?
- Which representation and access obligations can checking enforce, and which
  remain explicit foreign assumptions?
- What contiguous collection and numerical choices are justified by measured
  workloads before broader zero-copy or SIMD support?
- Where can ordinary Ash libraries suffice, and where does evidence justify
  a language, Core or toolchain addition?
