# Initial foreign and memory contracts

> These contracts are comparison inputs under
> [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> They describe the admitted experiment fragment and obligations to investigate,
> not current Ash or verified provider implementations.

## Contract roles

For each operation distinguish foreign preconditions, foreign postconditions,
provider checks, client checks, and inferred relationships. Foreign contracts
come from the cited upstream API and the exact build selected for execution.
The observed runtime input is recorded in [environment.json](environment.json).
Tests cannot establish that arbitrary native implementations obey the contract.

The first slice uses private connection and statement owners, copied scalar and
byte values, and one stable arena backing allocation. Addresses are private
adapter data. The later slice adds retained inputs and scoped output views.

A resource type definition links these contracts to its provider, formal
identity parameter, associated effect interface, and checked handlers. A
resource expression establishes an instance with a fresh identity and lexical
lifetime. Follow the types between those two positions using the
[typing study](semantics.md#resource-type-definition); the resource type name is
not an independent provider designator. Program-lifetime resources remain open.

## SQLite inventory

The table names the selected symbol boundary; signatures must be checked against
the chosen headers before the adapter is compiled. Use `sqlite3_int64` for the
integer value boundary and checked conversions for parameter indices, lengths,
and column indices. Preserve Ash's integer range rather than silently truncate.

| Calls | Native contract and provider obligation |
| --- | --- |
| `sqlite3_libversion`, `sqlite3_sourceid`, `sqlite3_compileoption_get` | Record the actual runtime and configuration. The metadata observation does not prove header compatibility or provider correctness. |
| `sqlite3_initialize`, `sqlite3_shutdown` | [Initialization](https://www.sqlite.org/c3ref/initialize.html) concerns the library, not one connection. Choose a host-owned setup lifetime; do not let a connection shut down shared native state. |
| `sqlite3_open_v2`, `sqlite3_errcode`, `sqlite3_errmsg` | [Open](https://www.sqlite.org/c3ref/open.html) may fail with a non-null connection. Retain a guard before publication, copy diagnostics while valid, and close any returned partial owner. Failed establishment exposes no client handle. |
| `sqlite3_prepare_v2` | [Prepare](https://www.sqlite.org/c3ref/prepare.html) consumes SQL input for one compilation and can succeed without a statement for empty input. Distinguish that from failure. Keep any returned tail as an offset into the input, not an escaping pointer. |
| `sqlite3_bind_int64`, `sqlite3_bind_blob` | [Binding](https://www.sqlite.org/c3ref/bind_blob.html) has checked index, size, and statement-state requirements. The initial BLOB path uses a native copy; the later retained path keeps stable valid input until the declared release point. Empty BLOB must not become SQL null accidentally. |
| `sqlite3_step` | [Step](https://www.sqlite.org/c3ref/step.html) separates a row, completed execution, and error. Preserve those outcomes and permit column access only for an admitted row. Do not rely on automatic reset as an unstated protocol rule. |
| `sqlite3_column_type`, `sqlite3_column_int64`, `sqlite3_column_blob`, `sqlite3_column_bytes` | [Column access](https://www.sqlite.org/c3ref/column_blob.html) needs a current row and valid column. Validate kind/conversion and access interval; copy bytes before ending it. Distinguish null, empty bytes, and conversion allocation failure. The library owns returned byte storage. |
| `sqlite3_reset`, `sqlite3_clear_bindings` | [Reset](https://www.sqlite.org/c3ref/reset.html) and [clear bindings](https://www.sqlite.org/c3ref/clear_bindings.html) have different contracts. Reset is not proof that retained bound storage has been relinquished. Record both protocol and access postconditions. |
| `sqlite3_finalize` | [Finalize](https://www.sqlite.org/c3ref/finalize.html) consumes the statement even when reporting a preceding error. Completion reporting must not retry through that consumed pointer. |
| `sqlite3_close` | [Close](https://www.sqlite.org/c3ref/close.html) can refuse while dependent objects remain. Preserve the still-live owner on refusal. Use explicit statement completion order rather than silently substituting deferred destruction. |

The first native tests may pass a null tail-output pointer and reject multiple
SQL statements at the public wrapper boundary. Any later general SQL API must
state its handling of unused input. A host-wide shutdown comparison is isolated
from other SQLite users; ordinary tests need not claim ownership of global state.

### Ash-facing state and obligations

Use conceptual identities `C` for a connection and `S` for its statement. A
statement depends on its connection. Non-owning access can be aliased within
that relationship; only the resource scope owns completion. Returning a copied
integer or copied bytes does not retain either owner.

Record statement states sufficient to guard the selected operations: prepared,
row available, completed/error, and finalized. These are experiment protocol
states, not a selected source typestate syntax. Compare static evidence with
runtime validation followed by typed evidence when the native outcome is dynamic.

The candidate effect API has exact connection/statement instances. Operations
must not choose an instance merely from an operand's address. Provider methods
and interpreters relate to authenticated identities and origin facts. Selected
evidence alone must not manufacture a connection or publish a forged owner.

The reporting envelope is an open source-design choice. It must retain the body
outcome, ordered completion reports, and whether each native owner was consumed
or remains live. Guard disposal handles unpublished state. Internal exhaustion
is separate from an ordinary native error; no source-cleanup guarantee is added
for divergence or host termination.

## Arena contract

The first arena is one independently acquired block with fixed byte capacity.
Typed object access is related to its fresh owner identity. Contents are opaque
to clients except through typed operations. Reclamation happens at arena
completion; aliases and object bindings own no release operation.

| Property | Initial contract or choice to resolve before coding |
| --- | --- |
| Capacity | Name payload capacity in bytes. Account for alignment padding within it; report object/access metadata separately. Test arithmetic before reservation. |
| Zero capacity and zero-sized objects | Compare a valid empty arena with rejection of zero capacity. Choose before tests. Define whether a zero-sized object requires a distinct identity and metadata. |
| Object layout | Define size, alignment, and field representation for the admitted integers, tuples, and references. Native layout is not assumed to equal arbitrary Ash heap layout. |
| Address stability | Backing storage does not move during the owner's lifetime. Foreign access still needs compatible layout, permitted aliases, and a valid interval. |
| Publication | Publish an object only after initialization finishes. Specify cursor rollback and disposal of partial initialization; earlier objects remain valid after failure. |
| Sharing | Creating an alias preserves identity and dependencies without copying payloads. Immutable shared objects need no individual release authority. |
| Nested arenas | Inner objects may depend on live outer storage. Reject surviving outer state with inner dependencies unless a separately checked scoped-access case establishes removal. |
| Completion | Run required actions while storage remains available, then reclaim once. Bulk release does not imply discovery or invocation of general object destructors. |
| Copying | Separate independent deep copying from shallow alias transport. Define preserved sharing and supported cycles; do not call a shallow copy independent. |
| Ownership restriction | The owner cannot be returned, packaged with values, reference-counted past its scope, or transferred between processes. Captured control may retain the owned scope under the admitted continuation rules. |

Native backing storage can use a system allocation primitive through the isolated
adapter. That does not place SQLite's internal allocations in the arena. The
study concerns the contracts between those storage owners, not a mandatory
single allocator for all memory.

## Inference and explicit information

| Information | First comparison |
| --- | --- |
| Local owner relationships | Infer from acquisition and actual retained values. Require equivalent public facts when a helper body is unavailable. |
| Closure and aggregate dependencies | Follow selected values and real captures, including operation/evidence metadata. A plain result type must not hide retained access. |
| Effects | Infer exact requested instances and outward rows. Declare foreign primitive effects and any trusted interpretation explicitly. |
| Foreign layout and retained use | Supply explicit contracts; headers and source usage do not establish foreign retention or memory safety. |
| Access exclusivity and invalidation | Compare inferred use with declared operation postconditions. An owner identity is insufficient to describe a row view's shorter validity. |
| Numeric facts and native outcomes | Check at runtime where dynamic; expose justified facts to typed branches if the candidate supports them. |
| Arena policy | Describe fixed-capacity bulk reclamation explicitly. Inference does not invent a reclamation policy from client code. |

The admitted checker needs a defined join for branch-dependent owners, access,
and completion obligations. It must account for captured uses and finite work.
Public contract authenticity and primitive conformance remain separate from
merely assigning a function type.

## First review decisions

Before the first native slice, settle empty/zero-sized policies, numeric and byte
representations, initialization publication, outcome reporting, and host-effect
interpretation. Before retained access, settle release points, invalidating
operations, compatible aliases, and captured access. Record candidate choices
in [semantics](semantics.md) with their motivating case IDs.

Reference counting, tracing roots, general cycle copying, process heaps, and
ownership transfer are not required for the first native baselines. Their
pressure remains visible in the later cases and DN-0035; they require another
bounded contract before implementation.
