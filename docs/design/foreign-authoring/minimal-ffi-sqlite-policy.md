# SQLite policy for the minimal FFI cases

This library contract belongs to
[DN-0057](../DN-0057-checked-ffi-module-boundaries.md). It owns the portable
SQLite signatures, constants, input and output roles, conversion assumptions
and diagnostic rules for the [worked cases](minimal-ffi-contract-cases.md).
The [canonical transition table](minimal-ffi-transitions.md) owns outcome
precedence and lifecycle transitions for both execution modes. The
[ABI profile](minimal-ffi-abi-profile.md) supplies concrete target mappings;
platform executor profiles supply launch, storage and containment mechanisms.
No Linux layout or source syntax is defined here. These are proposed contracts,
not current Ash semantics or implementation authorization.

## Exact operation inventory

These are C signatures describing ABI facts, not proposed Ash syntax.
`D` below abbreviates the native `sqlite3_destructor_type` only in the table.

| Operation | Native signature |
| --- | --- |
| Host setup | `int sqlite3_initialize(void)` |
| Connection acquisition | `int sqlite3_open_v2(const char*, sqlite3**, int, const char*)` |
| Statement acquisition | `int sqlite3_prepare_v2(sqlite3*, const char*, int, sqlite3_stmt**, const char**)` |
| Bind copied text | `int sqlite3_bind_text(sqlite3_stmt*, int, const char*, int, D)` |
| Bind SQL null | `int sqlite3_bind_null(sqlite3_stmt*, int)` |
| Execute | `int sqlite3_step(sqlite3_stmt*)` |
| Column count | `int sqlite3_column_count(sqlite3_stmt*)` |
| Original column kind | `int sqlite3_column_type(sqlite3_stmt*, int)` |
| Text interval | `const unsigned char *sqlite3_column_text(sqlite3_stmt*, int)` |
| Text byte count | `int sqlite3_column_bytes(sqlite3_stmt*, int)` |
| Reset execution | `int sqlite3_reset(sqlite3_stmt*)` |
| Clear parameters | `int sqlite3_clear_bindings(sqlite3_stmt*)` |
| Statement consumption | `int sqlite3_finalize(sqlite3_stmt*)` |
| Connection close | `int sqlite3_close(sqlite3*)` |
| Primary/current code | `int sqlite3_errcode(sqlite3*)` |
| Extended diagnostic code | `int sqlite3_extended_errcode(sqlite3*)` |
| Optional diagnostic bytes | `const char *sqlite3_errmsg(sqlite3*)` |

Copied text/null binding supports repeated statement use and exercises the
required transient sentinel. Integer/BLOB binding, alternative prepare/open
variants and deferred close are not added by this inventory. This does not
remove those operations from the wider DN-0037 copying-binding program.
Initialization is host-owned before acquisition; a connection never shuts
down shared SQLite state. Threading and initialization configuration must
satisfy the serialized group contract.

## Constants, nulls and negative sentinels

| Native value | Meaning in this profile |
| --- | --- |
| `SQLITE_OK = 0` | Success only for operations whose contract admits it. |
| `SQLITE_ROW = 100`, `SQLITE_DONE = 101` | Step outcomes; neither is generic success for acquisition or close. |
| `SQLITE_NOMEM = 7`, `SQLITE_BUSY = 5`, `SQLITE_MISUSE = 21` | Allocation failure, close refusal/operation-specific busy, and detected misuse respectively. |
| Column tags 1, 2, 3, 4, 5 | Integer, float, text, BLOB, SQL null; the copied-text case accepts only 3 and 5. |
| `SQLITE_OPEN_READWRITE = 2`, `SQLITE_OPEN_CREATE = 4` | Fixed open flags `2 \| 4`; arbitrary caller flags are rejected. |
| Typed null VFS argument | Select default VFS; not a missing connection or empty path. |
| `SQLITE_TRANSIENT` | Native `((sqlite3_destructor_type)-1)` in the destructor argument only. |
| `SQLITE_STATIC` | Native destructor null; rejected because retained input is unsupported. |
| Negative input lengths | Rejected; the SQLite scan-to-zero mode is not used. |

The sentinel mapping follows SQLite's
[destructor constants](https://www.sqlite.org/c3ref/c_static.html). The bridge
materializes the declared typed constant. It never calls it or accepts an
arbitrary source integer as a destructor. This bounded sentinel role does not
admit general function pointers or callbacks.

Preserve each returned C status exactly, including extended codes. Recognize
only operation-appropriate outcomes. Unrecognized error codes remain numeric
native failures; do not invent ownership transitions from their names.
Impossible success/tag combinations and detected misuse are boundary
violations. Record any independently known consumption before quarantine.

## Input preparation

Paths and SQL are valid UTF-8 without embedded zero. Append one native zero
byte. Paths use the zero-terminated contract; SQL passes the explicit total
buffer size including the terminator. Keep the input allocation live until
all output interpretation requiring it has finished.

Use flags `READWRITE | CREATE` and null VFS. This supplies no writable-access
or filesystem-confinement guarantee. Accept only a database selected by the
host grant or explicit in-memory mode; URI handling is disabled for this
binding. Concrete path spelling and storage enforcement belong to executor
profiles. See [open](https://www.sqlite.org/c3ref/open.html).

Text binding uses a valid UTF-8, zero-free input and a nonnegative payload
byte length, excluding its added terminator, with `SQLITE_TRANSIENT`. Even
empty text has a non-null backing buffer. SQL null uses `sqlite3_bind_null`.
Parameter indices are positive native integers; the native call reports
invalid parameter positions. Admission and failed-binding recovery follow
L10–L17 in the [canonical table](minimal-ffi-transitions.md#sqlite-acquisition-and-lifecycle-table).
Input storage ends after return under
the declared copying assumption. See
[binding values](https://www.sqlite.org/c3ref/bind_blob.html).

## Output storage and acquisition interpretation

Every call's direct return is captured in its native type before conversion.
There is no fabricated default return if execution does not return. Slots
are valid native storage for the complete call, inaccessible to source code.
Initialize `db = NULL`, `stmt = NULL`, and `tail = NULL` before their respective
calls. A local publication flag begins false and changes only after admission.
Initialization makes storage defined; it does not prove the callee wrote it.

Acquisition outcomes are L1–L9 in the
[canonical lifecycle table](minimal-ffi-transitions.md#sqlite-acquisition-and-lifecycle-table).
The distinction between partial failed open, empty successful prepare and
failed prepare derives from [open](https://www.sqlite.org/c3ref/open.html) and
[prepare](https://www.sqlite.org/c3ref/prepare.html).

On successful prepare, require a non-null tail within the SQL payload through
its terminating position. Derive a checked offset while retaining the original
allocation; never export the pointer. The unused suffix must contain only
ASCII whitespace: bytes 9 through 13 or 32. Reject a second statement or other
suffix, including trailing comments after the first statement. This deliberately
restricts the wrapper rather than silently ignoring SQL. Empty/comment-only
input can still produce the no-statement outcome. On tail/admission failure,
finalize a conformingly acquired unpublished statement before releasing its
connection dependency. If partial-owner close refuses, retain/quarantine its
guard; never report disposal succeeded.

## Copied text and lifecycle rules

Use T1–T16 in the [canonical copied-text table](minimal-ffi-transitions.md#sqlite-copied-text-table)
for null/empty/conversion failures, row-scoped original-kind caching, copy
admission and publication. Native conversion refusal is T10; an admitted worker
refusal is T14; malformed worker success is T15. Parent capacity failure is
T13, independently of encoding. Use L10–L23 for binding/reset/step/native finish
and K1–K9 for local scope discharge. A lost session closes locally without a
stale native call or invented consumption. These rules are the same on each
target; only physical executor mechanisms belong to platform profiles.

Native contracts are documented by SQLite's
[column access](https://www.sqlite.org/c3ref/column_blob.html),
[reset](https://www.sqlite.org/c3ref/reset.html),
[clear bindings](https://www.sqlite.org/c3ref/clear_bindings.html),
[finalize](https://www.sqlite.org/c3ref/finalize.html) and
[close](https://www.sqlite.org/c3ref/close.html). Binding policy conservatively
blocks execution/rebinding after uncertainty even where a native implementation
might permit additional operations. A native declaration does not prove
adherence to any of these contracts.

## Diagnostic copying

Diagnostic codes are direct C integer results. Capture them while the
connection is live and before another mutating call. Optional `errmsg` bytes
are borrowed, zero-terminated native storage: null means unavailable. Copy
within a configured scan bound before invalidation; absent terminator,
invalid encoding or refusal of the separate optional diagnostic allowance
yields unavailable text with a reason. Actual runtime allocator/work failure
is terminal, preserving the original status and known disposition in reserved
control storage rather than promising an ordinary source report.
The bound limits scanning but does not prove native readability. Never query
an already closed connection or finalized statement. See
[error reporting](https://www.sqlite.org/c3ref/errcode.html). The
[common exhaustion design](minimal-ffi-exhaustion-and-ownership.md) specifies
the required reservations and report construction.

## Evidence

Apply the canonical table's distinguishing traces to both executors. Pair
native failures with runtime/worker/parent capacity refusal; observe original
status, owner disposition, dependency protection and source delivery separately.
Header/target representation checks belong to the ABI profile. Launch and
containment evidence belongs to the platform executor profile. A conforming
logical outcome does not establish native memory safety or database truth.
