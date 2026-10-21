# Minimal FFI ABI profile for the worked SQLite cases

This design refinement belongs to
[DN-0057](../DN-0057-checked-ffi-module-boundaries.md) and the
[worked contract cases](minimal-ffi-contract-cases.md). It supplies only concrete
target representations and native entry realization.
The [SQLite policy](minimal-ffi-sqlite-policy.md) owns signatures, constants,
input/output roles and native assumptions; the
[canonical transition table](minimal-ffi-transitions.md) owns lifecycle and
failure behavior in both modes. This profile defines no current Ash semantics
or source syntax and authorizes no implementation.

## Target and representation

Select Linux x86-64, System V AMD64 C calling convention, LP64, little-endian,
fixed-signature calls. Reject x32 and other data models for this profile.
Generated native code uses the target C compiler's calling convention; Ash
values are marshalled rather than passed using their internal representation.

| Native role | Required representation | Conversion and access |
| --- | --- | --- |
| C `int` | Signed 32-bit, size/alignment 4 bytes | Checked conversion from Ash integers; exact widening on return. |
| `unsigned char` | Unsigned 8-bit, size/alignment 1 byte | A byte, without character decoding. |
| C `char` | 8-bit, size/alignment 1 byte | String storage is treated as octets; plain-char signedness grants no numeric conversion. |
| Object pointer | Size/alignment 8 bytes | Native typed address confined to bridge/owner records; never an Ash integer or wire handle. |
| `sqlite3*`, `sqlite3_stmt*` | Distinct opaque incomplete C types | Only the correct live owner supplies access; no layout inspection or cross-cast. |
| `T**` output | Writable, aligned pointer-sized slot | Initialize with typed C null; do not infer initialization from untyped zeroed storage. |
| `const char*` input | UTF-8 byte storage | Call-specific length/termination contract; temporary storage remains stable through return. |
| `const unsigned char*` result | Native-owned byte interval | Copy only within the admitted validity window; never free it. |
| `sqlite3_destructor_type` | Native `void (*)(void*)`, size/alignment 8 bytes | Only the declared transient sentinel is admitted here; no callable value is exposed. |

The bridge build checks sizes, alignments, integer bounds, exact function
prototypes and required constant values against its selected headers. The
repository's [SQLite header](../../../foreign-adapter/vendor/sqlite3.h) supplies
the reference inventory; delivery must identify its actual headers and binary.
Compilation against headers does not prove the binary matches them.
Function-pointer sentinels use typed native C expressions, not a guessed
object-pointer representation. Structures, native enums by value, floating
point, variadic calls, callbacks and integer/opaque-address interchange are
outside these two cases.

All byte counts and indices are checked before narrowing. For C `int`, admit
only -2147483648 through 2147483647; call-specific lengths and indices have
stricter nonnegative bounds. Check allocation arithmetic and configured limits
before allocation. The SQLite input policy's payload-plus-terminator length
must fit
both the C argument and host allocation limits. These checks do not prove a
returned native address is readable.

## Native entry and output realization

Realize every C prototype and constant role from the
[SQLite policy](minimal-ffi-sqlite-policy.md) through the target C compiler.
Reject a missing or incompatible prototype/constant before associated
acquisition. Use the selected library's typed `SQLITE_TRANSIENT` expression
in its declared destructor slot, never an Ash integer or guessed object
pointer. This role grants no callback support.

Output slots use the required native alignment, size and typed null
initialization. Direct returns retain exact native types before conversion.
Initialized storage alone establishes no successful output. Outcome-dependent
publication/disposal follows the common and SQLite transition tables, rather
than a second target-specific ownership table.

In-process calls execute this ABI in the host; isolated calls execute it only
inside the worker. Native pointers, slots and sentinels never enter protocol
messages. Parent admission uses logical contract identities and values, not
this target's address representation. Wire encoding is separate from the C ABI.

## Target evidence

Check target/header sizes, alignments, prototypes, integer limits and constant
materialization, plus exact generated-entry association. Apply the canonical
acquisition, copy and completion cases without changing their meanings.
Demonstrate typed null slots, checked narrowing and rejection of unsupported
shapes. Native address validity and adherence to declared ownership/retention
remain explicit assumptions, not consequences of successful compilation.
