# CP-0024: Smaller foreign-library boundary

- ID: `CP-0024`
- Status: proposed
- Related: [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [TASK-0050](../tasks/TASK-0050-checked-ffi-regions-control-program.md)

> The user agreed the smaller responsibility boundary on 2026-10-24. This is
> the S1 technical design for independent review, not implemented Ash. The
> previous checked-host proposal is [retained in Git](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/proposals/CP-0024-checked-foreign-host-profile.md).

## Current behavior

Main `7949b6d9` supplies generated typed Rust bridges, managed immutable Bytes,
ordinary effects, cleanup and handlers. Its foreign declarations also implement
numeric conversion, owner, outcome and window policy. The milestone has retired
the additional artifact/receipt/protected-launch stack in
[PR138](https://github.com/dikini/ash-lang/pull/138), but inherited source policy
remains. Neither implementation already provides this smaller interface.

## Proposed behavior

### Address and byte mapping

`@builtin.foreign` exports opaque nominal `Address`, using the existing nominal
identity/type rules and a private runtime data-pointer representation. It is not
an Int, Bytes, resource handle or function pointer. Export no constructor or
integer conversion. Preserve the pointer itself rather than round-tripping it
through an integer. Reuse ordinary value capture, tuples and function passing.
Runtime addresses are not source literals or serialized image constants.

The builtin exposes three pure operations:

- `null : Unit -> Address` returns the C null data pointer.
- `is_null : Address -> Bool` tests that value for null.
- `equal : (Address, Address) -> Bool` compares data-pointer values, including null.

Equality establishes neither allocation identity nor validity. There is no
ordering, address arithmetic, automatic dereference, copying or freeing.
Copying an Address copies its pointer value and creates no lifetime obligation.
An ordinary module may encapsulate it with cleanup or a resource; raw addresses
themselves acquire no resource dependency or escape restriction.

Bytes remains the existing managed immutable byte sequence. A Bytes argument
maps to one read-only C data pointer. The generated call retains its backing
until that synchronous call returns. There is no hidden length, terminator,
encoding or mutable view. For empty Bytes, no readable byte is promised; the
pointer value does not encode its length or emptiness. The native function must
not mutate that backing. If it retains or returns the pointer, the module must
keep the original Bytes alive for every subsequent native use. Returning an
Address does not capture or infer that relationship, and managed backing must
never be passed to a freeing function.

No new memory operation is required initially. Ordinary Bytes operations provide
length, byte access, construction and comparison. Interpreting memory behind an
Address remains the module's responsibility under assumed native validity;
there is initially no Address-to-Bytes/String conversion or arbitrary memory
read/write operation. A concrete unmet interpretation is reported as a gap.

### Source imports and calls

Reuse passive foreign libraries, symbol operations, imports and generated typed
bridges on `x86_64-unknown-linux-gnu`. A symbol needs only its source signature
and C link name; remove the redundant representation/operand/outcome DSL from
this path. For example, proposed source syntax is:

```ash
import @builtin.foreign as F

pub foreign library Fixture {
    profile "x86_64-unknown-linux-gnu"
    symbol Make : Unit -> F.Address { name "fixture_make" }
    symbol Fail : Unit -> F.Address { name "fixture_fail" }
    symbol Echo : F.Address -> F.Address { name "fixture_echo" }
    symbol EchoBytes : Bytes -> F.Address { name "fixture_echo_bytes" }
    symbol Release : F.Address -> Unit { name "fixture_release" }
}
```

A client uses `import fixture as Fixture` for this passive Ash module and invokes
`perform Fixture.Make.call ()`. Each symbol retains the existing operation
identity and ordinary effect row: this call has result `F.Address` and effect
`Fixture.Make`. The generated linked host handles the required symbol effects
through the existing interpreter/build path. There is no foreign host token,
checked-call wrapper, special policy handler or new admission protocol. Ordinary
source handlers can implement these operations for tests using normal rules.

`Unit` as the whole domain means zero C arguments; a whole Address or Bytes
means one pointer argument. A flat tuple of Address/Bytes supplies arguments in
source order. Reject Unit tuple components, nested tuples and unsupported source
types rather than inventing ABI slots. Address arguments/results preserve raw
pointer values, including null. Bytes is argument-only. A Unit result maps to C
void. No scalar ABI, out-pointer, variadic, callback or struct-by-value slot is
supported initially. A signature outside this mapping is a static diagnostic.

Use a typed `extern "C"` call with the selected native link name. The declaration
asserts that its C signature and behavior match; the compiler does not verify
that assertion. Native calls retain their ordinary symbol effects, including
calls returning Unit. Pure null/equality operations do not perform memory access.
Future memory access must retain ordinary effects for mutable foreign state;
this proposal introduces no pure memory-read claim.

### Module policy and ordinary cleanup

The binding module supplies all foreign checks, conversions and lifetime
interpretation in ordinary Ash functions and handlers. Foreign behavior is
assumed, not ensured. An address result is not an allocation/ownership witness.

The small fixture allocates a fixed three-byte object in `make`, returns null
from `fail`, preserves pointer identity in `echo`, and frees only its own
allocation in `release`. Ash branches on null, compares an echo result and uses
existing scoped cleanup to call release on the successful make path, including
an ordinary early/error return. Test Bytes echo separately with its backing
retained and no release. No C numeric slot is needed. This demonstrates observed
calls and ordinary cleanup; it does not certify foreign lifetime behavior.

## Semantic delta and implementation boundary

Replace the active foreign entry, not add a permanent second FFI stack. Delete
the obsolete numeric/owner/output/window/status/host/quarantine declarations,
compiler-interpreted policy, their runtime ledgers and exclusively dependent
fixtures/tests. Shared source projections survive only until their last policy
caller is removed. Replace old policy-bearing library examples rather than keep
an executable compatibility route; Git preserves their previous implementations.

Reuse the parser/module pipeline, nominal identities, effect operations,
`src/build/bridge.rs` typed generation, ordinary host/linking and image/Core
validation. Add only Address value transport and supported call preparation to
that path. Ordinary local resources, generic cells, cleanup, handlers, work/depth
limits and unrelated generic compiler fixes remain. Existing machinery governs
artifacts originating in FFI; origin adds no admission or validation protocol.

## Affected specification areas

S2 updates [foreign declarations](../../spec/static-semantics.md#source-foreign-declarations),
[source resources](../../spec/static-semantics.md#source-resource-declarations)
and [native-owner execution](../../spec/dynamic-semantics.md#source-resource-execution-with-native-owners)
where obsolete policy is removed, plus Address value/effect rules. Preserve the
ordinary language rules; no general resource-State extension is required.
AD-0013's generated bridge/build decision remains; its foreign guard/contract
claims must be narrowed with the implementation. Current specification and
accepted decisions remain current truth until that transition is retained.

## Resulting specification truth

The implemented boundary will be the mapping above, with ordinary Ash checks and
module-authored policy. This docs-only S1 candidate establishes no new runtime
behavior and does not complete S2-S4.

## Interactions and non-goals

SQLite is a required [canary #133](https://github.com/dikini/ash-lang/issues/133).
`sqlite3_libversion(void)` and `sqlite3_sourceid(void)` fit Address returns; test
null/equality and pointer passing after implementation. Their text cannot yet be
read as String/Bytes. `sqlite3_open` and `sqlite3_prepare_v2` need C int results
and out-pointer slots, and preparation also needs a C int input: report these
unsupported shapes without a shim that hides them. Full SQLite is not required.

C-aligned primitive representations are future work discovered/prioritized as
needed, not a scheduled catalogue or initial prerequisite. No implicit numeric,
String/NUL or length conversion; no new resource-State/copy framework, native
correctness guarantee, security/host/quarantine, receipt, protected launch or
isolation requirement. Later regions/control/workers remain separate work.

## Required evidence

[S1 #131](https://github.com/dikini/ash-lang/issues/131) reviews this concrete
mapping and removal boundary before implementation.
[S2 #132](https://github.com/dikini/ash-lang/issues/132) tests passive imports,
Address/null/equality and ordinary capture, exact generated pointer/void calls,
Bytes backing, missing native effects, unsupported signatures and removal of the
old policy routes. Ordinary Core/image reconstruction must still reject malformed
data; no live pointer is encoded in an image.
[S3 #133](https://github.com/dikini/ash-lang/issues/133) supplies the fixture's
normal/null/error paths, ordinary cleanup and SQLite coverage/gap observations.
[S4 #134](https://github.com/dikini/ash-lang/issues/134) updates spec/docs and runs
the full normal workspace gate at the connected implementation/example checkpoint.
Evidence establishes observed behavior and ordinary language invariants only.
