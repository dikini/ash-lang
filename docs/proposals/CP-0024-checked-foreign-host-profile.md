# CP-0024: Smaller foreign-library boundary

- ID: `CP-0024`
- Status: proposed
- Related: [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [TASK-0050](../tasks/TASK-0050-checked-ffi-regions-control-program.md)

> The user agreed the smaller responsibility boundary on 2026-10-24. Detailed
> interface and memory mapping remain design work. This proposal is not current
> Ash and does not authorize implementation. The previous checked-host proposal
> under this ID is [retained in Git](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/proposals/CP-0024-checked-foreign-host-profile.md).

## Current behavior

Main `7949b6d9` contains generated typed native bridges, managed byte values,
ordinary effects, cleanup and handlers. Its foreign declarations also carry
compiler-interpreted owner, outcome and window policy. The milestone contains
additional checked-host work. Neither existing implementation is automatically
compliant with the smaller boundary. This plan revision changes no product code
or normative specification.

## Proposed behavior

Initially expose only bytes and an opaque raw C address. The importing module
explicitly interprets foreign memory and lifetime. Passing an address does not
by itself establish ownership, validity, liveness or permission to free memory.
Foreign behavior remains assumed; the compiler cannot ensure it.

Contracts, checks and conversions belong in ordinary Ash binding-module code.
The compiler performs ordinary language type/effect/resource checks and
supported representation/ABI call generation. A declaration that causes the
compiler to implement a foreign policy is not ordinary Ash checking merely
because it is written in a `.ash` file.

Foreign-backed and local resources use the existing abstract resource rules.
First reuse ordinary cleanup, handlers and existing memory/value abstractions.
Copying is ordinary conversion or memory reuse, not a new foreign protocol.
Do not require a new generic-State facility, copy subsystem or pointer API before
showing that the existing abstractions are insufficient.

[S1 #131](https://github.com/dikini/ash-lang/issues/131) must resolve the source address representation, null/equality operations,
byte backing and native-call mapping, ordinary effects, and explicit module
assumptions for reads or retained addresses. Bytes is a managed sequence, not
an assumed by-value C ABI. An address is not an implicit Int or Bytes conversion.
These details remain proposed until reviewed; this text selects no builtin name,
new resource extension, hidden length/NUL conversion or copy edge behavior.

## Semantic delta

Replace the planned checked-host responsibility split with module-authored
ordinary checks and a smaller representation/call boundary. Decide the minimum
changes to the existing product during S1, including inherited compiler policy
that must leave the selected path. Do not create a permanent parallel FFI stack.

## Affected specification areas

The eventual implementation must update
[foreign declarations](../../spec/static-semantics.md#source-foreign-declarations),
[source resources](../../spec/static-semantics.md#source-resource-declarations)
where affected, and
[execution](../../spec/dynamic-semantics.md#source-resource-execution-with-native-owners).
Those current rules remain normative until a product transition is implemented
and integrated.

## Resulting specification truth

After the reviewed implementation and integration, the supported boundary will
match the agreed responsibilities and S1's accepted interface design. This
planning revision alone establishes no new language or runtime behavior.

## Interactions

Reuse AD-0013's generated build/call machinery and ordinary Ash resource rules.
Existing work remains available in Git; no reset or product removal is part of
this documentation checkpoint.

## Non-goals

No C numeric primitive types or implicit conversions. Explicit conversions such
as int64 to Int would belong in ordinary Ash libraries if the needed
representations later exist. C-aligned primitive representations are future
work discovered as needed, not a scheduled type catalogue or an initial
bytes/address prerequisite. Full SQLite coverage, security/host/quarantine
mechanisms, receipts, protected launch and isolation are outside this delivery.
Earlier F1-F8 planning gates are superseded as active assignments, not completed.

## Required evidence

[S1 #131](https://github.com/dikini/ash-lang/issues/131) reviews the address/byte design and minimum reuse/removal plan.
[S2 #132](https://github.com/dikini/ash-lang/issues/132), [S3 #133](https://github.com/dikini/ash-lang/issues/133) and [S4 #134](https://github.com/dikini/ash-lang/issues/134) later
provide one small native-call example with ordinary Ash normal/error handling,
ordinary cleanup, focused type/effect/resource and representation tests, matching
documentation, and the normal workspace gate. They establish only observed
behavior and ordinary language invariants, not arbitrary foreign correctness.

SQLite remains a required [canary #133](https://github.com/dikini/ash-lang/issues/133)
during design and integration. After S1 design, exercise currently representable
calls and report
concrete unsupported cases, differences and gaps, with contracts/checks in
ordinary Ash. The small native fixture complements this canary; it does not
replace it. A discovered representation gap is reported for later prioritization,
not an automatic machinery change or a requirement to deliver numeric types now.
