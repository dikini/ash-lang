# TASK-0050: Smaller foreign-library boundary

- ID: `TASK-0050`
- Status: active
- Related: [CP-0024](../proposals/CP-0024-checked-foreign-host-profile.md),
  [owned plan](plans/checked-ffi-regions-control.md)

> This task records the agreed work boundary and delivery plan. It does not
> define Ash semantics. CP-0024 records the independently reviewed, accepted
> S1 design; S2 implementation follows its retention and assignment.

## Dependencies

Preserve current Main language behavior and unrelated milestone work. PR138
removed the obsolete artifact/receipt/protected-launch stack under the user's
cleanup authorization without resetting the product tree to Main.
Root owns issue revisions and subsequent implementation assignments. Accepted
S1 design must precede new API implementation; earlier local pointer/reset drafts
remain unmerged and do not supply accepted technical decisions.

## Agreed work boundary

Initially support bytes and opaque raw C addresses. The binding module explicitly
interprets memory and lifetime and supplies all foreign contracts, checks and
conversions in ordinary Ash. The compiler performs only ordinary language checks
and supported representation/ABI calls. A type without an Ash representation is
not usable through FFI; no implicit numeric conversion is introduced.

Foreign-backed and local resources share existing abstract resource rules.
Reuse ordinary resources, memory, cleanup and handlers; add no separate FFI
lifecycle or copy protocol. Foreign behavior remains assumed, not ensured.
Default to reuse or removal. If an addition is uncertain, presume overengineering
and simplify it; only a concrete missing capability justifies a new mechanism.
SQLite is a required canary for coverage, differences and concrete gaps, without
requiring full SQLite implementation initially. C-aligned primitive needs are
future work discovered and prioritized as needed, not a fixed phase/catalogue.

This records the user's scope, not new normative semantics. S1 reviewed the
technical API and memory mapping through [CP-0024](../proposals/CP-0024-checked-foreign-host-profile.md);
the accepted proposal, rather than this task, governs implementation.

## Work

Overall [program #51](https://github.com/dikini/ash-lang/issues/51) still tracks
later [M2 #53](https://github.com/dikini/ash-lang/issues/53),
[M3 #54](https://github.com/dikini/ash-lang/issues/54) and
[M4 #55](https://github.com/dikini/ash-lang/issues/55). Their regions, retained
control and worker scope remains unchanged and later; it is not required for the
initial M1 FFI delivery. Each later milestone owns its scoped design gates.

- [S1 #131](https://github.com/dikini/ash-lang/issues/131): settle the bytes/raw-address interface and minimum reuse/removal design.
- [S2 #132](https://github.com/dikini/ash-lang/issues/132): implement the reviewed slim representation/ABI calls in the existing path.
- [S3 #133](https://github.com/dikini/ash-lang/issues/133): demonstrate ordinary Ash binding checks and existing cleanup/handlers.
- [S4 #134](https://github.com/dikini/ash-lang/issues/134): integrate documentation, focused tests and the normal workspace gate.

Retain [SQLite canary #133](https://github.com/dikini/ash-lang/issues/133) in S1
design and S3/S4 integration. After S1 design, exercise representable calls and
report concrete unsupported cases/differences. The small fixture complements it. Full SQLite
coverage and numeric representation delivery are not required now; discovered
C-aligned representation gaps are future work to prioritize as needed.

The obsolete artifact/launch retirement is delivered by PR138. S1 has reviewed
and accepted the concrete Address/Bytes mapping in CP-0024. S2 implementation is
next after design retention and assignment. See the owned plan for the reuse
and removal sequence and final verification owner.

## Progress

The planning/issue revision was delivered by
[PR135](https://github.com/dikini/ash-lang/pull/135), with the SQLite canary
clarification delivered by [PR136](https://github.com/dikini/ash-lang/pull/136).
[Parent #52](https://github.com/dikini/ash-lang/issues/52) tracks the revised work.
The user subsequently authorized removal of unnecessary code. The first slice
retired the artifact/receipt/protected-launch build stack in
[PR138](https://github.com/dikini/ash-lang/pull/138), preserving ordinary builds
and runtime machinery. S1 accepted nominal opaque Address, synchronous
read-only Bytes arguments and ordinary symbol effects, without a new memory API.
This S1 documentation delivery implements no new API or native execution.

The old F1-F8 workplan and checked-host/full-SQLite/deployment assignments are
superseded. Items #57-64 and the premature #130 are deprecated as active work.
Previously completed results retain their historical completion and recorded
scope; unfinished old criteria are not claimed satisfied.

S2 is in progress. The connected image restoration tests pass four cases, and
the generated pointer/Bytes/void fixture passes static and shared linking,
repeated execution after source removal, exact native call order and loader
refusal before calls. The full normal workspace gate and final review remain
pending; these focused results do not complete S2 or M1 acceptance.

The preparation calibration retained the actual executed ordinary handled-row
fixture at depths 42 and 43. A bounded diagnostic carried the normal source
census through complete image encoding and Rust emission: 2,181,566 units for
P = 3,494 at depth 42 and 2,330,800 for P = 3,510 at depth 43, about 28 ms for
the latter. Native-input path checks and host building/execution were outside
that diagnostic. Independent review accepted the preparation-only `850P`
coefficient in [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
with about 28% reserve over the depth-43 observation. Normal public preparation
regressions, exhausted-budget checks and native execution remain separate gates.

The current WIP checkpoint also passes the five public native-preparation cases
(including the normal depth-42/43 workload), seven slim FFI cases and eight
syntax plus eight admission cases. A broader library run exposed ordinary
regressions and a small-stack overflow before completion. Restoring the ordinary
polymorphic recursive-initializer validation branch makes the two generic Cell
acquisition cases pass; summary authentication and remaining failures are still
under repair. This checkpoint is a draft, not an accepted delivery or Main gate.

The removal preserves ordinary Cell execution and body-free generic resource
metadata used by kind and import checking. Nonbuiltin provider execution used
the retired foreign policy engine and now receives the existing unsupported
resource diagnostic. [DN-0036](../design/DN-0036-foreign-library-and-memory-provider-experiments.md)
retained experimental evidence without adopting that execution model as product
semantics; this transition does not add a general resource-State capability.

## Verification

For S1, independently review the proposed mapping, removal boundary and SQLite
gaps; check affected documentation links and authority. PR138 recorded the
retirement workspace check and focused ordinary regressions. S1 runs no compiler
or native program.
The developer owns the full normal gate at the integrated slim path plus example
checkpoint before M1 acceptance and Main integration.

## Discoveries

Existing foreign declarations contain compiler-interpreted policy. Existing
cleanup, handlers and memory/value abstractions are the reuse baseline; no new
resource-State or copying subsystem is assumed necessary.

## Deviations

This smaller boundary replaces the
[prior workplan](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/plans/checked-ffi-regions-control.md).
The earlier planning revision did not remove product code. The separately
authorized retirement now removes the obsolete launch stack without resetting
Main or completing the earlier gates.
