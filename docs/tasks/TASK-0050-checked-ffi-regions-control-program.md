# TASK-0050: Smaller foreign-library boundary

- ID: `TASK-0050`
- Status: active
- Related: [CP-0024](../proposals/CP-0024-checked-foreign-host-profile.md),
  [owned plan](plans/checked-ffi-regions-control.md)

> This task records the agreed work boundary and delivery plan. It does not
> define Ash semantics or authorize implementation. Technical interface and
> memory mapping remain proposed in CP-0024 pending S1 design review.

## Dependencies

Preserve current Main specification truth and the milestone product tree.
Root owns issue revisions and subsequent implementation assignments. S1 design
review must precede source implementation; earlier local pointer/reset drafts
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

This records the user's scope, not new normative semantics. S1 must review the
technical API and memory mapping in [CP-0024](../proposals/CP-0024-checked-foreign-host-profile.md)
before implementation; this task chooses neither.

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

S1 design review is next. S2-S4 remain held, not execution assignments. See the
owned plan for the bounded completion conditions.

## Progress

The planning/issue revision was delivered by
[PR135](https://github.com/dikini/ash-lang/pull/135), with the SQLite canary
clarification delivered by [PR136](https://github.com/dikini/ash-lang/pull/136).
[Parent #52](https://github.com/dikini/ash-lang/issues/52) tracks the revised work.
S1 design review is next; S2-S4 implementation remains held. No API, native
execution or product implementation is accepted by those documentation changes.

The old F1-F8 workplan and checked-host/full-SQLite/deployment assignments are
superseded. Items #57-64 and the premature #130 are deprecated as active work.
Previously completed results retain their historical completion and recorded
scope; unfinished old criteria are not claimed satisfied.

## Verification

For this revision, check the docs-only diff, links, consistent S1-S4 issue map,
proposed technical status and independent review. No compiler or native run is
required. Product verification belongs to later assigned implementation stages.

## Discoveries

Existing foreign declarations contain compiler-interpreted policy. Existing
cleanup, handlers and memory/value abstractions are the reuse baseline; no new
resource-State or copying subsystem is assumed necessary.

## Deviations

This smaller boundary replaces the
[prior workplan](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/plans/checked-ffi-regions-control.md).
It does not reset Main, remove product code or complete the earlier gates.
