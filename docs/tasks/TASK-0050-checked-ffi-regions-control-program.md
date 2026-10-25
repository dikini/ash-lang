# TASK-0050: Smaller foreign-library boundary

- ID: `TASK-0050`
- Status: active
- Related: [CP-0024](../proposals/CP-0024-checked-foreign-host-profile.md),
  [owned plan](plans/checked-ffi-regions-control.md)

> This task records the agreed work boundary and delivery plan. It does not
> define Ash semantics. CP-0024 records the independently reviewed, accepted
> S1 design. S1–S3 are retained; S4 specification and checkpoint work is active.

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
retained, as is S3. S4 specification and checkpoint work is active. See the owned
plan for the reuse/removal sequence and final verification owner.

## Progress

[S1 #131](https://github.com/dikini/ash-lang/issues/131) accepted CP-0024's
nominal opaque Address, synchronous read-only Bytes arguments and ordinary
symbol effects, without a new memory API. The first retirement in
[PR138](https://github.com/dikini/ash-lang/pull/138) removed the additional
artifact/receipt/protected-launch stack. The old F1-F8 plan and unfinished
checked-host/full-SQLite/deployment assignments are superseded; historical
results retain only their recorded scope.

[S2 #132](https://github.com/dikini/ash-lang/issues/132) is complete on the
milestone branch through [PR140](https://github.com/dikini/ash-lang/pull/140),
squash `f23edbb79da864eb1926cfd5ca6add36a1ed89b9`. Its tree exactly matches
reviewed head `9b1e8308`, with sole parent S1 `2766e826`. Independent review and
post-retention acceptance checked all four S2 criteria. Strict all-target,
all-feature Clippy, formatting, 47 architecture cases and 31 focused
source/import/native cases pass. The all-feature library passes 1,548 cases at
parent `8c7f29c7`; the final delta deletes only obsolete Rustdoc and blank lines.
The native evidence includes actual static/shared pointer/Bytes/void calls,
source removal, repeated activation, loader refusal and synchronous backing
observations. These focused receipts are not a complete workspace gate.

The removal preserves ordinary Cell execution, capture, cleanup, and body-free
generic resource metadata used by kind and import checking. Nonbuiltin provider
execution depended on the retired policy engine and now receives the existing
unsupported-resource diagnostic. [DN-0036](../design/DN-0036-foreign-library-and-memory-provider-experiments.md)
retained experimental evidence without adopting that execution model as product
semantics; this transition adds no general resource-State capability. Ordinary
constructor-original, canonical identity, malformed Core/image and exact/short/
retry guards remain. The [ordinary regression record](evidence/slim-ffi-s2-row-work.md)
records the causal baseline comparisons and test-accounting corrections; no
phantom work charge was added to preserve a stale test expectation.

The preparation-only `850P` calibration in
[AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
retains the executed ordinary handled-row workloads at depths 42 and 43. The
bounded census/encoding/emission diagnostic measured 2,330,800 units for
P = 3,510 at depth 43, about 28 ms, excluding native-input path checks and host
build/execution. The coefficient gives about 28% reserve over that observation;
all other ledgers, depth, overflow and exhaustion rules remain unchanged.
Normal public depth-42/43 preparation passes separately.

[S3 #133](https://github.com/dikini/ash-lang/issues/133) is retained through
[PR141](https://github.com/dikini/ash-lang/pull/141), squash
`859741fc11f417d994f6139748cc8e263176e7cd`, with reviewed tree and sole S2
parent verified. Independent review and acceptance checked all five criteria.
The additive fixture demonstrates ordinary null/length checks, cleanup on
normal completion and Stop/discard, and managed Bytes kept alive across uses.
The direct SQLite canary uses only libversion/sourceid pointer returns; C numeric
results, output-pointer storage and foreign text readback remain explicit gaps.
The three native harness tests pass: the retained pointer controls, the binding
with static/shared linkage, and direct installed SQLite getters. The binding
observes the expected `merfmrbebb` event order and all result checks; SQLite
returns nonnull, repeatable addresses without text dereference. Seven source
FFI cases, including ordinary handler override, also pass. The focused receipt
`/tmp/slim-s3-native2.log` has SHA256
`a0522c6d0940e9bbd93a2afbe7739e3b5512f6182a489e668ec50590ac33778b`;
it uses Rust 1.97.1, all features, locked dependencies, a cleared wrapper and
one job with the existing shared/nested-host caches. Native harness runtime is
9.37 seconds.

[S4 #134](https://github.com/dikini/ash-lang/issues/134) is active. The connected
specification update covers Address null/equality and selected native
invocation/return with unchanged continuation, synchronous Bytes keepalive,
ordinary handler/cleanup behavior and explicit external-call assumptions.
Current implementation inventories/tool contracts replace the retired policy
promises. The whole AD-0013 gas section remains byte-identical. The fresh normal
workspace gate, final review and retained-result verification remain pending
before M1 acceptance. Main integration retains its separate human gate.

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
