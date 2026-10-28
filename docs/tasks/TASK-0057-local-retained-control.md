# TASK-0057: Local retained control

- ID: `TASK-0057`
- Status: active
- Related: [DN-0056](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md),
  [CP-0026](../proposals/CP-0026-scoped-owned-continuation-storage.md)

> This task organizes work. It does not define Ash semantics. C4 is active
> under the accepted proposal; C2 and C3 are retained and accepted.

## Dependencies

[M3 #54](https://github.com/dikini/ash-lang/issues/54) covers C1–C5. The
starting product baseline is `3ae29ab980080d0c58c19e0e7ddb8f0a309ba723`;
[R5 #70](https://github.com/dikini/ash-lang/issues/70) records region product
acceptance. C1 requires independently reviewed semantics, a bounded ownership
and completion model and the frozen proof gate. C2 requires accepted C1 and its
proof gate. C3 requires reviewed C2 carriers and its own bounded analysis proof.
C4 requires connected C2/C3. C5 retains the complete integrated evidence and
the separate Main gate.

## Work

Follow the [task-owned execution plan](plans/local-retained-control.md). Its
sequences and implementation candidates have no semantic authority. C1 fixes
the store, move, interpretation, branch authority, current-consumer, support
and failure contracts. The model tests that contract and returns discrepancies
to the proposal before acceptance. Later deliveries cover store execution,
checked drain analysis, scheduling libraries and milestone closure without
narrowing the original issue criteria.

## Progress

CP-0026 is accepted. Its bounded model and correspondence passed independent
source review and the frozen integration build; the
[record](evidence/local-retained-control/c1-model/README.md) identifies the
inputs and limits. C1 was retained and independently verified at
`6d530614d426db3f31fd0e9fe1f01d12399f78c9` by
[PR #160](https://github.com/dikini/ash-lang/pull/160); [C1 #71](https://github.com/dikini/ash-lang/issues/71)
is closed. The reviewed C2 store delivery was retained at
`e12d4242a35ffe01ccd9d3e90342992e77f94613` by
[PR #161](https://github.com/dikini/ash-lang/pull/161). Internal fixtures exercise private root,
Retain and structural Continue through a store frame, including the current
consumer's adapter and a running cleanup. Source-derived capture checks cover
an imported continuation helper, enclosing and captured support, and actual
interpreter conflicts. A separate focused control inspection checks saved
cuts at Retain, including cuts never continued and later checkpoints; real
restoration checks the current consumer's interpreter.
An ordinary Probe can be intercepted by a source handler; internal checks
exercise its driver restriction and actual Store-provider selection. Image
codecs preserve Store/Root/Retain carriers and generic Continue round-trips.
C3's normal-return analysis and bounded proof were retained by
[PR #162](https://github.com/dikini/ash-lang/pull/162). Focused checks
exercise a drain before outer-discard close, and reject both a missing drain and
new retained work after a drain. A branch that constructs a fresh answer under
an allocator handler owned by its capture also passes the focused query. When
the allocator handler is outside the capture, the cleanup's distinct forwarding
handler changes the selected interpretation and admission rejects it under the
accepted contract. Conservative case tracking can reject a safe program that
matches an earlier branch result after another checkpoint.

A source-derived linked Core fixture also checks reuse of an aggregate and its
payload computation. Each case assignment now clears older aggregate origins
before their payloads can be projected, and Resume drops the returned origin.
The bounded correspondence passed independent source review, and its frozen
[proof run](evidence/local-retained-control/c3-model/README.md) completed.
Its receipt passed independent audit. Linked validation now runs the release
analysis after the carrier, type and scope checks. Public source execution
drains recursive and imported continuations and an outer-discard cleanup;
undrained, stale, intercepted and unknown-result paths are refused. Identity
and folding transformations and decoded images are revalidated. The image
test also rejects a changed Probe match that would permit an undrained close.
Linked validation rejects a same-typed cleanup callback replacement that leaves
retained work, after both identity and folding transformations. Control
dispatch separates its stack work without changing the limits or charges; the
64 KiB, 384-level abandonment regression completes with 4,864 work units and
preserves exact-budget failure and retry behavior.

The standalone Core validator retains its 983,040 work limit. The public
source driver's input-sized allowance admitted the outer-discard fixture at
1,309,582 of 78,225,000 units. Its encoded image used 1,355,242 of 1,753,834
startup units. These are measurements of those paths, not a general bound.
The connected seven-stage workspace gate passed on reviewed `12df10ef`, and
its tree was independently verified at retained milestone commit
`d256bef288ac6b828e475c9dcaaf710812405b7a`. The original
[C2 #72](https://github.com/dikini/ash-lang/issues/72) and
[C3 #73](https://github.com/dikini/ash-lang/issues/73) criteria are accepted.

C4 is developing ordinary scheduling policy in
[`libraries/scheduling.ash`](../../libraries/scheduling.ash). The first named-root
coroutine case selects P while Q remains retained, observes R's continuation,
and drains Q before the store closes. Its public-driver result records P's
answer and the event order. A second case yields repeatedly during drain; its
event order requires each new key to resume the next suffix and complete the
branch. The cooperative queue requeues each fresh key behind the other ready
work, and a lost-key fixture reaches the retained-release refusal. An empty
queue runs with an allocator handler enclosing the Store. The host-default-only
variant remains a conservative release refusal. Calls now defer control entry
until their strict arguments have value alternatives, preserving the existing
delivery prefix for value-revision replay. The gas example writes its accounting
before each explicit guard: the false guard continues, and the true guard
yields so Q can observe the committed value before P resumes. Suspended cleanup
and checkpoints around resume remain.
C4, C5 and the final integrated and Main gates remain open.

## Verification

Use focused positive, negative and regression checks for each changed behavior
and affected callers. The model and C3 analysis each require a reviewed frozen
scoped [AD-0012](../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
gate. The connected C2/C3 workspace checkpoint is complete. Because C4 changes
shared capture analysis, the product developer owns a fresh seven-stage Cargo
checkpoint for the complete C4 candidate before its integration. The final
integrated C5 checkpoint remains required and may serve as the pre-Main gate
only while inputs remain equal. Record exact refs, source/configuration/tool
pins and receipts; transfer evidence only with demonstrated equality. Main
merge remains a separate human gate.

## Discoveries

Current control already moves one-shot captures and tracks cleanup completion;
generic cells do not own them. Current region support determines storage
validity and release, not completion transfer. Existing outer resource aliases
can remain shared across sequential branches while their scope owner stays
unique. DN-0056's drain argument is paper evidence; the C3 model and reviewed
correspondence above check the selected bounded analysis.

An optional imported Cell guard returned `type.internal` during source checking
in the connected P/Q gas specimen; a one-branch comparator passed. The specimen
and helper are `c4-gas-guard-v1.ash` and `c4-gas-guard-library-v1.ash` in the
shared C4 evidence directory. Its `c4-gas-guard-v1.log` has SHA-256
`d5dcc8c6acb6d89d18d1cff61cff9dcab85ce8c0101a1ac13134cb1eb5519b47`.
The delivered gas policy uses inline accounting and makes no general claim
about imported Cell helpers.

## Deviations

The recursion examples in [syntax](../../spec/syntax.md),
[name resolution](../../spec/name-resolution.md),
[dynamic semantics](../../spec/dynamic-semantics.md), and the
[tool guide](../tools/ash.md) now use `saved` in place of the reserved
`retain` keyword. Their executable fixtures use the same name.

Return any semantic or proof gap to CP-0026 and DN-0056 before product
delivery; keep original issue criteria open until their full scopes are retained
and verified.
