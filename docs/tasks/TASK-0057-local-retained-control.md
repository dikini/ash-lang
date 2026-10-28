# TASK-0057: Local retained control

- ID: `TASK-0057`
- Status: active
- Related: [DN-0056](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md),
  [CP-0026](../proposals/CP-0026-scoped-owned-continuation-storage.md)

> This task organizes work. It does not define Ash semantics. C2 is active
> under the accepted proposal; public release still depends on C3.

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
is closed. C2 store work is active. Internal fixtures exercise private root,
Retain and structural Continue through a store frame, including the current
consumer's adapter and a running cleanup. Source-derived capture checks cover
an imported continuation helper, enclosing and captured support, and actual
interpreter conflicts. A separate focused control inspection checks saved
cuts at Retain, including cuts never continued and later checkpoints; real
restoration checks the current consumer's interpreter. This C2 work remains
subject to independent review and the remaining acceptance checks.
An ordinary Probe can be intercepted by a source handler; internal checks
exercise its driver restriction and actual Store-provider selection. Image
codecs preserve Store/Root/Retain carriers and generic Continue round-trips,
while public Store release remains rejected until C3.
C2–C5 and the connected full-workspace and Main gates remain open.

## Verification

Use focused positive, negative and regression checks for each changed behavior
and affected callers. The model and C3 analysis each require a reviewed frozen
scoped [AD-0012](../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
gate. The next full Cargo workspace checkpoint is the connected C2/C3 runtime
ready for C4; the product developer owns it. A final integrated gate precedes
Main and may serve as the pre-Main gate only while inputs remain equal. Record
exact refs, source/configuration/tool pins and receipts; transfer evidence only
with demonstrated equality. Main merge remains a separate human gate.

## Discoveries

Current control already moves one-shot captures and tracks cleanup completion;
generic cells do not own them. Current region support determines storage
validity and release, not completion transfer. Existing outer resource aliases
can remain shared across sequential branches while their scope owner stays
unique. DN-0056's
drain argument is paper evidence, not a checked analysis or implementation.

## Deviations

The reserved `retain` keyword requires renaming the existing recursion
examples in [syntax](../../spec/syntax.md),
[name resolution](../../spec/name-resolution.md),
[dynamic semantics](../../spec/dynamic-semantics.md), and the
[tool guide](../tools/ash.md) when C5 updates current documentation. The
executable recursion fixtures and their embedded mirrors are renamed with the
parser change.

Return any semantic or proof gap to CP-0026 and DN-0056 before product
delivery; keep original issue criteria open until their full scopes are retained
and verified.
