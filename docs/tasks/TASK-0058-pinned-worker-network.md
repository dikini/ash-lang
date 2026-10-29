# TASK-0058: Pinned worker network

- ID: `TASK-0058`
- Status: active
- Related: [CP-0027](../proposals/CP-0027-pinned-workers-and-copied-channels.md), [DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md), [M4 issue #55](https://github.com/dikini/ash-lang/issues/55)

> This task organizes work. It does not define Ash semantics. The proposed
> contract is not yet accepted and cannot authorize product implementation.

## Dependencies

M1–M3 are complete on Main at `67c79ddc32a813cc0c9ddab2962f9e2aa849b028`;
their acceptance is recorded in [#51](https://github.com/dikini/ash-lang/issues/51).
N1 requires independent contract, platform and proof review, accepted semantic
proposal and converged host/channel decision before product reliance. The
[owned execution plan](plans/pinned-worker-network.md) sequences the original
[N1–N6 issues](https://github.com/dikini/ash-lang/issues/55) and their gates.
An accepted checker contract and bounded proof assignment precede checker
product work; its proof and actual Core reconstruction gate precede N4/N5
release reasoning. Main integration requires separate authorization.

## Work

Retain all original criteria in [#76](https://github.com/dikini/ash-lang/issues/76)
through [#81](https://github.com/dikini/ash-lang/issues/81). Prepare, review
and adopt N1; deliver worker/channel ownership and one-way completion; prove
the functional ledger and restricted checker; implement checked bidirectional
completion and two-phase shutdown; then demonstrate the cross-milestone program,
update the specification, verify and close. The linked plan assigns each
original acceptance obligation and verification boundary. Partial slices do
not close a whole criterion.

## Progress

N1 proposal and host/channel decision candidate are prepared for review. No
semantic acceptance, product implementation, independent review, retained
verification, or N1–N6 criterion is claimed. N-core, N-proof and N-final full
gates remain pending. The developer owns acceptance notes after retention; the
orchestrator assigns each next checkpoint and integration action.

The proposed source/Core entry, endpoint and completion representation in
CP-0027 is awaiting independent review together with the host/channel decision
candidate. Review must cover admission, capability injection, authenticated
envelope origin and failure/settlement interfaces before N2 authorization.
The N3 checker semantics require separate acceptance before checker work.

## Verification

For N1 check artifact authority, relevant links and cases, and independently
review the proposal, decision candidate and bounded proof assignments. For
product slices freeze source/configuration inputs, run focused positive,
negative, regression, proof and native checks required by the governing
artifacts, obtain independent review and verify actual retained commits. Run
fresh full workspace gates at the plan's checkpoints and before Main, reusing a
receipt only under its documented equality conditions. Use one Cargo job and
the compatible shared cache under the project workflow.

## Discoveries

Copying finite bytes removes the need for a general object-graph transfer in
N1. It does not authenticate a completion message, prove native visibility,
or discharge local retained-control completion. The live N6 issue requires
SQLite coverage and a gap assessment at the ordinary byte/pointer FFI boundary;
historical checked or isolated FFI modes are not prerequisites.
The analysis limitations in [#165](https://github.com/dikini/ash-lang/issues/165)
remain visible; this task neither adds a language restriction nor weakens the
existing checks to work around them.

## Deviations

None. Return any source/Core or control-envelope semantic gap found in review
to the proposal before implementation.
