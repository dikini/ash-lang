# TASK-0058: Pinned worker network

- ID: `TASK-0058`
- Status: active
- Related: [CP-0027](../proposals/CP-0027-pinned-workers-and-copied-channels.md), [CP-0028](../proposals/CP-0028-checked-functional-network-ledger.md), [AD-0017](../decisions/AD-0017-pinned-worker-host-and-transport.md), [DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md), [M4 issue #55](https://github.com/dikini/ash-lang/issues/55)

> This task organizes work. It does not define Ash semantics.

## Dependencies

M1–M3 are complete on Main at `67c79ddc32a813cc0c9ddab2962f9e2aa849b028`;
their acceptance is recorded in [#51](https://github.com/dikini/ash-lang/issues/51).
N1 contract and host/channel choice were independently reviewed at
`b296e17ce9e4f1760ce73df4f4716ef0c0fb2093` and are accepted in CP-0027 and
AD-0017. Product reliance additionally needs the assigned bounded preservation
evidence. The
[owned execution plan](plans/pinned-worker-network.md) sequences the original
[N1–N6 issues](https://github.com/dikini/ash-lang/issues/55) and their gates.
The checker contract in CP-0028 and its bounded proof assignment were
independently reviewed at `94c0be0375d19f8e60900d5d77be2f5caa746eb0` and the
transition is accepted. Its proof and actual Core reconstruction gate precede
N4/N5 release reasoning. N4 also requires a separately accepted, sound codec
extension before codec-dependent completion or release permission. Main
integration requires separate authorization.

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

The N1 source/Core contract and host/channel choice were retained on the M4
milestone branch at `993be1e7c932d1db20e62a706df5dab26698fa99` and its
[issue #76](https://github.com/dikini/ash-lang/issues/76) acceptance was read
back and closed. No product implementation is claimed. N-core, N-proof and
N-final gates remain pending.
The developer owns acceptance notes after retention; the orchestrator assigns
each next checkpoint and integration action. N3 contract acceptance is
recorded without claiming proof, checker implementation or issue acceptance.
The N3 proof and N4 codec, composition and release obligations remain open.

## Verification

For the N3 contract slice check artifact authority, relevant links and cases,
independently review adoption bookkeeping and verify the retained result. For
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
