# Local retained-control model

These bounded C1 ownership and C3 drain models support
[DN-0056](../DN-0056-scoped-continuation-retention-and-library-scheduling.md).
The historical [CP-0026](https://github.com/dikini/ash-lang/blob/ea2a7ffadefb0f485a9c8e0009975a47db5c6865/docs/proposals/CP-0026-scoped-owned-continuation-storage.md)
records the transition; the [specification](../../../spec/README.md) defines
language semantics. The models do not. The
[C1 correspondence map](correspondence.md) states its premises, proved claims
and reviewed product correspondence.

| Module | Scope |
| --- | --- |
| [Ownership](Ownership.lean) | Finite owner inventories, transfer and restore transitions, completion, support, generations and failure accounting. |
| [OwnershipExamples](OwnershipExamples.lean) | Concrete positive and negative traces over those transitions. |
| [DrainSafety](DrainSafety.lean) | Finite focused-State normal returns, port cases and the checked Store-close predecessor. |
| [WorkerChannel](WorkerChannel.lean) | Bounded two-worker ownership, copied FIFO channels, held-delivery completion, endpoint closure and registration accounting. |
| [NetworkLedgerTransitions](NetworkLedgerTransitions.lean) and [NetworkLedgerChecker](NetworkLedgerChecker.lean) | Finite ledger laws and definition-bound modeled checking. |
| [NetworkLedgerHistoryControl](NetworkLedgerHistoryControl.lean) | Conditional currentness and history through modeled control steps. |
| [NetworkLedgerCoverageClosure](NetworkLedgerCoverageClosure.lean) | Conditional correspondence between modeled ledger traces and protocol coverage. |

The C1 candidate passed independent source review and a frozen scoped
[AD-0012](../../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
integration build. The [gate record](../../tasks/evidence/local-retained-control/c1-model/README.md)
pins its sources, compiler, review and reports. C1's retained result was
independently verified.

The C3 [drain correspondence](drain-correspondence.md) records the concrete
control, value and completion premises used by the bounded analysis. Its
reviewed source completed a separate frozen [gate](../../tasks/evidence/local-retained-control/c3-model/README.md);
its receipt passed independent audit. Linked validation uses the drain analysis;
the connected C2/C3 checkpoint is retained and accepted.

The conditional M4 worker/channel model has a reviewed frozen
[source gate](../../tasks/evidence/pinned-worker-channel-proof/README.md).
Its [correspondence map](worker-channel-correspondence.md) states the runtime,
C3, native binding and transport premises that remain outside the model proof.
This prerequisite does not establish successful native shutdown, full N2
acceptance or current Ash language semantics.

The N3 ledger model and its [correspondence](network-ledger-correspondence.md)
record the assumptions needed to relate checked linked Core to the finite model.
They do not establish peer authentication, exclusive control or network release.

## Retained product evidence

- **C1 ownership.** [PR #160](https://github.com/dikini/ash-lang/pull/160)
  retained `6d530614d426db3f31fd0e9fe1f01d12399f78c9`. The frozen C1 evidence
  has SHA-256
  `fa3462c847fe90766c33ef6d069dceaf5a3febec0b1cb78d490efbf06d46ed0b`.
- **C2 Store and moves.** [PR #161](https://github.com/dikini/ash-lang/pull/161)
  retained `e12d4242a35ffe01ccd9d3e90342992e77f94613`. The
  [runtime tests](../../../src/eval/machine_retained_tests.rs) cover
  preparation, generation, one-shot restoration and disposal.
- **C3 release.** [PR #162](https://github.com/dikini/ash-lang/pull/162)
  retained `d256bef288ac6b828e475c9dcaaf710812405b7a`. The frozen C3 evidence
  has SHA-256
  `717fea322b63c90626938c0c98fadf3cbb2f4735a41959542fb1003ebafb3a90`.
  The connected seven-stage checkpoint was verified at that retained tree.
- **C4 libraries.** [PR #163](https://github.com/dikini/ash-lang/pull/163)
  retained `73f6304a69183682a94d85aa81f9b1a88c21ef5e`. The
  [scheduling tests](../../../tests/scheduling.rs) cover selection, queueing,
  gas, resume and repeated cleanup. Its fresh seven-stage
  [checkpoint audit](https://github.com/dikini/ash-lang/pull/163#issuecomment-6475295972)
  and [retained-result review](https://github.com/dikini/ash-lang/pull/163#issuecomment-6475359212)
  are separate records.

The [capture checks](../../../src/core/capture.rs) include
`retained_drain_tracks_actual_result_cases_and_fresh_probes`, the driver and
post-resume suffix checks, and support and interpreter negatives. The
[public tests](../../../tests/retained_control.rs) reject unproved drain paths
and exercise ordinary Probe interception. The
[linked validation tests](../../../src/core/validate.rs) reject a same-typed
cleanup callback substitution and recheck transformed control. The runtime
`retained_move_prepares_storage_before_taking_either_owner` test covers failed
preparation and retry without a partial move. Images are independently decoded
and validated before execution. These tests and reviewed correspondences
connect the bounded models to the implementation; the Lean results do not
mechanically prove the compiler or evaluator. [Issue #165](https://github.com/dikini/ash-lang/issues/165)
records two analysis limitations and their reproductions. The
[C5 checkpoint](https://github.com/dikini/ash-lang/issues/75#issuecomment-6476014597)
and [separate Main handoff](https://github.com/dikini/ash-lang/issues/54#issuecomment-6476014971)
remain open.

The bounded [one-way completion source gate](../../tasks/evidence/pinned-one-way-proof/README.md)
registers `OneWayCompletion` after the four retained parent modules. Its model
proofs and implementation correspondence have separate acceptance obligations.
