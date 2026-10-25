# Lexical region finite model

This bounded sequential model supplies R1 evidence for accepted
[CP-0025](../../proposals/CP-0025-lexical-region-construction.md), under
[TASK-0055](../../tasks/TASK-0055-lexical-regions.md) and its
[execution plan](../../tasks/plans/lexical-regions.md). It defines no current Ash
semantics. The contract is accepted for transition; current-head review,
milestone retention, retained verification and R1/R2 issue acceptance remain
pending. Product R3 is held until the accepted contract and matched proof are
retained and verified.

The reviewed eight-module candidate passed the frozen
[AD-0012](../../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
integration gate with 195 axiom reports. All eight modules used independently
validated cached artifacts; no module was freshly compiled in that gate.
The exact reviewed sources and generated registrations have been transferred
here. [Evidence](evidence.md) records the pins and pending retention boundary.

## Modules and invariant

| Module | Responsibility |
| --- | --- |
| [RegionModel](RegionModel.lean) | Finite owner/object state, fixed allocator association, pending backing, initialization/publication and component preservation. |
| [RegionControl](RegionControl.lean) | Whole/inline views, ordered cleanup, targeted availability and owner/control updates. |
| [RegionFrames](RegionFrames.lean) | Saved service-frame ownership and context preservation. |
| [RegionTransitions](RegionTransitions.lean) | Admitted concrete machine steps, local release guards and trace preservation. |
| [RegionProperties](RegionProperties.lean) | Fixed-pair, context, pending identity and distinct-registration consequences. |
| [RegionCoherence](RegionCoherence.lean) | Aggregate Coherent step/trace preservation, provider contexts and no returned live cursor. |
| [RegionExamples](RegionExamples.lean) | Cyclic graphs, caller/explicit placement and independent inline access examples. |
| [RegionMachineExamples](RegionMachineExamples.lean) | Full admitted setup, construction, refusal, cleanup, capture/resume/discard and bulk-close traces and negatives. |

`Coherent` combines `Safe`, retained preparing/live provider-context validity
and absence of returned-but-live cursors. `transition_coherent_preserves` and
`trace_coherent_preserves` derive it from concrete updates and local premises.
No transition assumes its successor is coherent. Component `Valid`, `Invariant`
and `MachineSafe` predicates are not substitutes for the aggregate theorem.

The [correspondence and assumptions](correspondence.md) map the model to the
accepted transition's source/Core contract, required examples and explicit proof limits.
Physical allocator correctness and lexical/compiler correspondence remain
separate obligations. No native-memory, whole-compiler or product implementation
claim follows from finite preservation.

Use the [existing integration runner](../../project/proof-tooling.md) for frozen
verification. [check.sh](check.sh) lists the eight modules in productive order;
[lean-toolchain](lean-toolchain) pins Lean 4.33.1. Do not repeat the gate at
identical inputs merely to replace valid cache reuse with fresh compilation.
