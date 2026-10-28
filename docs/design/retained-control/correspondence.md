# C1 model correspondence and limits

This map is part of the [DN-0056 proof assignment](../DN-0056-scoped-continuation-retention-and-library-scheduling.md#c1-bounded-ownership-and-completion-proof-assignment).
[CP-0026](../../proposals/CP-0026-scoped-owned-continuation-storage.md) records
the accepted transition implemented on the M3 milestone. The model is evidence
for its selected transitions, not a proof of the compiler or evaluator.

## Representation and assumptions

The model has one store activation, one sequential executor, finite lists of
slots and structural owners, and natural-number identities and generations.
It proves properties of each finite trace; it is not an exhaustive checker for
a globally finite state space. `Capture.owners` is the abstract inventory of a
branch's actual recursively owned closure, including nested clause, resource
and cleanup completion owners. The inventory is assumed complete and uses
distinct identities. Nested phases and cleanup phases represent their actual
states, and `savedResult` is an opaque body-result witness carried with the
capture. The model does not reconstruct a frame forest or execute action bodies.
The completed and disposed identity lists are ghost history for the uniqueness
argument; the proof does not require a runtime to retain those lists.

`Admit` requires the branch owner, excludes the store's own owner, checks that
outside support and completion are still represented, requires disjointness
from every fixed outside owner even when it is not referenced by the capture,
checks the fixed interpreter, and rejects an exported
branch-local owner. This is a local structural premise, not a new source
permission algebra. Source and linked Core checks derive these facts from
actual captures, values, evidence, control, and enclosing scopes.
`adminSuffixClear` is a local premise on the retain macro-step: the authenticated
private checkpoint clause has no skipped required suffix. It is not a source
assertion or a runtime permission. The implementation checks actual control
before consuming the hidden owner.

The store and consumer interpretation numbers stand for complete exact
contexts: the actual selected enclosing handler/provider frames, activation,
instantiation and precedence. Equality is a model assumption; the proof does
not show that same-typed effects, handler IDs or arbitrary runtime activations
are interchangeable. The implementation reconstructs selection at each actual
consumer and checks surviving external frames and possible nearer interception.
Structural enclosure of `N` supplies the support boundary; no new occurrence
identity follows from this model.

Restore has implicit unit input and a single model answer family. `Delivery`
distinguishes a fresh root's answer from a continued consumer's `Some` answer
and a missing key's `None`. The model does not formalize general `A<N>`, rows,
source spelling or elaboration. In particular, the answer may contain
`Key<N>`, while generic-cell payloads are checked before the fresh owner scope.
Elaboration and independent validation bind the Store identity before checking
that answer contract without moving the initializer into the new scope.

`Step.retain` combines the atomic owner move and the administrative checkpoint
clause's return. Its explicit `adminSuffixClear` and `Admit` premises cover the
model boundary. The product checks the actual clause and its completion; the
root remains active until the clause suffix returns. Ordinary private-clause
`resume` and checked inner-handler discard are not modelled by a new transition.
The private checkpoint owner cannot use discard to abandon its branch.
`Step.refuse` records the unchanged ownership state at failed preparation; it
does not add a source-level success or recovery result.

## Proved model claims

| Obligation | Named result and scope |
| --- | --- |
| Unique ownership and completion | `step_accounting`, `step_preserves_unique` and `trace_preserves_unique` account for fresh-root creation, selected moves, root completion and internal teardown. No step assumes a safe successor. |
| Slot identity and capacity | `trace_preserves_slot_ids`, `trace_preserves_generation_bound` and `normal_step_preserves_capacity` preserve the stated initial bounds. Recycling requires a larger representable natural generation. |
| One restoration per key | `restore_requires_live_key`, `restored_key_spent`, `step_preserves_spent_key` and `restore_cannot_replay` use the actual store/slot/generation match and unique slot IDs; the result remains true across any finite model trace. |
| Support and current consumer | `trace_preserves_context` maintains the model's admission and current-consumer equality under the explicit fixed-context premises. The separate `admission_*` results expose the self-capture, outside-completion and escape guards. |
| Normal completion | `actual_finish_requires_completion` requires finished cleanup and consumed nested phases before the model delivers its normal finished answer. `source_release_predecessor` requires empty work; `no_work_excludes_clause`, `_active` and `_slot` connect that condition to actual represented control under `ContextSafe`. |
| Outer closing | `running_drain_is_not_skipped` and `outer_close_complete_trace` model an armed cleanup starting with live slots, restoring both branches, returning empty, then releasing. These are abstractions of existing Cleanup and close ordering, not new runtime or Core drain nodes. |
| Failure | The same owner accounting distinguishes successful disposal and a reported incomplete teardown. `leaked` is an abstract record of unresolved residual identities, not a claim that the runtime enumerates them or can recover forgotten objects. No source action is promised. |

The [examples](OwnershipExamples.lean) include a fresh root, one P capture
with a live nested clause, running cleanup and saved body result, Q retained in a separate slot,
current-consumer return, another yield during drain, stale-key non-replay,
shared outer support, refusal without a move, failed admission and incomplete
teardown after a partially completed disposal. They also exercise complete
disposal. The outer-support case proves only that the model permits two
sequential branches to refer to one still-live owner; it is not a concurrent
sharing or synchronization result. The outer-close trace supplies actual
empty work as a premise of its final drain step. It does not prove an arbitrary
library drain returns empty; that is C3's separate analysis and proof.

## Product correspondence

The retained [C2 delivery](https://github.com/dikini/ash-lang/pull/161) checks
actual Store ports, capture support, interpreter selection and structural
owners through source and linked Core. The
[evaluator](../../../src/eval/machine.rs) prepares retention and restoration
before moving ownership, keeps generation-qualified slots and returns restored
answers to the current consumer. Its iterative failure disposal can report
incomplete teardown; neither that behavior nor this model promises every
residual release.

The retained [C3 delivery](https://github.com/dikini/ash-lang/pull/162) checks
normal release after real root, clause and cleanup completion. The separate
[drain correspondence](drain-correspondence.md) records its concrete finite
analysis and the limits of the proof. The
[C4 library corpus](../../../tests/scheduling.rs) exercises current-consumer
return, repeated yields and running cleanup with the same Store mechanism.
The [proof-root evidence map](README.md#retained-product-evidence) links the
retained reviews and checks. These are reviewed implementation correspondence
and tests, not a mechanized proof of Rust or a termination, fairness,
native-provider, migration or multithreaded-safety claim.
