# C1 model correspondence and limits

This map is part of the candidate [DN-0056 proof assignment](../DN-0056-scoped-continuation-retention-and-library-scheduling.md#c1-bounded-ownership-and-completion-proof-assignment).
[CP-0026](../../proposals/CP-0026-scoped-owned-continuation-storage.md) remains
proposed. The model is evidence for its selected transitions, not language
authority or a proof of the compiler or evaluator.

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
permission algebra. The future source and linked Core checks must derive these
facts from actual captures, values, evidence, control, and enclosing scopes.
`adminSuffixClear` is a local premise on the retain macro-step: the authenticated
private checkpoint clause has no skipped required suffix. It is not a source
assertion or a runtime permission. A product must establish that premise from
actual control before consuming the hidden owner.

The store and consumer interpretation numbers stand for complete exact
contexts: the actual selected enclosing handler/provider frames, activation,
instantiation and precedence. Equality is a model assumption; the proof does
not show that same-typed effects, handler IDs or arbitrary runtime activations
are interchangeable. A product must reconstruct selection at each actual
consumer and prove its external frames survive, including possible nearer
interception. It may use structural enclosure of `N`; no new occurrence
identity follows from this model.

Restore has implicit unit input and a single model answer family. `Delivery`
distinguishes a fresh root's answer from a continued consumer's `Some` answer
and a missing key's `None`. The model does not formalize general `A<N>`, rows,
source spelling or elaboration. In particular, the answer may contain
`Key<N>` in CP-0026, while existing generic-cell payloads are checked before
the fresh owner scope. Product elaboration and independent validation must
bind the store identity before checking that answer contract without moving
the initializer into the new scope.

`Step.retain` combines the atomic owner move and the administrative checkpoint
clause's return. Its explicit `adminSuffixClear` and `Admit` premises cover the
model boundary; the product must prove their correspondence to the actual
clause and its completion. Existing ordinary private-clause `resume` and
checked inner-handler discard are inherited current behavior and are not
modelled by a new transition. The private checkpoint owner cannot use discard
to abandon its branch under the proposed contract.
`Step.refuse` records the unchanged ownership state at failed preparation; it
does not add a source-level success or recovery result.

## Proved candidate claims

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

## Product correspondence still required

- Relate the abstract inventory, structural disjointness and administrative
  suffix premise to the selected [current effect and resource rules](../../../spec/static-semantics.md#effects),
  their actual linked Core validation and the [evaluator machine](../../../src/eval/machine.rs).
  The current `CapturedContinuation`, clause owner, resource/cleanup boundaries,
  capture accounting and preflight logic are evidence to reuse, not a proof
  that the proposed store is implemented.
- Authenticate the fixed Unit/answer/row/interpreter ports and owner-indexed
  answer type through source, imports, linked Core and transformations. Check
  exact selected interpreters and all external support at each use and close.
- Implement preparation before committed transfer and restoration, generation
  exhaustion without wrap, and the new current-consumer answer adapter.
  Extend iterative teardown for slot-to-capture edges. If teardown itself
  exhausts its work storage, retain the current incomplete-teardown report;
  neither this model nor current teardown promises every residual release.
- Demonstrate that branch and cleanup completion accounting follows actual
  roots and captured owners rather than ordinary answer constructors or ready
  queue contents. Preserve the private-root association while its handler is
  temporarily absent and through any existing frame coalescing.
- Mechanize and implement the separate C3 normal-return relation, including
  authentic fresh probes, actual handler and cleanup suffixes, imported and
  recursive control, conservative unknowns and exhaustion. Model emptiness at
  a closing predecessor does not establish that analysis.
- Test the real source/Core/runtime transitions, transformed validation,
  region support and libraries against the full C1–C5 criteria. Complete the
  frozen proof integration, independent review, checkpoint gates and retained
  verification separately. No termination, fairness, native-provider,
  migration, multithreaded safety or whole-compiler claim follows here.
