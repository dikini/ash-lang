# Lexical region correspondence and assumptions

This report maps the bounded [model](README.md) to accepted
[CP-0025](../../proposals/CP-0025-lexical-region-construction.md). It supplies
R1/R2 evidence rather than current Ash semantics or product implementation.
The [gate and transfer record](evidence.md) identifies the exact reviewed inputs.

The aggregate `Coherent` predicate includes `Safe`, `ServiceContextsSafe` and
`NoReturnedCursors`. Its step/trace theorems derive the successor from actual
updates and local premises. The model is finite and sequential; ordinary
source evaluation, type/effect checking and foreign module contracts supply the
explicit assumptions below. Inaccessible physical object records do not impose
usable-reference liveness.

## Local guards and controls

| Obligation | Guard/update | Named control |
| --- | --- | --- |
| Publication is one-shot | State.publishedOnce is irreversible; publishGroup sets it and dropAccess preserves it. GroupReady requires false history. Exposure remains revocable and separate. | publication_history_persists_after_drop; published_record_cannot_republish; dropped_whole_cannot_republish |
| Refusal preserves unrelated requests | Full Transition.refuse (post-supply) requires pending=none. Transition.refuseBeforeStorage instead requires the actual current Pending.object=i and no backing/object. | unrelated_request_prefix; unrelated_pending_refusal_guard_rejects; nested_refusal_trace; nested_refusal_has_no_fake_storage |
| Release retires backing at successful return | Transition.cleanup cannot store returned; release start requires ReleaseReady. OwnerAvailable/ViewAvailable block source operations targeted at the running-release owner while other live owners remain available. Transition.finishClose consumes a running release's successful return and retires records atomically. There is no intermediate returned/live Transition. | transition_no_returned_cursor; trace_coherent_preserves; running_release_unavailable; source_view_denied_during_release; retired_cycle_not_inline_readable; cyclic_full_trace |
| Inline access requires publication and provenance | Inline ViewSafe requires publishedOnce. ViewOrigin additionally requires an available whole value or an exact retained alias, so historical bits alone do not invent a source view. | guarded_container_not_inline_readable; private_pending_has_no_view; InlineAccess.independent_inline_usable_after_close; InlineAccess.dependent_inline_unusable_after_close |
| Setup saves the actual context/cut | Transition.prepare requires exact equality to the current selected/currentCut. Provider callback still uses the saved preceding context/cut, separate from lexical parent. | arbitrary_saved_setup_rejected; arbitrary_saved_cut_rejected; request_callback_context; supply_returns_to_caller |
| Close runs the recorded cleanup list | State.cleanupActions records the existing ordinary completion obligations; Transition.beginClose requires exactly that list. Existing Source/Core checking supplies these obligations; the region extension does not synthesize or erase them. | omitted_cleanup_list_rejected; cleanup_step_preserves; complete_cleanup_has_run_every_action; unfinished_close_cannot_be_discarded |
| Live services retain their provider view | ServiceContextsSafe protects preparing/live records' precedingContext. ReleaseReady.providers checks them before physical release; transition_service_contexts and the full Coherent theorem preserve them. Inactive physical object dependencies are unaffected. Preparing parent ownership is also retained until abortPrepare/enter. | service_view_blocks_younger_close; close_service_contexts; transition_service_contexts; trace_coherent_preserves; outer_stale_capture_stays_physical |

`ReleaseReady` is an explicit current-state conjunction of actual context, usable graph/view, live-child, captured frame and retained provider-view guards. It is not successor-state safety. The same guards are checked before release begins and at normal successful return. Physical validity until the contractually successful release event, freshness/disjointness and reclamation are module assumptions; the model does not prove native memory behavior.

`OwnerAvailable` is targeted: no source use/new record can touch the owner currently being released. Callback work in a different live region is not globally banned. Provider context views are operational retained state; ordinary inaccessible object bits remain outside that liveness invariant.

## Operation correspondence

- EnterPrepare/EnterLive/abortPrepare preserve the prospective identity and fixed allocator pair; setup equality authenticates the saved preceding selection. No owner is published on aborted preparation. `parent` and `precedingContext` have separate roles.
- Request carries independent owner/extent/alignment metadata. The serviced pending identity, progress/history marker and typed ordinary operands are retained by evaluator/control admission rather than sent to the allocator. Source/Core guardedness and actual value/layout metadata remain local assumptions; this is not a whole compiler/lexical evaluator proof.
- Supply requires actual fresh registered backing and restores the saved caller; initialization is pending-only; GroupReady handles private cyclic slots without requiring every target initialized during each earlier initializer. `cyclic_full_trace` includes actual request/supply/init/publication/drop and both bulk closes; `cyclic_bulk_retired` checks both records.
- Whole roots retain the usable graph; inline views keep the physical container and the selected part's authenticated dependencies. The outer/younger controls keep inaccessible outer bytes after younger close. Inline views must have been derived/retained legitimately; a dead whole value is not recovered.
- Calls use current caller selection for subsequent allocation and leave existing closure residency/captures unchanged. CallerPlacement.construction_trace and caller/explicit request controls exercise actual allocation-record construction. Ordinary lexical function application and the validated template/environment mechanism are assumed, not reimplemented by this finite model.
- Canonical owner service uses saved preceding context and provider cut. suspendService saves an outer request; nested supply/refusal traces restore it exactly. captureFull moves only the owner/service-frame prefix; resume restores it above the resumer return frame. Outside frames and shared objects are preserved.
- Close cursors are keyed by the unique owner. Captured cursors are dormant and cannot be discarded; actions follow their recorded order. Release return is now atomic with bulk retirement. No pointer/reference alias gets completion ownership.

The finite region extension leaves ordinary source effects and lexical evaluation abstract. operandHistory is an opaque already-performed-effects marker; region transitions do not roll it back or replay it. Internal work/control exhaustion is not an ordinary source allocator refusal and carries no new cleanup guarantee. Source/Core access, cleanup/interpreter compatibility and foreign module guarantees are stated assumptions, never `Coherent successor` premises. No runtime implementation or proof of a native allocator is claimed.

## Admitted trace evidence

- Complete-predicate and control evidence: `initial_coherent`, `empty_coherent`, `cyclic_full_trace_coherent`,
  `nested_supply_coherent` and `nested_refusal_coherent` apply complete Coherent
  preservation to the actual traces. `vacant_coherent`, `setup_enter_trace` /
  `setup_enter_coherent`, and `setup_abort_trace` / `setup_abort_coherent` exercise
  authenticated same-identity preparation and both successful entry/abort.
  `caller_call_trace` / `caller_call_coherent` bind a published whole callable
  record, select the caller's default, and admit call. `caller_default_request`
  and `caller_explicit_left_request` use actual Transition.request with distinct
  targets. `call_keeps_existing_closure` checks unchanged capture/backing and
  the two fresh pending owners. `admitted_discard_trace` /
  `admitted_discard_coherent` admit capture then owner-free discard while retaining
  the outside owners. This uses full Transition/Trace, not only component updates.
- Nonempty cleanup and captured-control evidence: `recordedMachine` stores actual cleanupActions [17,23].
  `recorded_action_prefix` starts closing with exactly that list, starts action17,
  captures/resumes its exact cursor and owner prefix, and returns through saved
  frames. `recorded_action_finish_trace` finishes17 and starts/finishes23.
  `captured_action_exact` records unchanged cursor, moved/restored owners, outside
  frame and consumed ticket; `captured_unfinished_discard_rejected` denies discard.
  `recorded_cleanup_trace` completes release and atomic bulk close;
  `recorded_cleanup_coherent` uses aggregate preservation; `recorded_cleanup_exact`
  checks [17,23] order. `other_owner_request_during_release` admits an actual
  request to left while right's release runs, exercising targeted availability.
- Independent inline lifetime evidence: `outer_full_construction` uses actual request/supply/initialize/publish.
  `inline_bind_drop_trace` retains the independent inline root and drops whole
  access. `retained_inline_release_trace` then passes ReleaseReady, releases the
  younger right owner and atomically closes it. `retained_inline_coherent`,
  `retained_inline_use`, and `retained_inline_call` preserve and admit retained
  access. Existing InlineAccess negatives reject whole/dependent views afterward;
  the outer object and its backing remain physical until outer close. The model
  does not require inaccessible physical-record dependencies to remain live.

## Operation and assumption readback

This readback compared the finite model with the CP-0025 semantic candidate at
`a21d0001c34a4ac5a0557e34cfcfb4ea2b1e44a0`, especially its explicit lowering,
operational contract and R1 handoff. That semantic content is now accepted for
transition, with retention still pending. The correspondence
below identifies modeled updates and source/Core obligations; it does not claim
that those obligations are implemented or proved by finite preservation.

**Default and explicit allocation.** Implicit construction lowers through the
private generated `DefaultAlloc` handler to `RegionAllocate(selected_view,
request)`. `using r` supplies that explicit default operand. Explicit
`RegionAllocate(other_view, request)` can instead target a different live owner;
it does not change the caller's default. In the model, `Requirements.owner` is the
actual request target. `ConstructionStep.request` and `Transition.request` check
that owner's record, freshness, provider context/cut and targeted availability;
they do **not** require `request.owner = heap.selected`. Equality is a lowering
obligation for default construction, not a generic request invariant. The
CallerPlacement controls exercise default placement choices without asserting
that every admitted request is implicit. Existing closure records and captures
remain unchanged; `Transition.call` checks usable/available access but is an
identity heap/control step, not an implementation of lexical application.

**Preparation, backing and local construction.** `prepare` authenticates
`precedingContext` and `providerCut` against current selection/cut; `enter`
publishes the same prospective region identity with its fixed `Association`.
`abortPrepare` publishes no live owner. `requestStorage` retains the pending
object, caller context/cut and operand-history marker, then switches to the
owner's saved provider context/cut. `ReplyAdmitted`, fresh-backing admission and
`supplyStorage` check/register the requested owner's backing and restore the
caller. Pending-only initialization retains local fields/captures; publication
requires the finite ready graph and unused publication history. These checks do
not prove physical freshness, disjointness or storage validity. Guarded source
initialization and authenticated field/layout metadata remain input obligations.

**Context query and cleanup.** CP-0025's Unit `DefaultAlloc.context ()` returns a
small dependency-bearing `RegionView` for the actual selection. Core evaluates
the cleanup action once, queries that view, and retains both in its ordinary
owned cleanup frame. The generated action-local handler answers `context` with
the saved view and forwards `allocate q` to `RegionAllocate(saved_view, q)`.
Neither the action nor younger captures cross the query. The finite
`Transition.contextQuery` checks selected owner and `OwnerAvailable`, then leaves
the machine unchanged: it abstracts the query and does not construct a typed
RegionView result. `SavedContextsSafe`, saved pending/return/captured contexts and
`ServiceContextsSafe` model retained operational dependencies; `cleanupActions`
and close cursors model recorded action identities/order. They do not encode the
per-action RegionView payload or generate its two Core handler clauses. Their
correct registration, retention and explicit use remain source/Core obligations.

**Effects and owner discharge.** CP-0025 expands default allocation in source
value-function computation annotations before checking, without duplicating an
explicit member or changing row-tail/lacks rules. Summaries and Core retain full
rows. `RegionAllocate` includes its explicit operand rows and `DefaultAlloc`;
the enclosing region boundary includes provider evaluation, allocate and release
rows unconditionally. Discharge additionally requires a live protecting owner
boundary for every targeted invocation. An unknown owner cannot disappear by
removing the default effect. The finite model has no effect-row checker; live
owners, views and control admission are a correspondence obligation's finite
inputs, not a proof of full row expansion, discharge or static/Core validation.

**Canonical provider execution and handler compatibility.** The accepted transition's
primitive invokes the saved allocate member at the supplied owner's canonical
interpretation position, using its lexical instantiation and preceding allocation
context. `providerCut`, `requestStorage`, `suspendService`/`returnService`, and the
saved/captured frame operations represent switching and restoring that position
without overwriting outside control. `parent` separately constrains owner
ordering. Nat cut identities and membership in `liveCuts` do not prove lexical
dispatch or handler compatibility.

In the CP's Console example, H surrounds region setup and J surrounds body
construction. Provider Console reaches H for normal allocation and cleanup
allocation; J stays in the serviced segment. A cleanup's own Console use may
require J. Removing J can admit allocation-only cleanup if H and the owner
service survive; removing required H cannot be repaired by another outer
same-instance handler. Provider-local handlers retain ordinary precedence.
The action-local adapter does not restore removed interpreters. These are exact
source/Core cleanup-context and dispatch obligations, not consequences of equal
rows, numeric cuts or finite preservation. The finite running-release guards
also restrict access to the targeted owner while leaving other available owners
usable; they do not establish arbitrary provider code's behavior during close.

**Close and assumptions.** Recorded cleanup runs before release. `ReleaseReady`
checks current contexts, usable graph/view dependencies, children, captured
frames and provider contexts before release and successful return. `finishClose`
combines that return with bulk retirement; the fixed pair is not redirected by
a later default. `Coherent` preservation derives the successor from these local
premises. It does not prove release termination, native allocator correctness,
lexical evaluation, full static/Core validation or handler compatibility.

### Omitted-isolation countermodel (outside the admitted module contract)

Let two live owners A and B share one provider state, with distinct registered
backings a and b and valid replies for each owner. Both objects are published;
B's object depends only on B. Suppose `release(A)` incorrectly resets the shared
provider's entire validity set from `{a, b}` to `{}` and reports success. A's
ordinary dependent-use and cleanup checks can all pass, while B's still-live
object loses physical backing. Reply-owner/association checking alone cannot
exclude this behavior. It violates CP-0025's explicit requirement that successful
release preserve other regions. The model's owner-specific `closeRegion` update
preserves B's record because it assumes that contract; it cannot certify this
faulty provider. This finite countermodel explains the isolation premise without
adding addresses, a native protocol or a new proof framework.


