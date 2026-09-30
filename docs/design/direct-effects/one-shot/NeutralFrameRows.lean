import ChainOwnerAgreement

/-!
Recover ordinary source requirements from phase-neutral code and pending
contexts, preserving full contracts and exact exported rows. Connect consumed
waiting chains to positional saved-frame checks used by actual resumption.
-/

namespace Ash.OneShot.NeutralFrameRows
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open ClauseProtection (Ticket Derives exportAt phaseContext)
open ClauseProtectionFrames (ContextDerives)
open CallableProtectionFrames (Tables contextOf ContextSummarizes)
open PhaseContextChains (Chain Source stackOf)
open Syntax (UseState)

variable {ticket : Ticket}

theorem phase_between (forward : before = UseState.consumed → middle = .consumed)
    (backward : middle = UseState.consumed → before = .consumed) : middle = before := by
  cases before <;> cases middle <;> simp_all

theorem export_append (left : exportAt ticket inside phase first = some firstRow)
    (right : exportAt ticket inside phase second = some secondRow) :
    exportAt ticket inside phase (first ++ second) = some (firstRow ++ secondRow) := by
  unfold exportAt at left right ⊢
  simp only [residual_rows_append, left, right, merge]

theorem cleanup_export
    (exported : residualize (.barrier true :: phaseContext ticket inside phase) latent = some row) :
    exportAt ticket inside phase (qualify true latent) = some row := by
  simpa only [exportAt, residualize, DisposalProtection.through_barrier] using exported

/-- Phase neutrality rules out continuation consumption anywhere in this
    evaluation path. The recovered source contract includes latent effects. -/
theorem neutral_code
    (source : Derives operations policy ticket inside environment before code after contract row)
    (same : before = after) :
    ∃ raw, Summarizes operations environment code contract raw ∧ exportAt ticket inside before raw = some row := by
  induction source with
  | stable summary exported => exact ⟨_, summary, exported⟩
  | pair left right ihLeft ihRight =>
      cases same
      have middle := phase_between (ClauseProtection.phase_monotone left) (ClauseProtection.phase_monotone right)
      cases middle
      obtain ⟨a, first, firstRow⟩ := ihLeft rfl
      obtain ⟨b, second, secondRow⟩ := ihRight rfl
      exact ⟨a ++ b, .pair first second, export_append firstRow secondRow⟩
  | app function argument exported ihFunction ihArgument =>
      cases same
      have middle := phase_between (ClauseProtection.phase_monotone function) (ClauseProtection.phase_monotone argument)
      cases middle
      obtain ⟨f, callable, functionRow⟩ := ihFunction rfl
      obtain ⟨a, operand, argumentRow⟩ := ihArgument rfl
      exact ⟨_, .app callable operand, export_append (export_append functionRow argumentRow) exported⟩
  | bind initializer body ihInitializer ihBody =>
      cases same
      have middle := phase_between (ClauseProtection.phase_monotone initializer) (ClauseProtection.phase_monotone body)
      cases middle
      obtain ⟨a, first, firstRow⟩ := ihInitializer rfl
      obtain ⟨b, second, secondRow⟩ := ihBody rfl
      exact ⟨a ++ b, .bind first second, export_append firstRow secondRow⟩
  | branch condition yes no ihCondition ihYes ihNo =>
      cases same
      have middle := phase_between (ClauseProtection.phase_monotone condition) (ClauseProtection.phase_monotone yes)
      cases middle
      obtain ⟨c, test, conditionRow⟩ := ihCondition rfl
      obtain ⟨a, left, yesRow⟩ := ihYes rfl
      obtain ⟨b, right, noRow⟩ := ihNo rfl
      exact ⟨_, .branch test left right, export_append (export_append conditionRow yesRow) noRow⟩
  | perform known operand exported ih =>
      cases same
      obtain ⟨a, argument, argumentRow⟩ := ih rfl
      exact ⟨_, .perform known argument, export_append argumentRow exported⟩
  | resume allowed operand exported ih =>
      cases same
      cases ClauseProtection.phase_monotone operand rfl
  | discard allowed unprotected exported => cases same
  | cleanup callback body exported ihCallback ihBody =>
      cases same
      have middle := phase_between (ClauseProtection.phase_monotone callback) (ClauseProtection.phase_monotone body)
      cases middle
      obtain ⟨a, action, callbackRow⟩ := ihCallback rfl
      obtain ⟨b, returned, bodyRow⟩ := ihBody rfl
      exact ⟨_, .cleanup action returned, export_append (export_append callbackRow bodyRow) (cleanup_export exported)⟩
  | resource initializer body outward exported ih =>
      cases same
      obtain ⟨raw, initial, initialExport⟩ := ih rfl
      exact ⟨_, .resource initial body outward, export_append initialExport exported⟩

/-- The context's raw requirements are obtained from its actual pending code;
    matching phases do not justify assigning it an empty effect row. -/
theorem neutral_context
    (source : ContextDerives operations policy ticket inside environment position phase input phase output row) :
    ∃ raw, ContextSummarizes operations environment position input output raw ∧
      exportAt ticket inside phase raw = some row := by
  cases source with
  | pairLeft right =>
      obtain ⟨raw, summary, exported⟩ := neutral_code right rfl
      exact ⟨raw, .pairLeft summary, exported⟩
  | pairRight left => exact ⟨[], .pairRight left, residual_empty _⟩
  | appFunction argument exported =>
      obtain ⟨raw, summary, argumentRow⟩ := neutral_code argument rfl
      exact ⟨_, .appFunction summary, export_append argumentRow exported⟩
  | appArgument function exported => exact ⟨_, .appArgument function, exported⟩
  | bind body =>
      obtain ⟨raw, summary, exported⟩ := neutral_code body rfl
      exact ⟨raw, .bind summary, exported⟩
  | branch yes no =>
      obtain ⟨a, left, yesRow⟩ := neutral_code yes rfl
      obtain ⟨b, right, noRow⟩ := neutral_code no rfl
      exact ⟨a ++ b, .branch left right, export_append yesRow noRow⟩
  | perform known exported => exact ⟨_, .perform known, exported⟩
  | cleanup body exported =>
      obtain ⟨raw, summary, bodyRow⟩ := neutral_code body rfl
      exact ⟨_, .cleanup summary, export_append bodyRow (cleanup_export exported)⟩
  | resource body outward exported => exact ⟨_, .resource body outward, exported⟩

theorem consumed_export_empty_inside (raw : Footprint) : exportAt ticket [] .consumed raw = some raw := by
  simp [exportAt, phaseContext, ClauseProtection.ownedMode, residualize, DisposalProtection.through_barrier, qualify]

theorem consumed_export (inside : ProtectionContracts.Context) (raw : Footprint) :
    exportAt ticket inside .consumed raw = residualize inside raw := by
  unfold exportAt phaseContext
  rw [residual_append]
  cases exported : residualize inside raw <;>
    simp [ClauseProtection.ownedMode, residualize, DisposalProtection.through_barrier, qualify]

theorem consumed_context
    (source : ContextDerives operations policy ticket [] environment position .consumed input .consumed output row) :
    ContextSummarizes operations environment position input output row := by
  obtain ⟨raw, summary, exported⟩ := neutral_context source
  rw [consumed_export_empty_inside] at exported
  exact Option.some.inj exported ▸ summary

theorem neutral_code_iff :
    Derives operations policy ticket inside environment phase code phase contract row ↔
      ∃ raw, Summarizes operations environment code contract raw ∧ exportAt ticket inside phase raw = some row :=
  ⟨fun source => neutral_code source rfl, fun ⟨_, summary, exported⟩ => .stable summary exported⟩

theorem neutral_context_iff :
    ContextDerives operations policy ticket inside environment position phase input phase output row ↔
      ∃ raw, ContextSummarizes operations environment position input output raw ∧ exportAt ticket inside phase raw = some row :=
  ⟨neutral_context, fun ⟨_, summary, exported⟩ => ClauseProtectionFrames.stable_context summary exported⟩

/-- The row is derived at each actual saved frame position. No footprint is
    assigned to the chain independently of its source contexts. -/
theorem consumed_chain_rows
    (source : Chain operations policy ticket [] environment frames before input after output row)
    (spent : before = .consumed) : SavedFrameRequirements.Rows operations tables (stackOf frames .nil) row := by
  induction source with
  | nil => exact .nil
  | cons head rest ih =>
      cases spent
      have middle := ClauseProtectionFrames.context_phase_monotone head rfl
      cases middle
      refine .push (.plain (consumed_context head)) ?_ (ih rfl)
      rw [PhaseContextChains.plain_prefix_residual]
      rfl

/-- A remaining interpretation suffix acts on each frame's raw source row.
    Its own pending requirements are appended after the prefix requirements. -/
theorem consumed_chain_rows_append
    (source : Chain operations policy ticket (contextOf tables tail) environment frames before input after output row)
    (spent : before = .consumed)
    (suffix : SavedFrameRequirements.Rows operations tables tail tailRow) :
    SavedFrameRequirements.Rows operations tables (stackOf frames tail) (row ++ tailRow) := by
  induction source with
  | nil => exact suffix
  | cons head rest ih =>
      cases spent
      have middle := ClauseProtectionFrames.context_phase_monotone head rfl
      cases middle
      rename_i first middleInput headRow remaining final result restRow frame
      obtain ⟨raw, summary, exported⟩ := neutral_context head
      have actual : residualize (contextOf tables (stackOf remaining tail)) raw = some headRow := by
        rw [PhaseContextChains.plain_prefix_residual]
        exact (consumed_export _ _).symm.trans exported
      simpa only [stackOf, List.append_assoc] using SavedFrameRequirements.Rows.push
        (SavedFrameRequirements.FrameSource.plain (plain := frame) summary) actual (ih rfl)

/-- Adding only plain evaluation frames preserves the selected exact handler
    and includes those frames in the actual captured prefix. -/
theorem capture_plain_prefix
    (cut : HandlerCut requested whole capture tail handler) (frames : List PlainData) :
    HandlerCut requested (stackOf frames whole) (stackOf frames capture) tail handler := by
  induction frames with
  | nil => exact cut
  | cons frame rest ih => exact .push (.plain frame) _ _ _ _ (by simp [ExecFrame.erase, PlainData.erase, Frame.target]) ih

theorem capture_rows_from_neutral_prefix
    (cut : HandlerCut requested whole capture tail handler)
    (captured : SavedFrameRequirements.Rows operations tables capture captureRow)
    (source : Chain operations policy ticket (contextOf tables capture) environment frames .consumed input after output row) :
    HandlerCut requested (stackOf frames whole) (stackOf frames capture) tail handler ∧
      SavedFrameRequirements.Rows operations tables (stackOf frames capture) (row ++ captureRow) :=
  ⟨capture_plain_prefix cut frames, consumed_chain_rows_append source rfl captured⟩

theorem plain_prefix_check (tables : Tables) (frames : List PlainData) (tail : Stack) (row : Footprint) :
    checkFootprint (contextOf tables (stackOf frames tail)) row = checkFootprint (contextOf tables tail) row := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => simpa only [stackOf, CallableProtectionFrames.check_plain_context] using ih

theorem consumed_chain_checked
    (source : Chain operations policy ticket [] environment frames .consumed input after output row)
    (accepted : checkFootprint (contextOf tables tail) row = true)
    (outside : SavedFrameRequirements.Checked operations tables [] tail) :
    SavedFrameRequirements.Checked operations tables [] (stackOf frames tail) := by
  have rows := consumed_chain_rows (tables := tables) source rfl
  have checked := SavedFrameRequirements.rows_checked rows accepted
  have joined := SavedFrameRequirements.checked_append
    (by simpa only [List.append_nil] using checked) outside
  simpa only [PhaseContextChains.stack_tail_append, Stack.append] using joined

theorem resume_waiting_rows
    (source : Source operations policy ticket [] (contextOf tables tail) environment
      (.resume ticket.binder value) frames .available after output row) :
    ∃ remaining, Chain operations policy ticket [] environment frames .consumed ticket.answer after output remaining ∧
      SavedFrameRequirements.Rows operations tables (stackOf frames .nil) remaining ∧
      checkFootprint (contextOf tables tail) remaining = true := by
  obtain ⟨remaining, chain, accepted⟩ := PhaseContextChains.pending_after_resume source
  exact ⟨remaining, chain, consumed_chain_rows chain rfl, accepted⟩

theorem resume_waiting_checked
    (source : Source operations policy ticket [] (contextOf tables tail) environment
      (.resume ticket.binder value) frames .available after output row)
    (outside : SavedFrameRequirements.Checked operations tables [] tail) :
    SavedFrameRequirements.Checked operations tables [] (stackOf frames tail) := by
  obtain ⟨remaining, chain, rows, accepted⟩ := resume_waiting_rows source
  exact consumed_chain_checked chain accepted outside

theorem resume_row_accepted
    (source : Source operations policy ticket [] (contextOf tables tail) environment
      (.resume ticket.binder value) frames .available after output row)
    (isValue : value.IsValue) :
    checkFootprint (contextOf tables (stackOf frames tail)) ticket.resumeRow = true := by
  rw [plain_prefix_check]
  cases source with
  | checked current pending accepted =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      cases current with
      | stable summary exported => cases summary
      | resume allowed operand exported =>
          have checked : Derives operations policy ticket [] environment .available
              (.resume ticket.binder value) .consumed ticket.answer _ := .resume allowed operand exported
          simpa only [Stack.append] using SavedFrameRequirements.source_resume_checks_caller
            (tables := tables) (front := .nil) (tail := tail) checked accepted.1 isValue

/-- Both the waiting prefix's positional check and the runtime owner equality
    follow from the source chain. The captured row must still be authenticated
    against the actual captured frames, and the outside tail retains its own
    source certificate. -/
theorem resume_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume ticket.binder value, scope, stackOf frames (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy ticket [] (contextOf tables tail) environment
      (.resume ticket.binder value) frames .available after output row)
    (captured : SavedFrameRequirements.Rows operations tables capture ticket.resumeRow)
    (outside : SavedFrameRequirements.Checked operations tables [] tail)
    (isValue : value.IsValue) :
    let initial : NamedState := ⟨⟨⟨.resume ticket.binder value, scope,
      stackOf frames (.live owner input answer capture caller tail)⟩, issued, completed⟩, activations⟩
    let next : Configuration := ⟨value, scope, capture.append (stackOf frames (.spent owner answer caller tail))⟩
    NamedAccessStep ambient initial (ScopedPortJoint.advanceState initial next [] [.ticket owner]) ∧
      CompletionJoint.Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState initial next [] [.ticket owner]) result outgoing bound ∧
      SavedFrameRequirements.Checked operations tables [] next.stack ∧
      ∃ remaining, Chain operations policy ticket [] environment frames .consumed ticket.answer after output remaining ∧
        SavedFrameRequirements.Rows operations tables (stackOf frames .nil) remaining ∧
        checkFootprint (contextOf tables tail) remaining = true := by
  obtain ⟨step, nextValid, pending⟩ := ChainOwnerAgreement.resume_joint valid source isValue
  have waiting := resume_waiting_checked source outside
  have accepted := resume_row_accepted source isValue
  have callerChecked : SavedFrameRequirements.Checked operations tables [] ((stackOf frames .nil).append tail) := by
    simpa only [PhaseContextChains.stack_tail_append, Stack.append] using waiting
  have captureAccepted : checkFootprint (contextOf tables ((stackOf frames .nil).append tail) ++ []) ticket.resumeRow = true := by
    simpa only [PhaseContextChains.stack_tail_append, Stack.append, List.append_nil] using accepted
  have restored := SavedFrameRequirements.resume_recomposition (owner := owner) (answer := answer) (scope := caller)
    captured captureAccepted callerChecked
  exact ⟨step, nextValid, by simpa only [PhaseContextChains.stack_tail_append, Stack.append] using restored,
    resume_waiting_rows source⟩

namespace Examples
open ClauseProtection.Examples (effectF capturedTicket requestF operations policy)

theorem available_request_retains_protection : ∃ raw,
    Summarizes operations CallableProtection.Environment.empty requestF .scalar raw ∧
      exportAt capturedTicket [] .available raw = some [⟨effectF, 0, true⟩] :=
  neutral_code (ClauseProtection.Examples.request_summary .available) rfl

theorem consumed_request_still_has_effect :
    Summarizes operations CallableProtection.Environment.empty requestF .scalar [⟨effectF, 0, false⟩] := by
  obtain ⟨raw, summary, exported⟩ := neutral_code
    (ClauseProtection.Examples.request_summary (environment := CallableProtection.Environment.empty) .consumed) rfl
  rw [consumed_export_empty_inside] at exported
  exact Option.some.inj exported ▸ summary

def callback : Code := .lambda 7 requestF

theorem neutral_cleanup_keeps_protected_invocation : ∃ raw,
    Summarizes operations CallableProtection.Environment.empty (.cleanup callback .unit) .scalar raw ∧
      exportAt capturedTicket [] .consumed raw = some [⟨effectF, 0, true⟩] := by
  have action : Derives operations policy capturedTicket [] CallableProtection.Environment.empty .consumed callback .consumed
      (.function .scalar .scalar [⟨effectF, 0, false⟩]) [] := .stable (.lambda (.perform rfl .unit)) rfl
  have source : Derives operations policy capturedTicket [] CallableProtection.Environment.empty .consumed
      (.cleanup callback .unit) .consumed .scalar [⟨effectF, 0, true⟩] :=
    .cleanup action (.stable .unit rfl) rfl
  exact neutral_code source rfl

theorem waiting_callable_keeps_latent_row : SavedFrameRequirements.Rows operations tables
    (stackOf [PhaseContextChains.Examples.bindFrame, PhaseContextChains.Examples.applyFrame] .nil)
    [⟨effectF, 0, false⟩] := by
  obtain ⟨input, summary, chain, accepted⟩ := PhaseContextChains.source_return
    PhaseContextChains.Examples.after_return_source PhaseContextChains.Examples.returned_callable_closed.1
  exact consumed_chain_rows chain rfl

open SavedFrameRequirements.Examples (readFrame demand beforeRelease afterRelease)

theorem consumed_read_context : ContextDerives SavedFrameRequirements.Examples.operations policy capturedTicket []
    CallableProtection.Environment.empty readFrame.context .consumed .scalar .consumed .scalar demand :=
  .bind (.stable (.perform rfl .reference) rfl)

theorem consumed_read_requires_remaining_provider :
    SavedFrameRequirements.Checked SavedFrameRequirements.Examples.operations SavedFrameRequirements.Examples.tables [] beforeRelease ∧
      ¬ SavedFrameRequirements.Checked SavedFrameRequirements.Examples.operations SavedFrameRequirements.Examples.tables [] afterRelease := by
  have source : Chain SavedFrameRequirements.Examples.operations policy capturedTicket [] CallableProtection.Environment.empty
      [readFrame] .consumed .scalar .consumed .scalar demand := Chain.cons (frame := readFrame) consumed_read_context .nil
  have provider : SavedFrameRequirements.Checked SavedFrameRequirements.Examples.operations SavedFrameRequirements.Examples.tables []
      (.push (.cell 42 8 .none .integer) .nil) := .push .cell rfl .nil
  exact ⟨consumed_chain_checked source (by decide) provider, SavedFrameRequirements.Examples.released_provider_cannot_check_suffix⟩

namespace Joint
open CallableFrames.Examples (s1 clauseBody outside)
open CallableJoint.CaptureExample (initial source_enters_request)
open GenerativeFrames.Examples (declarations)
open CallableContracts.Examples (scalar)
open PhaseBoundaries.Examples (phaseTicket functionContract)
open SavedFrameRequirements.Examples (tables callable_outside_rows)

theorem callable_capture_rows_from_phase : SavedFrameRequirements.Rows SavedFrameRequirements.Examples.operations tables
    CallableFrames.Examples.captured [] := by
  have pending : ContextDerives SavedFrameRequirements.Examples.operations CallableJoint.CaptureExample.policy (phaseTicket false)
      (contextOf tables (.push (.handler CallableFrames.Examples.handler) .nil)) CallableProtection.Environment.empty
      CallableFrames.Examples.pendingFunction.context .consumed .scalar .consumed functionContract [] :=
    .bind (.stable (.lambda (.variable rfl)) (residual_empty _))
  have source := Chain.cons (frame := CallableFrames.Examples.pendingFunction) pending .nil
  have suffix : SavedFrameRequirements.Rows SavedFrameRequirements.Examples.operations tables
      (.push (.handler CallableFrames.Examples.handler) .nil) [] := .push .handler rfl .nil
  exact consumed_chain_rows_append source rfl suffix

theorem admitted_resume_derives_waiting_certificate : ∃ state registry,
    NamedAccessSteps [] initial state ∧
      CompletionJoint.Valid declarations CallableJoint.CaptureExample.policy registry [] state .integer [] scalar ∧
      SavedFrameRequirements.Checked SavedFrameRequirements.Examples.operations tables [] state.execution.configuration.stack ∧
      state.execution.configuration.expression = .integer 17 ∧ Owner.ticket 5 ∈ state.execution.completed := by
  obtain ⟨registry, row, captureStep, capturedValid, _, _, _⟩ := PhaseBoundaries.Examples.capture_joined
  have source : Source SavedFrameRequirements.Examples.operations CallableJoint.CaptureExample.policy (phaseTicket false)
      [] (contextOf tables outside) CallableProtection.Environment.empty clauseBody [] .available .consumed functionContract [] :=
    Source.checked (outside := contextOf tables outside) PhaseBoundaries.Examples.clause_checked .nil (by decide)
  have focus : Focus clauseBody (.resume 10 (.integer 17)) (.bind 4 (.variable 4)) :=
    .bind (by intro impossible; cases impossible)
  obtain ⟨plain, shape, savedScope, focusStep, focusedValid, _, focusedSource⟩ := PhaseContextChains.focus_joint
    (inside := .nil) (tables := tables) capturedValid source (PhaseBoundaries.Boundary.live rfl) focus
  have outsideChecked := SavedFrameRequirements.rows_checked callable_outside_rows (outside := []) rfl
  obtain ⟨resumeStep, resumedValid, checked, pending⟩ := resume_joint focusedValid focusedSource callable_capture_rows_from_phase outsideChecked trivial
  refine ⟨_, registry, ?_, resumedValid, checked, rfl, ?_⟩
  · exact CallableJoint.execution_append source_enters_request.1
      (.next captureStep (.next focusStep (.next resumeStep (.refl _))))
  · simp [ScopedPortJoint.advanceState]

end Joint
end Examples

end Ash.OneShot.NeutralFrameRows

#print axioms Ash.OneShot.NeutralFrameRows.phase_between
#print axioms Ash.OneShot.NeutralFrameRows.export_append
#print axioms Ash.OneShot.NeutralFrameRows.cleanup_export
#print axioms Ash.OneShot.NeutralFrameRows.neutral_code
#print axioms Ash.OneShot.NeutralFrameRows.neutral_context
#print axioms Ash.OneShot.NeutralFrameRows.consumed_export_empty_inside
#print axioms Ash.OneShot.NeutralFrameRows.consumed_context
#print axioms Ash.OneShot.NeutralFrameRows.consumed_chain_rows
#print axioms Ash.OneShot.NeutralFrameRows.plain_prefix_check
#print axioms Ash.OneShot.NeutralFrameRows.consumed_chain_checked
#print axioms Ash.OneShot.NeutralFrameRows.resume_waiting_rows
#print axioms Ash.OneShot.NeutralFrameRows.resume_waiting_checked
#print axioms Ash.OneShot.NeutralFrameRows.resume_row_accepted
#print axioms Ash.OneShot.NeutralFrameRows.resume_joint
#print axioms Ash.OneShot.NeutralFrameRows.neutral_code_iff
#print axioms Ash.OneShot.NeutralFrameRows.neutral_context_iff
#print axioms Ash.OneShot.NeutralFrameRows.Examples.available_request_retains_protection
#print axioms Ash.OneShot.NeutralFrameRows.Examples.consumed_request_still_has_effect
#print axioms Ash.OneShot.NeutralFrameRows.Examples.neutral_cleanup_keeps_protected_invocation
#print axioms Ash.OneShot.NeutralFrameRows.Examples.waiting_callable_keeps_latent_row
#print axioms Ash.OneShot.NeutralFrameRows.Examples.consumed_read_context
#print axioms Ash.OneShot.NeutralFrameRows.Examples.consumed_read_requires_remaining_provider
#print axioms Ash.OneShot.NeutralFrameRows.Examples.Joint.admitted_resume_derives_waiting_certificate
#print axioms Ash.OneShot.NeutralFrameRows.consumed_export
#print axioms Ash.OneShot.NeutralFrameRows.consumed_chain_rows_append
#print axioms Ash.OneShot.NeutralFrameRows.capture_plain_prefix
#print axioms Ash.OneShot.NeutralFrameRows.capture_rows_from_neutral_prefix
#print axioms Ash.OneShot.NeutralFrameRows.Examples.Joint.callable_capture_rows_from_phase
