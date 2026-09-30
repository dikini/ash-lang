import SourceReinterpretation

/-!
A resume site's source checking view uses requirements evaluated at its actual
receiver. Updating the selected owner's source row is harmless after that owner
is consumed. Runtime port contracts and the underlying step remain unchanged.
Maintaining these views from complete source admission is still separate work.
-/

namespace Ash.OneShot.ResumeSpecialization
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals OwnerSource
open OwnerPhaseTransitions (Phases Trace)

def withRow (contract : ResumeContract) (row : Footprint) : ResumeContract := { contract with resumeRow := row }

def view (contracts : OwnerSource.Contracts) (owner : Nat) (row : Footprint) : OwnerSource.Contracts :=
  fun other => if other = owner then (contracts other).map (fun contract => withRow contract row) else contracts other

theorem view_selected (known : contracts owner = some contract) : view contracts owner row owner = some (withRow contract row) := by
  simp [view, known]

theorem view_other (different : other ≠ owner) : view contracts owner row other = contracts other := by simp [view, different]

theorem view_entry (known : contracts other = some contract) :
    ∃ next, view contracts owner row other = some next ∧ next.input = contract.input ∧
      next.answer = contract.answer ∧ next.held = contract.held := by
  by_cases same : other = owner
  · subst other; exact ⟨withRow contract row, view_selected known, rfl, rfl, rfl⟩
  · exact ⟨contract, (view_other same).trans known, rfl, rfl, rfl⟩

theorem trace_excludes_consumed (trace : Trace before (other :: rest) after) (spent : before owner = .consumed) : other ≠ owner := by
  intro same
  subst other
  have ready := OwnerPhaseTransitions.trace_available trace owner List.mem_cons_self
  rw [spent] at ready
  cases ready

theorem source_view
    (source : Derives operations policy contracts inside environment scope before code after result demand row)
    (spent : before owner = .consumed) :
    Derives operations policy (view contracts owner actual) inside environment scope before code after result demand row := by
  induction source with
  | stable summary exported => exact .stable summary exported
  | pair left right ihLeft ihRight => exact .pair (ihLeft spent) (ihRight (source_monotone left spent))
  | app function argument exported ihFunction ihArgument => exact .app (ihFunction spent) (ihArgument (source_monotone function spent)) exported
  | bind initializer body ihInit ihBody => exact .bind (ihInit spent) (ihBody (source_monotone initializer spent))
  | branch condition yes no ihCondition ihYes ihNo =>
      have middle := source_monotone condition spent
      exact .branch (ihCondition spent) (ihYes middle) (ihNo middle)
  | perform known operand exported ih => exact .perform known (ih spent) exported
  | resume known resolved allowed operand transition ih =>
      have different := trace_excludes_consumed transition (source_monotone operand spent)
      exact .resume ((view_other different).trans known) resolved allowed (ih spent) transition
  | discard known resolved allowed unprotected closable transition =>
      have different := trace_excludes_consumed transition spent
      exact .discard ((view_other different).trans known) resolved allowed unprotected closable transition
  | cleanup callback body exported ihCallback ihBody => exact .cleanup (ihCallback spent) (ihBody (source_monotone callback spent)) exported
  | resource initializer body outward exported ih => exact .resource (ih spent) body outward exported

theorem context_view
    (source : ContextDerives operations policy contracts inside environment scope position before input after output demand row)
    (spent : before owner = .consumed) :
    ContextDerives operations policy (view contracts owner actual) inside environment scope position before input after output demand row := by
  cases source with
  | pairLeft right => exact .pairLeft (source_view right spent)
  | pairRight left => exact .pairRight left
  | appFunction argument exported => exact .appFunction (source_view argument spent) exported
  | appArgument function exported => exact .appArgument function exported
  | bind body => exact .bind (source_view body spent)
  | branch yes no => exact .branch (source_view yes spent) (source_view no spent)
  | perform known exported => exact .perform known exported
  | resume known resolved allowed transition =>
      exact .resume ((view_other (trace_excludes_consumed transition spent)).trans known) resolved allowed transition
  | cleanup body exported => exact .cleanup (source_view body spent) exported
  | resource body outward exported => exact .resource body outward exported

theorem frame_view
    (source : FrameSource operations policy contracts inside frame before input after output demand row)
    (spent : before owner = .consumed) :
    FrameSource operations policy (view contracts owner actual) inside frame before input after output demand row := by
  cases source with
  | plain context => exact .plain (context_view context spent)
  | handler => exact .handler
  | cell => exact .cell
  | armed callback exported => exact .armed callback exported
  | running saved => exact .running saved
  | closing => exact .closing
  | retiring transition => exact .retiring transition

theorem segment_view
    (source : Segment operations policy contracts tables fixed segment before input after output demand row)
    (spent : before owner = .consumed) :
    Segment operations policy (view contracts owner actual) tables fixed segment before input after output demand row := by
  induction source with
  | nil => exact .nil
  | push head tail ih => exact .push (frame_view head spent) (ih (OwnerPhaseTransitions.trace_monotone (frame_trace head) spent))
  | live known held consumed tail ih =>
      obtain ⟨next, nextKnown, inputSame, answerSame, heldSame⟩ := view_entry (owner := owner) (row := actual) known
      have restored := ih spent
      rw [← answerSame] at restored
      simpa only [answerSame] using Segment.live nextKnown (heldSame.trans held) consumed restored
  | spent known consumed tail ih =>
      obtain ⟨next, nextKnown, inputSame, answerSame, heldSame⟩ := view_entry (owner := owner) (row := actual) known
      have restored := ih spent
      rw [← answerSame] at restored
      simpa only [answerSame] using Segment.spent nextKnown consumed restored

theorem configuration_view
    (source : Source operations policy contracts tables fixed outside scope code segment before after output demand row)
    (spent : before owner = .consumed) :
    Source operations policy (view contracts owner actual) tables fixed outside scope code segment before after output demand row := by
  cases source with
  | checked current pending accepted =>
      exact .checked (source_view current spent) (segment_view pending (source_monotone current spent)) accepted

theorem view_restore (known : contracts owner = some contract) :
    view (view contracts owner actual) owner contract.resumeRow = contracts := by
  funext other
  by_cases same : other = owner
  · subst other
    simp [view, known, withRow]
  · simp [view, same]

theorem configuration_restore
    (known : contracts owner = some contract)
    (source : Source operations policy (view contracts owner actual) tables fixed outside scope code segment before after output demand row)
    (spent : before owner = .consumed) :
    Source operations policy contracts tables fixed outside scope code segment before after output demand row := by
  have restored := configuration_view (actual := contract.resumeRow) source spent
  simpa only [view_restore known] using restored

def sharedWithRow (contract : CoherentSourceTypes.Owners.Contract) (row : Footprint) : CoherentSourceTypes.Owners.Contract :=
  { contract with resumeRow := row }

def sharedView (contracts : CoherentSourceTypes.Owners.Contracts) (owner : Nat) (row : Footprint) : CoherentSourceTypes.Owners.Contracts :=
  fun other => if other = owner then (contracts other).map (fun contract => sharedWithRow contract row) else contracts other

theorem shared_view_selected (known : contracts owner = some contract) :
    sharedView contracts owner actual owner = some (sharedWithRow contract actual) := by simp [sharedView, known]

theorem shared_view_source (contracts : CoherentSourceTypes.Owners.Contracts) :
    (sharedView contracts owner row).source = view contracts.source owner row := by
  funext other
  by_cases same : other = owner <;> cases known : contracts other <;>
    simp [sharedView, view, CoherentSourceTypes.Owners.Contracts.source, known, same, sharedWithRow, withRow,
      CoherentSourceTypes.Owners.Contract.source]
  all_goals rfl

theorem shared_view_ports (contracts : CoherentSourceTypes.Owners.Contracts) :
    (sharedView contracts owner row).ports = contracts.ports := by
  funext other
  by_cases same : other = owner <;> cases known : contracts other <;>
    simp [sharedView, CoherentSourceTypes.Owners.Contracts.ports, known, same, sharedWithRow,
      CoherentSourceTypes.Owners.Contract.ports]
  all_goals rfl

theorem shared_view_other (different : other ≠ owner) : sharedView contracts owner row other = contracts other := by
  simp [sharedView, different]

theorem shared_source_view
    (source : CoherentSourceTypes.Owners.Derives operations policy contracts inside world environment allowed scope before code after result demand row)
    (spent : before owner = .consumed) :
    CoherentSourceTypes.Owners.Derives operations policy (sharedView contracts owner actual) inside world environment allowed scope before code after result demand row := by
  induction source with
  | stable summary exported => exact .stable summary exported
  | pair left right ihLeft ihRight => exact .pair (ihLeft spent) (ihRight (OwnerPhaseTransitions.trace_monotone (CoherentSourceTypes.Owners.source_trace left) spent))
  | app function argument admitted exported ihFunction ihArgument =>
      exact .app (ihFunction spent) (ihArgument (OwnerPhaseTransitions.trace_monotone (CoherentSourceTypes.Owners.source_trace function) spent)) admitted exported
  | bind initializer body ihInit ihBody =>
      exact .bind (ihInit spent) (ihBody (OwnerPhaseTransitions.trace_monotone (CoherentSourceTypes.Owners.source_trace initializer) spent))
  | branch condition yes no ihCondition ihYes ihNo =>
      have middle := OwnerPhaseTransitions.trace_monotone (CoherentSourceTypes.Owners.source_trace condition) spent
      exact .branch (ihCondition spent) (ihYes middle) (ihNo middle)
  | perform known admitted operand formed exported ih => exact .perform known admitted (ih spent) formed exported
  | resume known resolved permission operand transition admitted formed ih =>
      have different := trace_excludes_consumed transition (OwnerPhaseTransitions.trace_monotone (CoherentSourceTypes.Owners.source_trace operand) spent)
      exact .resume ((shared_view_other different).trans known) resolved permission (ih spent) transition admitted formed
  | discard known resolved permission unprotected closable transition admitted =>
      exact .discard ((shared_view_other (trace_excludes_consumed transition spent)).trans known) resolved permission unprotected closable transition admitted
  | cleanup callback body admitted exported ihCallback ihBody =>
      exact .cleanup (ihCallback spent) (ihBody (OwnerPhaseTransitions.trace_monotone (CoherentSourceTypes.Owners.source_trace callback) spent)) admitted exported
  | resource initializer body formed effectsBound admitted outward exported ih =>
      exact .resource (ih spent) body formed effectsBound admitted outward exported

theorem shared_resume_source
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (permission : (policy binder).resume = true)
    (argument : CoherentSourceTypes.Summary operations world environment allowed value contract.input [])
    (transition : Trace before (owner :: contract.resumeDemand) after)
    (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket) :
    CoherentSourceTypes.Owners.Derives operations policy (sharedView contracts owner actual) inside world environment allowed scope
      before (.resume binder value) after contract.answer (owner :: contract.resumeDemand) actual ∧
    ScopedPorts.Typed operations.ports world environment.ports ticket allowed (.resume binder value) contract.answer.port := by
  have source : CoherentSourceTypes.Owners.Derives operations policy (sharedView contracts owner actual) inside world environment allowed scope
      before (.resume binder value) after contract.answer (owner :: contract.resumeDemand) actual :=
    .resume (contract := sharedWithRow contract actual) (shared_view_selected known) resolved permission
      (.stable (row := []) argument (by simp [exportAt, residual_empty])) transition admitted formed
  exact ⟨source, CoherentSourceTypes.Owners.port_typing source (by simpa only [shared_view_ports] using scopeTyped)⟩

section Resume
variable {front tail fixed capture originalReceiver : Stack}

/-- The caller checks the recomputed row. It need not be covered by the row
    cached when the continuation was captured. Both source states are derived. -/
theorem resume_from_rechecked
    (saved : OwnerCaptureContracts.SavedSource operations policy contracts tables originalReceiver capture base capturedAfter contract)
    (consumed : base owner = .consumed)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (permission : (policy binder).resume = true)
    (operand : Summarizes operations environment value contract.input []) (closed : ClosedValue value)
    (pending : Segment operations policy contracts tables fixed
      (front.append (.live owner inputType answerType capture caller tail)) capturedAfter contract.answer after output remaining restRow)
    (received : Segment operations policy contracts tables
      ((front.append (.spent owner answerType caller tail)).append fixed) capture
      base contract.input capturedAfter contract.answer contract.resumeDemand actual)
    (accepted : checkFootprint outside (actual ++ restRow) = true) :
    RawStep ⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩
      ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ [] [.ticket owner] ∧
    Source operations policy (view contracts owner actual) tables fixed outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail))
      (OwnerPhaseTransitions.introduce base owner) after output (owner :: (contract.resumeDemand ++ remaining)) (actual ++ restRow) ∧
    Source operations policy contracts tables fixed outside scope value
      (capture.append (front.append (.spent owner answerType caller tail)))
      base after output (contract.resumeDemand ++ remaining) (actual ++ restRow) := by
  have captured : Segment operations policy (view contracts owner actual) tables
      ((front.append (.spent owner answerType caller tail)).append fixed) capture
      base contract.input capturedAfter contract.answer contract.resumeDemand actual :=
    segment_view received consumed
  let moved : OwnerCaptureContracts.SavedSource operations policy (view contracts owner actual) tables
      ((front.append (.spent owner answerType caller tail)).append fixed) capture base capturedAfter (withRow contract actual) :=
    ⟨actual, captured, EffectBounds.covers_refl actual, saved.held⟩
  have past : capturedAfter owner = .consumed := OwnerPhaseTransitions.trace_monotone (OwnerCaptureContracts.saved_transition saved) consumed
  have pendingView := segment_view (actual := actual) pending past
  have start : Source operations policy (view contracts owner actual) tables fixed outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail))
      (OwnerPhaseTransitions.introduce base owner) after output (owner :: (contract.resumeDemand ++ remaining)) (actual ++ restRow) := by
    have current : Derives operations policy (view contracts owner actual)
        (OwnerPhases.ofStack tables ((front.append (.live owner inputType answerType capture caller tail)).append fixed))
        environment scope (OwnerPhaseTransitions.introduce base owner) (.resume binder value) capturedAfter contract.answer
        (owner :: contract.resumeDemand) actual :=
      .resume (contract := withRow contract actual) (view_selected (row := actual) known) resolved permission
        (.stable (row := []) operand (by simp [exportAt, residual_empty]))
        (OwnerCaptureContracts.saved_resume_transition moved consumed)
    exact .checked current pendingView accepted
  obtain ⟨waiting, waitingRow, names, effects, restored⟩ := OwnerSourceResumption.restored_source start (view_selected known) resolved closed.1
    (OwnerCaptureContracts.saved_resume_segment moved consumed) moved.covered
  have sameDemand : remaining = waiting := by simpa only [withRow, List.cons.injEq, true_and, List.append_cancel_left_eq] using names
  have sameRow : restRow = waitingRow := List.append_cancel_left effects
  subst waiting
  subst waitingRow
  rw [OwnerCaptureContracts.spend_introduced consumed] at restored
  exact ⟨.resume binder owner scope caller inputType answerType front capture tail value closed resolved, start, configuration_restore known restored consumed⟩

theorem resume_at_receiver
    (saved : OwnerCaptureContracts.SavedSource operations policy contracts tables originalReceiver capture base capturedAfter contract)
    (consumed : base owner = .consumed)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (permission : (policy binder).resume = true)
    (operand : Summarizes operations environment value contract.input []) (closed : ClosedValue value)
    (pending : Segment operations policy contracts tables fixed
      (front.append (.live owner inputType answerType capture caller tail)) capturedAfter contract.answer after output remaining restRow) :
    ∃ requirements : SourceReinterpretation.Requirements,
      requirements.evaluate (OwnerPhases.ofStack tables originalReceiver) = some saved.actualRow ∧
      ∀ actual, requirements.evaluate (OwnerPhases.ofStack tables ((front.append (.spent owner answerType caller tail)).append fixed)) = some actual →
        checkFootprint outside (actual ++ restRow) = true →
        RawStep ⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩
          ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ [] [.ticket owner] ∧
        Source operations policy (view contracts owner actual) tables fixed outside scope (.resume binder value)
          (front.append (.live owner inputType answerType capture caller tail))
          (OwnerPhaseTransitions.introduce base owner) after output (owner :: (contract.resumeDemand ++ remaining)) (actual ++ restRow) ∧
        Source operations policy contracts tables fixed outside scope value
          (capture.append (front.append (.spent owner answerType caller tail)))
          base after output (contract.resumeDemand ++ remaining) (actual ++ restRow) := by
  obtain ⟨requirements, original, recheck⟩ := SourceReinterpretation.segment_rechecks saved.source
  exact ⟨requirements, original, fun _ checked accepted =>
    resume_from_rechecked saved consumed known resolved permission operand closed pending (recheck _ _ checked) accepted⟩

/-- Adding the established runtime invariant joins the same named resume to
    source specialization. The source base must match the actual ownership map. -/
theorem resume_at_receiver_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (saved : OwnerCaptureContracts.SavedSource operations policy contracts tables originalReceiver capture base capturedAfter contract)
    (consumed : base owner = .consumed)
    (starts : OwnerPhaseTransitions.introduce base owner = OwnerPhaseTransitions.available
      (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (permission : (policy binder).resume = true)
    (operand : Summarizes operations environment value contract.input []) (closed : ClosedValue value)
    (pending : Segment operations policy contracts tables .nil
      (front.append (.live owner inputType answerType capture caller tail)) capturedAfter contract.answer afterPhase output remaining restRow) :
    ∃ requirements : SourceReinterpretation.Requirements,
      requirements.evaluate (OwnerPhases.ofStack tables originalReceiver) = some saved.actualRow ∧
      ∀ actual, requirements.evaluate (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail))) = some actual →
        checkFootprint outside (actual ++ restRow) = true →
        let before : NamedState := ⟨⟨⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
          issued, completed⟩, activations⟩
        let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
        NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket owner]) ∧
        CompletionJoint.Valid declarations policy registry ambient (ScopedPortJoint.advanceState before after [] [.ticket owner]) result outgoing bound ∧
        Trace (OwnerPhaseTransitions.available (ownedTickets before.execution.configuration.stack)) [owner]
          (OwnerPhaseTransitions.available (ownedTickets after.stack)) ∧
        Source operations policy contracts tables .nil outside scope value after.stack
          (OwnerPhaseTransitions.available (ownedTickets after.stack)) afterPhase output
          (contract.resumeDemand ++ remaining) (actual ++ restRow) := by
  obtain ⟨requirements, original, recheck⟩ := resume_at_receiver saved consumed known resolved permission operand closed pending
  refine ⟨requirements, original, ?_⟩
  intro actual checked accepted
  obtain ⟨raw, start, restored⟩ := recheck actual
    (by simpa only [OwnerSourceResumption.stack_append_empty] using checked) accepted
  obtain ⟨step, preserved, transition, projection⟩ := OwnerPhaseTransitions.resume_joint valid resolved closed.1 tables
  have phases := OwnerPhaseTransitions.trace_result transition
  rw [← starts] at phases
  simp only [OwnerPhaseTransitions.spendAll, OwnerCaptureContracts.spend_introduced consumed] at phases
  exact ⟨step, preserved, transition, phases.symm ▸ restored⟩

end Resume

namespace Examples
open SourceReinterpretation.Examples (firstEffect secondEffect secondRow original changedHandler capture tables operations policy locatedRequirements)
open OwnerPhaseTransitions (empty)

def contract : ResumeContract := ⟨.scalar, .scalar, false, [], [], [], none⟩
def contracts : OwnerSource.Contracts := fun owner => if owner = 19 then some contract else none
def front : Stack := .push (.handler changedHandler) .nil
def beforeStack : Stack := front.append (.live 19 .unit .unit capture .none original)
def afterStack : Stack := capture.append (front.append (.spent 19 .unit .none original))
def outside : ProtectionContracts.Context := [.handler secondEffect 5 [(0, SourceReinterpretation.Examples.quiet)]]

theorem extension : OwnerCaptureContracts.Extends SourceReinterpretation.Examples.contracts contracts := by
  intro owner previous known
  simp [SourceReinterpretation.Examples.contracts] at known

def saved : OwnerCaptureContracts.SavedSource operations policy contracts tables original capture empty empty contract :=
  ⟨[], OwnerCaptureContracts.segment_extension SourceReinterpretation.Examples.captured_source extension,
    EffectBounds.covers_refl [], rfl⟩

theorem pending : Segment operations policy contracts tables .nil beforeStack empty .scalar empty .scalar [] [] := by
  have known : contracts 19 = some contract := by simp [contracts]
  exact .push .handler (.live known rfl rfl (.push .handler .nil))

theorem rechecked : locatedRequirements.evaluate (OwnerPhases.ofStack tables ((front.append (.spent 19 .unit .none original)).append .nil)) = some secondRow := by decide

theorem received : Segment operations policy contracts tables
    ((front.append (.spent 19 .unit .none original)).append .nil) capture empty .scalar empty .scalar [] secondRow :=
  OwnerCaptureContracts.segment_extension (SourceReinterpretation.Examples.located_reconstructs rechecked) extension

theorem caller_accepts : checkFootprint outside secondRow = true := by decide
theorem missing_provider_rejected : checkFootprint [] secondRow = false := by decide
theorem cached_bound_still_insufficient : ¬ EffectBounds.Covers contract.resumeRow secondRow :=
  SourceReinterpretation.Examples.old_bound_rejects_new_requirement

/-- This open fragment requires the second effect at its outside interface.
    It demonstrates one actual resume, not full closed-program admission. -/
theorem changed_handler_resume :
    RawStep ⟨.resume 7 .unit, .ticket 7 19, beforeStack⟩ ⟨.unit, .ticket 7 19, afterStack⟩ [] [.ticket 19] ∧
    Source operations policy (view contracts 19 secondRow) tables .nil outside (.ticket 7 19) (.resume 7 .unit) beforeStack
      (OwnerPhaseTransitions.introduce empty 19) empty .scalar [19] secondRow ∧
    Source operations policy contracts tables .nil outside (.ticket 7 19) .unit afterStack
      empty empty .scalar [] secondRow := by
  have result := resume_from_rechecked (front := front) (fixed := Stack.nil) (scope := Execution.Scope.ticket 7 19)
    (binder := 7) (value := Code.unit) (outside := outside) saved rfl (by simp [contracts]) rfl rfl
    (environment := CallableProtection.Environment.empty) Summarizes.unit CallableProtection.Examples.unit_closed pending received
    (by simpa only [List.append_nil] using caller_accepts)
  simpa only [contract, List.nil_append, List.append_nil, beforeStack, afterStack] using result

theorem specialized_record_retains_shape :
    view contracts 19 secondRow 19 = some (withRow contract secondRow) ∧
    (withRow contract secondRow).input = contract.input ∧ (withRow contract secondRow).answer = contract.answer ∧
    (withRow contract secondRow).resumeDemand = contract.resumeDemand ∧
    (withRow contract secondRow).closeRow = contract.closeRow :=
  ⟨view_selected (by simp [contracts]), rfl, rfl, rfl, rfl⟩

theorem actual_owner_phases :
    OwnerPhaseTransitions.introduce empty 19 = OwnerPhaseTransitions.available (ownedTickets beforeStack) ∧
    empty = OwnerPhaseTransitions.available (ownedTickets afterStack) := by
  have beforeOwners : ownedTickets beforeStack = [19] := rfl
  have afterOwners : ownedTickets afterStack = [] := rfl
  rw [beforeOwners, afterOwners]
  constructor
  · funext owner
    simp [OwnerPhaseTransitions.introduce, OwnerPhaseTransitions.available, empty]
  · rfl

theorem source_matches_actual_owners :
    Source operations policy (view contracts 19 secondRow) tables .nil outside (.ticket 7 19) (.resume 7 .unit) beforeStack
      (OwnerPhaseTransitions.available (ownedTickets beforeStack)) empty .scalar [19] secondRow ∧
    Source operations policy contracts tables .nil outside (.ticket 7 19) .unit afterStack
      (OwnerPhaseTransitions.available (ownedTickets afterStack)) empty .scalar [] secondRow := by
  simpa only [← actual_owner_phases.1, ← actual_owner_phases.2] using changed_handler_resume.2

theorem resuming_spent_owner_rejected :
    ¬ Derives operations policy (view contracts 19 secondRow) inside environment (.ticket 7 19) empty
      (.resume 7 .unit) after result demand row := by
  intro source
  exact OwnerSource.resume_consumed_rejected source rfl rfl

theorem shared_port_contract_unchanged :
    (sharedView CoherentSourceTypes.OwnerExamples.registry.contracts 19 secondRow).ports =
      CoherentSourceTypes.OwnerExamples.registry.runtime.joint.effects :=
  (shared_view_ports _).trans (CoherentSourceTypes.Owners.registry_ports _)

end Examples

end Ash.OneShot.ResumeSpecialization

#print axioms Ash.OneShot.ResumeSpecialization.view_selected
#print axioms Ash.OneShot.ResumeSpecialization.view_other
#print axioms Ash.OneShot.ResumeSpecialization.view_entry
#print axioms Ash.OneShot.ResumeSpecialization.trace_excludes_consumed
#print axioms Ash.OneShot.ResumeSpecialization.source_view
#print axioms Ash.OneShot.ResumeSpecialization.context_view
#print axioms Ash.OneShot.ResumeSpecialization.frame_view
#print axioms Ash.OneShot.ResumeSpecialization.segment_view
#print axioms Ash.OneShot.ResumeSpecialization.configuration_view
#print axioms Ash.OneShot.ResumeSpecialization.view_restore
#print axioms Ash.OneShot.ResumeSpecialization.configuration_restore
#print axioms Ash.OneShot.ResumeSpecialization.shared_view_selected
#print axioms Ash.OneShot.ResumeSpecialization.shared_view_source
#print axioms Ash.OneShot.ResumeSpecialization.shared_view_ports
#print axioms Ash.OneShot.ResumeSpecialization.shared_view_other
#print axioms Ash.OneShot.ResumeSpecialization.shared_source_view
#print axioms Ash.OneShot.ResumeSpecialization.shared_resume_source
#print axioms Ash.OneShot.ResumeSpecialization.resume_from_rechecked
#print axioms Ash.OneShot.ResumeSpecialization.resume_at_receiver
#print axioms Ash.OneShot.ResumeSpecialization.resume_at_receiver_joint
#print axioms Ash.OneShot.ResumeSpecialization.Examples.extension
#print axioms Ash.OneShot.ResumeSpecialization.Examples.pending
#print axioms Ash.OneShot.ResumeSpecialization.Examples.rechecked
#print axioms Ash.OneShot.ResumeSpecialization.Examples.received
#print axioms Ash.OneShot.ResumeSpecialization.Examples.caller_accepts
#print axioms Ash.OneShot.ResumeSpecialization.Examples.missing_provider_rejected
#print axioms Ash.OneShot.ResumeSpecialization.Examples.cached_bound_still_insufficient
#print axioms Ash.OneShot.ResumeSpecialization.Examples.changed_handler_resume
#print axioms Ash.OneShot.ResumeSpecialization.Examples.specialized_record_retains_shape
#print axioms Ash.OneShot.ResumeSpecialization.Examples.actual_owner_phases
#print axioms Ash.OneShot.ResumeSpecialization.Examples.source_matches_actual_owners
#print axioms Ash.OneShot.ResumeSpecialization.Examples.resuming_spent_owner_rejected
#print axioms Ash.OneShot.ResumeSpecialization.Examples.shared_port_contract_unchanged
