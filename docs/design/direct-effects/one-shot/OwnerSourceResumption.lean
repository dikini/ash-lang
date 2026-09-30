import OwnerSource

/-!
Source preservation for one-shot restoration. Interpretation transport is
restricted to phase maps where the resumed owner has already been consumed;
it does not move handlers or erase a restored protected frame.
-/

namespace Ash.OneShot.OwnerSourceResumption
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open OwnerPhaseTransitions (Phases Trace spend project)
open OwnerSource

theorem stack_append_empty (stack : Stack) : stack.append .nil = stack := by
  induction stack with
  | nil => rfl
  | push frame rest ih => exact congrArg (Stack.push frame) ih
  | live owner input answer saved caller rest ihSaved ihRest => exact congrArg (Stack.live owner input answer saved caller) ihRest
  | spent owner answer caller rest ih => exact congrArg (Stack.spent owner answer caller) ih

theorem source_inside_spent
    (source : Derives operations policy contracts first environment scope before code after result demand row)
    (spent : before owner = .consumed)
    (same : ∀ phases, phases owner = .consumed → ∀ raw, exportAt first phases raw = exportAt second phases raw) :
    Derives operations policy contracts second environment scope before code after result demand row := by
  induction source with
  | stable summary exported => exact .stable summary ((same _ spent _).symm.trans exported)
  | pair left right ihLeft ihRight => exact .pair (ihLeft spent) (ihRight (source_monotone left spent))
  | app function argument exported ihFunction ihArgument =>
      have middle := source_monotone function spent
      exact .app (ihFunction spent) (ihArgument middle) ((same _ (source_monotone argument middle) _).symm.trans exported)
  | bind initializer body ihInit ihBody => exact .bind (ihInit spent) (ihBody (source_monotone initializer spent))
  | branch condition yes no ihCondition ihYes ihNo =>
      have middle := source_monotone condition spent
      exact .branch (ihCondition spent) (ihYes middle) (ihNo middle)
  | perform known operand exported ih =>
      exact .perform known (ih spent) ((same _ (source_monotone operand spent) _).symm.trans exported)
  | resume known resolved allowed operand transition ih => exact .resume known resolved allowed (ih spent) transition
  | discard known resolved allowed unprotected closable transition => exact .discard known resolved allowed unprotected closable transition
  | cleanup callback body exported ihCallback ihBody =>
      have middle := source_monotone callback spent
      apply Derives.cleanup (ihCallback spent) (ihBody middle)
      simp only [residualize, DisposalProtection.through_barrier] at exported ⊢
      exact (same _ (source_monotone body middle) _).symm.trans exported
  | resource initializer body outward exported ih =>
      exact .resource (ih spent) body outward ((same _ (source_monotone initializer spent) _).symm.trans exported)

theorem context_inside_spent
    (source : ContextDerives operations policy contracts first environment scope position before input after output demand row)
    (spent : before owner = .consumed)
    (same : ∀ phases, phases owner = .consumed → ∀ raw, exportAt first phases raw = exportAt second phases raw) :
    ContextDerives operations policy contracts second environment scope position before input after output demand row := by
  cases source with
  | pairLeft right => exact .pairLeft (source_inside_spent right spent same)
  | pairRight left => exact .pairRight left
  | appFunction argument exported =>
      exact .appFunction (source_inside_spent argument spent same) ((same _ (source_monotone argument spent) _).symm.trans exported)
  | appArgument function exported => exact .appArgument function ((same _ spent _).symm.trans exported)
  | bind body => exact .bind (source_inside_spent body spent same)
  | branch yes no => exact .branch (source_inside_spent yes spent same) (source_inside_spent no spent same)
  | perform known exported => exact .perform known ((same _ spent _).symm.trans exported)
  | resume known resolved allowed transition => exact .resume known resolved allowed transition
  | cleanup body exported =>
      apply ContextDerives.cleanup (source_inside_spent body spent same)
      simp only [residualize, DisposalProtection.through_barrier] at exported ⊢
      exact (same _ (source_monotone body spent) _).symm.trans exported
  | resource body outward exported => exact .resource body outward ((same _ spent _).symm.trans exported)

theorem frame_inside_spent
    (source : FrameSource operations policy contracts first frame before input after output demand row)
    (spent : before owner = .consumed)
    (same : ∀ phases, phases owner = .consumed → ∀ raw, exportAt first phases raw = exportAt second phases raw) :
    FrameSource operations policy contracts second frame before input after output demand row := by
  cases source with
  | plain source => exact .plain (context_inside_spent source spent same)
  | handler => exact .handler
  | cell => exact .cell
  | armed callback exported => exact .armed callback ((same _ spent _).symm.trans exported)
  | running saved => exact .running saved
  | closing => exact .closing
  | retiring transition => exact .retiring transition

theorem export_prefix_spent (front : Stack)
    (same : ∀ phases, phases owner = .consumed →
      project (OwnerPhases.ofStack tables first) phases = project (OwnerPhases.ofStack tables second) phases)
    (spent : phases owner = .consumed) :
    exportAt (OwnerPhases.ofStack tables (front.append first)) phases raw =
      exportAt (OwnerPhases.ofStack tables (front.append second)) phases raw := by
  simp only [exportAt, OwnerPhases.stack_append, OwnerPhaseTransitions.project_append, same phases spent]

theorem segment_fixed_spent
    (source : Segment operations policy contracts tables first segment before input after output demand row)
    (spent : before owner = .consumed)
    (same : ∀ phases, phases owner = .consumed →
      project (OwnerPhases.ofStack tables first) phases = project (OwnerPhases.ofStack tables second) phases) :
    Segment operations policy contracts tables second segment before input after output demand row := by
  induction source with
  | nil => exact .nil
  | push head tail ih =>
      exact .push (frame_inside_spent head spent (fun phases consumed raw => export_prefix_spent _ same consumed))
        (ih (OwnerPhaseTransitions.trace_monotone (frame_trace head) spent))
  | live known held consumed tail ih => exact .live known held consumed (ih spent)
  | spent known consumed tail ih => exact .spent known consumed (ih spent)

theorem live_spent_project (spent : phases owner = .consumed) :
    project (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)) phases =
      project (OwnerPhases.ofStack tables (.spent owner answerType caller tail)) phases := by
  simp [OwnerPhases.ofStack, project, spent]

section Restoration
variable {front capture tail fixed : Stack}

/-- The pending caller retains every frame and every other live group. Only
    the selected owner's physical marker changes, after its source phase has
    already been consumed by the resumed computation. -/
theorem pending_live_to_spent
    (source : Segment operations policy contracts tables fixed
      (front.append (.live owner inputType answerType capture caller tail)) before input after output demand row)
    (spent : before owner = .consumed) :
    Segment operations policy contracts tables fixed
      (front.append (.spent owner answerType caller tail)) before input after output demand row := by
  obtain ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ :=
    segment_decompose (front := front) source
  cases second with
  | live known held consumed rest =>
      have changed := segment_fixed_spent first spent (fun phases done => live_spent_project
        (tables := tables) (capture := capture) (caller := caller) (inputType := inputType)
        (answerType := answerType) (tail := tail.append fixed) done)
      rw [names, effects]
      exact segment_append changed (.spent known consumed rest)

theorem resume_source_parts
    (source : Source operations policy contracts tables fixed outside scope (.resume binder value) segment before after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (isValue : value.IsValue) :
    ∃ environment middle remaining restRow,
      Summarizes operations environment value contract.input [] ∧
      Trace before (owner :: contract.resumeDemand) middle ∧
      Segment operations policy contracts tables fixed segment middle contract.answer after output remaining restRow ∧
      demand = owner :: (contract.resumeDemand ++ remaining) ∧
      row = contract.resumeRow ++ restRow ∧ checkFootprint outside row = true := by
  cases source with
  | checked current pending accepted => cases current with
      | stable summary exported => cases summary
      | resume actual target allowed operand transition =>
          have ownerSame := Option.some.inj (target.symm.trans resolved)
          subst_vars
          have contractSame := Option.some.inj (actual.symm.trans known)
          subst_vars
          obtain ⟨summary, phases, noDemand, noRow⟩ := value_summary operand isValue
          subst_vars
          exact ⟨_, _, _, _, summary, transition, pending, rfl, rfl, accepted⟩

/-- The saved derivation is checked at the actual restored suffix, including
    arbitrary waiting frames. A row bound alone cannot supply this premise. -/
theorem restored_source
    (source : Source operations policy contracts tables fixed outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail)) before after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (isValue : value.IsValue)
    (saved : Segment operations policy contracts tables
      ((front.append (.spent owner answerType caller tail)).append fixed) capture
      (spend before owner) contract.input
      (OwnerPhaseTransitions.spendAll before (owner :: contract.resumeDemand)) contract.answer
      contract.resumeDemand actualRow)
    (covered : EffectBounds.Covers contract.resumeRow actualRow) :
    ∃ remaining restRow,
      demand = owner :: (contract.resumeDemand ++ remaining) ∧ row = contract.resumeRow ++ restRow ∧
      Source operations policy contracts tables fixed outside scope value
        (capture.append (front.append (.spent owner answerType caller tail)))
        (spend before owner) after output (contract.resumeDemand ++ remaining) (actualRow ++ restRow) := by
  obtain ⟨environment, middle, remaining, restRow, valueSource, transition, pending, names, effects, accepted⟩ :=
    resume_source_parts source known resolved isValue
  have consumed := OwnerPhaseTransitions.trace_consumed transition (List.mem_cons_self (a := owner) (l := contract.resumeDemand))
  have changed := pending_live_to_spent pending consumed
  have endpoint := OwnerPhaseTransitions.trace_result transition
  rw [endpoint] at changed
  have composed := segment_append saved changed
  have acceptedActual := EffectBounds.check_covered (effects ▸ accepted)
    (EffectBounds.covers_append_bounds covered (EffectBounds.covers_refl restRow))
  have restored := Source.checked
    (Derives.stable (scope := scope) (phases := spend before owner) (row := []) valueSource
      (by simp [exportAt, residual_empty])) composed (by simpa only [List.nil_append] using acceptedActual)
  exact ⟨remaining, restRow, names, effects, by simpa only [List.nil_append] using restored⟩

/-- The source transition and the ownership transition describe the same
    named runtime step. The resulting source map is the actual restored
    stack's ownership map, not a separately chosen annotation. -/
theorem resume_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (isValue : value.IsValue)
    (source : Source operations policy contracts tables .nil outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail))
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      finalPhase output demand row)
    (saved : Segment operations policy contracts tables
      (front.append (.spent owner answerType caller tail)) capture
      (spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner)
      contract.input
      (OwnerPhaseTransitions.spendAll
        (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
        (owner :: contract.resumeDemand)) contract.answer contract.resumeDemand actualRow)
    (covered : EffectBounds.Covers contract.resumeRow actualRow) :
    let before : NamedState := ⟨⟨⟨.resume binder value, scope,
      front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket owner]) ∧
    CompletionJoint.Valid declarations policy registry ambient
      (ScopedPortJoint.advanceState before after [] [.ticket owner]) result outgoing bound ∧
    Trace (OwnerPhaseTransitions.available (ownedTickets before.execution.configuration.stack)) [owner]
      (OwnerPhaseTransitions.available (ownedTickets after.stack)) ∧
    ∃ remaining restRow,
      demand = owner :: (contract.resumeDemand ++ remaining) ∧ row = contract.resumeRow ++ restRow ∧
      Source operations policy contracts tables .nil outside scope value after.stack
        (OwnerPhaseTransitions.available (ownedTickets after.stack)) finalPhase output
        (contract.resumeDemand ++ remaining) (actualRow ++ restRow) := by
  obtain ⟨step, preserved, transition, _⟩ := OwnerPhaseTransitions.resume_joint valid resolved isValue tables
  obtain ⟨remaining, restRow, names, effects, restored⟩ := restored_source source known resolved isValue
    (by simpa only [stack_append_empty] using saved) covered
  have phases := OwnerPhaseTransitions.trace_result transition
  change OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) =
    spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner at phases
  exact ⟨step, preserved, transition, remaining, restRow, names, effects, phases.symm ▸ restored⟩

end Restoration

namespace Examples
open OpenOwnerUses.Examples (operations policy tickets tables tail)
open OwnerPhaseTransitions.Examples (capture beforeResume afterResume)
open OwnerSource.Examples (contracts captured initial)

theorem restored_initial_map :
    spend (OwnerPhaseTransitions.available (ownedTickets beforeResume.stack)) 19 = initial := by
  have after := OwnerPhaseTransitions.trace_result OwnerPhaseTransitions.Examples.actual_phase_transition
  exact after.symm

theorem saved_at_actual_suffix : Segment operations policy contracts tables
    (.spent 19 .integer (.ticket 10 9) tail) capture
    (spend (OwnerPhaseTransitions.available (ownedTickets beforeResume.stack)) 19) captured.input
    (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets beforeResume.stack))
      (19 :: captured.resumeDemand)) captured.answer captured.resumeDemand [] := by
  rw [restored_initial_map]
  change Segment operations policy contracts tables _ capture initial .scalar
    (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets beforeResume.stack)) [19, 29, 9]) .scalar [29, 9] []
  rw [← OwnerPhaseTransitions.trace_result OwnerSource.Examples.restoration_source_trace]
  exact OwnerSource.Examples.captured_source _

/-- This after-source is derived from the before-source through the general
    theorem; the existing hand-built after-source is not a premise. -/
theorem source_from_before : Source operations policy contracts tables .nil [] (.ticket 20 19) .unit
    afterResume.stack (OwnerPhaseTransitions.available (ownedTickets afterResume.stack))
    OwnerPhaseTransitions.empty .scalar [29, 9] [] := by
  obtain ⟨remaining, restRow, names, effects, restored⟩ := restored_source
    (front := .nil) OwnerSource.Examples.before_resume_source
    (contract := captured) rfl rfl trivial
    (by simpa only [Stack.append, stack_append_empty] using saved_at_actual_suffix) (EffectBounds.covers_refl [])
  have emptyDemand : remaining = [] := by simpa [captured] using names.symm
  have emptyRow : restRow = [] := effects.symm
  subst remaining
  subst restRow
  have phases := OwnerPhaseTransitions.trace_result OwnerPhaseTransitions.Examples.actual_phase_transition
  change OwnerPhaseTransitions.available (ownedTickets afterResume.stack) =
    spend (OwnerPhaseTransitions.available (ownedTickets beforeResume.stack)) 19 at phases
  rw [← phases] at restored
  exact restored

theorem restored_runtime_evidence :
    RawStep beforeResume afterResume [] [.ticket 19] ∧
    ConfigurationUsage policy tickets afterResume ∧
    Source operations policy contracts tables .nil [] afterResume.scope afterResume.expression afterResume.stack
      (OwnerPhaseTransitions.available (ownedTickets afterResume.stack))
      OwnerPhaseTransitions.empty .scalar [29, 9] [] :=
  ⟨OwnerPhaseTransitions.Examples.actual_resume, OwnerPhaseTransitions.Examples.after_resume_usage, source_from_before⟩

theorem resumption_does_not_consume_nested_owners :
    (OwnerPhaseTransitions.available (ownedTickets afterResume.stack)) 19 = .consumed ∧
    (OwnerPhaseTransitions.available (ownedTickets afterResume.stack)) 29 = .available ∧
    (OwnerPhaseTransitions.available (ownedTickets afterResume.stack)) 9 = .available := by decide

theorem second_resume_rejected :
    ¬ Derives operations policy contracts inside environment (.ticket 20 19)
      (OwnerPhaseTransitions.available (ownedTickets afterResume.stack)) (.resume 20 .unit) after result demand row :=
  fun source => resume_consumed_rejected source rfl rfl

/-- Removing the phase premise would erase a still-live protection barrier. -/
theorem available_marker_not_equivalent :
    exportAt [.live 19 true] (OwnerPhaseTransitions.available [19]) [⟨.user 71 [], 0, false⟩] ≠
      exportAt [.spent 19] (OwnerPhaseTransitions.available [19]) [⟨.user 71 [], 0, false⟩] := by decide

/-- Spending the owner does not erase a running cleanup restored above it. -/
theorem restored_barrier_retained :
    exportAt [.ordinary (.barrier true), .spent 19] OwnerPhaseTransitions.empty [⟨.user 71 [], 0, false⟩] =
      some [⟨.user 71 [], 0, true⟩] := by decide

end Examples

end Ash.OneShot.OwnerSourceResumption

#print axioms Ash.OneShot.OwnerSourceResumption.stack_append_empty
#print axioms Ash.OneShot.OwnerSourceResumption.source_inside_spent
#print axioms Ash.OneShot.OwnerSourceResumption.context_inside_spent
#print axioms Ash.OneShot.OwnerSourceResumption.frame_inside_spent
#print axioms Ash.OneShot.OwnerSourceResumption.export_prefix_spent
#print axioms Ash.OneShot.OwnerSourceResumption.segment_fixed_spent
#print axioms Ash.OneShot.OwnerSourceResumption.live_spent_project
#print axioms Ash.OneShot.OwnerSourceResumption.pending_live_to_spent
#print axioms Ash.OneShot.OwnerSourceResumption.resume_source_parts
#print axioms Ash.OneShot.OwnerSourceResumption.restored_source
#print axioms Ash.OneShot.OwnerSourceResumption.resume_joint
#print axioms Ash.OneShot.OwnerSourceResumption.Examples.restored_initial_map
#print axioms Ash.OneShot.OwnerSourceResumption.Examples.saved_at_actual_suffix
#print axioms Ash.OneShot.OwnerSourceResumption.Examples.source_from_before
#print axioms Ash.OneShot.OwnerSourceResumption.Examples.restored_runtime_evidence
#print axioms Ash.OneShot.OwnerSourceResumption.Examples.resumption_does_not_consume_nested_owners
#print axioms Ash.OneShot.OwnerSourceResumption.Examples.second_resume_rejected
#print axioms Ash.OneShot.OwnerSourceResumption.Examples.available_marker_not_equivalent
#print axioms Ash.OneShot.OwnerSourceResumption.Examples.restored_barrier_retained
