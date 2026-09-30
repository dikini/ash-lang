import DeclaredConnectedRecomposition

/-! Resumption uses the selected action's saved structural interface. Record
removal, closing-record recomposition, phase transport and ownership uniqueness
reuse the existing declared and recursive proofs.
-/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open DeclaredSourceClosing (Records)
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (Phases Trace available spend spendAll)
open RecursiveConsumption (remove_owner_append)
variable {front capture tail : Stack}

theorem resume_segments
    (source : Segment operations policy contracts tables actions world
      (front.append (.live owner inputType answerType capture caller tail)) contract.answer output pendingDemand pendingRequirements resumes incoming [])
    (closing : Records operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) disposals)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true) (allowed : contract.resumeEffects ⊆ incoming)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (invocation : Checked (resumes ++ disposals)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail)))
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow)
    (pending : Checked (resumes ++ disposals) []
      (spendAll (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
        (owner :: contract.resumeDemand)) pendingRequirements pendingRow) :
    ∃ (combined : Requirements (contract.resumeDemand ++ pendingDemand)) (nextResumes nextDisposals : Store),
      Segment operations policy contracts tables actions world (capture.append (front.append (.spent owner answerType caller tail)))
        contract.input output (contract.resumeDemand ++ pendingDemand) combined nextResumes [] [] ∧
      Records operations policy contracts tables world (capture.append (front.append (.spent owner answerType caller tail))) nextDisposals ∧
      Checked (nextResumes ++ nextDisposals) []
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        combined (resumeRow ++ pendingRow) ∧
      (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm (nextResumes ++ nextDisposals) ∧
      (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))).Nodup ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, waitingEvaluation⟩ :=
    replace_live source known actionKnown permitted
  obtain ⟨nextDisposals, nextClosing, disposalPermutation⟩ := DeclaredSourceClosing.resume_records closing unique
  have resumeUnique := RecursiveTransport.source_records_unique source.source.erase unique
  have ownersUnique := (RecursiveTransport.record_owners_sublist source.source.erase).nodup unique
  have resumePermutation := RecursiveRecomposition.removed_records ownersUnique permutation
  have erasedPermutation : (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm
      ((capturedRecords ++ waitingRecords) ++ nextDisposals) := by
    rw [remove_owner_append]
    exact resumePermutation.append disposalPermutation
  have keysUnique := RecursiveRecords.combined_unique source.source.erase (DeclaredSourceClosing.records_erase closing) unique
  have erasedUnique := RecursiveTransport.remove_owner_unique (owner := owner) keysUnique
  have capturedKnown := RecursiveRecords.lookup_append (second := disposals)
    (RecursiveTransport.lookup_of_member resumeUnique (permutation.mem_iff.mpr List.mem_cons_self))
  obtain ⟨body, selectedContext, actual, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation invocation
  have sameTemplate := Option.some.inj (actual.symm.trans capturedKnown)
  have sameBody := eq_of_heq (Sigma.mk.inj sameTemplate).2
  subst body
  let initial := available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))
  have consumed : spend initial owner owner = .consumed := OwnerPhaseTransitions.spend_self initial owner
  have contexts : RecursiveTransport.normalize (spend initial owner)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail))) =
      RecursiveTransport.normalize (spend initial owner)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail))) := by
    simpa only [List.append_nil] using (RecursiveRecomposition.normalize_replaced (front := front) (capture := capture) (tail := tail)
      (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := []) consumed)
  have bodyWaiting := RecursiveTransport.checked_transport bodyChecked
    (RecursiveTransport.remove_consumed_agrees consumed) contexts
  have bodyCollected := RecursiveTransport.checked_permuted bodyWaiting erasedUnique erasedPermutation
  have consumedAfter : spendAll initial (owner :: contract.resumeDemand) owner = .consumed := by
    rw [OwnerPhaseTransitions.spendAll_at, if_pos List.mem_cons_self]
  have pendingWaiting : Checked (resumes ++ disposals) []
      (spendAll initial (owner :: contract.resumeDemand)) waitingReq pendingRow := by
    apply RecursiveRequirements.evaluate_sound
    rw [waitingEvaluation (resumes ++ disposals) [] _ consumedAfter]
    exact RecursiveRequirements.checked_complete pending
  have pendingErased := RecursiveTransport.checked_remove_consumed pendingWaiting consumedAfter
  have pendingCollected := RecursiveTransport.checked_permuted pendingErased erasedUnique erasedPermutation
  obtain ⟨combined, combinedSource, combinedCheck⟩ := segment_append_checked saved (waiting.input_weaken allowed)
    (receiving := []) (by simpa only [List.append_nil] using bodyCollected) pendingCollected
  have trace := OwnerPhaseTransitions.resume_phase_trace unique
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  change available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) =
    spend initial owner at actualPhases
  rw [← actualPhases] at combinedCheck
  have afterUnique := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).2
  exact ⟨combined, _, nextDisposals, combinedSource, nextClosing, combinedCheck, erasedPermutation, afterUnique, trace⟩

theorem resume_cut_preserves
    (source : State operations policy contracts tables actions world outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail)) output demand row)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value)
    (actionKnown : actions owner = some rights) (permitted : rights.resume = true) :
    ∃ remaining, State operations policy contracts tables actions world outside scope value
      (capture.append (front.append (.spent owner answerType caller tail))) output remaining row ∧
      demand = owner :: remaining ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  cases source with
  | checked current scopeTyped pendingSource closing unique evaluated accepted accounting =>
      subst demand
      cases current with
      | stable summary => cases summary
      | callable summary => cases summary
      | resume known sourceResolved permission operand admitted formed =>
          rename_i contract actualOwner operandDemand operandRequirements
          have sameOwner := Option.some.inj (sourceResolved.symm.trans resolved)
          subst actualOwner
          have noDemand := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase operand) closed.1
          obtain ⟨currentRow, pendingRow, currentChecked, pendingChecked, rows⟩ :=
            RecursiveRequirements.checked_sequence_parts evaluated
          have currentAt := RecursiveRequirements.checked_prepend_iff.mp currentChecked
          simp only [List.append_nil] at currentAt
          obtain ⟨operandRow, resumeRow, operandChecked, resumeChecked, currentRows⟩ :=
            RecursiveRequirements.checked_sequence_parts currentAt
          have operandEmpty := Option.some.inj ((RecursiveRequirements.checked_complete operandChecked).symm.trans
            (RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase operand) closed.1))
          subst operandRow
          simp only [List.nil_append] at currentRows
          subst currentRow
          simp only [noDemand, List.nil_append, spendAll] at resumeChecked pendingChecked
          obtain ⟨combined, nextResumes, nextDisposals, combinedSource, nextClosing, combinedCheck, permutation, afterUnique, trace⟩ :=
            resume_segments pendingSource closing known actionKnown permitted admitted unique resumeChecked pendingChecked
          have acceptedAfter : checkFootprint outside (resumeRow ++ pendingRow) = true := by simpa only [rows] using accepted
          have afterValid := value_configuration
            (DeclaredSourceValues.change_allowed (DeclaredSourceValues.value_summary operand closed.1) closed.1 [])
            closed.1 scopeTyped combinedSource nextClosing afterUnique combinedCheck acceptedAfter
          rw [← rows] at afterValid
          refine ⟨_, afterValid, ?_, trace⟩
          simp only [noDemand, List.nil_append, List.cons_append]


/-- Preserve the complete runtime invariant for the actual resolved boundary.
The source proof and runtime proof use the same cut and consumed owner. -/
theorem resume_preserves
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ output demand row bound)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) :
    ∃ remaining,
      let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
      let state : NamedState := ⟨⟨⟨.resume binder value, scope,
        front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] [.ticket owner]) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] [.ticket owner]) output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := usage
  obtain ⟨rights, actionKnown, permitted⟩ := ScopedActionInterfaces.resume_requires_action code resolved
  have closed := (ContinuationBounds.resume_operand_bound (environment := fun _ => .unknown)
    resolved (DeclaredReturnAdmission.ports before.current.source) isValue).1
  obtain ⟨remaining, next, accounting, trace⟩ := resume_cut_preserves source resolved closed actionKnown permitted
  obtain ⟨runtimeRemaining, step, current, runtimeAccounting⟩ := DeclaredExecution.resume_preserves before.current resolved isValue
  have raw := RawStep.resume binder owner scope caller inputType answerType front capture tail value closed resolved
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  refine ⟨remaining, step, ?_, accounting⟩
  apply assemble_entry before.current raw freshOwners current.names.unique step.checks
    ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ history retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

/-- Current usage determines the owner and live boundary; neither is an
additional progress premise. -/
theorem resume_progress
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : value.IsValue) :
    ∃ after owner remaining,
      NamedAccessStep [] ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Run operations declarations policy registry tables after output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := usage
  obtain ⟨owner, resolved, same⟩ := DeclaredClosingInvariant.resume_owner code
  have present : owner ∈ activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := ScopedPortJoint.active_ticket_has_boundary present
  subst stack
  obtain ⟨remaining, step, next, accounting⟩ := resume_preserves before resolved isValue
  exact ⟨_, owner, remaining, step, next, accounting⟩

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.resume_segments

#print axioms Ash.OneShot.DeclaredConnectedSources.resume_cut_preserves

#print axioms Ash.OneShot.DeclaredConnectedSources.resume_preserves
#print axioms Ash.OneShot.DeclaredConnectedSources.resume_progress
