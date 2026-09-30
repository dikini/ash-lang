import DeclaredSourceStates
import AnnotatedRecomposition

/-! One-shot resumption retains hereditary evidence in the restored capture
and waiting caller. Record authentication, removal, phase transition and
uniqueness reuse RecursiveConsumption and RecursiveTransport. -/
namespace Ash.OneShot.DeclaredSourceResumption
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open DeclaredSourceFrames (Segment)
open DeclaredSourceStates (CheckedState)
open DeclaredSourceClosing (Records)
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (Phases Trace available spend spendAll)
open RecursiveConsumption (remove_owner_append)
variable {front capture tail : Stack}

theorem resume_segments
    (source : Segment operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) contract.answer output pendingDemand pendingRequirements resumes)
    (closing : Records operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) disposals)
    (known : contracts owner = some contract)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (invocation : Checked (resumes ++ disposals)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail)))
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow)
    (pending : Checked (resumes ++ disposals) []
      (spendAll (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
        (owner :: contract.resumeDemand)) pendingRequirements pendingRow) :
    ∃ (combined : Requirements (contract.resumeDemand ++ pendingDemand)) (nextResumes nextDisposals : Store),
      Segment operations policy contracts tables world (capture.append (front.append (.spent owner answerType caller tail)))
        contract.input output (contract.resumeDemand ++ pendingDemand) combined nextResumes ∧
      Records operations policy contracts tables world (capture.append (front.append (.spent owner answerType caller tail))) nextDisposals ∧
      Checked (nextResumes ++ nextDisposals) []
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        combined (resumeRow ++ pendingRow) ∧
      (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm (nextResumes ++ nextDisposals) ∧
      (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))).Nodup ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, waitingEvaluation⟩ :=
    AnnotatedRecomposition.replace_live source known
  obtain ⟨nextDisposals, nextClosing, disposalPermutation⟩ := DeclaredSourceClosing.resume_records closing unique
  have resumeUnique := RecursiveTransport.source_records_unique source.erase unique
  have ownersUnique := (RecursiveTransport.record_owners_sublist source.erase).nodup unique
  have resumePermutation := RecursiveRecomposition.removed_records ownersUnique permutation
  have erasedPermutation : (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm
      ((capturedRecords ++ waitingRecords) ++ nextDisposals) := by
    rw [remove_owner_append]
    exact resumePermutation.append disposalPermutation
  have keysUnique := RecursiveRecords.combined_unique source.erase (DeclaredSourceClosing.records_erase closing) unique
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
  obtain ⟨combined, combinedSource, combinedCheck⟩ := AnnotatedRecomposition.segment_append_checked saved waiting
    (receiving := []) (by simpa only [List.append_nil] using bodyCollected) pendingCollected
  have trace := OwnerPhaseTransitions.resume_phase_trace unique
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  change available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) =
    spend initial owner at actualPhases
  rw [← actualPhases] at combinedCheck
  have afterUnique := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).2
  exact ⟨combined, _, nextDisposals, combinedSource, nextClosing, combinedCheck, erasedPermutation, afterUnique, trace⟩

theorem resume_cut_preserves
    (source : CheckedState operations policy contracts tables world outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail)) output demand row)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ remaining, CheckedState operations policy contracts tables world outside scope value
      (capture.append (front.append (.spent owner answerType caller tail))) output remaining row ∧
      demand = owner :: remaining ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  cases source with
  | checked source closing unique evaluated accepted => cases source with
      | checked current scopeTyped pendingSource => cases current with
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
                resume_segments pendingSource closing known unique resumeChecked pendingChecked
              let restored := capture.append (front.append (.spent owner answerType caller tail))
              have valueChecked : Checked (nextResumes ++ nextDisposals) [] (available (ownedTickets restored))
                  (.request (OwnerPhases.ofStack tables restored) []) [] := .request (by simp [OwnerSource.exportAt, residual_empty])
              have afterSource := DeclaredSourceStates.Configuration.checked
                (DeclaredSourceValues.expression (DeclaredSourceValues.value_summary operand closed.1) _) scopeTyped combinedSource
              have acceptedAfter : checkFootprint outside (resumeRow ++ pendingRow) = true := by simpa only [rows] using accepted
              have afterValid := CheckedState.checked afterSource nextClosing afterUnique
                (Checked.sequence valueChecked combinedCheck) acceptedAfter
              rw [← rows] at afterValid
              refine ⟨_, afterValid, ?_, trace⟩
              simp only [noDemand, List.nil_append, List.cons_append]

theorem resume_step_preserves
    (source : CheckedState operations policy contracts tables world outside scope (.resume binder value) stack output demand row)
    (closed : ClosedValue value) (step : RawStep ⟨.resume binder value, scope, stack⟩ next created completed) :
    ∃ owner remaining, next.expression = value ∧ next.scope = scope ∧
      CheckedState operations policy contracts tables world outside next.scope next.expression next.stack output remaining row ∧
      demand = owner :: remaining ∧ created = [] ∧ completed = [.ticket owner] ∧
      Trace (available (ownedTickets stack)) [owner] (available (ownedTickets next.stack)) := by
  cases step with
  | focus plain focus tail => exact False.elim (RecursiveRecomposition.focus_resume_not_value focus closed.1)
  | plug plain value impossible scope tail => cases impossible.1
  | leaveHandler handler value impossible scope tail => cases impossible.1
  | leaveCell identity payload answer savedScope scope value impossible tail => cases impossible.1
  | startCleanup action saved impossible scope tail => cases impossible.1
  | leaveClause ticket answer value impossible scope caller tail => cases impossible.1
  | resume binder owner scope caller inputType answerType front capture tail value ready resolved =>
      obtain ⟨remaining, checked, demand, trace⟩ := resume_cut_preserves source resolved closed
      exact ⟨owner, remaining, rfl, rfl, checked, demand, rfl, rfl, trace⟩

theorem resume_progress
    (source : CheckedState operations policy contracts tables world outside scope (.resume binder value) stack output demand row)
    (closed : ClosedValue value) :
    ∃ owner restored, RawStep ⟨.resume binder value, scope, stack⟩ ⟨value, scope, restored⟩ [] [.ticket owner] :=
  RecursiveConsumption.resume_progress (DeclaredSourceStates.checked_state_erase source) closed

theorem resume_preserves
    (source : CheckedState operations policy contracts tables world outside scope (.resume binder value) stack output demand row)
    (closed : ClosedValue value) :
    ∃ owner restored remaining,
      RawStep ⟨.resume binder value, scope, stack⟩ ⟨value, scope, restored⟩ [] [.ticket owner] ∧
      CheckedState operations policy contracts tables world outside scope value restored output remaining row ∧
      demand = owner :: remaining ∧ Trace (available (ownedTickets stack)) [owner] (available (ownedTickets restored)) := by
  obtain ⟨owner, restored, step⟩ := resume_progress source closed
  obtain ⟨actual, remaining, valueSame, scopeSame, checked, demand, created, completed, transition⟩ := resume_step_preserves source closed step
  have sameOwner : owner = actual := Owner.ticket.inj (List.cons.inj completed).1
  subst actual
  exact ⟨owner, restored, remaining, step, checked, demand, transition⟩


end Ash.OneShot.DeclaredSourceResumption

#print axioms Ash.OneShot.DeclaredSourceResumption.resume_segments
#print axioms Ash.OneShot.DeclaredSourceResumption.resume_cut_preserves
#print axioms Ash.OneShot.DeclaredSourceResumption.resume_step_preserves
#print axioms Ash.OneShot.DeclaredSourceResumption.resume_progress
#print axioms Ash.OneShot.DeclaredSourceResumption.resume_preserves
