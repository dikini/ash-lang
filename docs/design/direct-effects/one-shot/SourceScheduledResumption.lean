import SourceScheduledSplitting
import SourceScheduledScopedInvocations
import SourceScheduledRetirement

/-! Resumption recomposes the actual typed saved plan with its caller.
Structural checks come from the invocation rule; ownership and requirement
accounting reuse the existing consumption and recomposition lemmas. -/
namespace Ash.OneShot.SourceScheduledResumption
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value)
open SourceRetainedPlans (Forest)
open SourceScheduledFrames (Segment)
open SourceScheduledChecks (Local)
open SourceScheduledSavedPlans (Saved Matches)
open SourceDependencyOwners (owners)
open SourceScheduledNeutral (OwnerCut)
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (spend spendAll)

theorem owner_cut_append {hints : SourceContextualHints.Hints scope} (front : Forest hints)
    (absent : owner ∉ owners scope) :
    OwnerCut owner (front.append (.live (owner := owner) saved tail)) front saved tail := by
  induction front with
  | nil => exact .hit
  | plain plan rest ih => exact .plain (ih absent)
  | handler rest ih => exact .handler (ih absent)
  | cell rest ih => exact .cell (ih absent)
  | cleanup plan rest ih => exact .cleanup (ih absent)
  | running rest ih => exact .running (ih absent)
  | live saved rest ihSaved ihRest =>
      apply OwnerCut.live
      · intro same; subst owner; exact absent List.mem_cons_self
      · exact ihRest (fun member => absent (List.mem_cons_of_mem _ (List.mem_append_right _ member)))
  | spent rest ih => exact .spent (ih absent)

variable {front capture tail : Stack}

/-- The invocation's restored schedule reconstructs the same typed saved
computation and caller. Neither source nor scheduling of the successor is an
independent premise. -/
theorem replace_live
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      (front.append (.live owner inputType answerType capture caller tail)) input output demand requirements records forest .nil incoming outgoing)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (invocation : Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) forest) :
    ∃ (capturedRequirements : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingRequirements : Requirements demand) (waitingRecords : Store)
      (saved waiting : Saved),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward (spend phases owner) world
        capture contract.input contract.answer contract.resumeDemand capturedRequirements capturedRecords
        saved.forest waiting.forest [] contract.resumeEffects ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward (spend phases owner) world
        (front.append (.spent owner answerType caller tail)) input output demand waitingRequirements waitingRecords
        waiting.forest .nil incoming outgoing ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (capturedRecords ++ waitingRecords)) ∧
      (∀ annotations, Matches annotations forest → Matches annotations (saved.forest.append waiting.forest)) ∧
      ∀ store receiving before, before owner = .consumed →
        evaluate store receiving before waitingRequirements = evaluate store receiving before requirements := by
  obtain ⟨middle, boundary, firstDemand, secondDemand, firstReq, secondReq, firstRecords, secondRecords,
    firstScope, secondScope, firstHints, secondHints, firstForest, secondForest,
    first, second, sameScope, sameHints, sameForest, sameDemand, sameRecords, evaluation⟩ :=
    SourceScheduledFrames.segment_split source
  cases sameScope
  cases sameHints
  cases sameForest
  cases second with
  | live actual actualAction inputAnnotation answerAnnotation scope held saved savedBound rest resume close bound =>
    cases Option.some.inj (actual.symm.trans known)
    cases Option.some.inj (actualAction.symm.trans actionKnown)
    have absent : owner ∉ owners firstScope := by
      intro member
      have owned := recursive_live_tickets_owned front
        (by simpa only [SourceDependencyOwners.realized_owners first.source.source.matches.realizes] using member)
      have separated := (List.nodup_append.mp (by simpa only [owned_tickets_append] using unique)).2.2
      exact separated owner owned owner List.mem_cons_self rfl
    obtain ⟨access, savedCheck, firstCheck, tailCheck⟩ :=
      (SourceScheduledScopedInvocations.resume_iff (owner_cut_append firstForest absent)).mp invocation
    have firstNext := first.recheck firstCheck
    have boundaryNext := Segment.spent known answerAnnotation scope (rest.recheck tailCheck) bound
    obtain ⟨waitingReq, waitingSource, waitingEvaluation⟩ := SourceScheduledFrames.segment_append firstNext boundaryNext
      (SourceDependencyProjection.scope_append_nil _).symm (SourcePlannedRecomposition.hints_append_nil _).symm
      (SourceScheduledRecomposition.forest_append_nil _).symm
    have savedNext := (saved.recheck savedCheck).output_weaken (savedBound permitted)
    subst demand
    subst records
    refine ⟨_, _, waitingReq, _, ⟨_, _, _⟩, ⟨_, _, _⟩, savedNext, waitingSource, ?_, ?_, ?_⟩
    · simpa only [List.append_assoc] using RecursiveRecomposition.move_records
        (prefixRecords := firstRecords) (List.Perm.refl _)
    · intro annotations matched
      exact matched.resume
    · intro store receiving before consumed
      rw [waitingEvaluation, evaluation]
      congr 1
      apply RecursiveTransport.evaluate_transport (fun _ _ => rfl)
      simpa only [Stack.append] using
        (RecursiveRecomposition.normalize_replaced (front := .nil) (capture := capture) (tail := tail)
          (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := receiving) consumed).symm

open RecursiveRequirements (Checked)
open OwnerPhaseTransitions (Trace available)
open RecursiveConsumption (remove_owner_append)

/-- Resumption preserves typed plans together with the established record,
effect and one-shot ownership accounting. -/
theorem resume_segments
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) world
      (front.append (.live owner inputType answerType capture caller tail)) contract.answer output
      pendingDemand pendingRequirements resumes forest .nil incoming [])
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world
      (front.append (.live owner inputType answerType capture caller tail)) disposals)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true) (allowed : contract.resumeEffects ⊆ incoming)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (scheduled : Local outward actions
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) world
      (.invoke (key := ⟨owner, .resume⟩)) forest)
    (invocation : Checked (resumes ++ disposals)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail)))
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow)
    (pending : Checked (resumes ++ disposals) []
      (spendAll (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
        (owner :: contract.resumeDemand)) pendingRequirements pendingRow) :
    ∃ (combined : Requirements (contract.resumeDemand ++ pendingDemand)) (nextResumes nextDisposals : Store)
      (nextForest : Saved),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) world
        (capture.append (front.append (.spent owner answerType caller tail))) contract.input output
        (contract.resumeDemand ++ pendingDemand) combined nextResumes nextForest.forest .nil [] [] ∧
      DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world
        (capture.append (front.append (.spent owner answerType caller tail))) nextDisposals ∧
      Checked (nextResumes ++ nextDisposals) []
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        combined (resumeRow ++ pendingRow) ∧
      (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm (nextResumes ++ nextDisposals) ∧
      nextDisposals ⊆ disposals ∧
      (∀ annotations, Matches annotations forest → Matches annotations nextForest.forest) ∧
      (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))).Nodup ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, savedForest, waitingForest, saved, waiting, permutation, matched, waitingEvaluation⟩ :=
    replace_live source known actionKnown permitted unique scheduled
  obtain ⟨nextDisposals, nextClosing, disposalPermutation⟩ := DeclaredSourceClosing.resume_records closing unique
  have erased := source.source.source.erase.erase
  have resumeUnique := RecursiveTransport.source_records_unique erased.source.erase unique
  have ownersUnique := (RecursiveTransport.record_owners_sublist erased.source.erase).nodup unique
  have resumePermutation := RecursiveRecomposition.removed_records ownersUnique permutation
  have erasedPermutation : (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm
      ((capturedRecords ++ waitingRecords) ++ nextDisposals) := by
    rw [remove_owner_append]
    exact resumePermutation.append disposalPermutation
  have keysUnique := RecursiveRecords.combined_unique erased.source.erase (DeclaredSourceClosing.records_erase closing) unique
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
  simp only [spendAll] at pendingCollected
  obtain ⟨combined, combinedSource, evaluation⟩ := SourceScheduledFrames.segment_append saved (waiting.input_weaken allowed)
    (SourceDependencyProjection.scope_append_nil _).symm (SourcePlannedRecomposition.hints_append_nil _).symm
    (SourceScheduledRecomposition.forest_append_nil _).symm
  have combinedCheck : Checked ((capturedRecords ++ waitingRecords) ++ nextDisposals) []
      (spend initial owner) combined (resumeRow ++ pendingRow) := by
    apply RecursiveRequirements.evaluate_sound
    rw [evaluation, List.append_nil, RecursiveRequirements.checked_complete bodyCollected,
      RecursiveRequirements.checked_complete pendingCollected]
    rfl
  have trace := OwnerPhaseTransitions.resume_phase_trace unique
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  change available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) =
    spend initial owner at actualPhases
  rw [← actualPhases] at combinedCheck
  change Segment _ _ _ _ _ _ _ _ (spend initial owner) _ _ _ _ _ _ _ _ _ _ _ _ at combinedSource
  rw [← actualPhases] at combinedSource
  have afterUnique := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).2
  have disposalSubset : nextDisposals ⊆ disposals := by
    intro entry member
    exact RecursiveTransport.remove_owner_sublist.subset (disposalPermutation.mem_iff.mpr member)
  exact ⟨combined, _, nextDisposals, ⟨_, _, _⟩, combinedSource, nextClosing, combinedCheck, erasedPermutation,
    disposalSubset, matched, afterUnique, trace⟩

private theorem resume_access_rights
    (checked : SourceDependencyCapture.ResumeChecked actions phases owner scope result) :
    ∃ rights, actions owner = some rights ∧ rights.resume = true := by
  cases checked with
  | checked located known permission available => exact ⟨_, known, permission⟩

private theorem contextual_resume_rights
    (checked : SourceContextualInvocations.Resume actions phases owner hints result) :
    ∃ rights, actions owner = some rights ∧ rights.resume = true := by
  cases checked with
  | checked found access compatible => exact resume_access_rights access

private theorem resume_rights
    (checked : Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) forest) :
    ∃ rights, actions owner = some rights ∧ rights.resume = true := by
  cases checked with
  | resume found access same restored => exact contextual_resume_rights access

/-- A ready resume preserves the full scheduled state. Its current invocation
check supplies permission and all checks of the recomposed source. -/
theorem resume_cut_preserves
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.resume binder value) (front.append (.live owner inputType answerType capture caller tail))
      forest output demand row evidence)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ remaining, ∃ nextForest : Saved,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        scope value (capture.append (front.append (.spent owner answerType caller tail))) nextForest.forest output remaining row evidence ∧
      demand = owner :: remaining ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  cases state with
  | checked current scopeTyped pendingSource closing templates matched contextual unique evaluated accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    subst demand
    generalize signatureSame : SourcePlanSignatures.signature plan = currentSignature at current
    cases current with
    | resume known sourceResolved permission operand admitted formed =>
      have sameOwner := Option.some.inj (sourceResolved.symm.trans resolved)
      cases sameOwner
      cases plan with
      | sequence operandPlan invocationPlan =>
        cases invocationPlan
        have scheduled := by
          cases contextual with
          | sequence operandCheck invocationCheck => exact invocationCheck
        obtain ⟨rights, actionKnown, permitted⟩ := resume_rights scheduled
        have erasedOperand := DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
          (SourcePlannedSources.expression_erase operand))
        have noDemand := SourceTemplates.expression_value_demand erasedOperand closed.1
        obtain ⟨currentRow, pendingRow, currentChecked, pendingChecked, rows⟩ :=
          RecursiveRequirements.checked_sequence_parts evaluated
        have currentAt := RecursiveRequirements.checked_prepend_iff.mp currentChecked
        simp only [List.append_nil] at currentAt
        obtain ⟨operandRow, resumeRow, operandChecked, resumeChecked, currentRows⟩ :=
          RecursiveRequirements.checked_sequence_parts currentAt
        have operandEmpty := Option.some.inj ((RecursiveRequirements.checked_complete operandChecked).symm.trans
          (RecursiveRecomposition.value_evaluation erasedOperand closed.1))
        subst operandRow
        simp only [List.nil_append] at currentRows
        subst currentRow
        simp only [noDemand, List.nil_append, spendAll] at resumeChecked pendingChecked
        obtain ⟨combined, nextResumes, nextDisposals, nextForest, combinedSource, nextClosing, combinedCheck,
          permutation, disposalSubset, nextMatches, afterUnique, trace⟩ :=
          resume_segments pendingSource closing known actionKnown permitted admitted unique scheduled resumeChecked pendingChecked
        have raw := RawStep.resume binder owner scope caller inputType answerType front capture tail value closed resolved
        have templatesAfter := templates.after_step nextClosing disposalSubset raw (by simp) unique
        have acceptedAfter : checkFootprint outside (resumeRow ++ pendingRow) = true := by simpa only [rows] using accepted
        have afterValid := SourceScheduledValues.value_configuration
          (SourcePlannedSources.Values.change_allowed (SourcePlannedSources.Values.summary operand closed.1) closed.1 [])
          closed.1 scopeTyped combinedSource nextClosing templatesAfter (nextMatches annotations matched) afterUnique combinedCheck acceptedAfter
        rw [← rows] at afterValid
        refine ⟨_, nextForest, afterValid, ?_, trace⟩
        simp only [noDemand, List.nil_append, List.cons_append]

end Ash.OneShot.SourceScheduledResumption

#print axioms Ash.OneShot.SourceScheduledResumption.replace_live

#print axioms Ash.OneShot.SourceScheduledResumption.resume_segments

#print axioms Ash.OneShot.SourceScheduledResumption.resume_cut_preserves

#print axioms Ash.OneShot.SourceScheduledResumption.owner_cut_append
