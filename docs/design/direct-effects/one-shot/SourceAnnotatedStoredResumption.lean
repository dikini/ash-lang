import SourceAnnotatedStoredState
import SourceAnnotatedStoredCuts
import SourceConsumingBoundResumption

/-! One-shot resumption keeps the original stored declaration packets paired
with their source while moving the saved computation above its caller. Existing
requirement, phase and ownership proofs account for the consumed owner. -/
namespace Ash.OneShot.SourceConsumingStoredBounds
open SourceAnnotatedRuntime (Stack)
variable {families : SourceDependencyCapture.Families} {front capture tail : Stack}

def StackBounds.resumeSaved
    (stored : StackBounds families (front.append (.live owner input answer capture caller tail))) :
    StackBounds families capture :=
  match (stored.splitAt front (.live owner input answer capture caller tail)).2 with
  | .live saved _ => saved

def StackBounds.resumeWaiting
    (stored : StackBounds families (front.append (.live owner input answer capture caller tail))) :
    StackBounds families (front.append (.spent owner answer caller tail)) :=
  let parts := stored.splitAt front (.live owner input answer capture caller tail)
  match parts.2 with
  | .live _ remaining => parts.1.append (.spent remaining)

theorem StackBounds.resume_parts
    (stored : StackBounds families (front.append (.live owner input answer capture caller tail))) :
    stored.resumeSaved.append stored.resumeWaiting = stored.resume := by
  unfold StackBounds.resumeSaved StackBounds.resumeWaiting StackBounds.resume
  generalize stored.splitAt front (.live owner input answer capture caller tail) = parts
  rcases parts with ⟨first, second⟩
  cases second
  rfl

end Ash.OneShot.SourceConsumingStoredBounds

namespace Ash.OneShot.SourceAnnotatedStoredResumption

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value)
open SourceRetainedPlans (Forest)
open SourceAnnotatedStoredTyping (Segment)
open SourceConsumingStoredBounds (StackBounds)
open SourceScheduledChecks (Local)
open SourceScheduledSavedPlans (Saved Matches)
open SourceDependencyOwners (owners)
open SourceScheduledResumption (owner_cut_append)
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (spend spendAll)

variable {front capture tail : SourceAnnotatedRuntime.Stack}

theorem value_configuration_atPackets
    (summary : SourceAnnotatedSources.ValueSummary operations policy contracts world (fun _ => none) [] code input)
    (isValue : code.erase.IsValue)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket)
    (pending : SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world stack input output demand requirements records forest .nil incoming [] stored)
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
    (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (unique : (ownedTickets stack.erase).Nodup)
    (checked : RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase)) requirements row)
    (accepted : checkFootprint outside row = true) :
    SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code stack .pure forest output demand row stored evidence := by
  have current : RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase))
      ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables stack.erase)) [] :=
    .request (row := []) (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  exact .checked (SourceAnnotatedSources.Values.change_context summary isValue incoming scope) scopeTyped
    pending closing templates matched .pure unique
    (by simpa only [List.nil_append] using RecursiveRequirements.Checked.sequence current checked) accepted rfl

/-- The invocation's restored schedule reconstructs the same typed saved
computation and caller. Neither source nor scheduling of the successor is an
independent premise. -/
theorem replace_live [SourceScheduledChecks.DeclarationProjection admission certification]
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      (front.append (.live owner inputType answerType capture caller tail)) input output demand requirements records forest .nil incoming outgoing stored)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true)
    (unique : (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase))).Nodup)
    (invocation : Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) forest) :
    ∃ (capturedRequirements : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingRequirements : Requirements demand) (waitingRecords : Store)
      (saved waiting : Saved),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward (spend phases owner) world
        capture contract.input contract.answer contract.resumeDemand capturedRequirements capturedRecords
        saved.forest waiting.forest [] contract.resumeEffects stored.resumeSaved ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward (spend phases owner) world
        (front.append (.spent owner answerType caller tail)) input output demand waitingRequirements waitingRecords
        waiting.forest .nil incoming outgoing stored.resumeWaiting ∧
      SourceBoundSnapshots.ResumeForest owner forest (saved.forest.append waiting.forest) ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (capturedRecords ++ waitingRecords)) ∧
      (∀ annotations, Matches annotations forest → Matches annotations (saved.forest.append waiting.forest)) ∧
      ∀ store receiving before, before owner = .consumed →
        evaluate store receiving before waitingRequirements = evaluate store receiving before requirements := by
  obtain ⟨middle, boundary, firstDemand, secondDemand, firstReq, secondReq, firstRecords, secondRecords,
    firstScope, secondScope, firstHints, secondHints, firstForest, secondForest,
    first, second, sameScope, sameHints, sameForest, sameDemand, sameRecords, evaluation⟩ :=
    SourceAnnotatedStoredTyping.segment_split source
  cases sameScope
  cases sameHints
  cases sameForest
  unfold StackBounds.resumeSaved StackBounds.resumeWaiting
  generalize piecesKnown : stored.splitAt front (.live owner inputType answerType capture caller tail) = pieces at *
  rcases pieces with ⟨firstStored, secondStored⟩
  dsimp only [Prod.fst, Prod.snd] at *
  cases second with
  | live actual actualAction inputAnnotation answerAnnotation scope held saved savedBound rest resume close bound =>
    cases Option.some.inj (actual.symm.trans known)
    cases Option.some.inj (actualAction.symm.trans actionKnown)
    have absent : owner ∉ owners firstScope := by
      intro member
      have owned := recursive_live_tickets_owned front.erase
        (by simpa only [SourceDependencyOwners.realized_owners first.forget.erase.source.source.matches.realizes] using member)
      have separated := (List.nodup_append.mp (by simpa only [owned_tickets_append] using unique)).2.2
      exact separated owner owned owner List.mem_cons_self rfl
    obtain ⟨access, savedCheck, firstCheck, tailCheck⟩ :=
      (SourceScheduledScopedInvocations.resume_iff (owner_cut_append firstForest absent)).mp invocation
    have firstNext := first.recheck firstCheck
    have boundaryNext := Segment.spent known answerAnnotation scope (rest.recheck tailCheck) bound
    obtain ⟨waitingReq, waitingSource, waitingEvaluation⟩ := SourceAnnotatedStoredTyping.segment_append firstNext boundaryNext
      (SourceDependencyProjection.scope_append_nil _).symm (SourcePlannedRecomposition.hints_append_nil _).symm
      (SourceScheduledRecomposition.forest_append_nil _).symm
    have savedNext := (saved.recheck savedCheck).output_weaken (savedBound permitted)
    subst demand
    subst records
    refine ⟨_, _, waitingReq, _, ⟨_, _, _⟩, ⟨_, _, _⟩, savedNext, waitingSource, .cut firstForest _ _, ?_, ?_, ?_⟩
    · simpa only [List.append_assoc] using RecursiveRecomposition.move_records
        (prefixRecords := firstRecords) (List.Perm.refl _)
    · intro annotations matched
      exact matched.resume
    · intro store receiving before consumed
      rw [waitingEvaluation, evaluation]
      congr 1
      apply RecursiveTransport.evaluate_transport (fun _ _ => rfl)
      simpa only [Stack.append, SourceAnnotatedRuntime.Stack.erase] using
        (RecursiveRecomposition.normalize_replaced (front := .nil) (capture := capture.erase) (tail := tail.erase)
          (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := receiving) consumed).symm

open RecursiveRequirements (Checked)
open OwnerPhaseTransitions (Trace available)
open RecursiveConsumption (remove_owner_append)

/-- Resumption preserves typed plans together with the established record,
effect and one-shot ownership accounting. -/
theorem resume_segments [SourceScheduledChecks.DeclarationProjection admission certification]
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase)))) world
      (front.append (.live owner inputType answerType capture caller tail)) contract.answer output
      pendingDemand pendingRequirements resumes forest .nil incoming [] stored)
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world
      (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase)) disposals)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true) (allowed : contract.resumeEffects ⊆ incoming)
    (unique : (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase))).Nodup)
    (scheduled : Local outward actions
      (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase)))) world
      (.invoke (key := ⟨owner, .resume⟩)) forest)
    (invocation : Checked (resumes ++ disposals)
      (OwnerPhases.ofStack tables (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase)))
      (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase))))
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow)
    (pending : Checked (resumes ++ disposals) []
      (spendAll (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase))))
        (owner :: contract.resumeDemand)) pendingRequirements pendingRow) :
    ∃ (combined : Requirements (contract.resumeDemand ++ pendingDemand)) (nextResumes nextDisposals : Store)
      (nextForest : Saved),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (available (ownedTickets (capture.erase.append (front.erase.append (.spent owner answerType caller tail.erase))))) world
        (capture.append (front.append (.spent owner answerType caller tail))) contract.input output
        (contract.resumeDemand ++ pendingDemand) combined nextResumes nextForest.forest .nil [] [] stored.resume ∧
      DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world
        (capture.erase.append (front.erase.append (.spent owner answerType caller tail.erase))) nextDisposals ∧
      Checked (nextResumes ++ nextDisposals) []
        (available (ownedTickets (capture.erase.append (front.erase.append (.spent owner answerType caller tail.erase)))))
        combined (resumeRow ++ pendingRow) ∧
      (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm (nextResumes ++ nextDisposals) ∧
      nextDisposals ⊆ disposals ∧
      (∀ annotations, Matches annotations forest → Matches annotations nextForest.forest) ∧
      (ownedTickets (capture.erase.append (front.erase.append (.spent owner answerType caller tail.erase)))).Nodup ∧
      Trace (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase)))) [owner]
        (available (ownedTickets (capture.erase.append (front.erase.append (.spent owner answerType caller tail.erase))))) ∧
      SourceBoundSnapshots.ResumeForest owner forest nextForest.forest := by
  obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, savedForest, waitingForest, saved, waiting, shape, permutation, matched, waitingEvaluation⟩ :=
    replace_live source known actionKnown permitted unique scheduled
  obtain ⟨nextDisposals, nextClosing, disposalPermutation⟩ := DeclaredSourceClosing.resume_records closing unique
  have erased := source.forget.erase.source.source.erase.erase
  simp only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] at erased
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
  let initial := available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase)))
  have consumed : spend initial owner owner = .consumed := OwnerPhaseTransitions.spend_self initial owner
  have contexts : RecursiveTransport.normalize (spend initial owner)
      (OwnerPhases.ofStack tables (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase))) =
      RecursiveTransport.normalize (spend initial owner)
        (OwnerPhases.ofStack tables (front.erase.append (.spent owner answerType caller tail.erase))) := by
    simpa only [List.append_nil] using (RecursiveRecomposition.normalize_replaced (front := front.erase) (capture := capture.erase) (tail := tail.erase)
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
  obtain ⟨combined, combinedSource, evaluation⟩ := SourceAnnotatedStoredTyping.segment_append saved (waiting.input_weaken allowed)
    (SourceDependencyProjection.scope_append_nil _).symm (SourcePlannedRecomposition.hints_append_nil _).symm
    (SourceScheduledRecomposition.forest_append_nil _).symm
  have combinedCheck : Checked ((capturedRecords ++ waitingRecords) ++ nextDisposals) []
      (spend initial owner) combined (resumeRow ++ pendingRow) := by
    apply RecursiveRequirements.evaluate_sound
    rw [evaluation]
    simp only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase, List.append_nil]
    rw [RecursiveRequirements.checked_complete bodyCollected,
      RecursiveRequirements.checked_complete pendingCollected]
    rfl
  have trace := OwnerPhaseTransitions.resume_phase_trace unique
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  change available (ownedTickets (capture.erase.append (front.erase.append (.spent owner answerType caller tail.erase)))) =
    spend initial owner at actualPhases
  rw [← actualPhases] at combinedCheck
  change Segment _ _ _ _ _ _ _ _ (spend initial owner) _ _ _ _ _ _ _ _ _ _ _ _ _ at combinedSource
  rw [StackBounds.resume_parts] at combinedSource
  rw [← actualPhases] at combinedSource
  have afterUnique := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).2
  have disposalSubset : nextDisposals ⊆ disposals := by
    intro entry member
    exact RecursiveTransport.remove_owner_sublist.subset (disposalPermutation.mem_iff.mpr member)
  exact ⟨combined, _, nextDisposals, ⟨_, _, _⟩, combinedSource, nextClosing, combinedCheck, erasedPermutation,
    disposalSubset, matched, afterUnique, trace, shape⟩

omit admission certification in
private theorem resume_access_rights
    (checked : SourceDependencyCapture.ResumeChecked actions phases owner scope result) :
    ∃ rights, actions owner = some rights ∧ rights.resume = true := by
  cases checked with
  | checked located known permission available => exact ⟨_, known, permission⟩

omit admission certification in
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
theorem resume_cut_preserves_snapshot [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.resume hint binder value) (front.append (.live owner inputType answerType capture caller tail))
      snapshot.plan snapshot.forest output demand row stored evidence)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value.erase) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        scope value (capture.append (front.append (.spent owner answerType caller tail))) nextSnapshot.plan nextSnapshot.forest output remaining row stored.resume evidence ∧
      demand = owner :: remaining ∧
      Trace (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase)))) [owner]
        (available (ownedTickets (capture.erase.append (front.erase.append (.spent owner answerType caller tail.erase))))) ∧
      SourceBoundSnapshots.Resumed owner snapshot nextSnapshot := by
  rcases snapshot with ⟨dependencies, plan, bounds, receiving, hints, forest, pendingBounds⟩
  cases state with
  | checked current scopeTyped pendingSource closing templates matched contextual unique evaluated accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    simp only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] at pendingSource closing templates contextual unique evaluated
    subst demand
    generalize signatureSame : SourcePlanSignatures.signature plan = currentSignature at current
    cases current with
    | checked hint metadata node => cases node with
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
            (SourcePlannedSources.expression_erase operand.erase))
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
            permutation, disposalSubset, nextMatches, afterUnique, trace, shape⟩ :=
            resume_segments pendingSource closing known actionKnown permitted admitted unique scheduled resumeChecked pendingChecked
          have templatesAfter := templates.after_step
            (nextRoot := capture.append (front.append (.spent owner answerType caller tail)))
            (by simpa only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using nextClosing)
            disposalSubset (fun _ _ located => SourceAnnotatedRuntime.resume_capture_origin located)
            (by simpa only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using unique)
          have acceptedAfter : checkFootprint outside (resumeRow ++ pendingRow) = true := by simpa only [rows] using accepted
          have eraseNext : (capture.append (front.append (.spent owner answerType caller tail))).erase =
              capture.erase.append (front.erase.append (.spent owner answerType caller tail.erase)) := by
            simp only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase]
          rw [← eraseNext] at combinedSource nextClosing afterUnique combinedCheck
          have afterValid := value_configuration_atPackets
            (SourceAnnotatedSources.Values.change_allowed (SourceAnnotatedSources.Values.summary operand closed.1) closed.1 [])
            closed.1 scopeTyped combinedSource nextClosing templatesAfter (nextMatches annotations matched) afterUnique combinedCheck acceptedAfter
          rw [← rows] at afterValid
          obtain ⟨nextPending, moved⟩ := shape.snapshot
            (before := ⟨_, _, bounds, _, _, forest, pendingBounds⟩)
          refine ⟨_, SourceBoundSnapshots.Snapshot.value nextPending, afterValid, ?_, trace, moved⟩
          simp only [noDemand, List.nil_append, List.cons_append]

end Ash.OneShot.SourceAnnotatedStoredResumption

#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.resume_parts
#print axioms Ash.OneShot.SourceAnnotatedStoredResumption.value_configuration_atPackets
#print axioms Ash.OneShot.SourceAnnotatedStoredResumption.replace_live
#print axioms Ash.OneShot.SourceAnnotatedStoredResumption.resume_segments
#print axioms Ash.OneShot.SourceAnnotatedStoredResumption.resume_cut_preserves_snapshot
