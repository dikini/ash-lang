import SourceScheduledDisposal

/-! Ordinary branch selection and cleanup entry preserve actual retained plans.
Source decomposition and the established requirement equations supply the
successor checks; no rechecking premise is added for the successor. -/
namespace Ash.OneShot.SourceScheduledEntries
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked evaluate)
open SourcePlanSignatures (signature)
open SourcePlannedSources (Expression ValueSummary)
open SourceRetainedPlans (Forest)
open OwnerPhaseTransitions (spendAll)

/-- Branch selection retains the selected source plan and may narrow the
checked effect row while preserving the ownership multiset. -/
theorem branch_preserves
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.branch (.boolean flag) yes no) stack forest output demand row evidence) :
    ∃ remaining nextRow,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        scope (if flag then yes else no) stack forest output remaining nextRow evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    subst demand
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | branch condition yesSource noSource same =>
      cases plan with
      | sequence conditionPlan branches => cases branches with
        | choice yesPlan noPlan =>
          cases signatureSame
          cases contextual with
          | sequence conditionCheck choices => cases choices with
            | choice yesCheck noCheck =>
              have erasedCondition := DeclaredSources.expression_erase
                (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase condition))
              have empty := SourceTemplates.expression_value_demand erasedCondition trivial
              cases empty
              obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
              have activeCheck := RecursiveRequirements.checked_prepend_iff.mp currentCheck
              have evaluated := RecursiveRequirements.checked_complete activeCheck
              rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation erasedCondition trivial,
                RecursiveRecomposition.merge_empty_left] at evaluated
              obtain ⟨yesRow, noRow, yesChecked, noChecked, rfl⟩ :=
                RecursiveExpressions.choice_parts (RecursiveRequirements.evaluate_sound evaluated)
              simp only [List.nil_append] at pendingCheck ⊢
              cases flag with
              | false =>
                have nextPending := pendingCheck
                rw [RecursiveExpressions.spend_permutation same] at nextPending
                have included := (List.sublist_append_right yesRow noRow).append (List.Sublist.refl pendingRow)
                exact ⟨_, _, .checked noSource scopeTyped pending closing templates matched noCheck unique
                  (.sequence (RecursiveRequirements.checked_prepend_iff.mpr noChecked) nextPending)
                  (checked_footprint_subset accepted included.subset) rfl,
                  same.append_right _, included⟩
              | true =>
                have included := (List.sublist_append_left yesRow noRow).append (List.Sublist.refl pendingRow)
                exact ⟨_, _, .checked yesSource scopeTyped pending closing templates matched yesCheck unique
                  (.sequence (RecursiveRequirements.checked_prepend_iff.mpr yesChecked) pendingCheck)
                  (checked_footprint_subset accepted included.subset) rfl, .refl _, included⟩

/-- Cleanup installation stores the actual callback source and latent plan.
The original cleanup rule supplies both body and protected callback checks. -/
theorem cleanup_annotations
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.cleanup callback body) stack forest output demand row evidence)
    (isValue : callback.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    ∀ identity answerType, ScopedPorts.eraseType answerType = answerPort →
    ∃ action : ActionData, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      RawStep ⟨.cleanup callback body, scope, stack⟩ ⟨body, scope, .push (.armed action) stack⟩ [.cleanup identity] [] ∧
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        scope body (.push (.armed action) stack) nextForest.forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | cleanup callbackSource bodySource admitted =>
      cases plan with
      | sequence initialPlan cleanupPlan => cases cleanupPlan with
        | cleanup callbackPlan bodyPlan =>
          cases signatureSame
          cases contextual with
          | sequence initialCheck cleanupCheck => cases cleanupCheck with
            | cleanup bodyCheck callbackCheck =>
              have erasedCallback := DeclaredSources.expression_erase
                (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase callbackSource))
              have empty := SourceTemplates.expression_value_demand erasedCallback isValue
              cases empty
              rename_i requests latent callbackDep initialDep bodyDemand bodyReq bodyDep callbackReq
              have summary := SourcePlannedSources.Values.change_allowed
                (SourcePlannedSources.Values.summary callbackSource isValue) isValue []
              have callbackTyped := (DeclaredSourceValues.erase (SourceDependencyFrames.value_erase
                (SourcePlannedSources.expression_erase summary))).ports .none
              have closed := ScopedPorts.typed_value_closed callbackTyped isValue
              refine ⟨input.erase.erase.port, requests, ?_⟩
              intro identity answerType answerSame
              let action : ActionData := ⟨identity, callback, closed, scope, answerType, requests⟩
              have frame : SourceScheduledFrames.Frame (evidence := evidence) operations policy contracts tables families required outward actions
                  (OwnerPhaseTransitions.available (ownedTickets stack)) world (forest.append .nil)
                  (.armed action) input input [] (.request [] (qualify true latent))
                  (.cleanup action.requests callbackDep) (fun rest => .cleanup rest) (fun rest => .cleanup callbackPlan rest) allowed allowed :=
                .armed ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩ summary (by simp only [action, answerSame])
                  (.armed ⟨_, scopeTyped⟩ callbackTyped admitted)
                  ((SourceScheduledRecomposition.local_append_nil (Forest.running forest)).mpr callbackCheck)
              have templatesAfter := templates.transport (nextRoot := .push (.armed action) stack)
                (fun _ _ known => known) (fun _ _ known => known)
                (fun _ _ located => .push located)
              refine ⟨action, ⟨_, _, .cleanup (needs := requests) callbackPlan forest⟩, rfl, rfl, rfl, .enterCleanup action body stack, ?_⟩
              refine .checked bodySource scopeTyped (.push frame pending (List.Subset.refl _)) (.push closing) templatesAfter
                (.cleanup matched) bodyCheck unique ?_ accepted ?_
              · apply RecursiveRequirements.evaluate_sound
                have original := RecursiveRequirements.checked_complete checked
                simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                  RecursiveRequirements.evaluate_emit, RecursiveRecomposition.value_evaluation erasedCallback isValue,
                  spendAll, RecursiveRecomposition.merge_empty_left, List.nil_append, List.append_nil] at original
                simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                  RecursiveContexts.evaluate_request, RecursiveEntries.armed_context, List.append_nil,
                  RecursiveContexts.evaluate_plain, ownedTickets, spendAll]
                simpa only [ProtectionResiduals.merge_assoc] using original
              · simpa only [List.nil_append] using accounting

theorem cleanup_preserves
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.cleanup callback body) stack forest output demand row evidence)
    (isValue : callback.IsValue) (identity : Nat) :
    ∃ action : ActionData, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      action.identity = identity ∧
      RawStep ⟨.cleanup callback body, scope, stack⟩ ⟨body, scope, .push (.armed action) stack⟩ [.cleanup identity] [] ∧
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        scope body (.push (.armed action) stack) nextForest.forest output demand row evidence := by
  obtain ⟨answerPort, requests, admitted⟩ := cleanup_annotations state isValue
  obtain ⟨action, saved, same, _, _, raw, next⟩ := admitted identity (ScopedPorts.embedPort answerPort) (by simp)
  exact ⟨action, saved, same, raw, next⟩

end Ash.OneShot.SourceScheduledEntries

#print axioms Ash.OneShot.SourceScheduledEntries.branch_preserves

#print axioms Ash.OneShot.SourceScheduledEntries.cleanup_annotations
#print axioms Ash.OneShot.SourceScheduledEntries.cleanup_preserves
