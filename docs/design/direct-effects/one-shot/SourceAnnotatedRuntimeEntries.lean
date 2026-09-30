import SourceAnnotatedRuntimeReturnSteps

/-! Cleanup entry retains the annotated callback and body with their actual
source plans. Existing requirement equations derive the installed-frame check. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeEntries

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked evaluate)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)
open OwnerPhaseTransitions (spendAll)

/-- Cleanup installation stores the actual callback source and latent plan.
The original cleanup rule supplies both body and protected callback checks. -/
theorem cleanup_annotations_exact_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope (.cleanup hint callback body) stack snapshot.plan snapshot.forest output demand row evidence)
    (isValue : callback.erase.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    SourceFocusHints.inputPort Instantiation.Environment.empty hint = some answerPort ∧
    SourceFocusHints.inputPort Instantiation.Environment.empty callback.hint = some (.function .unit .unit requests) ∧
    ∀ identity answerType, ScopedPorts.eraseType answerType = answerPort →
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      action.action = callback ∧ action.scope = scope ∧
      RawStep ⟨.cleanup callback.erase body.erase, scope, stack.erase⟩ ⟨body.erase, scope, .push (.armed action.erase) stack.erase⟩ [.cleanup identity] [] ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        scope body (.push (.armed action) stack) nextSnapshot.plan nextSnapshot.forest output demand row evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot := by
  rcases snapshot with ⟨rootDependencies, plan, bounds, receiving, hints, forest, queuedMetadata⟩
  dsimp only at state ⊢
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | checked hintCheck metadata node => cases node with
      | cleanup callbackSource bodySource admitted =>
        cases plan with
        | sequence initialPlan cleanupPlan => cases cleanupPlan with
          | cleanup callbackPlan bodyPlan =>
            cases signatureSame
            cases contextual with
            | sequence initialCheck cleanupCheck => cases cleanupCheck with
              | cleanup bodyCheck callbackCheck =>
                have erasedCallback := DeclaredSources.expression_erase
                  (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase callbackSource.erase))
                have empty := SourceTemplates.expression_value_demand erasedCallback isValue
                cases empty
                rename_i requests latent callbackDep initialDep bodyDemand bodyReq bodyDep callbackReq
                have summary := SourceAnnotatedSources.Values.change_allowed
                  (SourceAnnotatedSources.Values.summary callbackSource isValue) isValue []
                have callbackTyped := (DeclaredSourceValues.erase (SourceDependencyFrames.value_erase
                  (SourcePlannedSources.expression_erase summary.erase))).ports .none
                have closed := ScopedPorts.typed_value_closed callbackTyped isValue
                refine ⟨input.erase.erase.port, requests, SourceFocusHints.check_source_iff.mp hintCheck,
                  SourceFocusHints.check_source_iff.mp callbackSource.hint_checked, ?_⟩
                intro identity answerType answerSame
                let action : SourceAnnotatedRuntime.Action := ⟨identity, callback, closed, scope, answerType, requests⟩
                have frame : SourceAnnotatedRuntimeTyping.Frame (evidence := evidence) operations policy contracts tables families required outward actions
                    (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world (forest.append .nil)
                    (.armed action) input input [] (.request [] (qualify true latent))
                    (.cleanup action.requests callbackDep) (fun rest => .cleanup rest) (fun rest => .cleanup callbackPlan rest) allowed allowed :=
                  .armed ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩ summary (by simp only [action, answerSame])
                    (.armed ⟨_, scopeTyped⟩ callbackTyped admitted)
                    ((SourceScheduledRecomposition.local_append_nil (Forest.running forest)).mpr callbackCheck)
                have templatesAfter := templates.transport (nextRoot := .push (.armed action) stack)
                  (fun _ _ known => known) (fun _ _ known => known)
                  (fun _ _ located => .push located)
                let nextSnapshot : SourceBoundSnapshots.Snapshot world :=
                  ⟨_, bodyPlan, bounds.second.cleanupBody, _, _, .cleanup (needs := requests) callbackPlan forest,
                    .cleanup bounds.second.cleanupCallback queuedMetadata⟩
                refine ⟨action, nextSnapshot, rfl, rfl, rfl, rfl, rfl,
                  .enterCleanup action.erase body.erase stack.erase, ?_, .step bounds queuedMetadata⟩
                refine .checked bodySource scopeTyped (.push frame pending (List.Subset.refl _)) (.push closing) templatesAfter
                  (.cleanup matched) bodyCheck unique ?_ accepted ?_
                · apply RecursiveRequirements.evaluate_sound
                  have original := RecursiveRequirements.checked_complete checked
                  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                    RecursiveRequirements.evaluate_emit, RecursiveRecomposition.value_evaluation erasedCallback isValue,
                    spendAll, RecursiveRecomposition.merge_empty_left, List.nil_append, List.append_nil] at original
                  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                    RecursiveContexts.evaluate_request, RecursiveEntries.armed_context, List.append_nil,
                    RecursiveContexts.evaluate_plain, SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase, ownedTickets, spendAll]
                  simpa only [ProtectionResiduals.merge_assoc] using original
                · simpa only [List.nil_append] using accounting

theorem cleanup_annotations_exact
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.cleanup hint callback body) stack forest output demand row evidence)
    (isValue : callback.erase.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    SourceFocusHints.inputPort Instantiation.Environment.empty hint = some answerPort ∧
    SourceFocusHints.inputPort Instantiation.Environment.empty callback.hint = some (.function .unit .unit requests) ∧
    ∀ identity answerType, ScopedPorts.eraseType answerType = answerPort →
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      action.action = callback ∧ action.scope = scope ∧
      RawStep ⟨.cleanup callback.erase body.erase, scope, stack.erase⟩ ⟨body.erase, scope, .push (.armed action.erase) stack.erase⟩ [.cleanup identity] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        scope body (.push (.armed action) stack) nextForest.forest output demand row evidence := by
  obtain ⟨_, plan, indexed⟩ := state.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot world :=
    ⟨_, plan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
  obtain ⟨answerPort, requests, portKnown, requestsKnown, admitted⟩ :=
    cleanup_annotations_exact_snapshot snapshot indexed isValue
  refine ⟨answerPort, requests, portKnown, requestsKnown, ?_⟩
  intro identity answerType answerSame
  obtain ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, callbackSame, scopeSame, raw, next, _⟩ :=
    admitted identity answerType answerSame
  exact ⟨action, ⟨_, _, nextSnapshot.forest⟩, identitySame, typeSame, requestsSame, callbackSame, scopeSame, raw, next.state⟩

theorem cleanup_annotations
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.cleanup hint callback body) stack forest output demand row evidence)
    (isValue : callback.erase.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    ∀ identity answerType, ScopedPorts.eraseType answerType = answerPort →
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      RawStep ⟨.cleanup callback.erase body.erase, scope, stack.erase⟩ ⟨body.erase, scope, .push (.armed action.erase) stack.erase⟩ [.cleanup identity] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        scope body (.push (.armed action) stack) nextForest.forest output demand row evidence := by
  obtain ⟨answerPort, requests, portKnown, requestsKnown, admitted⟩ := cleanup_annotations_exact state isValue
  refine ⟨answerPort, requests, ?_⟩
  intro identity answerType answerSame
  obtain ⟨action, saved, identitySame, typeSame, requestsSame, callbackSame, scopeSame, raw, next⟩ :=
    admitted identity answerType answerSame
  exact ⟨action, saved, identitySame, typeSame, requestsSame, raw, next⟩


theorem cleanup_preserves
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.cleanup hint callback body) stack forest output demand row evidence)
    (isValue : callback.erase.IsValue) (identity : Nat) :
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      action.identity = identity ∧
      RawStep ⟨.cleanup callback.erase body.erase, scope, stack.erase⟩ ⟨body.erase, scope, .push (.armed action.erase) stack.erase⟩ [.cleanup identity] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        scope body (.push (.armed action) stack) nextForest.forest output demand row evidence := by
  obtain ⟨answerPort, requests, admitted⟩ := cleanup_annotations state isValue
  obtain ⟨action, saved, same, _, _, raw, next⟩ := admitted identity (ScopedPorts.embedPort answerPort) (by simp)
  exact ⟨action, saved, same, raw, next⟩

end Ash.OneShot.SourceAnnotatedRuntimeEntries

#print axioms Ash.OneShot.SourceAnnotatedRuntimeEntries.cleanup_annotations
#print axioms Ash.OneShot.SourceAnnotatedRuntimeEntries.cleanup_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeEntries.cleanup_annotations_exact

#print axioms Ash.OneShot.SourceAnnotatedRuntimeEntries.cleanup_annotations_exact_snapshot
