import SourceScheduledWorld

/-! Fresh resource entry preserves the exact body and retained plans. The
existing finite requirement support supplies a fresh identity at which the
source's hidden resource requirements can be opened. -/
namespace Ash.OneShot.SourceScheduledResources
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked evaluate)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)
open OwnerPhaseTransitions (available spendAll)

/-- Resource entry exposes a finite forbidden-name set and an answer port.
Every supplied identity and type passing those data checks preserves the source
state. Freshness includes hidden requirement support as well as live resources. -/
theorem resource_annotations
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.resource binder initializer body) stack forest output demand row evidence)
    (isValue : initializer.IsValue) :
    ∃ forbidden : List Nat, ∃ answerPort : ScopedPorts.Port,
    ∀ identity answer, identity ∉ world → identity ∉ forbidden → ScopedPorts.eraseType answer = answerPort →
    ∃ payload, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      initializer = .integer payload ∧
      RawStep ⟨.resource binder initializer body, scope, stack⟩
        ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack⟩ [.resource identity] [] ∧
      SourceScheduledState.State operations policy contracts tables families required actions annotations (world ++ [identity]) outward outside
        scope (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) nextForest.forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    have erasedOriginal := DeclaredSources.expression_erase
      (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase current))
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | resource initial bodySource formed effectsBound admitted hidden =>
      cases plan with
      | sequence initialPlan resourcePlan => cases resourcePlan with
        | resource bodyPlans =>
          cases signatureSame
          cases contextual with
          | sequence initialCheck resourceCheck => cases resourceCheck with
            | resource bodyCheck =>
              have erasedInitial := DeclaredSources.expression_erase
                (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase initial))
              have empty := SourceTemplates.expression_value_demand erasedInitial isValue
              cases empty
              obtain ⟨payload, rfl⟩ := ScopedPorts.typed_integer_value (SourceTemplates.expression_ports erasedInitial scopeTyped) isValue
              obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ :=
                RecursiveRequirements.checked_sequence_parts checked
              have currentAt := RecursiveRequirements.checked_prepend_iff.mp currentCheck
              have evaluated := RecursiveRequirements.checked_complete currentAt
              simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation erasedInitial isValue,
                RecursiveRecomposition.merge_empty_left, List.append_nil, spendAll] at evaluated
              have outwardCheck := RecursiveRequirements.evaluate_sound evaluated
              obtain ⟨forbidden, preserved⟩ := ResourceRequirements.checked_open_resource outwardCheck
              refine ⟨forbidden, input.erase.erase.port, ?_⟩
              intro identity answer freshWorld freshRequirements answerSame
              have bodyChecked := preserved identity freshRequirements _ (hidden identity freshWorld)
              have frame : SourceScheduledFrames.Frame (evidence := evidence) operations policy contracts tables families required outward actions
                  (available (ownedTickets stack)) (world ++ [identity]) (forest.append .nil)
                  (.cell identity payload scope answer) input input [] (.request [] [])
                  (.cell identity) (fun rest => .cell rest) (fun rest => .cell rest) (.cell identity :: allowed) allowed :=
                .cell ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩
                  (by simpa only [answerSame] using fun member => freshWorld (formed member))
                  (by simp only [answerSame])
                  (.cell ⟨_, scopeTyped⟩ (by simpa only [answerSame] using fun member => freshWorld (formed member)))
              have templatesAfter := (templates.world_weaken (List.subset_append_left world [identity])).transport
                (nextRoot := .push (.cell identity payload scope answer) stack)
                (fun _ _ known => known) (fun _ _ known => known) (fun _ _ located => .push located)
              have ready := ScopedPorts.typed_resource_closed (SourceTemplates.expression_ports erasedOriginal scopeTyped)
              refine ⟨payload, ⟨_, _, .cell (identity := identity) forest⟩, rfl,
                .enterCell binder identity payload body scope answer stack ready, ?_⟩
              refine .checked (bodySource identity freshWorld) scopeTyped
                (.push frame (pending.world_weaken (List.subset_append_left _ _)) (List.cons_subset_cons _ admitted))
                (.push (DeclaredSourceClosing.records_world_weaken closing (List.subset_append_left _ _)))
                templatesAfter (.cell matched) (bodyCheck identity freshWorld) unique ?_ accepted ?_
              · apply RecursiveRequirements.evaluate_sound
                simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                  OwnerPhases.ofStack, OwnerPhases.frameEntry, List.append_nil,
                  RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, ownedTickets, spendAll]
                simp only [List.nil_append] at pendingCheck
                rw [RecursiveRequirements.checked_complete bodyChecked, RecursiveRequirements.checked_complete pendingCheck]
                rfl
              · simpa only [List.nil_append] using accounting

theorem resource_preserves
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.resource binder initializer body) stack forest output demand row evidence)
    (isValue : initializer.IsValue) :
    ∃ identity payload answer, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      identity ∉ world ∧ initializer = .integer payload ∧
      RawStep ⟨.resource binder initializer body, scope, stack⟩
        ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack⟩ [.resource identity] [] ∧
      SourceScheduledState.State operations policy contracts tables families required actions annotations (world ++ [identity]) outward outside
        scope (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) nextForest.forest output demand row evidence := by
  obtain ⟨forbidden, answerPort, admitted⟩ := resource_annotations state isValue
  obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name (world ++ forbidden)
  have freshWorld : identity ∉ world := fun member => fresh (List.mem_append_left _ member)
  have freshRequirements : identity ∉ forbidden := fun member => fresh (List.mem_append_right _ member)
  obtain ⟨payload, nextForest, same, raw, next⟩ :=
    admitted identity (ScopedPorts.embedPort answerPort) freshWorld freshRequirements (by simp)
  exact ⟨identity, payload, _, nextForest, freshWorld, same, raw, next⟩

end Ash.OneShot.SourceScheduledResources

#print axioms Ash.OneShot.SourceScheduledResources.resource_annotations
#print axioms Ash.OneShot.SourceScheduledResources.resource_preserves
