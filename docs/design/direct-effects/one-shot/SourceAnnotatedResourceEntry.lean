import SourceAnnotatedRuntimeResources
import ResourceRowNarrowing
import SourceBoundResources

/-! Resource entry uses the actual source hint and historical resource freshness.
The outward row may narrow, removing the earlier hidden support exclusion. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeResources

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked evaluate)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)
open OwnerPhaseTransitions (available spendAll)

/-- A ready resource source supplies its concrete initializer and finite answer
port. No successor-state assumption is needed to choose entry annotations. -/
theorem resource_input_data
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.resource hint binder initializer body) stack forest output demand row evidence)
    (isValue : initializer.erase.IsValue) :
    ∃ initialHint payload answerPort,
      initializer = .integer initialHint payload ∧
      SourceFocusHints.inputPort Instantiation.Environment.empty hint = some answerPort := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | checked hintCheck metadata node => cases node with
      | resource initial bodySource formed effectsBound admitted hidden =>
        have erasedInitial := DeclaredSources.expression_erase
          (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase initial.erase))
        obtain ⟨payload, same⟩ := ScopedPorts.typed_integer_value
          (SourceTemplates.expression_ports erasedInitial scopeTyped) isValue
        cases initializer <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at same
        cases same
        exact ⟨_, _, _, rfl, SourceFocusHints.check_source_iff.mp hintCheck⟩

/-- Every fresh supplied resource identity and matching finite answer annotation
preserves the actual source, with a possibly smaller checked effect row. -/
theorem resource_narrowing_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope (.resource hint binder initializer body) stack snapshot.plan snapshot.forest output demand row evidence)
    (isValue : initializer.erase.IsValue) (freshWorld : identity ∉ world)
    (ports : SourceFocusHints.inputPort Instantiation.Environment.empty hint = some (ScopedPorts.eraseType answer)) :
    ∃ payload, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (world ++ [identity]), ∃ nextRow,
      initializer.erase = .integer payload ∧
      RawStep ⟨.resource binder initializer.erase body.erase, scope, stack.erase⟩
        ⟨body.erase.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack.erase⟩ [.resource identity] [] ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations (world ++ [identity]) outward outside
        scope (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) nextSnapshot.plan nextSnapshot.forest output demand nextRow evidence ∧
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot := by
  rcases snapshot with ⟨dependencies, plan, bounds, receiving, hints, forest, queued⟩
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    have erasedOriginal := DeclaredSources.expression_erase
      (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase current.erase))
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | checked hintCheck metadata node => cases node with
      | resource initial bodySource formed effectsBound admitted hidden =>
        cases plan with
        | sequence initialPlan resourcePlan => cases resourcePlan with
          | resource bodyPlans =>
            cases signatureSame
            cases contextual with
            | sequence initialCheck resourceCheck => cases resourceCheck with
              | resource bodyCheck =>
                have erasedInitial := DeclaredSources.expression_erase
                  (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase initial.erase))
                have empty := SourceTemplates.expression_value_demand erasedInitial isValue
                cases empty
                obtain ⟨payload, initialSame⟩ := ScopedPorts.typed_integer_value (SourceTemplates.expression_ports erasedInitial scopeTyped) isValue
                cases initializer <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at initialSame
                cases initialSame
                obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ :=
                  RecursiveRequirements.checked_sequence_parts checked
                have currentAt := RecursiveRequirements.checked_prepend_iff.mp currentCheck
                have evaluated := RecursiveRequirements.checked_complete currentAt
                simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation erasedInitial isValue,
                  RecursiveRecomposition.merge_empty_left, List.append_nil, spendAll] at evaluated
                have outwardCheck := RecursiveRequirements.evaluate_sound evaluated
                have answerSame : ScopedPorts.eraseType answer = input.erase.erase.port :=
                  Option.some.inj (ports.symm.trans (SourceFocusHints.check_source_iff.mp hintCheck))
                obtain ⟨openedRow, bodyChecked, bodyIncluded⟩ :=
                  ResourceRequirements.checked_open_resource_sublist outwardCheck (hidden identity freshWorld)
                have frame : SourceAnnotatedRuntimeTyping.Frame (evidence := evidence) operations policy contracts tables families required outward actions
                    (available (ownedTickets stack.erase)) (world ++ [identity]) (forest.append .nil)
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
                refine ⟨payload, ⟨_, bodyPlans identity, bounds.second.resourceBody freshWorld, _, _,
                    .cell (identity := identity) forest, .cell (queued.world_weaken (List.subset_append_left _ _))⟩,
                  openedRow ++ pendingRow, rfl,
                  .enterCell binder identity payload body.erase scope answer stack.erase ready, ?_, bodyIncluded.append (.refl _), .step bounds queued freshWorld⟩
                refine .checked (bodySource identity freshWorld) scopeTyped
                  (.push frame (pending.world_weaken (List.subset_append_left _ _)) (List.cons_subset_cons _ admitted))
                  (.push (DeclaredSourceClosing.records_world_weaken closing (List.subset_append_left _ _)))
                  templatesAfter (.cell matched) (bodyCheck identity freshWorld) unique ?_
                  (checked_footprint_subset accepted (bodyIncluded.append (.refl _)).subset) ?_
                · apply RecursiveRequirements.evaluate_sound
                  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                    OwnerPhases.ofStack, OwnerPhases.frameEntry, List.append_nil,
                    RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase, ownedTickets, spendAll]
                  simp only [List.nil_append] at pendingCheck
                  rw [RecursiveRequirements.checked_complete bodyChecked, RecursiveRequirements.checked_complete pendingCheck]
                  rfl
                · simpa only [List.nil_append] using accounting

theorem resource_narrowing
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.resource hint binder initializer body) stack forest output demand row evidence)
    (isValue : initializer.erase.IsValue) (freshWorld : identity ∉ world)
    (ports : SourceFocusHints.inputPort Instantiation.Environment.empty hint = some (ScopedPorts.eraseType answer)) :
    ∃ payload, ∃ nextForest : SourceScheduledSavedPlans.Saved, ∃ nextRow,
      initializer.erase = .integer payload ∧
      RawStep ⟨.resource binder initializer.erase body.erase, scope, stack.erase⟩
        ⟨body.erase.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack.erase⟩ [.resource identity] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations (world ++ [identity]) outward outside
        scope (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) nextForest.forest output demand nextRow evidence ∧
      nextRow.Sublist row := by
  obtain ⟨dependencies, plan, indexed⟩ := state.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot world :=
    ⟨_, plan, .absent, _, _, forest, .absent forest⟩
  obtain ⟨payload, nextSnapshot, nextRow, same, raw, next, included, _⟩ :=
    resource_narrowing_snapshot snapshot indexed isValue freshWorld ports
  exact ⟨payload, ⟨_, _, nextSnapshot.forest⟩, nextRow, same, raw, next.state, included⟩

end Ash.OneShot.SourceAnnotatedRuntimeResources

#print axioms Ash.OneShot.SourceAnnotatedRuntimeResources.resource_narrowing

#print axioms Ash.OneShot.SourceAnnotatedRuntimeResources.resource_narrowing_snapshot

#print axioms Ash.OneShot.SourceAnnotatedRuntimeResources.resource_input_data
