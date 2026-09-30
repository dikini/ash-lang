import SourceAnnotatedRuntimeReturns

/-! Handler, resource, cleanup and spent-clause returns retain annotated saved
code. The original empty-head, phase and closing-record transport proofs supply
their existing ownership and effect accounting. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeBoundaries

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements evaluate)
open SourcePlannedTyping (Value)
open SourceAnnotatedSources (Expression ValueSummary)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)
open OwnerPhaseTransitions (spendAll)
open SourceAnnotatedRuntimeReturns (value_pending value_configuration value_configuration_atPlan)

theorem finish_cleanup_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope (.unit hint) (.push (.running action value closed) tail) snapshot.plan snapshot.forest output demand row evidence) :
    ∃ next : SourceBoundSnapshots.Snapshot world,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        action.scope value tail next.plan next.forest output demand row evidence ∧
      SourceBoundSnapshots.Exited .running snapshot next := by
  rcases snapshot with ⟨rootDependencies, rootPlan, rootBounds, receiving, hints, wholeForest, queuedMetadata⟩
  dsimp only at state ⊢
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state.state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | running scopeKnown callback saved annotation interface =>
      cases matched with
      | running matched => cases queuedMetadata with
      | running remaining =>
        obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        exact ⟨SourceBoundSnapshots.Snapshot.value remaining, value_configuration_atPlan saved closed.1 scopeTyped rest closing templatesAfter
          matched unique (RecursiveCompletion.empty_head checked) accepted, .running rootBounds remaining⟩

theorem finish_cleanup
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.unit hint) (.push (.running action value closed) tail) wholeForest output demand row evidence) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        action.scope value tail rest.forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, wholeForest, SourceBoundSnapshots.Retained.absent wholeForest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          scope (.unit hint) (.push (.running action value closed) tail) snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting
      obtain ⟨next, typed, _⟩ := finish_cleanup_snapshot snapshot indexed
      exact ⟨⟨_, _, next.forest⟩, typed.state⟩

/-- Returning across this frame retains every saved-plan certificate. -/
theorem finish_close_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope (.unit hint) (.push (.closing identity caller) tail) snapshot.plan snapshot.forest output demand row evidence) :
    ∃ next : SourceBoundSnapshots.Snapshot world,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        caller (.unit hint) tail next.plan next.forest output demand row evidence ∧
      SourceBoundSnapshots.Exited .running snapshot next := by
  rcases snapshot with ⟨rootDependencies, rootPlan, rootBounds, receiving, hints, wholeForest, queuedMetadata⟩
  dsimp only at state ⊢
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state.state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | closing scopeKnown interface =>
      cases matched with
      | running matched => cases queuedMetadata with
      | running remaining =>
        obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        exact ⟨SourceBoundSnapshots.Snapshot.value remaining, value_configuration_atPlan summary trivial scopeTyped rest closing templatesAfter
          matched unique (RecursiveCompletion.empty_head checked) accepted, .running rootBounds remaining⟩

theorem finish_close
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.unit hint) (.push (.closing identity caller) tail) wholeForest output demand row evidence) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        caller (.unit hint) tail rest.forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, wholeForest, SourceBoundSnapshots.Retained.absent wholeForest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          scope (.unit hint) (.push (.closing identity caller) tail) snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting
      obtain ⟨next, typed, _⟩ := finish_close_snapshot snapshot indexed
      exact ⟨⟨_, _, next.forest⟩, typed.state⟩

/-- Returning across this frame retains every saved-plan certificate. -/
theorem leave_handler_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.handler handler) tail) snapshot.plan snapshot.forest output demand row evidence) (isValue : value.erase.IsValue) :
    ∃ next : SourceBoundSnapshots.Snapshot world,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        handler.scope value tail next.plan next.forest output demand row evidence ∧
      SourceBoundSnapshots.Exited .handler snapshot next := by
  rcases snapshot with ⟨rootDependencies, rootPlan, rootBounds, receiving, hints, wholeForest, queuedMetadata⟩
  dsimp only at state ⊢
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state.state isValue
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | handler scope annotation clauses coverage uniqueClauses declarations recipes supplied capabilities modes =>
      cases matched with
      | handler matched => cases queuedMetadata with
      | handler remaining =>
        obtain ⟨ticket, scopeTyped⟩ := scope
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        exact ⟨SourceBoundSnapshots.Snapshot.value remaining, value_configuration_atPlan summary isValue scopeTyped rest closing templatesAfter
          matched unique (RecursiveCompletion.empty_head checked) accepted, .handler rootBounds remaining⟩

theorem leave_handler
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.handler handler) tail) wholeForest output demand row evidence) (isValue : value.erase.IsValue) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        handler.scope value tail rest.forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, wholeForest, SourceBoundSnapshots.Retained.absent wholeForest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          scope value (.push (.handler handler) tail) snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting
      obtain ⟨next, typed, _⟩ := leave_handler_snapshot snapshot indexed isValue
      exact ⟨⟨_, _, next.forest⟩, typed.state⟩

/-- Returning across this frame retains every saved-plan certificate. -/
theorem leave_cell_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.cell identity payload caller answer) tail) snapshot.plan snapshot.forest output demand row evidence) (isValue : value.erase.IsValue) :
    ∃ next : SourceBoundSnapshots.Snapshot world,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        caller value tail next.plan next.forest output demand row evidence ∧
      SourceBoundSnapshots.Exited .cell snapshot next := by
  rcases snapshot with ⟨rootDependencies, rootPlan, rootBounds, receiving, hints, wholeForest, queuedMetadata⟩
  dsimp only at state ⊢
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state.state isValue
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | cell scopeKnown noEscape annotation interface =>
      cases matched with
      | cell matched => cases queuedMetadata with
      | cell remaining =>
        obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        exact ⟨SourceBoundSnapshots.Snapshot.value remaining, value_configuration_atPlan summary isValue scopeTyped rest closing templatesAfter
          matched unique (RecursiveCompletion.empty_head checked) accepted, .cell rootBounds remaining⟩

theorem leave_cell
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.cell identity payload caller answer) tail) wholeForest output demand row evidence) (isValue : value.erase.IsValue) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        caller value tail rest.forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, wholeForest, SourceBoundSnapshots.Retained.absent wholeForest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          scope value (.push (.cell identity payload caller answer) tail) snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting
      obtain ⟨next, typed, _⟩ := leave_cell_snapshot snapshot indexed isValue
      exact ⟨⟨_, _, next.forest⟩, typed.state⟩

theorem leave_clause_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope value (.spent owner answer caller tail) snapshot.plan snapshot.forest output demand row evidence)
    (isValue : value.erase.IsValue) :
    ∃ next : SourceBoundSnapshots.Snapshot world,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        caller value tail next.plan next.forest output demand row evidence ∧
      SourceBoundSnapshots.Exited .spent snapshot next := by
  rcases snapshot with ⟨rootDependencies, rootPlan, rootBounds, receiving, hints, wholeForest, queuedMetadata⟩
  dsimp only at state ⊢
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state.state isValue
  cases closing with
  | spent closing => cases pending with
  | spent known annotation scope rest bound =>
    cases matched with
    | spent matched => cases queuedMetadata with
    | spent remaining =>
      obtain ⟨firstRow, tailRow, firstCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have evaluated := RecursiveRequirements.checked_complete firstCheck
      simp only [RecursiveRecomposition.evaluate_spent] at evaluated
      split at evaluated
      · have firstEmpty := Option.some.inj evaluated.symm
        subst firstRow
        obtain ⟨ticket, scopeTyped⟩ := scope
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | spent inner => exact inner)
        exact ⟨SourceBoundSnapshots.Snapshot.value remaining, value_configuration_atPlan summary isValue scopeTyped rest closing templatesAfter matched unique
          (by simpa only [same, List.nil_append, spendAll, SourceAnnotatedRuntime.Stack.erase, ownedTickets] using tailCheck) accepted, .spent rootBounds remaining⟩
      · cases evaluated

theorem leave_clause
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.spent owner answer caller tail) wholeForest output demand row evidence)
    (isValue : value.erase.IsValue) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        caller value tail rest.forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, wholeForest, SourceBoundSnapshots.Retained.absent wholeForest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          scope value (.spent owner answer caller tail) snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting
      obtain ⟨next, typed, _⟩ := leave_clause_snapshot snapshot indexed isValue
      exact ⟨⟨_, _, next.forest⟩, typed.state⟩

/-- Cleanup startup runs the exact retained callback plan under the running
protection marker and retains the value to return after callback completion. -/
theorem start_cleanup_bounds (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.armed action) tail) snapshot.plan snapshot.forest output demand row evidence)
    (closed : ClosedValue value.erase) :
    ∃ rest : SourceScheduledSavedPlans.Saved, ∃ callbackDependencies,
    ∃ callback : Plan callbackDependencies, ∃ queued : SourcePlanBounds.Annotation world callback,
    ∃ remaining : SourceBoundSnapshots.Retained world rest.forest,
      let next := SourceBoundSnapshots.Snapshot.startCleanup queued remaining
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        .none (.app .unit action.action (.unit .unit)) (.push (.running action value closed) tail)
        next.plan next.forest output demand row evidence ∧ SourceBoundSnapshots.StartedCleanup snapshot next := by
  rcases snapshot with ⟨rootDependencies, rootPlan, rootBounds, receiving, hints, wholeForest, queuedMetadata⟩
  dsimp only at state ⊢
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state.state closed.1
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | armed scopeKnown callback annotation interface callbackCheck =>
      rename_i restScope restHints restForest callbackDep latent callbackPlan
      cases matched with
      | cleanup matched => cases queuedMetadata with
      | cleanup queued remaining =>
        cases interface with
        | armed caller callable requests =>
          obtain ⟨callbackRow, tailRow, headCheck, tailCheck, same⟩ :=
            RecursiveRequirements.checked_sequence_parts checked
          have exported := RecursiveRequirements.checked_complete headCheck
          simp only [RecursiveRequirements.evaluate_prepend, RecursiveContexts.evaluate_request, List.append_nil] at exported
          have invocation : Expression operations policy contracts world action.requests .none (fun _ => none)
              (.app .unit action.action (.unit .unit)) .unit []
              (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
              (signature (.sequence .pure (.sequence .pure callbackPlan))) :=
            .checked (by change true = true; rfl) (SourceAnnotatedCode.Term.check_closed_iff.mpr (by
                change action.action.freeNames ++ [] = []
                simpa only [List.append_nil, SourceAnnotatedCode.Term.ResourceClosed] using callback.resource_closed))
              (.app (SourceAnnotatedSources.Values.change_context callback action.closed.1 action.requests .none)
                (.checked (by decide) (by decide) .unit) (List.Subset.refl _))
          have currentCheck : RecursiveRequirements.Checked (records ++ disposals)
              (OwnerPhases.ofStack tables (.push (.running action.erase value.erase closed) tail.erase))
              (OwnerPhaseTransitions.available (ownedTickets tail.erase))
              (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent) callbackRow := by
            apply RecursiveRequirements.evaluate_sound
            simpa only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
              RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left,
              spendAll, List.nil_append, RecursiveContexts.evaluate_request,
              RecursiveCompletion.running_export, SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase, ownedTickets] using exported
          have currentPrefixed : RecursiveRequirements.Checked (records ++ disposals) []
              (OwnerPhaseTransitions.available (ownedTickets tail.erase))
              ((Requirements.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent).prepend
                (OwnerPhases.ofStack tables (.push (.running action.erase value.erase closed) tail.erase))) callbackRow :=
            RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)
          have empty : RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets tail.erase))
              ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables tail.erase)) [] :=
            .request (row := []) (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
          have savedTyped : ScopedPorts.Typed operations.erase.erase.ports world ScopedPorts.TypeEnv.empty .none [] value.erase
              (ScopedPorts.eraseType action.answer) := by
            have environmentSame : (SourcePlannedTyping.Environment.erase (fun _ => none)).erase.ports = ScopedPorts.TypeEnv.empty := by
              funext name; rfl
            simpa only [← annotation, environmentSame] using
              (DeclaredSourceValues.erase (SourceDependencyFrames.value_erase (SourcePlannedSources.expression_erase summary.erase))).ports .none
          have templatesAfter := templates.transport (nextRoot := .push (.running action value closed) tail)
            (fun _ _ known => known) (fun _ _ known => known)
            (fun _ _ located => by cases located with | push inner => exact .push inner)
          have localCallback := (SourceScheduledRecomposition.local_append_nil (Forest.running restForest)).mp callbackCheck
          have nextPending := RecursiveRequirements.Checked.sequence empty tailCheck
          rw [same] at accepted ⊢
          refine ⟨⟨_, _, restForest⟩, _, callbackPlan, queued, remaining, SourceAnnotatedRuntimeState.AtPlan.checked invocation .none
            (.push (.running scopeKnown callback summary annotation (.running caller callable savedTyped requests)) rest requests)
            (.push closing) templatesAfter (.running matched) (.sequence .pure (.sequence .pure localCallback)) unique ?_ accepted rfl, .step rootBounds queued remaining⟩
          simpa only [List.nil_append, SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase, ownedTickets] using RecursiveRequirements.Checked.sequence currentPrefixed nextPending

theorem start_cleanup
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.armed action) tail) wholeForest output demand row evidence)
    (closed : ClosedValue value.erase) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        .none (.app .unit action.action (.unit .unit)) (.push (.running action value closed) tail) (.running rest.forest) output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, wholeForest, SourceBoundSnapshots.Retained.absent wholeForest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          scope value (.push (.armed action) tail) snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting
      obtain ⟨rest, _, _, _, _, next, _⟩ := start_cleanup_bounds snapshot indexed closed
      exact ⟨rest, next.state⟩

/-- Cleanup startup moves the exact queued callback annotation into the
current computation, preserving the entire remaining annotation queue. -/
theorem start_cleanup_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.armed action) tail) snapshot.plan snapshot.forest output demand row evidence)
    (closed : ClosedValue value.erase) :
    ∃ next : SourceBoundSnapshots.Snapshot world,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        .none (.app .unit action.action (.unit .unit)) (.push (.running action value closed) tail)
        next.plan next.forest output demand row evidence ∧ SourceBoundSnapshots.StartedCleanup snapshot next := by
  obtain ⟨rest, _, callback, queued, remaining, next, moved⟩ := start_cleanup_bounds snapshot state closed
  exact ⟨SourceBoundSnapshots.Snapshot.startCleanup queued remaining, next, moved⟩


end Ash.OneShot.SourceAnnotatedRuntimeBoundaries

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.finish_cleanup

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.finish_close

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.leave_handler

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.leave_cell

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.leave_clause

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.start_cleanup

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.finish_cleanup_snapshot

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.finish_close_snapshot

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.leave_handler_snapshot

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.leave_cell_snapshot

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.leave_clause_snapshot

#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.start_cleanup_bounds
#print axioms Ash.OneShot.SourceAnnotatedRuntimeBoundaries.start_cleanup_snapshot
