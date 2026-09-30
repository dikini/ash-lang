import SourceScheduledFocus

/-! A returned value recomposes with its actual retained context plan. Pure
value evaluation changes no ownership or interpretation; source construction
and effect equations reuse the established structural context rules. -/
namespace Ash.OneShot.SourceScheduledValues
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements evaluate)
open ProtectionResiduals (merge)
open OwnerPhaseTransitions (spendAll)
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value)
open SourcePlannedSources (Expression Context ValueSummary summary_expression)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceScheduledChecks (Local)
open SourceRetainedPlans (Forest)

/-- Plugging a pure returned value preserves the context's complete source
plan. Application-argument contexts retain the already evaluated function too. -/
theorem plug_checked {plan : Plan dependencies} {hints : Hints receiving} {forest : Forest hints}
    (context : Context operations policy contracts world environment allowed scope position input output demand requirements (signature plan))
    (checked : Local outward actions phases world plan forest)
    (value : ValueSummary operations policy contracts world environment allowed code input) :
    ∃ (combined : Requirements demand) (nextDependencies : Dependencies) (nextPlan : Plan nextDependencies),
      Expression operations policy contracts world allowed scope environment (position.plug code) output
        demand combined (signature nextPlan) ∧ Local outward actions phases world nextPlan forest ∧
      ∀ store receiving before, evaluate store receiving before combined = evaluate store receiving before requirements := by
  have child := summary_expression value scope
  generalize sameSignature : signature plan = checking at context
  cases context with
  | pairLeft right =>
      refine ⟨_, _, .sequence .pure plan, (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.pair child right), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | pairRight left =>
      refine ⟨_, _, .sequence .pure plan, (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.pair (summary_expression left scope) child), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | appFunction argument admitted =>
      refine ⟨_, _, .sequence .pure plan, (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.app child argument admitted), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | appArgument function admitted =>
      refine ⟨_, _, .sequence .pure (.sequence .pure plan), (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.app (summary_expression function scope) child admitted), .sequence .pure (.sequence .pure checked), ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left,
        RecursiveContexts.evaluate_request, List.nil_append]
  | bind body =>
      refine ⟨_, _, .sequence .pure plan, (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.bind child body), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | branch yes no same =>
      refine ⟨_, _, .sequence .pure plan, (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.branch child yes no same), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | perform known admitted formed =>
      refine ⟨_, _, .sequence .pure plan, (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.perform known admitted child formed), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left, RecursiveContexts.evaluate_request, List.nil_append]
  | resume known resolved permission admitted formed =>
      refine ⟨_, _, .sequence .pure plan, (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.resume known resolved permission child admitted formed), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | cleanup body admitted =>
      refine ⟨_, _, .sequence .pure plan, (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.cleanup child body admitted), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | resource body formed effectsBound admitted hidden =>
      refine ⟨_, _, .sequence .pure plan, (by simpa only [signature, sameSignature, ScopedExecution.Context.plug, List.nil_append] using Expression.resource child body formed effectsBound admitted hidden), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]

/-- A returned value contributes no pending ownership demand or effects.
All retained source, map and certificate witnesses remain the same. -/
theorem value_pending
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope value stack forest output demand row evidence)
    (isValue : value.IsValue) :
    ∃ (input : Value) (incoming : List Instance) (requirements : Requirements demand)
      (records disposals : RecursiveRequirements.Store),
      ValueSummary operations policy contracts world (fun _ => none) [] value input ∧
      ScopedPorts.EffectScopeKnown contracts.erase.erase.ports scope ∧
      SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets stack)) world stack input output demand requirements records forest .nil incoming [] ∧
      DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack disposals ∧
      SourceScheduledClosingRecords.Records operations policy contracts tables annotations world stack disposals ∧
      SourceScheduledSavedPlans.Matches annotations forest ∧
      (ownedTickets stack).Nodup ∧
      RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack)) requirements row ∧
      checkFootprint outside row = true := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      subst demand
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
          (SourcePlannedSources.expression_erase current))) isValue
      subst_vars
      refine ⟨_, _, _, _, _, SourcePlannedSources.Values.change_allowed
        (SourcePlannedSources.Values.summary current isValue) isValue [], ⟨_, scopeTyped⟩,
        pending, closing, templates, matched, unique, RecursiveRequirements.evaluate_sound ?_, accepted⟩
      have evaluation := RecursiveRequirements.checked_complete checked
      simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveRecomposition.value_evaluation
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
            (SourcePlannedSources.expression_erase current))) isValue,
        spendAll, RecursiveRecomposition.merge_empty_left] using evaluation

theorem value_configuration
    (summary : ValueSummary operations policy contracts world (fun _ => none) [] code input)
    (isValue : code.IsValue)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket)
    (pending : SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack)) world stack input output demand requirements records forest .nil incoming [])
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack disposals)
    (templates : SourceScheduledClosingRecords.Records operations policy contracts tables annotations world stack disposals)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (unique : (ownedTickets stack).Nodup)
    (checked : RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack)) requirements row)
    (accepted : checkFootprint outside row = true) :
    SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope code stack forest output demand row evidence := by
  have current : RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
      ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables stack)) [] :=
    .request (row := []) (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  exact .checked (summary_expression (SourcePlannedSources.Values.change_allowed summary isValue incoming) _) scopeTyped
    pending closing templates matched .pure unique
    (by simpa only [List.nil_append] using RecursiveRequirements.Checked.sequence current checked) accepted rfl

/-- Returning into a plain frame preserves the complete scheduled state.
The retained context supplies both the actual plan and its local check. -/
theorem plug_preserves
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.plain plain) tail) wholeForest output demand row evidence)
    (closed : ClosedValue value) :
    ∃ rest : SourceScheduledSavedPlans.Saved, ∃ dependencies, ∃ contextPlan : Plan dependencies,
      HEq wholeForest (Forest.plain contextPlan rest.forest) ∧
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        plain.scope (plain.context.plug value) tail rest.forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      subst demand
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
          (SourcePlannedSources.expression_erase current))) closed.1
      subst_vars
      cases closing with
      | push closing => cases pending with
      | push frame pending bound => cases frame with
        | plain context frameScope inputAnnotation outputAnnotation contextCheck =>
          cases matched with
          | plain matched =>
            obtain ⟨combined, dependencies, plan, combinedSource, combinedCheck, evaluation⟩ :=
              plug_checked context ((SourceScheduledRecomposition.local_append_nil _).mp contextCheck)
                (SourcePlannedSources.Values.change_allowed (SourcePlannedSources.Values.summary current closed.1) closed.1 _)
            have templatesAfter := templates.transport (nextRoot := tail)
              (fun _ _ known => known) (fun _ _ known => known)
              (fun _ _ located => by cases located with | push inner => exact inner)
            refine ⟨⟨_, _, _⟩, _, _, HEq.rfl, SourceScheduledState.State.checked combinedSource frameScope pending closing templatesAfter
              matched combinedCheck unique ?_ accepted rfl⟩
            apply RecursiveRequirements.evaluate_sound
            have oldEvaluation := RecursiveRequirements.checked_complete checked
            simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
              RecursiveRecomposition.value_evaluation
                (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
                  (SourcePlannedSources.expression_erase current))) closed.1,
              RecursiveRecomposition.merge_empty_left, spendAll, RecursiveContexts.plain_owners] at oldEvaluation
            simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation]
            exact oldEvaluation

/-- Returning across this frame retains every saved-plan certificate. -/
theorem finish_cleanup
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope .unit (.push (.running action value closed) tail) wholeForest output demand row evidence) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        action.scope value tail rest.forest output demand row evidence := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | running scopeKnown callback saved annotation interface =>
      cases matched with
      | running matched =>
        obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        exact ⟨⟨_, _, _⟩, value_configuration saved closed.1 scopeTyped rest closing templatesAfter
          matched unique (RecursiveCompletion.empty_head checked) accepted⟩

/-- Returning across this frame retains every saved-plan certificate. -/
theorem finish_close
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope .unit (.push (.closing identity caller) tail) wholeForest output demand row evidence) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        caller .unit tail rest.forest output demand row evidence := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | closing scopeKnown interface =>
      cases matched with
      | running matched =>
        obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        exact ⟨⟨_, _, _⟩, value_configuration .unit trivial scopeTyped rest closing templatesAfter
          matched unique (RecursiveCompletion.empty_head checked) accepted⟩

/-- Returning across this frame retains every saved-plan certificate. -/
theorem leave_handler
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.handler handler) tail) wholeForest output demand row evidence) (isValue : value.IsValue) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        handler.scope value tail rest.forest output demand row evidence := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state isValue
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | handler scope annotation clauses coverage uniqueClauses declarations recipes supplied capabilities modes =>
      cases matched with
      | handler matched =>
        obtain ⟨ticket, scopeTyped⟩ := scope
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        exact ⟨⟨_, _, _⟩, value_configuration summary isValue scopeTyped rest closing templatesAfter
          matched unique (RecursiveCompletion.empty_head checked) accepted⟩

/-- Returning across this frame retains every saved-plan certificate. -/
theorem leave_cell
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.cell identity payload caller answer) tail) wholeForest output demand row evidence) (isValue : value.IsValue) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        caller value tail rest.forest output demand row evidence := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state isValue
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | cell scopeKnown noEscape annotation interface =>
      cases matched with
      | cell matched =>
        obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        exact ⟨⟨_, _, _⟩, value_configuration summary isValue scopeTyped rest closing templatesAfter
          matched unique (RecursiveCompletion.empty_head checked) accepted⟩

theorem leave_clause
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.spent owner answer caller tail) wholeForest output demand row evidence)
    (isValue : value.IsValue) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        caller value tail rest.forest output demand row evidence := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state isValue
  cases closing with
  | spent closing => cases pending with
  | spent known annotation scope rest bound =>
    cases matched with
    | spent matched =>
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
        exact ⟨⟨_, _, _⟩, value_configuration summary isValue scopeTyped rest closing templatesAfter matched unique
          (by simpa only [same, List.nil_append, spendAll, ownedTickets] using tailCheck) accepted⟩
      · cases evaluated

/-- Cleanup startup runs the exact retained callback plan under the running
protection marker and retains the value to return after callback completion. -/
theorem start_cleanup
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.armed action) tail) wholeForest output demand row evidence)
    (closed : ClosedValue value) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        .none (.app action.action .unit) (.push (.running action value closed) tail) (.running rest.forest) output demand row evidence := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state closed.1
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | armed scopeKnown callback annotation interface callbackCheck =>
      rename_i restScope restHints restForest callbackDep latent callbackPlan
      cases matched with
      | cleanup matched =>
        cases interface with
        | armed caller callable requests =>
          obtain ⟨callbackRow, tailRow, headCheck, tailCheck, same⟩ :=
            RecursiveRequirements.checked_sequence_parts checked
          have exported := RecursiveRequirements.checked_complete headCheck
          simp only [RecursiveRequirements.evaluate_prepend, RecursiveContexts.evaluate_request, List.append_nil] at exported
          have invocation : Expression operations policy contracts world action.requests .none (fun _ => none)
              (.app action.action .unit) .unit []
              (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
              (signature (.sequence .pure (.sequence .pure callbackPlan))) :=
            .app (summary_expression (SourcePlannedSources.Values.change_allowed callback action.closed.1 action.requests) .none)
              .unit (List.Subset.refl _)
          have currentCheck : RecursiveRequirements.Checked (records ++ disposals)
              (OwnerPhases.ofStack tables (.push (.running action value closed) tail))
              (OwnerPhaseTransitions.available (ownedTickets tail))
              (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent) callbackRow := by
            apply RecursiveRequirements.evaluate_sound
            simpa only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
              RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left,
              spendAll, List.nil_append, RecursiveContexts.evaluate_request,
              RecursiveCompletion.running_export, ownedTickets] using exported
          have currentPrefixed : RecursiveRequirements.Checked (records ++ disposals) []
              (OwnerPhaseTransitions.available (ownedTickets tail))
              ((Requirements.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent).prepend
                (OwnerPhases.ofStack tables (.push (.running action value closed) tail))) callbackRow :=
            RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)
          have empty : RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets tail))
              ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables tail)) [] :=
            .request (row := []) (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
          have savedTyped : ScopedPorts.Typed operations.erase.erase.ports world ScopedPorts.TypeEnv.empty .none [] value
              (ScopedPorts.eraseType action.answer) := by
            have environmentSame : (SourcePlannedTyping.Environment.erase (fun _ => none)).erase.ports = ScopedPorts.TypeEnv.empty := by
              funext name; rfl
            simpa only [← annotation, environmentSame] using
              (DeclaredSourceValues.erase (SourceDependencyFrames.value_erase (SourcePlannedSources.expression_erase summary))).ports .none
          have templatesAfter := templates.transport (nextRoot := .push (.running action value closed) tail)
            (fun _ _ known => known) (fun _ _ known => known)
            (fun _ _ located => by cases located with | push inner => exact .push inner)
          have localCallback := (SourceScheduledRecomposition.local_append_nil (Forest.running restForest)).mp callbackCheck
          have nextPending := RecursiveRequirements.Checked.sequence empty tailCheck
          rw [same] at accepted ⊢
          refine ⟨⟨_, _, _⟩, SourceScheduledState.State.checked invocation .none
            (.push (.running scopeKnown callback summary annotation (.running caller callable savedTyped requests)) rest requests)
            (.push closing) templatesAfter (.running matched) (.sequence .pure (.sequence .pure localCallback)) unique ?_ accepted rfl⟩
          simpa only [List.nil_append, ownedTickets] using RecursiveRequirements.Checked.sequence currentPrefixed nextPending

/-- Every actual returned-value step except ticket retirement preserves the
same scheduled state, demand and row. Retirement changes the phase map and is
a separate transport obligation; it is not silently classified as pure. -/
theorem value_step_without_retirement
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope value stack forest output demand row evidence)
    (isValue : value.IsValue)
    (step : RawStep ⟨value, scope, stack⟩ next created completed)
    (noRetirement : RecursiveCompletion.retiredTickets completed = []) :
    ∃ nextForest : SourceScheduledSavedPlans.Saved,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack nextForest.forest output demand row evidence ∧ created = [] ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) []
        (OwnerPhaseTransitions.available (ownedTickets next.stack)) := by
  cases step <;> try cases isValue
  case focus => exact False.elim (ScopedPorts.focus_is_not_value (by assumption) isValue)
  case plug =>
    obtain ⟨rest, dependencies, contextPlan, same, next⟩ := plug_preserves state (by assumption)
    exact ⟨rest, next, rfl, .nil⟩
  case leaveHandler =>
    obtain ⟨rest, next⟩ := leave_handler state (show ClosedValue _ from by assumption).1
    exact ⟨rest, next, rfl, .nil⟩
  case leaveCell =>
    obtain ⟨rest, next⟩ := leave_cell state (show ClosedValue _ from by assumption).1
    exact ⟨rest, next, rfl, .nil⟩
  case startCleanup =>
    obtain ⟨rest, next⟩ := start_cleanup state (by assumption)
    exact ⟨⟨_, _, .running rest.forest⟩, next, rfl, .nil⟩
  case finishCleanup =>
    obtain ⟨rest, next⟩ := finish_cleanup state
    exact ⟨rest, next, rfl, .nil⟩
  case leaveClause =>
    obtain ⟨rest, next⟩ := leave_clause state (show ClosedValue _ from by assumption).1
    exact ⟨rest, next, rfl, .nil⟩
  case finishClose =>
    obtain ⟨rest, next⟩ := finish_close state
    exact ⟨rest, next, rfl, .nil⟩
  case retire => cases noRetirement

end Ash.OneShot.SourceScheduledValues

#print axioms Ash.OneShot.SourceScheduledValues.plug_checked

#print axioms Ash.OneShot.SourceScheduledValues.plug_preserves

#print axioms Ash.OneShot.SourceScheduledValues.value_pending
#print axioms Ash.OneShot.SourceScheduledValues.value_configuration
#print axioms Ash.OneShot.SourceScheduledValues.finish_cleanup
#print axioms Ash.OneShot.SourceScheduledValues.finish_close
#print axioms Ash.OneShot.SourceScheduledValues.leave_handler
#print axioms Ash.OneShot.SourceScheduledValues.leave_cell

#print axioms Ash.OneShot.SourceScheduledValues.leave_clause
#print axioms Ash.OneShot.SourceScheduledValues.start_cleanup

#print axioms Ash.OneShot.SourceScheduledValues.value_step_without_retirement
