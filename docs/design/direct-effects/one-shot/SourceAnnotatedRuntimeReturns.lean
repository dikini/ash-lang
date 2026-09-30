import SourceAnnotatedRuntimeFocus
import SourceBoundExits

/-! Returned values recompose with their actual annotated saved contexts.
The established plan reconstruction, value evaluation and combined row proofs
are reused without assuming successor annotations or successful execution. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeReturns

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements evaluate)
open ProtectionResiduals (merge)
open OwnerPhaseTransitions (spendAll)
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value)
open SourceAnnotatedSources (Expression Node Context ValueSummary)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceScheduledChecks (Local)
open SourceRetainedPlans (Forest)

theorem plug_checked_node_bounds {plan : Plan dependencies} {hints : Hints receiving} {forest : Forest hints}
    (context : Context operations policy contracts world environment allowed scope position input output demand requirements (signature plan))
    (checked : Local outward actions phases world plan forest)
    (value : ValueSummary operations policy contracts world environment allowed code input)
    (isValue : code.erase.IsValue) (bounds : SourcePlanBounds.Annotation world plan) :
    let next := bounds.plug position
    ∃ (combined : Requirements demand),
      Node operations policy contracts world allowed scope environment (position.plug code) output
        demand combined (signature next.2.1) ∧ Local outward actions phases world next.2.1 forest ∧
      ∀ store receiving before, evaluate store receiving before combined = evaluate store receiving before requirements := by
  have child := SourceAnnotatedSources.Values.change_context value isValue allowed scope
  generalize sameSignature : signature plan = checking at context
  cases context with
  | pairLeft right =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.pair child right), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | pairRight left leftValue =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.pair (SourceAnnotatedSources.Values.change_context (SourceAnnotatedSources.Values.summary left leftValue) leftValue _ scope) child), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | appFunction argument admitted =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.app child argument admitted), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | appArgument function functionValue admitted =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.app (SourceAnnotatedSources.Values.change_context (SourceAnnotatedSources.Values.summary function functionValue) functionValue _ scope) child admitted), .sequence .pure (.sequence .pure checked), ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left,
        RecursiveContexts.evaluate_request, List.nil_append]
  | bind body =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.bind child body), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | branch yes no same =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.branch child yes no same), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | perform known admitted formed =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.perform known admitted child formed), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left, RecursiveContexts.evaluate_request, List.nil_append]
  | resume known resolved permission admitted formed =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.resume known resolved permission child admitted formed), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]
  | cleanup body admitted =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.cleanup child body admitted), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | resource body formed effectsBound admitted hidden =>
      refine ⟨_, (by simpa only [SourcePlanBounds.Annotation.plug, signature, sameSignature, SourceAnnotatedCode.Context.plug, List.nil_append] using Node.resource child body formed effectsBound admitted hidden), .sequence .pure checked, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]

theorem plug_checked_node {plan : Plan dependencies} {hints : Hints receiving} {forest : Forest hints}
    (context : Context operations policy contracts world environment allowed scope position input output demand requirements (signature plan))
    (checked : Local outward actions phases world plan forest)
    (value : ValueSummary operations policy contracts world environment allowed code input)
    (isValue : code.erase.IsValue) :
    ∃ (combined : Requirements demand) (nextDependencies : Dependencies) (nextPlan : Plan nextDependencies),
      Node operations policy contracts world allowed scope environment (position.plug code) output
        demand combined (signature nextPlan) ∧ Local outward actions phases world nextPlan forest ∧
      ∀ store receiving before, evaluate store receiving before combined = evaluate store receiving before requirements := by
  obtain ⟨combined, node, checked, evaluation⟩ := plug_checked_node_bounds context checked value isValue .absent
  exact ⟨combined, _, _, node, checked, evaluation⟩

/-- Finite saved metadata is sufficient to lift the checked node back to a
complete annotated expression at the original context's result type. -/
theorem plug_checked_bounds {plan : Plan dependencies} {hints : Hints receiving} {forest : Forest hints}
    (context : Context operations policy contracts world environment allowed scope position input output demand requirements (signature plan))
    (hint : SourceFocusHints.checkSource Instantiation.Environment.empty position.hint output = true)
    (closed : position.ResourceClosed)
    (checked : Local outward actions phases world plan forest)
    (value : ValueSummary operations policy contracts world environment allowed code input)
    (isValue : code.erase.IsValue) (bounds : SourcePlanBounds.Annotation world plan) :
    let next := bounds.plug position
    ∃ (combined : Requirements demand),
      Expression operations policy contracts world allowed scope environment (position.plug code) output
        demand combined (signature next.2.1) ∧ Local outward actions phases world next.2.1 forest ∧
      ∀ store receiving before, evaluate store receiving before combined = evaluate store receiving before requirements := by
  obtain ⟨combined, node, nextCheck, evaluation⟩ := plug_checked_node_bounds context checked value isValue bounds
  refine ⟨combined, .checked ?_ ?_ node, nextCheck, evaluation⟩
  · simpa only [SourceAnnotatedCode.Context.plug_hint] using hint
  · exact SourceAnnotatedCode.Term.check_closed_iff.mpr ((position.plug_closed_iff code).mpr ⟨closed, value.resource_closed⟩)

theorem plug_checked {plan : Plan dependencies} {hints : Hints receiving} {forest : Forest hints}
    (context : Context operations policy contracts world environment allowed scope position input output demand requirements (signature plan))
    (hint : SourceFocusHints.checkSource Instantiation.Environment.empty position.hint output = true)
    (closed : position.ResourceClosed)
    (checked : Local outward actions phases world plan forest)
    (value : ValueSummary operations policy contracts world environment allowed code input)
    (isValue : code.erase.IsValue) :
    ∃ (combined : Requirements demand) (nextDependencies : Dependencies) (nextPlan : Plan nextDependencies),
      Expression operations policy contracts world allowed scope environment (position.plug code) output
        demand combined (signature nextPlan) ∧ Local outward actions phases world nextPlan forest ∧
      ∀ store receiving before, evaluate store receiving before combined = evaluate store receiving before requirements := by
  obtain ⟨combined, source, checked, evaluation⟩ := plug_checked_bounds context hint closed checked value isValue .absent
  exact ⟨combined, _, _, source, checked, evaluation⟩

theorem value_pending
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope value stack forest output demand row evidence)
    (isValue : value.erase.IsValue) :
    ∃ (input : Value) (incoming : List Instance) (requirements : Requirements demand)
      (records disposals : RecursiveRequirements.Store),
      ValueSummary operations policy contracts world (fun _ => none) [] value input ∧
      ScopedPorts.EffectScopeKnown contracts.erase.erase.ports scope ∧
      SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world stack input output demand requirements records forest .nil incoming [] ∧
      DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals ∧
      SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals ∧
      SourceScheduledSavedPlans.Matches annotations forest ∧
      (ownedTickets stack.erase).Nodup ∧
      RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase)) requirements row ∧
      checkFootprint outside row = true := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      subst demand
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
          (SourcePlannedSources.expression_erase current.erase))) isValue
      subst_vars
      refine ⟨_, _, _, _, _, SourceAnnotatedSources.Values.change_allowed
        (SourceAnnotatedSources.Values.summary current isValue) isValue [], ⟨_, scopeTyped⟩,
        pending, closing, templates, matched, unique, RecursiveRequirements.evaluate_sound ?_, accepted⟩
      have evaluation := RecursiveRequirements.checked_complete checked
      simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveRecomposition.value_evaluation
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
            (SourcePlannedSources.expression_erase current.erase))) isValue,
        spendAll, RecursiveRecomposition.merge_empty_left] using evaluation

theorem value_configuration_atPlan
    (summary : ValueSummary operations policy contracts world (fun _ => none) [] code input)
    (isValue : code.erase.IsValue)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket)
    (pending : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world stack input output demand requirements records forest .nil incoming [])
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
    (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (unique : (ownedTickets stack.erase).Nodup)
    (checked : RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase)) requirements row)
    (accepted : checkFootprint outside row = true) :
    SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope code stack .pure forest output demand row evidence := by
  have current : RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase))
      ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables stack.erase)) [] :=
    .request (row := []) (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  exact .checked (SourceAnnotatedSources.Values.change_context summary isValue incoming scope) scopeTyped
    pending closing templates matched .pure unique
    (by simpa only [List.nil_append] using RecursiveRequirements.Checked.sequence current checked) accepted rfl

theorem value_configuration
    (summary : ValueSummary operations policy contracts world (fun _ => none) [] code input)
    (isValue : code.erase.IsValue)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket)
    (pending : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world stack input output demand requirements records forest .nil incoming [])
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
    (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (unique : (ownedTickets stack.erase).Nodup)
    (checked : RecursiveRequirements.Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase)) requirements row)
    (accepted : checkFootprint outside row = true) :
    SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope code stack forest output demand row evidence :=
  (value_configuration_atPlan summary isValue scopeTyped pending closing templates matched unique checked accepted).state

/-- Return advances the persistent snapshot and the plan-indexed shared
state on the same raw step, retaining the exact queued bounds and queue tail. -/
theorem plug_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.plain plain) tail) snapshot.plan snapshot.forest output demand row evidence)
    (closed : ClosedValue value.erase) :
    ∃ next : SourceBoundSnapshots.Snapshot world,
      RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨value, scope, .push (.plain plain) tail⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨plain.context.plug value, plain.scope, tail⟩) [] [] ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        plain.scope (plain.context.plug value) tail next.plan next.forest output demand row evidence ∧
      SourceBoundSnapshots.Returned plain.context snapshot next := by
  rcases snapshot with ⟨rootDependencies, rootPlan, rootBounds, receiving, hints, wholeForest, queuedMetadata⟩
  dsimp only at state ⊢
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      subst demand
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
          (SourcePlannedSources.expression_erase current.erase))) closed.1
      subst_vars
      cases closing with
      | push closing => cases pending with
      | push frame pending bound => cases frame with
        | plain context hint metadata frameScope inputAnnotation outputAnnotation contextCheck =>
          cases matched with
          | plain matched => cases queuedMetadata with
          | plain queued remaining =>
            obtain ⟨combined, combinedSource, combinedCheck, evaluation⟩ :=
              plug_checked_bounds context hint metadata ((SourceScheduledRecomposition.local_append_nil _).mp contextCheck)
                (SourceAnnotatedSources.Values.change_allowed (SourceAnnotatedSources.Values.summary current closed.1) closed.1 _) closed.1 queued
            have templatesAfter := templates.transport (nextRoot := tail)
              (fun _ _ known => known) (fun _ _ known => known)
              (fun _ _ located => by cases located with | push inner => exact inner)
            let next := SourceBoundSnapshots.Snapshot.returned (.plain queued remaining)
              (queued.plug plain.context).2.1 (queued.plug plain.context).2.2
            refine ⟨next, SourceAnnotatedRuntime.plug_executes plain value closed scope tail,
              SourceAnnotatedRuntimeState.AtPlan.checked combinedSource frameScope pending closing templatesAfter
                matched combinedCheck unique ?_ accepted rfl, .plain rootBounds queued remaining⟩
            apply RecursiveRequirements.evaluate_sound
            have oldEvaluation := RecursiveRequirements.checked_complete checked
            simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
              RecursiveRecomposition.value_evaluation
                (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
                  (SourcePlannedSources.expression_erase current.erase))) closed.1,
              RecursiveRecomposition.merge_empty_left, spendAll, SourceAnnotatedRuntime.Stack.erase,
              SourceAnnotatedRuntime.Frame.erase, RecursiveContexts.plain_owners] at oldEvaluation
            simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation]
            exact oldEvaluation


/-- Returning into a plain frame preserves the complete scheduled state.
The retained context supplies both the actual plan and its local check. -/
theorem plug_preserves
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.plain plain) tail) wholeForest output demand row evidence)
    (closed : ClosedValue value.erase) :
    ∃ rest : SourceScheduledSavedPlans.Saved, ∃ dependencies, ∃ contextPlan : Plan dependencies,
      HEq wholeForest (Forest.plain contextPlan rest.forest) ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        plain.scope (plain.context.plug value) tail rest.forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, wholeForest, SourceBoundSnapshots.Retained.absent wholeForest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          scope value (.push (.plain plain) tail) snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting
      obtain ⟨next, step, typed, returned⟩ := plug_snapshot snapshot indexed closed
      obtain ⟨dependencies, contextPlan, same⟩ := returned.forest
      exact ⟨⟨next.scope, next.hints, next.forest⟩, dependencies, contextPlan, same, typed.state⟩


end Ash.OneShot.SourceAnnotatedRuntimeReturns

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.plug_checked_node

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.plug_checked

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.value_pending

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.value_configuration

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.plug_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.plug_checked_node_bounds
#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.plug_checked_bounds

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.plug_snapshot

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.value_configuration_atPlan
