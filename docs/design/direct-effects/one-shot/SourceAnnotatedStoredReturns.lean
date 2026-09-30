import SourceAnnotatedStoredResumption
import SourceAnnotatedRuntimeReturns
import SourceBoundExits

/-! Returned values recompose with their actual annotated saved contexts.
The established plan reconstruction, value evaluation and combined row proofs
are reused without assuming successor annotations or successful execution. -/
namespace Ash.OneShot.SourceAnnotatedStoredReturns

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

open SourceAnnotatedRuntimeReturns (plug_checked_bounds)

theorem value_pending
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope value stack plan forest output demand row stored evidence)
    (isValue : value.erase.IsValue) :
    ∃ (input : Value) (incoming : List Instance) (requirements : Requirements demand)
      (records disposals : RecursiveRequirements.Store),
      ValueSummary operations policy contracts world (fun _ => none) [] value input ∧
      ScopedPorts.EffectScopeKnown contracts.erase.erase.ports scope ∧
      SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world stack input output demand requirements records forest .nil incoming [] stored ∧
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

theorem plug_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.plain plain) tail) snapshot.plan snapshot.forest output demand row (.push .plain stored) evidence)
    (closed : ClosedValue value.erase) :
    ∃ next : SourceBoundSnapshots.Snapshot world,
      RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨value, scope, .push (.plain plain) tail⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨plain.context.plug value, plain.scope, tail⟩) [] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        plain.scope (plain.context.plug value) tail next.plan next.forest output demand row stored evidence ∧
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
      | push frame pending bound => rcases frame with ⟨frame, packetSource⟩; cases frame with
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
              SourceAnnotatedRuntimeState.AtPackets.checked combinedSource frameScope pending closing templatesAfter
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


end Ash.OneShot.SourceAnnotatedStoredReturns

#print axioms Ash.OneShot.SourceAnnotatedStoredReturns.value_pending
#print axioms Ash.OneShot.SourceAnnotatedStoredReturns.plug_snapshot
