import SourceScheduledRuntimeCells

/-! Existing structural clause recipes discharge the capture-site obligations
from the actual request, retained source and finite handler-requirement check.
The retained pending judgment supplies the current requirement check. -/
namespace Ash.OneShot.SourceScheduledState
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceRetainedPlans (Forest)
open SourcePlanSignatures (signature)

theorem capture_from_recipes {hints : SourceContextualHints.Hints receiving} {forest : Forest hints}
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole forest output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      State operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  apply capture_preserves state cut isValue selected found freshContract freshAction freshAnnotation supported
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals sourcePlan
    generalize frozen : Instantiation.freezeEffect requested = actualEffect at current
    generalize planSignature : signature sourcePlan = checking at current
    cases current with
    | perform operationKnown admitted operandSource formed =>
      cases freeze_effect_injective frozen
      cases sourcePlan with
      | sequence operandPlan requestPlan =>
        cases requestPlan
        cases contextual with
        | sequence operandCheck requestCheck =>
          have clauseModes : SourceTemplates.ClauseModes handler.clauses (tables handler) := by
            obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
              capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
              SourceDependencyFrames.capture_segments cut pending.source.source.erase
            cases frame with
            | handler scope annotation clauses coverage unique declarations capabilities modes => exact modes
          have freshErased : contracts.erase.erase owner = none := by
            simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
          have absent := RecursiveCapture.fresh_unowned pending.source.source.erase.erase.source.erase freshErased
          intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
          exact SourceScheduledAllocationData.capture_requirements_from_recipe cut pending.source.source.matches
            recipes clauseModes selected found declared requestCheck pending.pending pending.pending.compatible freshAction absent plannedCut chosen


/-- Disposal certificates follow from the source request and the selected
clause's action bound. Reuse the existing capture certificate construction. -/
theorem capture_certificate_from_source
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase))
    (disposes : code.requiredActions.dispose = true)
    (record : CoherentSourceTypes.Owners.Record) :
    Nonempty (DeclaredClosingInvariant.Certificate operations.erase.erase.ports world record capture) := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals sourcePlan
    generalize frozen : Instantiation.freezeEffect requested = actualEffect at current
    generalize planSignature : signature sourcePlan = checking at current
    cases current with
    | perform operationKnown admitted operandSource formed =>
      cases freeze_effect_injective frozen
      cases sourcePlan with
      | sequence operandPlan requestPlan =>
        cases requestPlan
        cases contextual with
        | sequence operandCheck requestCheck =>
          have clauseModes : SourceTemplates.ClauseModes handler.clauses (tables handler) := by
            obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
              capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
              SourceDependencyFrames.capture_segments cut pending.source.source.erase
            cases frame with
            | handler scope annotation clauses coverage unique declarations capabilities modes => exact modes
          obtain ⟨actual, actualFound, permission⟩ := SourceTemplates.selected_clause_mode selected clauseModes
          cases Option.some.inj (actualFound.symm.trans found)
          have permitted := permission disposes
          have internal := SourceDependencySchemes.capture_internal_uses cut pending.source.source.erase
            requestCheck.erase.erase found permitted
          have guard := SourceDependencyCapture.check_capture_outward_weaken
            (SourceDependencySchemes.checked_request requestCheck.erase.erase) (List.nil_subset record.annotation.closeEffects)
          obtain ⟨_, _, _, _, _, _, _, _, _, _, certificate, _⟩ :=
            SourceDependencyFrames.capture_certificate cut pending.source.source.erase guard found permitted supported internal
          exact ⟨certificate⟩

end Ash.OneShot.SourceScheduledState

#print axioms Ash.OneShot.SourceScheduledState.capture_from_recipes

#print axioms Ash.OneShot.SourceScheduledState.capture_certificate_from_source
