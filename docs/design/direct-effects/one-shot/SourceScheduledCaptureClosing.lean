import SourceScheduledCuts
import SourceScheduledClosing

/-! The physical handler cut supplies the retained source needed by closing
scheduling. Source, plan annotations and ownership accounting refer to the same
captured and waiting stacks. -/
namespace Ash.OneShot.SourceScheduledCaptureClosing
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledFrames (Segment)
open SourceScheduledChecks (Local)
open SourcePlannedClosingPlans (Plans Template Checked)
open RecursiveRequirements (Requirements Store)

/-- Derive the exact closing template and callback checks from the whole source
stack at its actual handler cut. The captured source and successful plan
construction are conclusions, using the established disposing-cut theorem. -/
theorem capture_closing {hints : Hints wholeScope} {forest : Forest hints}
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      whole input output demand requirements records forest .nil incoming outgoing)
    (request : Local outward actions phases world (.request (effect := requested) (operation := operation)) forest)
    (found : lookup operation (tables handler) = some offered)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler) = some modes)
    (disposes : offered.dispose = true) :
    ∃ plan, makePlan capture = some plan ∧
      InternalUses capture.erase.liveTickets capture.erase.pending ∧
    ∃ (answer : SourcePlannedTyping.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : Requirements capDemand) (tailReq : Requirements tailDemand)
      (capRecords tailRecords : Store) (capScope tailScope : SourceDependencyCapture.Scope),
    ∃ (savedHints : Hints capScope) (waitingHints : Hints tailScope),
    ∃ (savedForest : Forest savedHints) (waitingForest : Forest waitingHints),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        capture input answer capDemand capReq capRecords savedForest waitingForest incoming residual ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        tail answer output tailDemand tailReq tailRecords waitingForest .nil residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧
      HEq forest (savedForest.append waitingForest) ∧ demand = capDemand ++ tailDemand ∧
      records = capRecords ++ tailRecords ∧ ownedTickets whole = ownedTickets capture ++ ownedTickets tail ∧
      ∃ plans : Plans plan (SourceContextualInvocationHints.forClosing savedHints),
      ∃ raw, ∃ closingRequirements : Requirements (OwnerClosingSource.retirements plan),
        Template operations policy contracts tables world caller plans raw closingRequirements ∧
        Checked outward actions phases world (.running waitingHints) plans := by
  obtain ⟨derivedCap, derivedTail, derivedModes, plan, capRealizes, tailRealizes, same,
    selected, realizes, closing, unprotected, built, owners⟩ :=
    SourceDependencyCapture.checked_cut cut source.source.source.matches.realizes
      (SourceDependencySchemes.checked_request request.erase.erase) found disposes
  refine ⟨plan, built,
    SourceDependencySchemes.capture_internal_uses cut source.source.source.erase request.erase.erase found disposes, ?_⟩
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    savedHints, waitingHints, savedForest, waitingForest, annotation, frame, saved, waiting, scopeSame, hintsSame,
    forestSame, demandSame, recordsSame, selection, evaluation⟩ := SourceScheduledCuts.capture_segments cut source
  have chosen : SourceDependencyCapture.select requested operation wholeScope =
      some (.handler capScope tailScope offered modes) := by
    simpa only [SourceDependencyCapture.chosen, found, declared] using selection operation
  obtain ⟨actualSaved, actualWaiting, annotatedCut⟩ := SourcePlannedCuts.of_lookup hints chosen
  obtain ⟨rfl, rfl⟩ := annotatedCut.unique hintsSame
  have savedAtWaiting := saved.receiving_congr (SourceDependencyProjection.scope_append_nil _)
    (SourcePlannedRecomposition.hints_append_nil _) (SourceScheduledRecomposition.forest_append_nil _)
  obtain ⟨plans, raw, closingRequirements, template, checked⟩ :=
    SourceScheduledClosing.request_template (caller := caller) request annotatedCut forestSame disposes savedAtWaiting built
  refine ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    _, _, savedForest, waitingForest, savedAtWaiting, waiting, scopeSame, hintsSame, forestSame, demandSame, recordsSame,
    ?_, plans, raw, closingRequirements, template, checked⟩
  rw [handler_cut_reconstructs cut, owned_tickets_append]

end Ash.OneShot.SourceScheduledCaptureClosing

#print axioms Ash.OneShot.SourceScheduledCaptureClosing.capture_closing
