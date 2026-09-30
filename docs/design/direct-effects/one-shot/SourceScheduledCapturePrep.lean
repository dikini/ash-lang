import SourceScheduledNeutralChecks

/-! Fresh capture reconstructs retained-plan checks from the request and
pre-capture forest. Existing phase, permission and capability lemmas are reused. -/
namespace Ash.OneShot.SourceScheduledCapturePrep
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open OwnerPhaseTransitions (introduce spend)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

private theorem pending_congr {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints) (sameForest : HEq first second)
    (checked : Pending outward actions phases world first outside) : Pending outward actions phases world second outside := by
  cases sameScope
  cases sameHints
  cases sameForest
  exact checked

theorem cut_pending {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
    (checked : Pending outward actions phases world forest .nil) :
    Pending outward actions phases world saved waiting ∧ Pending outward actions phases world waiting .nil := by
  have joined := pending_congr cut.erase.reconstruct_scope cut.erase.hints cut.forest checked
  obtain ⟨inside, outside⟩ := (SourceScheduledRecomposition.pending_append_iff _ _ _).mp joined
  exact ⟨(SourceScheduledRecomposition.pending_outside_nil waiting).mp inside, outside⟩

/-- All retained-source checks follow from pre-capture judgments. The spent
phase is the original phase map because the newly introduced owner was fresh.
The independently supplied action permission determines which clause may use it. -/
theorem captured_checks [SourceScheduledChecks.DeclarationProjection admission certification] {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := effect) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    Pending outward (actions.insert owner rights) (introduce phases owner) world (.live (owner := owner) saved waiting) .nil ∧
    Pending outward (actions.insert owner rights) (spend (introduce phases owner) owner) world saved (.spent (owner := owner) waiting) ∧
    Pending outward (actions.insert owner rights) (spend (introduce phases owner) owner) world waiting .nil ∧
    (contract.dispose = true → captured.held = false ∧ SourceRecursiveRoutes.Closing outward captured.shape [] [] ∧
      Pending outward (actions.insert owner rights) (spend (introduce phases owner) owner) world
        saved.forClosing (.running (.spent (owner := owner) waiting))) := by
  have permissions := Syntax.fresh_usage_insert_extends (rights := rights) fresh
  have samePhases := OwnerCaptureContracts.spend_introduced consumed
  obtain ⟨inside, outside⟩ := cut_pending cut retained
  have savedNext := SourceScheduledTransport.pending_transport inside (fun _ ready => ready) permissions
  have waitingNext := SourceScheduledTransport.pending_transport outside (fun _ ready => ready) permissions
  have liveBefore : Pending outward actions phases world (.live (owner := owner) saved waiting) .nil :=
    .live ((SourceScheduledRecomposition.pending_outside_nil waiting).mpr inside) outside
  refine ⟨SourceScheduledTransport.pending_transport liveBefore SourceDependencySchemes.introduce_extends permissions, ?_, ?_, ?_⟩
  · rw [samePhases]
    exact SourceScheduledNeutralChecks.pending_outside_transport savedNext (.history .refl)
  · simpa only [samePhases] using waitingNext
  · intro disposes
    obtain ⟨unprotected, closing, _⟩ := SourceDependencyCapture.disposing_capture
      (SourceDependencySchemes.checked_request request.erase.erase) cut.erase.lookup disposes
    refine ⟨unprotected, closing, ?_⟩
    rw [samePhases]
    cases request with
    | request guard schedule =>
        have callback := schedule _ _ _ _ _ _ cut.erase saved waiting cut.forest disposes
        have callbackNext := SourceScheduledTransport.pending_transport callback (fun _ ready => ready) permissions
        exact SourceScheduledNeutralChecks.pending_outside_transport callbackNext (.running (.history .refl))

end Ash.OneShot.SourceScheduledCapturePrep

#print axioms Ash.OneShot.SourceScheduledCapturePrep.cut_pending
#print axioms Ash.OneShot.SourceScheduledCapturePrep.captured_checks
