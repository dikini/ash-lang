import SourcePlannedPhases

/-! Fresh capture derives the stronger retained-source premises from the
pre-capture request and pending forest. Phase restoration, fresh permission
extension and structural recomposition reuse established proofs. -/
namespace Ash.OneShot.SourcePlannedCapturePrep
open SourceContextualHints (Hints)
open SourcePlannedChecks (Local Pending)
open SourceContextualInvocationHints (forClosing)
open SourceContextualHintChecking (Compatible)
open OwnerPhaseTransitions (introduce spend)

private theorem pending_congr {first : Hints firstScope} {second : Hints secondScope}
    (same : firstScope = secondScope) (hints : HEq first second)
    (checked : Pending outward actions phases world first outside) : Pending outward actions phases world second outside := by
  cases same
  cases hints
  exact checked

private theorem compatible_congr {first : Hints firstScope} {second : Hints secondScope}
    (same : firstScope = secondScope) (hints : HEq first second)
    (checked : Compatible first outside) : Compatible second outside := by
  cases same
  cases hints
  exact checked

theorem cut_pending {hints : Hints scope} {saved : Hints captured} {waiting : Hints tail}
    (cut : SourcePlannedCuts.Cut effect operation contract modes hints saved waiting)
    (checked : Pending outward actions phases world hints .nil) :
    Pending outward actions phases world saved waiting ∧ Pending outward actions phases world waiting .nil := by
  have joined := pending_congr cut.reconstruct_scope cut.hints checked
  obtain ⟨inside, outside⟩ := (SourcePlannedRecomposition.pending_append_iff _ _ _).mp joined
  exact ⟨(SourcePlannedRecomposition.pending_outside_nil waiting).mp inside, outside⟩

theorem cut_compatible {hints : Hints scope} {saved : Hints captured} {waiting : Hints tail}
    (cut : SourcePlannedCuts.Cut effect operation contract modes hints saved waiting)
    (checked : Compatible hints .nil) :
    Compatible (.live (owner := owner) saved waiting) .nil ∧ Compatible waiting .nil := by
  have joined := compatible_congr cut.reconstruct_scope cut.hints checked
  obtain ⟨inside, outside⟩ := (SourceContextualHintChecking.compatible_append_iff _ _).mp joined
  exact ⟨.live inside outside, outside⟩

/-- All retained-source checks follow from pre-capture judgments. The spent
phase is the original phase map because the newly introduced owner was fresh.
The independently supplied action permission determines which clause may use it. -/
theorem captured_checks {hints : Hints scope} {saved : Hints captured} {waiting : Hints tail}
    (cut : SourcePlannedCuts.Cut effect operation contract modes hints saved waiting)
    (request : Local outward actions phases world (.request (effect := effect) (operation := operation)) hints)
    (retained : Pending outward actions phases world hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    Pending outward (actions.insert owner rights) (introduce phases owner) world (.live (owner := owner) saved waiting) .nil ∧
    Pending outward (actions.insert owner rights) (spend (introduce phases owner) owner) world saved (.spent (owner := owner) waiting) ∧
    Pending outward (actions.insert owner rights) (spend (introduce phases owner) owner) world waiting .nil ∧
    (contract.dispose = true → captured.held = false ∧ SourceRecursiveRoutes.Closing outward captured.shape [] [] ∧
      Pending outward (actions.insert owner rights) (spend (introduce phases owner) owner) world
        (forClosing saved) (.running (.spent (owner := owner) waiting))) := by
  have permissions := Syntax.fresh_usage_insert_extends (rights := rights) fresh
  have samePhases := OwnerCaptureContracts.spend_introduced consumed
  obtain ⟨inside, outside⟩ := cut_pending cut retained
  have savedNext := SourcePlannedPhases.pending_transport inside (fun _ ready => ready) permissions
  have waitingNext := SourcePlannedPhases.pending_transport outside (fun _ ready => ready) permissions
  have liveBefore : Pending outward actions phases world (.live (owner := owner) saved waiting) .nil :=
    .live ((SourcePlannedRecomposition.pending_outside_nil waiting).mpr inside) outside
  refine ⟨SourcePlannedPhases.pending_transport liveBefore SourceDependencySchemes.introduce_extends permissions, ?_, ?_, ?_⟩
  · rw [samePhases]
    exact SourcePlannedNeutralChecks.pending_outside_transport savedNext (.history .refl)
  · simpa only [samePhases] using waitingNext
  · intro disposes
    obtain ⟨unprotected, closing, _⟩ := SourceDependencyCapture.disposing_capture
      (SourceDependencySchemes.checked_request request.erase) cut.lookup disposes
    refine ⟨unprotected, closing, ?_⟩
    rw [samePhases]
    cases request with
    | request guard schedule =>
        have callback := schedule _ _ saved waiting _ _ cut.hints cut.lookup disposes
        have callbackNext := SourcePlannedPhases.pending_transport callback (fun _ ready => ready) permissions
        exact SourcePlannedNeutralChecks.pending_outside_transport callbackNext (.running (.history .refl))

end Ash.OneShot.SourcePlannedCapturePrep

#print axioms Ash.OneShot.SourcePlannedCapturePrep.cut_pending
#print axioms Ash.OneShot.SourcePlannedCapturePrep.cut_compatible
#print axioms Ash.OneShot.SourcePlannedCapturePrep.captured_checks
