import SourceBoundResumption

/-! Capture moves the original pending annotations under a fresh live owner.
The exact saved/waiting cut and the established split/recomposition proof
determine the successor data; no queued annotation is generated anew. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation)

inductive Captured (owner : Nat) : Snapshot world → Snapshot world → Prop where
  | cut {beforePlan : Plan beforeDependencies} {afterPlan : Plan afterDependencies}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      (before : Annotation world beforePlan) (after : Annotation world afterPlan)
      (captured : Retained world saved) (tail : Retained world waiting) :
      Captured owner ⟨_, beforePlan, before, _, _, saved.append waiting, captured.append tail⟩
        ⟨_, afterPlan, after, _, _, .live (owner := owner) saved waiting, .live captured tail⟩

/-- The physical source cut fixes both parts of the original pending data. -/
theorem capture_snapshot (before : Snapshot world)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut requested operation offered modes before.forest saved waiting)
    {plan : Plan dependencies} (current : Annotation world plan) :
    ∃ pending : Retained world (.live (owner := owner) saved waiting),
      Captured owner before ⟨_, plan, current, _, _, .live (owner := owner) saved waiting, pending⟩ := by
  rcases before with ⟨_, beforePlan, beforeCurrent, _, _, forest, retained⟩
  cases cut.erase.reconstruct_scope
  cases cut.erase.hints
  have forestSame := eq_of_heq cut.forest
  cases forestSame
  have reconstruct := retained.splitAt_append saved waiting
  generalize piecesKnown : retained.splitAt saved waiting = pieces at *
  rcases pieces with ⟨captured, tail⟩
  cases reconstruct
  exact ⟨_, .cut beforeCurrent current captured tail⟩

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- Current-clause admission is supplied by selection and generation. All
retained admission follows from the original snapshot and exact recomposition. -/
theorem Captured.admitted {before after : Snapshot world}
    (captured : Captured owner before after) (admitted : before.Admitted)
    (current : after.current.Admitted) : after.Admitted := by
  cases captured with
  | cut before after saved waiting =>
      obtain ⟨inside, outside⟩ := admitted.2.of_append
      exact ⟨current, .live inside outside⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.capture_snapshot
#print axioms Ash.OneShot.SourceBoundSnapshots.Captured.admitted
