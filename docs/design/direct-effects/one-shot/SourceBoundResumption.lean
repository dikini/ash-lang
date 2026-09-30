import SourceBoundAdmissionSteps

/-! Resumption rearranges the original pending annotations with their source
forests. The selected live boundary becomes spent; dormant branches and all
recorded bounds move unchanged. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

def Retained.append {front : Forest frontHints} {tail : Forest tailHints}
    (first : Retained world front) (second : Retained world tail) : Retained world (front.append tail) :=
  match first with
  | .nil => second
  | .plain code rest => .plain code (rest.append second)
  | .handler rest => .handler (rest.append second)
  | .cell rest => .cell (rest.append second)
  | .cleanup code rest => .cleanup code (rest.append second)
  | .running rest => .running (rest.append second)
  | .live saved rest => .live saved (rest.append second)
  | .spent rest => .spent (rest.append second)

def Retained.splitAt (front : Forest frontHints) (tail : Forest tailHints)
    (source : Retained world (front.append tail)) : Retained world front × Retained world tail :=
  match front with
  | .nil => ⟨.nil, source⟩
  | .plain _ rest => match source with
    | .plain code next =>
      let pieces := next.splitAt rest tail
      ⟨.plain code pieces.1, pieces.2⟩
  | .handler rest => match source with
    | .handler next =>
      let pieces := next.splitAt rest tail
      ⟨.handler pieces.1, pieces.2⟩
  | .cell rest => match source with
    | .cell next =>
      let pieces := next.splitAt rest tail
      ⟨.cell pieces.1, pieces.2⟩
  | .cleanup _ rest => match source with
    | .cleanup code next =>
      let pieces := next.splitAt rest tail
      ⟨.cleanup code pieces.1, pieces.2⟩
  | .running rest => match source with
    | .running next =>
      let pieces := next.splitAt rest tail
      ⟨.running pieces.1, pieces.2⟩
  | .live _ rest => match source with
    | .live saved next =>
      let pieces := next.splitAt rest tail
      ⟨.live saved pieces.1, pieces.2⟩
  | .spent rest => match source with
    | .spent next =>
      let pieces := next.splitAt rest tail
      ⟨.spent pieces.1, pieces.2⟩

theorem Retained.splitAt_append (front : Forest frontHints) (tail : Forest tailHints)
    (source : Retained world (front.append tail)) :
    (source.splitAt front tail).1.append (source.splitAt front tail).2 = source := by
  induction front with
  | nil => rfl
  | plain plan rest ih => cases source with
    | plain code next => simp only [Retained.splitAt, Retained.append]; rw [ih next]
  | handler rest ih => cases source with
    | handler next => simp only [Retained.splitAt, Retained.append]; rw [ih next]
  | cell rest ih => cases source with
    | cell next => simp only [Retained.splitAt, Retained.append]; rw [ih next]
  | cleanup plan rest ih => cases source with
    | cleanup code next => simp only [Retained.splitAt, Retained.append]; rw [ih next]
  | running rest ih => cases source with
    | running next => simp only [Retained.splitAt, Retained.append]; rw [ih next]
  | live saved rest ihSaved ih => cases source with
    | live dormant next => simp only [Retained.splitAt, Retained.append]; rw [ih next]
  | spent rest ih => cases source with
    | spent next => simp only [Retained.splitAt, Retained.append]; rw [ih next]

/-- The existing split follows the fixed forest boundary; joining source data
and splitting there recovers both original bound trees. -/
theorem Retained.splitAt_join {front : Forest frontHints} {tail : Forest tailHints}
    (first : Retained world front) (second : Retained world tail) :
    (first.append second).splitAt front tail = (first, second) := by
  induction first <;> simp_all only [Retained.append, Retained.splitAt]

/-- This relation exposes the exact forest rearrangement already performed by
the runtime resumption proof. It introduces no scheduling premise. -/
inductive ResumeForest (owner : Nat) : {beforeScope afterScope : SourceDependencyCapture.Scope} →
    {beforeHints : Hints beforeScope} → {afterHints : Hints afterScope} →
    Forest beforeHints → Forest afterHints → Prop where
  | cut (front : Forest frontHints) (saved : Forest savedHints) (tail : Forest tailHints) :
      ResumeForest owner (front.append (.live (owner := owner) saved tail))
        (saved.append (front.append (.spent (owner := owner) tail)))

inductive Resumed (owner : Nat) : Snapshot world → Snapshot world → Prop where
  | cut {plan : SourceDeclarationPlans.Plan dependencies}
      {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
      (current : SourcePlanBounds.Annotation world plan)
      (before : Retained world front) (captured : Retained world saved) (after : Retained world tail) :
      Resumed owner ⟨_, plan, current, _, _, _, before.append (.live (owner := owner) captured after)⟩
        (Snapshot.value (captured.append (before.append (.spent (owner := owner) after))))

theorem ResumeForest.snapshot {before : Snapshot world} {after : Forest afterHints}
    (shape : ResumeForest owner before.forest after) :
    ∃ pending : Retained world after, Resumed owner before (Snapshot.value pending) := by
  rcases before with ⟨_, plan, current, _, _, forest, retained⟩
  cases shape with
  | cut front saved tail =>
    have reconstruct := retained.splitAt_append front (.live (owner := owner) saved tail)
    generalize piecesKnown : retained.splitAt front (.live (owner := owner) saved tail) = pieces at *
    rcases pieces with ⟨first, remaining⟩
    cases remaining with
    | live captured last =>
      cases reconstruct
      exact ⟨_, .cut current first captured last⟩

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem Retained.Admitted.append {front : Forest frontHints} {tail : Forest tailHints}
    {first : Retained world front} {second : Retained world tail}
    (before : first.Admitted) (after : second.Admitted) : (first.append second).Admitted := by
  induction before with
  | nil => exact after
  | plain code rest ih => exact .plain code ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup code rest ih => exact .cleanup code ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ih => exact .live saved ih
  | spent rest ih => exact .spent ih

theorem Retained.Admitted.of_append {front : Forest frontHints} {tail : Forest tailHints}
    {first : Retained world front} {second : Retained world tail}
    (admitted : (first.append second).Admitted) : first.Admitted ∧ second.Admitted := by
  induction first with
  | nil => exact ⟨.nil, admitted⟩
  | plain code rest ih => cases admitted with
    | plain checked next => obtain ⟨before, after⟩ := ih next; exact ⟨.plain checked before, after⟩
  | handler rest ih => cases admitted with
    | handler next => obtain ⟨before, after⟩ := ih next; exact ⟨.handler before, after⟩
  | cell rest ih => cases admitted with
    | cell next => obtain ⟨before, after⟩ := ih next; exact ⟨.cell before, after⟩
  | cleanup code rest ih => cases admitted with
    | cleanup checked next => obtain ⟨before, after⟩ := ih next; exact ⟨.cleanup checked before, after⟩
  | running rest ih => cases admitted with
    | running next => obtain ⟨before, after⟩ := ih next; exact ⟨.running before, after⟩
  | live saved rest ihSaved ih => cases admitted with
    | live dormant next => obtain ⟨before, after⟩ := ih next; exact ⟨.live dormant before, after⟩
  | spent rest ih => cases admitted with
    | spent next => obtain ⟨before, after⟩ := ih next; exact ⟨.spent before, after⟩

theorem Resumed.admitted {before after : Snapshot world}
    (step : Resumed owner before after) (admitted : before.Admitted) : after.Admitted := by
  cases step with
  | cut current first captured last =>
    obtain ⟨before, remaining⟩ := admitted.2.of_append
    cases remaining with
    | live saved tail => exact Snapshot.value_admitted (saved.append (before.append (.spent tail)))

end
end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.splitAt_append
#print axioms Ash.OneShot.SourceBoundSnapshots.ResumeForest.snapshot
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Admitted.append
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Admitted.of_append
#print axioms Ash.OneShot.SourceBoundSnapshots.Resumed.admitted

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.splitAt_join
