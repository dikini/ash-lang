import SourceScheduledNeutral

/-! Owner annotations remember actual saved plans. Agreement is structural over
the entire retained forest, including captures inside dormant continuations.
The map records plan identity; it grants no continuation-use permission. -/
namespace Ash.OneShot.SourceScheduledSavedPlans
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
abbrev Receiving := SourceDependencyCapture.Scope

structure Saved where
  scope : Receiving
  hints : Hints scope
  forest : Forest hints

abbrev Annotations := Nat → Option Saved

def Annotations.scopes (annotations : Annotations) : Nat → Option Receiving :=
  fun owner => (annotations owner).map Saved.scope

def Annotations.insert (annotations : Annotations) (owner : Nat) (saved : Saved) : Annotations :=
  fun other => if other = owner then some saved else annotations other

inductive Matches (annotations : Annotations) : {scope : Receiving} → {hints : Hints scope} → Forest hints → Prop where
  | nil : Matches annotations .nil
  | plain : Matches annotations rest → Matches annotations (.plain plan rest)
  | handler : Matches annotations rest →
      Matches annotations (.handler (effect := effect) (table := table) (families := families) (required := required) rest)
  | cell : Matches annotations rest → Matches annotations (.cell (identity := identity) rest)
  | cleanup : Matches annotations rest → Matches annotations (.cleanup (needs := needs) plan rest)
  | running : Matches annotations rest → Matches annotations (.running rest)
  | live {savedHints : Hints captured} {saved : Forest savedHints}
      (known : annotations owner = some ⟨captured, savedHints, saved⟩)
      (inside : Matches annotations saved) (outside : Matches annotations rest) :
      Matches annotations (.live (owner := owner) saved rest)
  | spent : Matches annotations rest → Matches annotations (.spent (owner := owner) rest)

/-- The earlier scope-only bound follows from exact plan agreement. -/
theorem Matches.erase {hints : Hints scope} {forest : Forest hints}
    (matched : Matches annotations forest) : SourceDependencySchemes.Closing.Bound annotations.scopes scope := by
  induction matched with
  | nil => exact .nil
  | plain rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live known inside outside ihInside ihOutside => exact .live (by simp [Annotations.scopes, known]) ihInside ihOutside
  | spent rest ih => exact .spent ih

theorem Matches.congr {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    (matched : Matches annotations before) (scopeSame : beforeScope = afterScope)
    (hintsSame : HEq beforeHints afterHints) (forestSame : HEq before after) : Matches annotations after := by
  cases scopeSame
  cases hintsSame
  cases forestSame
  exact matched

theorem Matches.transport (matched : Matches annotations forest)
    (extension : ∀ owner saved, annotations owner = some saved → next owner = some saved) :
    Matches next forest := by
  induction matched with
  | nil => exact .nil
  | plain rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live known inside outside ihInside ihOutside => exact .live (extension _ _ known) ihInside ihOutside
  | spent rest ih => exact .spent ih

theorem matches_append (first : Forest front) (second : Forest tail) :
    Matches annotations (first.append second) ↔ Matches annotations first ∧ Matches annotations second := by
  induction first with
  | nil => exact ⟨fun matched => ⟨.nil, matched⟩, fun ⟨_, matched⟩ => matched⟩
  | plain plan rest ih =>
      constructor
      · intro matched; cases matched with | plain rest =>
          obtain ⟨inside, outside⟩ := ih.mp rest; exact ⟨.plain inside, outside⟩
      · rintro ⟨first, second⟩; cases first with | plain rest => exact .plain (ih.mpr ⟨rest, second⟩)
  | handler rest ih =>
      constructor
      · intro matched; cases matched with | handler rest =>
          obtain ⟨inside, outside⟩ := ih.mp rest; exact ⟨.handler inside, outside⟩
      · rintro ⟨first, second⟩; cases first with | handler rest => exact .handler (ih.mpr ⟨rest, second⟩)
  | cell rest ih =>
      constructor
      · intro matched; cases matched with | cell rest =>
          obtain ⟨inside, outside⟩ := ih.mp rest; exact ⟨.cell inside, outside⟩
      · rintro ⟨first, second⟩; cases first with | cell rest => exact .cell (ih.mpr ⟨rest, second⟩)
  | cleanup plan rest ih =>
      constructor
      · intro matched; cases matched with | cleanup rest =>
          obtain ⟨inside, outside⟩ := ih.mp rest; exact ⟨.cleanup inside, outside⟩
      · rintro ⟨first, second⟩; cases first with | cleanup rest => exact .cleanup (ih.mpr ⟨rest, second⟩)
  | running rest ih =>
      constructor
      · intro matched; cases matched with | running rest =>
          obtain ⟨inside, outside⟩ := ih.mp rest; exact ⟨.running inside, outside⟩
      · rintro ⟨first, second⟩; cases first with | running rest => exact .running (ih.mpr ⟨rest, second⟩)
  | live saved rest ihSaved ih =>
      constructor
      · intro matched; cases matched with | live known saved rest =>
          obtain ⟨inside, outside⟩ := ih.mp rest; exact ⟨.live known saved inside, outside⟩
      · rintro ⟨first, second⟩; cases first with | live known saved rest => exact .live known saved (ih.mpr ⟨rest, second⟩)
  | spent rest ih =>
      constructor
      · intro matched; cases matched with | spent rest =>
          obtain ⟨inside, outside⟩ := ih.mp rest; exact ⟨.spent inside, outside⟩
      · rintro ⟨first, second⟩; cases first with | spent rest => exact .spent (ih.mpr ⟨rest, second⟩)

theorem Matches.forClosing (matched : Matches annotations forest) : Matches annotations forest.forClosing := by
  induction matched with
  | nil => exact .nil
  | plain rest ih | handler rest ih | spent rest ih => exact ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live known inside outside ihInside ihOutside => exact (matches_append _ _).mpr ⟨ihInside, .running ihOutside⟩

theorem insert_extends (fresh : annotations owner = none) :
    ∀ other saved, annotations other = some saved → Annotations.insert annotations owner added other = some saved := by
  intro other saved known
  by_cases same : other = owner
  · subst other; rw [fresh] at known; cases known
  · simpa only [Annotations.insert, if_neg same] using known

theorem Matches.capture {savedHints : Hints captured} {saved : Forest savedHints}
    (matched : Matches annotations (saved.append waiting)) (fresh : annotations owner = none) :
    Matches (annotations.insert owner ⟨captured, savedHints, saved⟩) (.live (owner := owner) saved waiting) := by
  obtain ⟨inside, outside⟩ := (matches_append _ _).mp matched
  exact .live (by simp [Annotations.insert]) (inside.transport (insert_extends fresh)) (outside.transport (insert_extends fresh))

theorem Matches.resume {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (matched : Matches annotations (front.append (.live (owner := owner) saved tail))) :
    Matches annotations (saved.append (front.append (.spent (owner := owner) tail))) := by
  obtain ⟨before, captured⟩ := (matches_append _ _).mp matched
  cases captured with
  | live known inside outside => exact (matches_append _ _).mpr ⟨inside, (matches_append _ _).mpr ⟨before, .spent outside⟩⟩

theorem Matches.dispose {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (matched : Matches annotations (front.append (.live (owner := owner) saved tail))) :
    Matches annotations (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail)))) := by
  obtain ⟨before, captured⟩ := (matches_append _ _).mp matched
  cases captured with
  | live known inside outside =>
      exact (matches_append _ _).mpr ⟨inside.forClosing, .running ((matches_append _ _).mpr ⟨before, .spent outside⟩)⟩

/-- Active selection reads the same saved forest as the persistent annotation,
even when other captures occur in the intervening frames. -/
theorem Matches.selected {savedHints : Hints captured} {saved : Forest savedHints}
    (matched : Matches annotations whole)
    (cut : SourceScheduledNeutral.OwnerCut owner whole front saved tail) :
    annotations owner = some ⟨captured, savedHints, saved⟩ := by
  induction cut with
  | hit => cases matched with | live known inside outside => exact known
  | plain cut ih => cases matched with | plain rest => exact ih rest
  | handler cut ih => cases matched with | handler rest => exact ih rest
  | cell cut ih => cases matched with | cell rest => exact ih rest
  | cleanup cut ih => cases matched with | cleanup rest => exact ih rest
  | running cut ih => cases matched with | running rest => exact ih rest
  | live different cut ih => cases matched with | live known inside outside => exact ih outside
  | spent cut ih => cases matched with | spent rest => exact ih rest

end Ash.OneShot.SourceScheduledSavedPlans

#print axioms Ash.OneShot.SourceScheduledSavedPlans.Matches.transport
#print axioms Ash.OneShot.SourceScheduledSavedPlans.matches_append
#print axioms Ash.OneShot.SourceScheduledSavedPlans.Matches.forClosing
#print axioms Ash.OneShot.SourceScheduledSavedPlans.insert_extends
#print axioms Ash.OneShot.SourceScheduledSavedPlans.Matches.capture
#print axioms Ash.OneShot.SourceScheduledSavedPlans.Matches.resume
#print axioms Ash.OneShot.SourceScheduledSavedPlans.Matches.dispose
#print axioms Ash.OneShot.SourceScheduledSavedPlans.Matches.selected

#print axioms Ash.OneShot.SourceScheduledSavedPlans.Matches.congr

#print axioms Ash.OneShot.SourceScheduledSavedPlans.Matches.erase
