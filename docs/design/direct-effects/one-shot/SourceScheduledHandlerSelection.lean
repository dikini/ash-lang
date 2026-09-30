import SourceScheduledFreshRequests

/-! Classify the origin of an actual selected handler after insertion.
Either the new interpretation intercepts the request or an existing selected
handler retains its contract and exact plans up to one structural insertion. -/
namespace Ash.OneShot.SourceScheduledHandlerSelection
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
abbrev SelectedCut := SourceScheduledNeutral.Cut
open SourceScheduledInterpretationInsertion (Insertion Split)

/-- The new handler is selected through an effect-passing active prefix.
Dormant captures are carried verbatim, never searched for an interpretation. -/
inductive Intercept (effect : Instance) (operation : Nat) (contract : ClauseContract)
    (modes : SourcePlannedCuts.Modes) (table : List (Nat × ClauseContract))
    (families : SourceDependencyAnnotations.ClauseDependencies) (required : List SourceContextualHints.Requirement) :
    {beforeScope afterScope captured tail : Scope} →
    {beforeHints : Hints beforeScope} → {afterHints : Hints afterScope} →
    {savedHints : Hints captured} → {waitingHints : Hints tail} →
    Forest beforeHints → Forest afterHints → Forest savedHints → Forest waitingHints → Prop where
  | hit (known : lookup operation table = some contract)
      (declared : SourceDependencyCapture.lookupDependencies operation families = some modes) :
      Intercept effect operation contract modes table families required waiting
        (.handler (effect := effect) (table := table) (families := families) (required := required) waiting)
        (.handler (effect := effect) (table := table) (families := families) (required := required) .nil) waiting
  | plain : Intercept effect operation contract modes table families required before after saved waiting →
      Intercept effect operation contract modes table families required
        (.plain plan before) (.plain plan after) (.plain plan saved) waiting
  | handler (different : effect ≠ other) :
      Intercept effect operation contract modes table families required before after saved waiting →
      Intercept effect operation contract modes table families required
        (.handler (effect := other) (table := otherTable) (families := otherFamilies) (required := otherRequired) before)
        (.handler (effect := other) (table := otherTable) (families := otherFamilies) (required := otherRequired) after)
        (.handler (effect := other) (table := otherTable) (families := otherFamilies) (required := otherRequired) saved) waiting
  | cell (different : effect ≠ .cell identity) :
      Intercept effect operation contract modes table families required before after saved waiting →
      Intercept effect operation contract modes table families required
        (.cell (identity := identity) before) (.cell (identity := identity) after) (.cell (identity := identity) saved) waiting
  | cleanup : Intercept effect operation contract modes table families required before after saved waiting →
      Intercept effect operation contract modes table families required
        (.cleanup (needs := needs) plan before) (.cleanup (needs := needs) plan after) (.cleanup (needs := needs) plan saved) waiting
  | running : Intercept effect operation contract modes table families required before after saved waiting →
      Intercept effect operation contract modes table families required (.running before) (.running after) (.running saved) waiting
  | live : Intercept effect operation contract modes table families required before after saved waiting →
      Intercept effect operation contract modes table families required
        (.live (owner := owner) dormant before) (.live (owner := owner) dormant after) (.live (owner := owner) dormant saved) waiting
  | spent : Intercept effect operation contract modes table families required before after saved waiting →
      Intercept effect operation contract modes table families required
        (.spent (owner := owner) before) (.spent (owner := owner) after) (.spent (owner := owner) saved) waiting

/-- Every interception carries the existing authenticated runtime cut. -/
theorem Intercept.cut (intercepted : Intercept effect operation contract modes table families required before after saved waiting) :
    SelectedCut effect operation contract modes after saved waiting := by
  induction intercepted with
  | hit known declared => exact .hit known declared
  | plain next ih => exact .plain ih
  | handler different next ih => exact .handler different ih
  | cell different next ih => exact .cell different ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

/-- Interception identifies the actual old prefix, including its retained
plans and owner inventory. The selected handler adds no code to that prefix. -/
theorem Intercept.prefix {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (intercepted : Intercept effect operation contract modes table families required before after saved waiting) :
    ∃ prefixScope, ∃ prefixHints : Hints prefixScope, ∃ front : Forest prefixHints,
      SourceHandlerRequirements.reaches effect prefixScope = true ∧
      beforeScope = prefixScope.append tail ∧
      captured = prefixScope.append (.handler effect table families .nil) ∧
      HEq beforeHints (prefixHints.append waitingHints) ∧
      HEq savedHints (prefixHints.append (.handler (effect := effect) (table := table) (families := families) required .nil)) ∧
      HEq before (front.append waiting) ∧
      HEq saved (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) .nil)) := by
  induction intercepted with
  | hit known declared => refine ⟨_, .nil, .nil, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | plain next ih =>
      rename_i dependencies plan
      obtain ⟨_, _, front, passed, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, .plain plan front, passed, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | handler different next ih =>
      rename_i priorWaiting otherTable otherFamilies otherRequired
      obtain ⟨_, _, front, passed, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, .handler (table := otherTable) (families := otherFamilies) (required := otherRequired) front, by unfold SourceHandlerRequirements.reaches; rw [if_neg different]; exact passed, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | cell different next ih =>
      obtain ⟨_, _, front, passed, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, .cell front, by unfold SourceHandlerRequirements.reaches; rw [if_neg different]; exact passed, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | cleanup next ih =>
      rename_i needs dependencies plan
      obtain ⟨_, _, front, passed, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, .cleanup (needs := needs) plan front, passed, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | running next ih =>
      obtain ⟨_, _, front, passed, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, .running front, passed, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | live next ih =>
      rename_i owner dormantScope dormantHints dormant
      obtain ⟨_, _, front, passed, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, .live (owner := owner) dormant front, passed, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | spent next ih =>
      rename_i owner
      obtain ⟨_, _, front, passed, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, .spent (owner := owner) front, passed, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- The newly selected contract and modes are those of the inserted table. -/
theorem Intercept.entry (intercepted : Intercept effect operation contract modes table families required before after saved waiting) :
    lookup operation table = some contract ∧
      SourceDependencyCapture.lookupDependencies operation families = some modes := by
  induction intercepted with
  | hit known declared => exact ⟨known, declared⟩
  | plain next ih | handler different next ih | cell different next ih | cleanup next ih
  | running next ih | live next ih | spent next ih => exact ih

/-- Exhaustive origin classification, working backwards from an actual new
cut. Missing operations cannot appear in either branch. Existing selections
preserve their exact contract and mode families; their capture or waiting side
contains the insertion. -/
theorem cut_origin {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (changed : Insertion (.handler installed table families required) before after)
    (selected : SelectedCut effect operation contract modes after saved waiting) :
    (effect = installed ∧ Intercept installed operation contract modes table families required before after saved waiting) ∨
      ∃ oldCaptured oldTail, ∃ oldSavedHints : Hints oldCaptured, ∃ oldWaitingHints : Hints oldTail,
      ∃ oldSaved : Forest oldSavedHints, ∃ oldWaiting : Forest oldWaitingHints,
        SelectedCut effect operation contract modes before oldSaved oldWaiting ∧
        Split (.handler installed table families required) oldSaved oldWaiting saved waiting := by
  induction changed generalizing captured tail with
  | here => cases selected with
    | hit known declared => exact .inl ⟨rfl, .hit known declared⟩
    | handler different cut => exact .inr ⟨_, _, _, _, _, _, cut, .inside .here⟩
  | handler changed ih => cases selected with
    | hit known declared => exact .inr ⟨_, _, _, _, _, _, .hit known declared, .outside changed⟩
    | handler different next =>
        rcases ih next with ⟨rfl, intercepted⟩ | ⟨_, _, _, _, oldSaved, oldWaiting, oldCut, pieces⟩
        · exact .inl ⟨rfl, .handler different intercepted⟩
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .handler different oldCut, .inside (.handler inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .handler different oldCut, .outside inserted⟩
  | plain changed ih => cases selected with
    | plain next =>
        rcases ih next with ⟨rfl, intercepted⟩ | ⟨_, _, _, _, oldSaved, oldWaiting, oldCut, pieces⟩
        · exact .inl ⟨rfl, .plain intercepted⟩
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .plain oldCut, .inside (.plain inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .plain oldCut, .outside inserted⟩
  | cell changed ih => cases selected with
    | cell different next =>
        rcases ih next with ⟨rfl, intercepted⟩ | ⟨_, _, _, _, oldSaved, oldWaiting, oldCut, pieces⟩
        · exact .inl ⟨rfl, .cell different intercepted⟩
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .cell different oldCut, .inside (.cell inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .cell different oldCut, .outside inserted⟩
  | cleanup changed ih => cases selected with
    | cleanup next =>
        rcases ih next with ⟨rfl, intercepted⟩ | ⟨_, _, _, _, oldSaved, oldWaiting, oldCut, pieces⟩
        · exact .inl ⟨rfl, .cleanup intercepted⟩
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .cleanup oldCut, .inside (.cleanup inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .cleanup oldCut, .outside inserted⟩
  | running changed ih => cases selected with
    | running next =>
        rcases ih next with ⟨rfl, intercepted⟩ | ⟨_, _, _, _, oldSaved, oldWaiting, oldCut, pieces⟩
        · exact .inl ⟨rfl, .running intercepted⟩
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .running oldCut, .inside (.running inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .running oldCut, .outside inserted⟩
  | live changed ih => cases selected with
    | live next =>
        rcases ih next with ⟨rfl, intercepted⟩ | ⟨_, _, _, _, oldSaved, oldWaiting, oldCut, pieces⟩
        · exact .inl ⟨rfl, .live intercepted⟩
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .live oldCut, .inside (.live inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .live oldCut, .outside inserted⟩
  | spent changed ih => cases selected with
    | spent next =>
        rcases ih next with ⟨rfl, intercepted⟩ | ⟨_, _, _, _, oldSaved, oldWaiting, oldCut, pieces⟩
        · exact .inl ⟨rfl, .spent intercepted⟩
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .spent oldCut, .inside (.spent inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .spent oldCut, .outside inserted⟩

end Ash.OneShot.SourceScheduledHandlerSelection

#print axioms Ash.OneShot.SourceScheduledHandlerSelection.Intercept.cut
#print axioms Ash.OneShot.SourceScheduledHandlerSelection.cut_origin

#print axioms Ash.OneShot.SourceScheduledHandlerSelection.Intercept.prefix
#print axioms Ash.OneShot.SourceScheduledHandlerSelection.Intercept.entry
