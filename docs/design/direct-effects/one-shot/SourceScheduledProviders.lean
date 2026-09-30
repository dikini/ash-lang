import SourceScheduledNeutral
import SourcePlannedProviders
import SourceScheduledInterpretationInsertion

/-! Add one active builtin while retaining the actual plans. Handler and owner
cuts are the existing structural cuts; only their insertion transport is new. -/
namespace Ash.OneShot.SourceScheduledProviders
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyCapture (Scope select)
open SourceScheduledNeutral (Cut OwnerCut)

inductive Insertion (identity : Nat) : {first second : Scope} → {beforeHints : Hints first} → {afterHints : Hints second} →
    Forest beforeHints → Forest afterHints → Prop where
  | here : Insertion identity before (.cell (identity := identity) before)
  | plain : Insertion identity before after → Insertion identity (.plain plan before) (.plain plan after)
  | handler : Insertion identity before after →
      Insertion identity (.handler (effect := effect) (table := table) (families := families) (required := required) before)
        (.handler (effect := effect) (table := table) (families := families) (required := required) after)
  | cell : Insertion identity before after →
      Insertion identity (.cell (identity := other) before) (.cell (identity := other) after)
  | cleanup : Insertion identity before after →
      Insertion identity (.cleanup (needs := needs) plan before) (.cleanup (needs := needs) plan after)
  | running : Insertion identity before after → Insertion identity (.running before) (.running after)
  | live : Insertion identity before after → Insertion identity (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Insertion identity before after → Insertion identity (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Insertion.erase {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints} (changed : Insertion identity before after) :
    SourceProviderInsertion.Insertion identity beforeHints afterHints := by
  induction changed with
  | here => exact .here
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem Insertion.prefix (front : Forest hints) (changed : Insertion identity first second) :
    Insertion identity (front.append first) (front.append second) := by
  induction front with
  | nil => exact changed
  | plain plan rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup plan rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihRest
  | spent rest ih => exact .spent ih

theorem Insertion.suffix (changed : Insertion identity first second) (tail : Forest hints) :
    Insertion identity (first.append tail) (second.append tail) := by
  induction changed with
  | here => exact .here
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem Insertion.forClosing (changed : Insertion identity first second) :
    Insertion identity first.forClosing second.forClosing := by
  induction changed with
  | here => exact .here
  | plain next ih | handler next ih | spent next ih => exact ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact (Insertion.running ih).prefix _

inductive Split (identity : Nat) : {first outside second nextOutside : Scope} →
    {firstHints : Hints first} → {outsideHints : Hints outside} →
    {secondHints : Hints second} → {nextOutsideHints : Hints nextOutside} →
    Forest firstHints → Forest outsideHints → Forest secondHints → Forest nextOutsideHints → Prop where
  | inside (changed : Insertion identity before after) : Split identity before tail after tail
  | outside (changed : Insertion identity before after) : Split identity saved before saved after

/-- Closing retains the inserted provider on the same side of the schedule. -/
theorem Split.forClosing (changed : Split identity saved waiting nextSaved nextWaiting) :
    Split identity saved.forClosing (.running waiting) nextSaved.forClosing (.running nextWaiting) := by
  cases changed with
  | inside inserted => exact .inside inserted.forClosing
  | outside inserted => exact .outside (.running inserted)

/-- Invocation preserves the new provider through the spent-owner boundary. -/
theorem Split.spent_append (changed : Split identity caller waiting nextCaller nextWaiting) :
    Insertion identity (caller.append (.spent (owner := owner) waiting))
      (nextCaller.append (.spent (owner := owner) nextWaiting)) := by
  cases changed with
  | inside inserted => exact inserted.suffix _
  | outside inserted => exact (Insertion.spent inserted).prefix _

/-- Selection either changes to the builtin or retains the same handler and
its actual saved and waiting plans, with exactly one inserted provider. -/
theorem Insertion.cut {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints} (changed : Insertion identity before after)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes before saved waiting) :
    select effect operation second = some (.builtin identity) ∨
      ∃ captured tail, ∃ nextSaved : Hints captured, ∃ nextWaiting : Hints tail,
      ∃ nextSavedForest : Forest nextSaved, ∃ nextWaitingForest : Forest nextWaiting,
        SourceScheduledNeutral.Cut effect operation contract modes after nextSavedForest nextWaitingForest ∧
        Split identity saved waiting nextSavedForest nextWaitingForest := by
  induction changed generalizing captured tail with
  | here =>
      by_cases hit : effect = .cell identity
      · exact .inl (by simp only [select, if_pos hit])
      · exact .inr ⟨_, _, _, _, _, _, .cell hit cut, .inside .here⟩
  | handler changed ih => cases cut with
    | hit known declared => exact .inr ⟨_, _, _, _, _, _, .hit known declared, .outside changed⟩
    | handler different next =>
        rcases ih next with found | ⟨_, _, _, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, if_neg different, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .handler different nextCut, .inside (.handler inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .handler different nextCut, .outside inserted⟩
  | plain changed ih => cases cut with
    | plain next =>
        rcases ih next with found | ⟨_, _, _, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .plain nextCut, .inside (.plain inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .plain nextCut, .outside inserted⟩
  | cell changed ih => cases cut with
    | cell different next =>
        rcases ih next with found | ⟨_, _, _, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, if_neg different, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .cell different nextCut, .inside (.cell inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .cell different nextCut, .outside inserted⟩
  | cleanup changed ih => cases cut with
    | cleanup next =>
        rcases ih next with found | ⟨_, _, _, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .cleanup nextCut, .inside (.cleanup inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .cleanup nextCut, .outside inserted⟩
  | running changed ih => cases cut with
    | running next =>
        rcases ih next with found | ⟨_, _, _, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .running nextCut, .inside (.running inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .running nextCut, .outside inserted⟩
  | live changed ih => cases cut with
    | live next =>
        rcases ih next with found | ⟨_, _, _, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .live nextCut, .inside (.live inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .live nextCut, .outside inserted⟩
  | spent changed ih => cases cut with
    | spent next =>
        rcases ih next with found | ⟨_, _, _, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · cases pieces with
          | inside inserted => exact .inr ⟨_, _, _, _, _, _, .spent nextCut, .inside (.spent inserted)⟩
          | outside inserted => exact .inr ⟨_, _, _, _, _, _, .spent nextCut, .outside inserted⟩

theorem Insertion.shared (changed : Insertion identity before after) :
    SourceScheduledInterpretationInsertion.Insertion (.cell identity) before after := by
  induction changed with
  | here => exact .here
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem Insertion.of_shared (changed : SourceScheduledInterpretationInsertion.Insertion (.cell identity) before after) :
    Insertion identity before after := by
  induction changed with
  | here => exact .here
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem Split.of_shared (changed : SourceScheduledInterpretationInsertion.Split (.cell identity) front tail nextFront nextTail) :
    Split identity front tail nextFront nextTail := by
  cases changed with
  | inside inserted => exact .inside (Insertion.of_shared inserted)
  | outside inserted => exact .outside (Insertion.of_shared inserted)

/-- Owner selection keeps the identical saved plan. The provider is in the
clause caller or in the waiting suffix, never in that dormant plan. -/
theorem Insertion.owner_cut {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (changed : Insertion identity before after) (cut : OwnerCut owner before front saved tail) :
    ∃ nextFrontScope nextTailScope, ∃ nextFrontHints : Hints nextFrontScope, ∃ nextTailHints : Hints nextTailScope,
    ∃ nextFront : Forest nextFrontHints, ∃ nextTail : Forest nextTailHints,
      OwnerCut owner after nextFront saved nextTail ∧ Split identity front tail nextFront nextTail := by
  obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := changed.shared.owner_cut cut
  exact ⟨_, _, _, _, _, _, nextCut, Split.of_shared pieces⟩

/-- Retain the same local-provider order at the actual stored-plan layer. -/
def providerForest (provided : List Nat) (forest : Forest hints) :
    Forest (SourcePlannedProviders.providerHints provided hints) :=
  match provided with
  | [] => forest
  | identity :: rest => .cell (identity := identity) (providerForest rest forest)

end Ash.OneShot.SourceScheduledProviders

#print axioms Ash.OneShot.SourceScheduledProviders.Insertion.erase
#print axioms Ash.OneShot.SourceScheduledProviders.Insertion.prefix
#print axioms Ash.OneShot.SourceScheduledProviders.Insertion.suffix
#print axioms Ash.OneShot.SourceScheduledProviders.Insertion.forClosing
#print axioms Ash.OneShot.SourceScheduledProviders.Split.forClosing
#print axioms Ash.OneShot.SourceScheduledProviders.Split.spent_append
#print axioms Ash.OneShot.SourceScheduledProviders.Insertion.cut
#print axioms Ash.OneShot.SourceScheduledProviders.Insertion.owner_cut

#print axioms Ash.OneShot.SourceScheduledProviders.Insertion.shared
#print axioms Ash.OneShot.SourceScheduledProviders.Insertion.of_shared
#print axioms Ash.OneShot.SourceScheduledProviders.Split.of_shared
