import SourceScheduledNeutralChecks
import SourceHandlerInvocations

/-! Shared transport of actual stored plans through interpretation insertion.
The owner-cut proof is generalized from SourceScheduledProviders; saved plans
remain identical while one caller or waiting piece gains the new frame. -/
namespace Ash.OneShot.SourceScheduledInterpretationInsertion
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyCapture (Scope)
open SourceScheduledNeutral (OwnerCut)
abbrev Interpretation := SourceInterpretationInsertion.Frame

def applyForest (frame : Interpretation) : {scope : Scope} → {hints : Hints scope} →
    Forest hints → Forest (frame.apply hints) :=
  match frame with
  | .cell _ => .cell
  | .handler _ _ _ _ => .handler

inductive Insertion (frame : Interpretation) : {first second : Scope} → {beforeHints : Hints first} → {afterHints : Hints second} →
    Forest beforeHints → Forest afterHints → Prop where
  | here : Insertion frame before (applyForest frame before)
  | plain : Insertion frame before after → Insertion frame (.plain plan before) (.plain plan after)
  | handler : Insertion frame before after →
      Insertion frame (.handler (effect := effect) (table := table) (families := families) (required := required) before)
        (.handler (effect := effect) (table := table) (families := families) (required := required) after)
  | cell : Insertion frame before after →
      Insertion frame (.cell (identity := other) before) (.cell (identity := other) after)
  | cleanup : Insertion frame before after →
      Insertion frame (.cleanup (needs := needs) plan before) (.cleanup (needs := needs) plan after)
  | running : Insertion frame before after → Insertion frame (.running before) (.running after)
  | live : Insertion frame before after → Insertion frame (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Insertion frame before after → Insertion frame (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Insertion.erase {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints} (changed : Insertion frame before after) :
    SourceInterpretationInsertion.Insertion frame beforeHints afterHints := by
  induction changed with
  | here => cases frame <;> exact .here
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem Insertion.prefix (front : Forest hints) (changed : Insertion frame first second) :
    Insertion frame (front.append first) (front.append second) := by
  induction front with
  | nil => exact changed
  | plain plan rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup plan rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihRest
  | spent rest ih => exact .spent ih

theorem Insertion.suffix (changed : Insertion frame first second) (tail : Forest hints) :
    Insertion frame (first.append tail) (second.append tail) := by
  induction changed with
  | here => cases frame <;> exact .here
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

inductive Split (frame : Interpretation) : {first outside second nextOutside : Scope} →
    {firstHints : Hints first} → {outsideHints : Hints outside} →
    {secondHints : Hints second} → {nextOutsideHints : Hints nextOutside} →
    Forest firstHints → Forest outsideHints → Forest secondHints → Forest nextOutsideHints → Prop where
  | inside (changed : Insertion frame before after) : Split frame before tail after tail
  | outside (changed : Insertion frame before after) : Split frame saved before saved after

/-- Invocation preserves the new interpretation through the spent-owner boundary. -/
theorem Split.spent_append (changed : Split frame caller waiting nextCaller nextWaiting) :
    Insertion frame (caller.append (.spent (owner := owner) waiting))
      (nextCaller.append (.spent (owner := owner) nextWaiting)) := by
  cases changed with
  | inside inserted => exact inserted.suffix _
  | outside inserted => exact (Insertion.spent inserted).prefix _

/-- Recomposition keeps the saved plan verbatim and moves the insertion
through the same spent-owner and running-completion boundaries as execution. -/
theorem Split.resumed (changed : Split frame front tail nextFront nextTail) (saved : Forest savedHints) :
    Insertion frame (saved.append (front.append (.spent (owner := owner) tail)))
      (saved.append (nextFront.append (.spent (owner := owner) nextTail))) :=
  changed.spent_append.prefix saved

theorem Split.disposed (changed : Split frame front tail nextFront nextTail) (saved : Forest savedHints) :
    Insertion frame (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail))))
      (saved.forClosing.append (.running (nextFront.append (.spent (owner := owner) nextTail)))) :=
  (Insertion.running changed.spent_append).prefix saved.forClosing

/-- The plan-carrying split erases to exactly the shared source selection,
including the original saved annotations. -/
theorem Split.owner {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {nextFrontHints : Hints nextFrontScope} {nextTailHints : Hints nextTailScope}
    {front : Forest frontHints} {tail : Forest tailHints}
    {nextFront : Forest nextFrontHints} {nextTail : Forest nextTailHints}
    (changed : Split frame front tail nextFront nextTail) (saved : Hints savedScope) :
    SourceInterpretationInsertion.OwnerInsertion frame
      ⟨⟨_, _, _⟩, frontHints, saved, tailHints⟩ ⟨⟨_, _, _⟩, nextFrontHints, saved, nextTailHints⟩ := by
  cases changed with
  | inside inserted => exact .caller inserted.erase
  | outside inserted => exact .waiting inserted.erase

/-- Owner selection keeps the identical saved plan. The inserted interpretation is in the
clause caller or in the waiting suffix, never in that dormant plan. -/
theorem Insertion.owner_cut {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (changed : Insertion frame before after) (cut : OwnerCut owner before front saved tail) :
    ∃ nextFrontScope nextTailScope, ∃ nextFrontHints : Hints nextFrontScope, ∃ nextTailHints : Hints nextTailScope,
    ∃ nextFront : Forest nextFrontHints, ∃ nextTail : Forest nextTailHints,
      OwnerCut owner after nextFront saved nextTail ∧ Split frame front tail nextFront nextTail := by
  induction changed generalizing frontScope tailScope with
  | here => cases frame with
    | cell identity => exact ⟨_, _, _, _, _, _, .cell cut, .inside .here⟩
    | handler effect table families required => exact ⟨_, _, _, _, _, _, .handler cut, .inside .here⟩
  | plain changed ih => cases cut with
    | plain next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .plain nextCut, .inside (.plain inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .plain nextCut, .outside inserted⟩
  | handler changed ih => cases cut with
    | handler next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .handler nextCut, .inside (.handler inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .handler nextCut, .outside inserted⟩
  | cell changed ih => cases cut with
    | cell next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .cell nextCut, .inside (.cell inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .cell nextCut, .outside inserted⟩
  | cleanup changed ih => cases cut with
    | cleanup next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .cleanup nextCut, .inside (.cleanup inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .cleanup nextCut, .outside inserted⟩
  | running changed ih => cases cut with
    | running next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .running nextCut, .inside (.running inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .running nextCut, .outside inserted⟩
  | live changed ih => cases cut with
    | hit => exact ⟨_, _, _, _, _, _, .hit, .outside changed⟩
    | live different next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .live different nextCut, .inside (.live inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .live different nextCut, .outside inserted⟩
  | spent changed ih => cases cut with
    | spent next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .spent nextCut, .inside (.spent inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .spent nextCut, .outside inserted⟩

end Ash.OneShot.SourceScheduledInterpretationInsertion

#print axioms Ash.OneShot.SourceScheduledInterpretationInsertion.Insertion.erase
#print axioms Ash.OneShot.SourceScheduledInterpretationInsertion.Insertion.prefix
#print axioms Ash.OneShot.SourceScheduledInterpretationInsertion.Insertion.suffix
#print axioms Ash.OneShot.SourceScheduledInterpretationInsertion.Split.spent_append
#print axioms Ash.OneShot.SourceScheduledInterpretationInsertion.Insertion.owner_cut

#print axioms Ash.OneShot.SourceScheduledInterpretationInsertion.Split.resumed
#print axioms Ash.OneShot.SourceScheduledInterpretationInsertion.Split.disposed
#print axioms Ash.OneShot.SourceScheduledInterpretationInsertion.Split.owner
