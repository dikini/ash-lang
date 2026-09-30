import SourceContextualHints
import SourceDependencyInvocations

/-! Select and recompose annotated source scopes at the existing active owner
boundary. Invocation access and one-shot permission use the earlier checker;
handler compatibility is an independent finite test on the resulting hints. -/
namespace Ash.OneShot.SourceContextualInvocationHints
open ScopedExpressions
open SourceContextualHints (Hints)
open SourceDependencyCapture (OwnerSelection)
abbrev Receiving := SourceDependencyCapture.Scope

structure Annotated where
  scope : Receiving
  hints : Hints scope

structure Selection where
  scopes : OwnerSelection
  front : Hints scopes.front
  saved : Hints scopes.captured
  tail : Hints scopes.tail

def Selection.prepend (layer : Receiving → Receiving)
    (lift : {scope : Receiving} → Hints scope → Hints (layer scope)) (selected : Selection) : Selection :=
  ⟨selected.scopes.prepend layer, lift selected.front, selected.saved, selected.tail⟩

/-- Walk only the active spine. Dormant captures become part of the caller
when skipped, and are never searched for an invocation target. -/
def findOwner (owner : Nat) : {scope : Receiving} → Hints scope → Option Selection
  | _, .nil => none
  | .plain dependencies _, .plain rest =>
      (findOwner owner rest).map (Selection.prepend (.plain dependencies) .plain)
  | .handler effect table families _, .handler required rest =>
      (findOwner owner rest).map (Selection.prepend (.handler effect table families) (.handler required))
  | .cell identity _, .cell rest =>
      (findOwner owner rest).map (Selection.prepend (.cell identity) .cell)
  | .cleanup needs callback _, .cleanup rest =>
      (findOwner owner rest).map (Selection.prepend (.cleanup needs callback) .cleanup)
  | _, .running rest => (findOwner owner rest).map (Selection.prepend .running .running)
  | .live other _ _, .live saved rest =>
      if owner = other then some ⟨⟨.nil, _, _⟩, .nil, saved, rest⟩
      else (findOwner owner rest).map (Selection.prepend (.live other _) (.live saved))
  | .spent other _, .spent rest =>
      (findOwner owner rest).map (Selection.prepend (.spent other) .spent)

theorem find_owner_erases (hints : Hints scope) :
    (findOwner owner hints).map Selection.scopes = SourceDependencyCapture.findOwner owner scope := by
  induction hints with
  | nil => rfl
  | live saved rest ihSaved ihRest =>
      simp only [findOwner, SourceDependencyCapture.findOwner]
      split
      · rfl
      · rw [← ihRest]; cases findOwner owner rest <;> rfl
  | plain rest ih | handler required rest ih | cell rest ih | cleanup rest ih
  | running rest ih | spent rest ih =>
      simp only [findOwner, SourceDependencyCapture.findOwner]
      rw [← ih]
      cases findOwner owner rest <;> rfl

theorem selected_cut {hints : Hints scope} (found : findOwner owner hints = some selected) :
    SourceDependencyCapture.OwnerCut owner scope selected.scopes := by
  apply SourceDependencyCapture.find_owner_sound
  rw [← find_owner_erases hints, found]
  rfl

def forClosing : {scope : Receiving} → Hints scope → Hints scope.forClosing
  | _, .nil => .nil
  | .plain _ restScope, .plain rest => @forClosing restScope rest
  | .handler _ _ _ restScope, .handler _ rest => @forClosing restScope rest
  | .spent _ restScope, .spent rest => @forClosing restScope rest
  | _, .cell rest => .cell (forClosing rest)
  | _, .cleanup rest => .cleanup (forClosing rest)
  | _, .running rest => .running (forClosing rest)
  | _, .live saved rest => (forClosing saved).append (.running (forClosing rest))

def Selection.resumed (owner : Nat) (selected : Selection) : Annotated :=
  ⟨selected.scopes.resumed owner,
    selected.saved.append (selected.front.append (.spent (owner := owner) selected.tail))⟩

def Selection.disposed (owner : Nat) (selected : Selection) : Annotated :=
  ⟨selected.scopes.disposed owner,
    (forClosing selected.saved).append (.running (selected.front.append (.spent (owner := owner) selected.tail)))⟩

def checkResume (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    (owner : Nat) (hints : Hints scope) : Option Annotated :=
  match findOwner owner hints with
  | none => none
  | some selected =>
      if (SourceDependencyCapture.checkResume actions phases owner scope).isSome &&
          (selected.resumed owner).hints.check .nil then some (selected.resumed owner) else none

def checkDispose (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (owner : Nat) (hints : Hints scope) : Option Annotated :=
  match findOwner owner hints with
  | none => none
  | some selected =>
      if (SourceDependencyCapture.checkDispose outward actions phases owner scope).isSome &&
          (selected.disposed owner).hints.check .nil then some (selected.disposed owner) else none

end Ash.OneShot.SourceContextualInvocationHints

#print axioms Ash.OneShot.SourceContextualInvocationHints.find_owner_erases
#print axioms Ash.OneShot.SourceContextualInvocationHints.selected_cut
