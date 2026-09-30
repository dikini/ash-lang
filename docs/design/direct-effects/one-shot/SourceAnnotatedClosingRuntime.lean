import SourceAnnotatedRuntime

/-! Closing plans retain executable annotated callbacks from the saved stack.
Erasure commutes with plan construction and materialization, including nested
dormant captures. No source or future-execution evidence is stored here. -/
namespace Ash.OneShot.SourceAnnotatedRuntime
open ScopedExecution (Scope)

inductive CloseEntry where
  | release (identity : Nat) (payload : Int)
  | invoke (action : Action)
  | retire (ticket : Nat)

def CloseEntry.erase : CloseEntry → ScopedExecution.CloseEntry
  | .release identity payload => .release identity payload
  | .invoke action => .invoke action.erase
  | .retire ticket => .retire ticket

def CloseEntry.frame (scope : Scope) : CloseEntry → Frame
  | .release identity payload => .cell identity payload scope .unit
  | .invoke action => .armed { action with scope := scope, answer := .unit }
  | .retire ticket => .retiring ticket

def closeControl (scope : Scope) : List CloseEntry → Stack
  | [] => .nil
  | entry :: rest => .push (entry.frame scope) (closeControl scope rest)

theorem closeControl_erase (scope : Scope) (entries : List CloseEntry) :
    (closeControl scope entries).erase = ScopedExecution.closeControl scope (entries.map CloseEntry.erase) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp_all [closeControl, Stack.erase, CloseEntry.frame, Frame.erase,
        ScopedExecution.closeControl, ScopedExecution.CloseEntry.frame, CloseEntry.erase, Action.erase]

def makePlan : Stack → Option (List CloseEntry)
  | .nil => some []
  | .push frame rest => match frame, makePlan rest with
    | .plain _, plan | .handler _, plan => plan
    | .cell identity payload _ _, some plan => some (.release identity payload :: plan)
    | .armed action, some plan => some (.invoke action :: plan)
    | _, _ => none
  | .live ticket _ _ saved _ rest => match makePlan saved, makePlan rest with
    | some inside, some outside => some (inside ++ .retire ticket :: outside)
    | _, _ => none
  | .spent _ _ _ rest => makePlan rest

theorem makePlan_erase (stack : Stack) :
    ScopedExecution.makePlan stack.erase = (makePlan stack).map (List.map CloseEntry.erase) := by
  induction stack with
  | nil => rfl
  | push frame rest ih =>
      simp only [Stack.erase, ScopedExecution.makePlan, ih]
      cases frame <;> cases next : makePlan rest <;>
        simp [makePlan, next, Frame.erase, CloseEntry.erase]
  | live ticket input answer saved scope rest ihSaved ihRest =>
      simp only [Stack.erase, ScopedExecution.makePlan, ihSaved, ihRest]
      cases inside : makePlan saved <;> cases outside : makePlan rest <;>
        simp [makePlan, inside, outside, CloseEntry.erase]
  | spent ticket answer scope rest ih => exact ih

/-- Every successful existing machine plan comes from the actual annotated
stack. Callbacks are recovered from that stack, not invented from erased code. -/
theorem makePlan_of_raw (stack : Stack)
    (built : ScopedExecution.makePlan stack.erase = some raw) :
    ∃ plan, makePlan stack = some plan ∧ plan.map CloseEntry.erase = raw := by
  rw [makePlan_erase] at built
  cases found : makePlan stack with
  | none => simp [found] at built
  | some plan => exact ⟨plan, rfl, by simpa [found] using built⟩

end Ash.OneShot.SourceAnnotatedRuntime

#print axioms Ash.OneShot.SourceAnnotatedRuntime.closeControl_erase
#print axioms Ash.OneShot.SourceAnnotatedRuntime.makePlan_erase
#print axioms Ash.OneShot.SourceAnnotatedRuntime.makePlan_of_raw
