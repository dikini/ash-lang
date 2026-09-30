import ScopedUsage

/-! A finite syntax check constructs the existing one-shot usage derivation.
The checker follows the actual translated clause, including callable barriers
and agreement of both branch outcomes. It assumes no execution or typing. -/
namespace Ash.OneShot.CoreGraphCapabilities
open Syntax

mutual
def checkUse (policy : TicketPolicy) (scope : UseScope) (before : UseState)
    (fuel : Nat) (code : Expr) : Option {after : UseState // Uses policy scope before code after} :=
  match fuel with
  | 0 => none
  | fuel + 1 => match code with
    | .unit => some ⟨before, .unit⟩
    | .boolean _ => some ⟨before, .boolean⟩
    | .integer _ => some ⟨before, .integer⟩
    | .variable _ => some ⟨before, .variable⟩
    | .resourceRef _ => some ⟨before, .resourceRef⟩
    | .pair left right => do
        let first ← checkUse policy scope before fuel left
        let second ← checkUse policy scope first.val fuel right
        pure ⟨second.val, .pair first.property second.property⟩
    | .app left right => do
        let first ← checkUse policy scope before fuel left
        let second ← checkUse policy scope first.val fuel right
        pure ⟨second.val, .app first.property second.property⟩
    | .bind _ left right => do
        let first ← checkUse policy scope before fuel left
        let second ← checkUse policy scope first.val fuel right
        pure ⟨second.val, .bind first.property second.property⟩
    | .resource _ left right => do
        let first ← checkUse policy scope before fuel left
        let second ← checkUse policy scope first.val fuel right
        pure ⟨second.val, .resource first.property second.property⟩
    | .cleanup left right => do
        let first ← checkUse policy scope before fuel left
        let second ← checkUse policy scope first.val fuel right
        pure ⟨second.val, .cleanup first.property second.property⟩
    | .lambda _ body => do
        let checked ← checkUse policy .none .available fuel body
        if same : checked.val = .available then
          pure ⟨before, .lambda (by simpa only [same] using checked.property)⟩
        else none
    | .branch condition yes no => do
        let test ← checkUse policy scope before fuel condition
        let yesChecked ← checkUse policy scope test.val fuel yes
        let noChecked ← checkUse policy scope test.val fuel no
        if same : noChecked.val = yesChecked.val then
          pure ⟨yesChecked.val, .branch test.property yesChecked.property (same ▸ noChecked.property)⟩
        else none
    | .perform _ _ operand => do
        let checked ← checkUse policy scope before fuel operand
        pure ⟨checked.val, .perform checked.property⟩
    | .handle _ body clauses => do
        let checked ← checkUse policy scope before fuel body
        let declarations ← checkClauses policy fuel clauses
        pure ⟨checked.val, .handle checked.property declarations.down⟩
    | .resume binder operand => match scope with
      | .none => none
      | .ticket ticket rights =>
          if same : binder = ticket then do
            let checked ← checkUse policy (.ticket ticket rights) before fuel operand
            if available : checked.val = .available then
              if permission : rights.resume = true then
                pure ⟨.consumed, same.symm ▸ Uses.resume permission (available ▸ checked.property)⟩
              else none
            else none
          else none
    | .discard binder => match scope, before with
      | .ticket ticket rights, .available =>
          if same : binder = ticket then
            if permission : rights.dispose = true then
              some ⟨.consumed, same.symm ▸ Uses.discard permission⟩
            else none
          else none
      | _, _ => none

def checkClauses (policy : TicketPolicy) (fuel : Nat) (clauses : Clauses) : Option (PLift (ClausesUse policy clauses)) :=
  match fuel with
  | 0 => none
  | fuel + 1 => match clauses with
    | .nil => some ⟨.nil⟩
    | .cons _ _ binder body rest => do
        let checked ← checkUse policy (.ticket binder (policy binder)) .available fuel body
        if consumed : checked.val = .consumed then
          let declarations ← checkClauses policy fuel rest
          pure ⟨.cons (consumed ▸ checked.property) declarations.down⟩
        else none
end

def state (policy : TicketPolicy) (scope : UseScope) (before : UseState) (fuel : Nat) (code : ScopedExpressions.Code) : Option UseState :=
  (checkUse policy scope before fuel code.usageShape).map Subtype.val

theorem sound (accepted : state policy scope before fuel code = some after) :
    ScopedExpressions.Uses policy scope before code after := by
  unfold state at accepted
  cases checked : checkUse policy scope before fuel code.usageShape with
  | none => simp [checked] at accepted
  | some result =>
      simp only [checked, Option.map_some, Option.some.injEq] at accepted
      exact accepted ▸ result.property

private def allRights : TicketPolicy := fun _ => ⟨true, true⟩

/-- Both selected arms consume the same ticket; the suffix retains its syntax. -/
theorem consuming_choice :
    state allRights (.ticket 7 (allRights 7)) .available 8
      (.branch (.variable 9) (.bind 10 (.resume 7 .unit)
        (.app (.variable 3) (.pair (.variable 4) (.integer 11)))) (.discard 7)) = some .consumed := rfl

theorem duplicate_resume_rejected :
    state allRights (.ticket 7 (allRights 7)) .available 4
      (.bind 10 (.resume 7 .unit) (.resume 7 .unit)) = none := rfl

theorem callable_ticket_escape_rejected :
    state allRights (.ticket 7 (allRights 7)) .available 4 (.lambda 10 (.resume 7 .unit)) = none := rfl

end Ash.OneShot.CoreGraphCapabilities
#print axioms Ash.OneShot.CoreGraphCapabilities.sound
