import NetworkLedgerTransitions
import NetworkLedgerChecker

/-
A modeled registration evaluator invokes the modeled lookup and update bodies.
Their independent acceptance and normal-return results are composed below.
This does not authenticate actual Core or its allocation/control context.
-/
namespace Ash.NetworkLedger.RegistrationCheck

open Ash.NetworkLedger
open Ash.NetworkLedger.Checker

inductive Shape where
  | canonical | noReservation | noEnvelope | noIncrement
  deriving DecidableEq, Repr

structure Body where
  shape : Shape
  lookup : LookupBody
  update : UpdateBody
  deriving DecidableEq, Repr

def check (body : Body) : Bool := checkLookup body.lookup && checkUpdate body.update && decide (body.shape = .canonical)

def eval (body : Body) (fuel : Nat) (l : Ledger) (parent : Id) (destination : Nat)
    (payload : List UInt8) : Option (Ledger × Registration) := do
  let found ← evalLookup Record.id body.lookup parent fuel l.records
  match found with
  | none => some (l, .rejected)
  | some record =>
    if record.phase = .closed then some (l, .rejected)
    else
      let child := Id.work l.owner l.next
      let children := if body.shape = .noReservation then record.children
        else insert ⟨child, destination⟩ record.children
      let updated := { record with children := children }
      let records ← evalUpdate Record.id body.update parent updated fuel l.records
      let next := if body.shape = .noIncrement then l.next else l.next + 1
      let outputs := if body.shape = .noEnvelope then l.outputs
        else l.outputs ++ [.work child ⟨l.owner, parent⟩ destination payload]
      some ({ l with next := next, records := records, outputs := outputs },
            .registered child)

theorem check_parts (body : Body) (accepted : check body = true) :
    checkLookup body.lookup = true ∧ checkUpdate body.update = true ∧ body.shape = .canonical := by
  simpa [check, and_assoc] using accepted

theorem registration_checker_sound (body : Body) (fuel : Nat) (l : Ledger) (parent : Id)
    (destination : Nat) (payload : List UInt8) (out : Ledger × Registration)
    (accepted : check body = true) (returns : eval body fuel l parent destination payload = some out) :
    out = register l parent destination payload := by
  have checked := check_parts body accepted
  cases observed : evalLookup Record.id body.lookup parent fuel l.records with
  | none => simp [eval, observed] at returns
  | some found =>
    have lookupValue := lookup_checker_sound Record.id body.lookup parent fuel l.records found
      checked.1 observed
    cases found with
    | none =>
      simp [eval, observed] at returns
      simpa [register, ← lookupValue] using returns.symm
    | some record =>
      by_cases closed : record.phase = .closed
      · simp [eval, observed, closed] at returns
        simpa [register, ← lookupValue, closed] using returns.symm
      · let child := Id.work l.owner l.next
        let updated := { record with children := insert ⟨child, destination⟩ record.children }
        cases computed : evalUpdate Record.id body.update parent updated fuel l.records with
        | none => simp [eval, observed, closed, child, updated, computed, checked.2.2] at returns
        | some records =>
          have updateValue := update_checker_sound Record.id body.update parent updated fuel
            l.records records checked.2.1 computed
          simp [eval, observed, closed, child, updated, computed, checked.2.2] at returns
          simpa [register, ← lookupValue, closed, child, updated, ← updateValue] using returns.symm

theorem checked_registration_preserves (body : Body) (fuel : Nat) (l : Ledger) (parent : Id)
    (destination : Nat) (payload : List UInt8) (out : Ledger × Registration)
    (accepted : check body = true) (returns : eval body fuel l parent destination payload = some out)
    (invariant : LocalInvariant l) : LocalInvariant out.1 := by
  rw [registration_checker_sound body fuel l parent destination payload out accepted returns]
  exact registration_preserves_invariant l parent destination payload invariant

theorem linked_registration_sound (plan : Plan) (definitions : List (LinkedDefinition Body))
    (definition : LinkedDefinition Body) (fuel : Nat) (l : Ledger) (parent : Id)
    (destination : Nat) (payload : List UInt8) (out : Ledger × Registration)
    (accepted : checkLinkedSchema plan definitions check = true)
    (resolved : resolveLinked plan definitions = some definition)
    (returns : eval definition.body fuel l parent destination payload = some out) :
    out = register l parent destination payload := by
  have checked := (linked_schema_binding plan definitions check definition accepted resolved).2.2.2.2
  exact registration_checker_sound definition.body fuel l parent destination payload out checked returns

end Ash.NetworkLedger.RegistrationCheck
