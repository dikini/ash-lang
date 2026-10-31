import NetworkLedgerTransitions
import NetworkLedgerChecker

/-
Restricted modeled closure: compare the actual modeled returned record values,
including the checked lookup and update helper results. Actual control must
independently establish completion before this data transformation is used.
-/
namespace Ash.NetworkLedger.ClosureCheck

open Ash.NetworkLedger
open Ash.NetworkLedger.Checker

inductive Shape where
  | canonical | reopen | wrongParent
  deriving DecidableEq, Repr
structure Body where
  shape : Shape
  lookup : LookupBody
  update : UpdateBody
  deriving DecidableEq, Repr

def check (body : Body) : Bool :=
  checkLookup body.lookup && checkUpdate body.update && decide (body.shape = .canonical)

def eval (body : Body) (fuel : Nat) (l : Ledger) (q : Id) : Option Ledger := do
  let found ← evalLookup Record.id body.lookup q fuel l.records
  match found with
  | none => some l
  | some record =>
    if record.phase = .closed then some l
    else
      let newPhase := if body.shape = .reopen then Phase.open else Phase.closed
      let newParent := if body.shape = .wrongParent then none else record.parent
      let updated := { record with phase := newPhase, parent := newParent }
      let records ← evalUpdate Record.id body.update q updated fuel l.records
      some { l with records := records }

theorem check_parts (body : Body) (accepted : check body = true) :
    checkLookup body.lookup = true ∧ checkUpdate body.update = true ∧ body.shape = .canonical := by
  simpa [check, and_assoc] using accepted

theorem closure_checker_sound (body : Body) (fuel : Nat) (l : Ledger) (q : Id) (out : Ledger)
    (accepted : check body = true) (returns : eval body fuel l q = some out) : out = close l q := by
  have checked := check_parts body accepted
  cases observed : evalLookup Record.id body.lookup q fuel l.records with
  | none => simp [eval, observed] at returns
  | some found =>
    have lookupValue := lookup_checker_sound Record.id body.lookup q fuel l.records found
      checked.1 observed
    cases found with
    | none =>
      simp [eval, observed] at returns
      simpa [close, ← lookupValue] using returns.symm
    | some record =>
      by_cases closed : record.phase = .closed
      · simp [eval, observed, closed] at returns
        simpa [close, ← lookupValue, closed] using returns.symm
      · let updated := { record with phase := Phase.closed }
        cases computed : evalUpdate Record.id body.update q updated fuel l.records with
        | none => simp [eval, observed, closed, updated, computed, checked.2.2] at returns
        | some records =>
          have updateValue := update_checker_sound Record.id body.update q updated fuel
            l.records records checked.2.1 computed
          simp [eval, observed, closed, updated, computed, checked.2.2] at returns
          simpa [close, ← lookupValue, closed, updated, ← updateValue] using returns.symm

theorem checked_closure_preserves (body : Body) (fuel : Nat) (l : Ledger) (q : Id) (out : Ledger)
    (accepted : check body = true) (returns : eval body fuel l q = some out)
    (invariant : LocalInvariant l) : LocalInvariant out := by
  rw [closure_checker_sound body fuel l q out accepted returns]
  exact closure_preserves_invariant l q invariant

theorem linked_closure_sound (plan : Plan) (definitions : List (LinkedDefinition Body))
    (definition : LinkedDefinition Body) (fuel : Nat) (l : Ledger) (q : Id) (out : Ledger)
    (accepted : checkLinkedSchema plan definitions check = true)
    (resolved : resolveLinked plan definitions = some definition)
    (returns : eval definition.body fuel l q = some out) : out = close l q := by
  have checked := (linked_schema_binding plan definitions check definition accepted resolved).2.2.2.2
  exact closure_checker_sound definition.body fuel l q out checked returns

end Ash.NetworkLedger.ClosureCheck
