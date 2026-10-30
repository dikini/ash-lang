import NetworkLedgerTransitions
import NetworkLedgerChecker

/-
The modeled retirement checker composes checked lookup and removal results.
The caller's actual completion and transport/codec evidence remain premises.
-/
namespace Ash.NetworkLedger.RetirementCheck

open Ash.NetworkLedger
open Ash.NetworkLedger.Checker

inductive Shape where
  | canonical | ignoreChildren | noAck
  deriving DecidableEq, Repr
structure Body where
  shape : Shape
  lookup : LookupBody
  removalPlan : Plan
  removal : Definition
  deriving Repr

def check (body : Body) : Bool :=
  checkLookup body.lookup && Checker.check body.removalPlan body.removal && decide (body.shape = .canonical)

def eval (body : Body) (fuel : Nat) (l : Ledger) (q : Id) : Option Ledger := do
  let found ← evalLookup Record.id body.lookup q fuel l.records
  match found with
  | none => some l
  | some record =>
    match record.parent with
    | none => some l
    | some parent =>
      if record.phase = .closed ∧ (record.children = [] ∨ body.shape = .ignoreChildren) ∧ q ≠ .root then
        let removed ← Checker.eval Record.id body.removal.body q fuel l.records
        let outputs := if body.shape = .noAck then l.outputs else l.outputs ++ [.ack parent q]
        some { l with records := removed.1, outputs := outputs }
      else some l

theorem check_parts (body : Body) (accepted : check body = true) :
    checkLookup body.lookup = true ∧ Checker.check body.removalPlan body.removal = true ∧
      body.shape = .canonical := by
  simpa [check, and_assoc] using accepted

theorem retirement_checker_sound (body : Body) (fuel : Nat) (l : Ledger) (q : Id) (out : Ledger)
    (accepted : check body = true) (returns : eval body fuel l q = some out) : out = retire l q := by
  have checked := check_parts body accepted
  cases observed : evalLookup Record.id body.lookup q fuel l.records with
  | none => simp [eval, observed] at returns
  | some found =>
    have lookupValue := lookup_checker_sound Record.id body.lookup q fuel l.records found
      checked.1 observed
    cases found with
    | none =>
      simp [eval, observed] at returns
      simpa [retire, ← lookupValue] using returns.symm
    | some record =>
      cases parent : record.parent with
      | none =>
        simp [eval, observed, parent] at returns
        simpa [retire, ← lookupValue, parent] using returns.symm
      | some address =>
        by_cases ready : record.phase = .closed ∧ record.children = [] ∧ q ≠ .root
        · cases computed : Checker.eval Record.id body.removal.body q fuel l.records with
          | none => simp [eval, observed, parent, ready.1, ready.2.1, ready.2.2,
              checked.2.2, computed] at returns
          | some removed =>
            have removeValue := remove_checker_returns Record.id body.removalPlan body.removal q fuel
              l.records removed checked.2.1 computed
            simp [eval, observed, parent, ready.1, ready.2.1, ready.2.2, checked.2.2, computed] at returns
            simpa [retire, ← lookupValue, parent, ready.1, ready.2.1, ready.2.2, ← removeValue] using
              returns.symm
        · simp [eval, observed, parent, checked.2.2, ready] at returns
          simpa [retire, ← lookupValue, parent, ready] using returns.symm

theorem checked_retirement_preserves (body : Body) (fuel : Nat) (l : Ledger) (q : Id) (out : Ledger)
    (accepted : check body = true) (returns : eval body fuel l q = some out)
    (invariant : LocalInvariant l) : LocalInvariant out := by
  rw [retirement_checker_sound body fuel l q out accepted returns]
  exact retirement_preserves_invariant l q invariant

theorem linked_retirement_sound (plan : Plan) (definitions : List (LinkedDefinition Body))
    (definition : LinkedDefinition Body) (fuel : Nat) (l : Ledger) (q : Id) (out : Ledger)
    (accepted : checkLinkedSchema plan definitions check = true)
    (resolved : resolveLinked plan definitions = some definition)
    (returns : eval definition.body fuel l q = some out) : out = retire l q := by
  have checked := (linked_schema_binding plan definitions check definition accepted resolved).2.2.2.2
  exact retirement_checker_sound definition.body fuel l q out checked returns

end Ash.NetworkLedger.RetirementCheck
