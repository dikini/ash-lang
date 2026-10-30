import NetworkLedgerTransitions
import NetworkLedgerChecker

/-
A bounded modeled acknowledgement checker. Peer authentication and the source
of completion are separate protocol premises, not derived from data removal.
-/
namespace Ash.NetworkLedger.AcknowledgementCheck

open Ash.NetworkLedger
open Ash.NetworkLedger.Checker

inductive Shape where
  | canonical | ignorePeer | wrongPhase
  deriving DecidableEq, Repr
structure Body where
  shape : Shape
  recordLookup : LookupBody
  childLookup : LookupBody
  update : UpdateBody
  removalPlan : Plan
  removal : Definition
  deriving Repr

def check (body : Body) : Bool :=
  checkLookup body.recordLookup && checkLookup body.childLookup && checkUpdate body.update &&
    Checker.check body.removalPlan body.removal && decide (body.shape = .canonical)

def eval (body : Body) (fuel : Nat) (l : Ledger) (parent child : Id) (peer : Nat) : Option Ledger := do
  let found ← evalLookup Record.id body.recordLookup parent fuel l.records
  match found with
  | none => some l
  | some record =>
    let childEntry ← evalLookup Child.id body.childLookup child fuel record.children
    match childEntry with
    | none => some l
    | some entry =>
      if entry.destination = peer ∨ body.shape = .ignorePeer then
        let removed ← Checker.eval Child.id body.removal.body child fuel record.children
        let phase := if body.shape = .wrongPhase then Phase.open else record.phase
        let updated := { record with children := removed.1, phase := phase }
        let records ← evalUpdate Record.id body.update parent updated fuel l.records
        some { l with records := records }
      else some l

theorem check_parts (body : Body) (accepted : check body = true) :
    checkLookup body.recordLookup = true ∧ checkLookup body.childLookup = true ∧
      checkUpdate body.update = true ∧ Checker.check body.removalPlan body.removal = true ∧
      body.shape = .canonical := by
  simpa [check, and_assoc] using accepted

theorem acknowledgement_checker_sound (body : Body) (fuel : Nat) (l : Ledger) (p c : Id)
    (peer : Nat) (out : Ledger) (accepted : check body = true)
    (returns : eval body fuel l p c peer = some out) : out = acknowledge l p c peer := by
  have checked := check_parts body accepted
  cases found : evalLookup Record.id body.recordLookup p fuel l.records with
  | none => simp [eval, found] at returns
  | some parent =>
    have parentValue := lookup_checker_sound Record.id body.recordLookup p fuel l.records parent
      checked.1 found
    cases parent with
    | none =>
      simp [eval, found] at returns
      simpa [acknowledge, ← parentValue] using returns.symm
    | some record =>
      cases childFound : evalLookup Child.id body.childLookup c fuel record.children with
      | none => simp [eval, found, childFound] at returns
      | some childEntry =>
        have childValue := lookup_checker_sound Child.id body.childLookup c fuel record.children childEntry
          checked.2.1 childFound
        cases childEntry with
        | none =>
          simp [eval, found, childFound] at returns
          simpa [acknowledge, ← parentValue, ← childValue] using returns.symm
        | some entry =>
          by_cases peerMatch : entry.destination = peer
          · cases removed : Checker.eval Child.id body.removal.body c fuel record.children with
            | none => simp [eval, found, childFound, peerMatch, removed] at returns
            | some result =>
              have removeValue := remove_checker_returns Child.id body.removalPlan body.removal c fuel
                record.children result checked.2.2.2.1 removed
              let updated := { record with children := result.1 }
              cases computed : evalUpdate Record.id body.update p updated fuel l.records with
              | none => simp [eval, found, childFound, peerMatch, removed, checked.2.2.2.2,
                  updated, computed] at returns
              | some records =>
                have updateValue := update_checker_sound Record.id body.update p updated fuel
                  l.records records checked.2.2.1 computed
                simp [eval, found, childFound, peerMatch, removed, checked.2.2.2.2,
                  updated, computed] at returns
                simpa [acknowledge, ← parentValue, ← childValue, peerMatch, updated,
                  ← removeValue, ← updateValue] using returns.symm
          · simp [eval, found, childFound, peerMatch, checked.2.2.2.2] at returns
            simpa [acknowledge, ← parentValue, ← childValue, peerMatch] using returns.symm

theorem checked_acknowledgement_preserves (body : Body) (fuel : Nat) (l : Ledger) (p c : Id)
    (peer : Nat) (out : Ledger) (accepted : check body = true)
    (returns : eval body fuel l p c peer = some out) (invariant : LocalInvariant l) : LocalInvariant out := by
  rw [acknowledgement_checker_sound body fuel l p c peer out accepted returns]
  exact acknowledgement_preserves_invariant l p c peer invariant

theorem linked_acknowledgement_sound (plan : Plan) (definitions : List (LinkedDefinition Body))
    (definition : LinkedDefinition Body) (fuel : Nat) (l : Ledger) (p c : Id) (peer : Nat) (out : Ledger)
    (accepted : checkLinkedSchema plan definitions check = true)
    (resolved : resolveLinked plan definitions = some definition)
    (returns : eval definition.body fuel l p c peer = some out) : out = acknowledge l p c peer := by
  have checked := (linked_schema_binding plan definitions check definition accepted resolved).2.2.2.2
  exact acknowledgement_checker_sound definition.body fuel l p c peer out checked returns

end Ash.NetworkLedger.AcknowledgementCheck
