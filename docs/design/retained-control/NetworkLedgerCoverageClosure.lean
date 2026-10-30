import NetworkLedgerProtocol

/-
Conditional bridge to the existing finite protocol model. This module does not
establish the premises for an Ash program. In particular a source-level Closed
flag, output bytes, or a reported peer cannot discharge them.
-/
namespace Ash.NetworkLedger.CoverageClosure

open Ash.NetworkLedger
open Ash.NetworkLedger.Coupling

variable {Runtime : Type}

/-- Each named condition must be established by its owning N4 boundary. -/
structure Premises where
  localCompletion : Prop
  honestCodec : Prop
  authenticatedPeer : Prop
  faithfulTransport : Prop
  emissionDiscipline : Prop
  atMostOnceDispatch : Prop
  closedAdmission : Prop
  noUnaccountedProducers : Prop

def Premises.Hold (p : Premises) : Prop :=
  p.localCompletion ∧ p.honestCodec ∧ p.authenticatedPeer ∧ p.faithfulTransport ∧
  p.emissionDiscipline ∧ p.atMostOnceDispatch ∧ p.closedAdmission ∧ p.noUnaccountedProducers

/--
The reviewed correspondence maps every real normal control step to a finite
protocol trace, and each active real producer/control/message to a represented
token. These are substantive obligations, not consequences of coordinates.
`currentRoot` relates the actual current root observation to the modeled probe.
-/
structure Correspondence (p : Premises) (completed : Id → Prop)
    (realStep : Runtime → Runtime → Prop) (active : Runtime → Prop)
    (project : Runtime → ProtocolState) (currentRoot : Runtime → Prop) : Prop where
  step : p.Hold → ∀ {a b}, realStep a b → ProtocolTrace completed (project a) (project b)
  coversActive : p.Hold → ∀ r, active r → ∃ id, id ∈ (project r).tokens
  rootProbe : p.Hold → ∀ r, currentRoot r → probeRoot (project r).system.root.ledger = true

inductive RealTrace (realStep : Runtime → Runtime → Prop) : Runtime → Runtime → Prop where
  | refl (r : Runtime) : RealTrace realStep r r
  | next {a b c : Runtime} : RealTrace realStep a b → realStep b c → RealTrace realStep a c

theorem protocol_trace_trans (completed : Id → Prop) {a b c : ProtocolState}
    (first : ProtocolTrace completed a b) (second : ProtocolTrace completed b c) :
    ProtocolTrace completed a c := by
  induction second with
  | refl => exact first
  | next history step ih => exact .next ih step

theorem mapped_trace (p : Premises) (completed : Id → Prop)
    (realStep : Runtime → Runtime → Prop) (active : Runtime → Prop)
    (project : Runtime → ProtocolState) (root : Runtime → Prop)
    (corr : Correspondence p completed realStep active project root) (holds : p.Hold)
    {a b : Runtime} (trace : RealTrace realStep a b) :
    ProtocolTrace completed (project a) (project b) := by
  induction trace with
  | refl => exact .refl _
  | next history step ih =>
    exact protocol_trace_trans completed ih (corr.step holds step)

/--
Under the supplied correspondence, a current closed/empty root implies no
active application work, and this remains true along all admitted finite real
traces. It says nothing about endpoint or backing-resource settlement.
-/
theorem stable_app_quiet (p : Premises) (completed : Id → Prop)
    (realStep : Runtime → Runtime → Prop) (active : Runtime → Prop)
    (project : Runtime → ProtocolState) (root : Runtime → Prop)
    (corr : Correspondence p completed realStep active project root) (holds : p.Hold)
    (owner : Nat) (others : List Nat) (distinct : (owner :: others).Nodup)
    (a : Runtime) (prior : ProtocolTrace completed (initialProtocol owner others) (project a))
    (rootCurrent : root a) {b : Runtime} (suffix : RealTrace realStep a b) : ¬ active b := by
  have quiet := corr.rootProbe holds a rootCurrent
  have mapped := mapped_trace p completed realStep active project root corr holds suffix
  have same := initialized_protocol_quiet_trace_stable owner others distinct completed prior quiet mapped
  have empty := initialized_protocol_quiet_tokens_empty owner others distinct completed prior quiet
  intro running
  obtain ⟨id, member⟩ := corr.coversActive holds b running
  rw [same, empty] at member
  simp at member

end Ash.NetworkLedger.CoverageClosure
