import RecursiveBounds
import RecursiveOutwardCore

/-! Structural clause checks with explicit contextual invocation assumptions.
These are open derivations for the existing recursive Requirements, not new
computation syntax. Each assumption retains the exact mode, demand, receiving
interpretations, owner phases and row. Closing a derivation substitutes actual
authenticated invocation checks; no cached row is reinterpreted in its place. -/
namespace Ash.OneShot.ContextualClauseChecks
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Store Key Checked)
open OwnerPhaseTransitions (Phases spendAll)

structure Invocation where
  key : Key
  demand : List Nat
  receiving : OwnerPhases.Context
  before : Phases
  row : Footprint

def Invocation.Check (store : Store) (call : Invocation) : Prop :=
  Checked store call.receiving call.before (.invoke call.key call.demand []) call.row

/-- The only assumptions are explicitly listed continuation invocations.
Literal effects and their ordered interpretations are checked in the tree. -/
inductive Derivation : OwnerPhases.Context → Phases → {owners : List Nat} →
    Requirements owners → Footprint → List Invocation → Prop where
  | request (exported : OwnerSource.exportAt (nearer ++ receiving) before raw = some row) :
      Derivation receiving before (.request nearer raw) row []
  | retire (ready : before owner = .available) : Derivation receiving before (.retire owner) [] []
  | spent (consumed : before owner = .consumed) : Derivation receiving before (.spent owner) [] []
  | invoke : Derivation receiving before (.invoke key demand nearer) row
      [⟨key, demand, nearer ++ receiving, before, row⟩]
  | sequence {first : Requirements a} {second : Requirements b}
      (left : Derivation receiving before first firstRow firstCalls)
      (right : Derivation receiving (spendAll before a) second secondRow secondCalls) :
      Derivation receiving before (.sequence first second) (firstRow ++ secondRow) (firstCalls ++ secondCalls)
  | emitAfter {body : Requirements owners}
      (source : Derivation receiving before body bodyRow calls)
      (exported : OwnerSource.exportAt (nearer ++ receiving) (spendAll before owners) raw = some requestRow) :
      Derivation receiving before (.emitAfter body nearer raw) (bodyRow ++ requestRow) calls
  | choice (left : Derivation receiving before first firstRow firstCalls)
      (right : Derivation receiving before second secondRow secondCalls) :
      Derivation receiving before (.choice first second same) (firstRow ++ secondRow) (firstCalls ++ secondCalls)

/-- Substitute actual invocation derivations at precisely their recorded
contexts and phases. The existing structural checker supplies every other case. -/
theorem close
    (source : Derivation receiving before requirements row calls)
    (supplied : ∀ call ∈ calls, call.Check store) :
    Checked store receiving before requirements row := by
  induction source with
  | request exported => exact .request exported
  | retire ready => exact .retire ready
  | spent consumed => exact .spent consumed
  | invoke =>
      rename_i current initial key demand nearer result
      have actual : Checked store (nearer ++ current) initial (.invoke key demand []) result :=
        supplied _ List.mem_cons_self
      simpa only [Requirements.prepend, List.nil_append] using
        (RecursiveRequirements.checked_prepend_iff.mpr actual :
          Checked store current initial ((Requirements.invoke key demand []).prepend nearer) result)
  | sequence first second ihFirst ihSecond =>
      exact .sequence (ihFirst (fun call member => supplied call (List.mem_append_left _ member)))
        (ihSecond (fun call member => supplied call (List.mem_append_right _ member)))
  | emitAfter source exported ih => exact .emitAfter (ih supplied) exported
  | choice first second ihFirst ihSecond =>
      exact .choice (ihFirst (fun call member => supplied call (List.mem_append_left _ member)))
        (ihSecond (fun call member => supplied call (List.mem_append_right _ member)))

/-- Every existing finite check yields an open derivation whose explicitly
listed assumptions are authenticated by that very same check. -/
theorem open_checked
    (source : Checked store receiving before requirements row) :
    ∃ calls, Derivation receiving before requirements row calls ∧ ∀ call ∈ calls, call.Check store := by
  induction source with
  | request exported => exact ⟨[], .request exported, by simp⟩
  | retire ready => exact ⟨[], .retire ready, by simp⟩
  | spent consumed => exact ⟨[], .spent consumed, by simp⟩
  | invoke known ready selection body ih =>
      refine ⟨[_], .invoke, ?_⟩
      intro call member
      cases List.mem_singleton.mp member
      apply RecursiveRequirements.checked_prepend_iff.mp
      exact Checked.invoke known ready selection body
  | sequence first second ihFirst ihSecond =>
      obtain ⟨firstCalls, left, firstChecked⟩ := ihFirst
      obtain ⟨secondCalls, right, secondChecked⟩ := ihSecond
      refine ⟨_, .sequence left right, ?_⟩
      intro call member
      exact (List.mem_append.mp member).elim (firstChecked call) (secondChecked call)
  | emitAfter source exported ih =>
      obtain ⟨calls, opened, supplied⟩ := ih
      exact ⟨calls, .emitAfter opened exported, supplied⟩
  | choice first second ihFirst ihSecond =>
      obtain ⟨firstCalls, left, firstChecked⟩ := ihFirst
      obtain ⟨secondCalls, right, secondChecked⟩ := ihSecond
      refine ⟨_, .choice left right, ?_⟩
      intro call member
      exact (List.mem_append.mp member).elim (firstChecked call) (secondChecked call)

theorem exact_check_iff : Checked store receiving before requirements row ↔
    ∃ calls, Derivation receiving before requirements row calls ∧ ∀ call ∈ calls, call.Check store :=
  ⟨open_checked, fun ⟨_, source, supplied⟩ => close source supplied⟩

/-- Upper requirement trees and stores are specialized by the established
recursive bounds theorem after the explicit invocation obligations are closed. -/
theorem specialize_upper
    (source : Derivation receiving before upperRequirements upperRow calls)
    (supplied : ∀ call ∈ calls, call.Check upperStore)
    (stores : RecursiveBounds.StoreBounds actualStore upperStore)
    (bounded : RecursiveBounds.Bounds actualRequirements upperRequirements) :
    ∃ actualRow, Checked actualStore receiving before actualRequirements actualRow ∧
      EffectBounds.Covers upperRow actualRow :=
  RecursiveBounds.checked_below (close source supplied) stores bounded

/-- Sources without owner actions reuse the established outward factorization;
no continuation assumption is introduced by literal row interpretation. -/
theorem outward
    (source : RecursiveOutward.Outward requirements raw)
    (exported : raw.bind (residualize (OwnerPhaseTransitions.project receiving before)) = some row) :
    ∃ calls, Derivation receiving before requirements row calls ∧ ∀ call ∈ calls, call.Check store :=
  open_checked (RecursiveRequirements.evaluate_sound ((RecursiveOutward.evaluation source store receiving before).trans exported))

/-- Moving a prefix into the requirement tree preserves each invocation's
complete receiving context. This is reassociation, not handler exchange. -/
theorem relocate
    (source : Derivation inside before requirements row calls)
    (same : inside = front ++ outside) :
    Derivation outside before (requirements.prepend front) row calls := by
  induction source generalizing front outside with
  | request exported =>
      apply Derivation.request
      simpa only [List.append_assoc, ← same] using exported
  | retire ready => exact .retire ready
  | spent consumed => exact .spent consumed
  | invoke =>
      simpa only [Requirements.prepend, List.append_assoc, ← same] using
        (Derivation.invoke (receiving := outside) (nearer := _ ++ front) (before := _) (row := _))
  | sequence first second ihFirst ihSecond => exact .sequence (ihFirst same) (ihSecond same)
  | emitAfter source exported ih =>
      apply Derivation.emitAfter (ih same)
      simpa only [List.append_assoc, ← same] using exported
  | choice first second ihFirst ihSecond => exact .choice (ihFirst same) (ihSecond same)

/-- An invocation assumption never grants an owner absent from the exact
requirement demand. Branches use the existing owner-demand permutation. -/
theorem invocation_owner
    (source : Derivation receiving before (owners := owners) requirements row calls)
    (member : call ∈ calls) : call.key.owner ∈ owners := by
  induction source with
  | request | retire | spent => cases member
  | invoke => cases List.mem_singleton.mp member; exact List.mem_cons_self
  | sequence first second ihFirst ihSecond =>
      rcases List.mem_append.mp member with first | second
      · exact List.mem_append_left _ (ihFirst first)
      · exact List.mem_append_right _ (ihSecond second)
  | emitAfter source exported ih => exact ih member
  | @choice receiving before firstOwners first firstRow firstCalls secondOwners second secondRow secondCalls same left right ihLeft ihRight =>
      rcases List.mem_append.mp member with first | second
      · exact ihLeft first
      · exact same.mem_iff.mpr (ihRight second)

theorem no_owner_no_assumptions
    (source : Derivation receiving before (owners := []) requirements row calls) : calls = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro call member
  exact List.not_mem_nil (invocation_owner source member)

/-- Owner-free outward typing closes without any invocation assumption. -/
theorem outward_closed
    (source : RecursiveOutward.Outward requirements raw)
    (exported : raw.bind (residualize (OwnerPhaseTransitions.project receiving before)) = some row) :
    Derivation receiving before requirements row [] := by
  have empty := RecursiveOutward.no_owners source
  subst_vars
  obtain ⟨calls, opened, supplied⟩ := outward (store := []) source exported
  exact no_owner_no_assumptions opened ▸ opened


/-- One sequencing form composes owner-free work on either side of an
invocation. The suffix sees the phase map after the full invocation demand. -/
theorem around_invocation {first last : Requirements []}
    (initial : Derivation receiving before first initialRow [])
    (final : Derivation receiving (spendAll before (key.owner :: demand)) last finalRow []) :
    Derivation receiving before (.sequence first (.sequence (.invoke key demand []) last))
      (initialRow ++ (invocationRow ++ finalRow))
      [⟨key, demand, receiving, before, invocationRow⟩] := by
  exact .sequence initial (.sequence .invoke final)

theorem around_invocation_checked {first last : Requirements []}
    (initial : Derivation receiving before first initialRow [])
    (invocation : Checked store receiving before (.invoke key demand []) invocationRow)
    (final : Derivation receiving (spendAll before (key.owner :: demand)) last finalRow []) :
    Checked store receiving before (.sequence first (.sequence (.invoke key demand []) last))
      (initialRow ++ (invocationRow ++ finalRow)) := by
  apply close (around_invocation initial final)
  intro call member
  cases List.mem_singleton.mp member
  exact invocation

/-- Row containment records effects before and after the invocation while
leaving the actual sequential evaluation order unchanged. -/
theorem around_invocation_bound
    (initial : EffectBounds.Covers advertised initialRow)
    (final : EffectBounds.Covers advertised finalRow) :
    EffectBounds.Covers (advertised ++ invocationRow) (initialRow ++ (invocationRow ++ finalRow)) := by
  intro request member
  rcases List.mem_append.mp member with first | later
  · exact List.mem_append_left _ (initial first)
  · rcases List.mem_append.mp later with invoked | last
    · exact List.mem_append_right _ invoked
    · exact List.mem_append_left _ (final last)

/-- Existing outward proofs admit arbitrary owner-free source work here,
including local handlers and resources, rather than only literal expressions. -/
theorem outward_around_invocation {first last : Requirements []}
    (initial : RecursiveOutward.Outward first initialRaw)
    (initialExport : initialRaw.bind (residualize (OwnerPhaseTransitions.project receiving before)) = some initialRow)
    (invocation : Checked store receiving before (.invoke key demand []) invocationRow)
    (final : RecursiveOutward.Outward last finalRaw)
    (finalExport : finalRaw.bind
      (residualize (OwnerPhaseTransitions.project receiving (spendAll before (key.owner :: demand)))) = some finalRow)
    (initialBound : EffectBounds.Covers advertised initialRow)
    (finalBound : EffectBounds.Covers advertised finalRow) :
    Checked store receiving before (.sequence first (.sequence (.invoke key demand []) last))
      (initialRow ++ (invocationRow ++ finalRow)) ∧
    EffectBounds.Covers (advertised ++ invocationRow) (initialRow ++ (invocationRow ++ finalRow)) :=
  ⟨around_invocation_checked (outward_closed initial initialExport) invocation (outward_closed final finalExport),
    around_invocation_bound initialBound finalBound⟩


end Ash.OneShot.ContextualClauseChecks

#print axioms Ash.OneShot.ContextualClauseChecks.close
#print axioms Ash.OneShot.ContextualClauseChecks.open_checked
#print axioms Ash.OneShot.ContextualClauseChecks.exact_check_iff
#print axioms Ash.OneShot.ContextualClauseChecks.specialize_upper
#print axioms Ash.OneShot.ContextualClauseChecks.outward
#print axioms Ash.OneShot.ContextualClauseChecks.relocate
#print axioms Ash.OneShot.ContextualClauseChecks.invocation_owner
#print axioms Ash.OneShot.ContextualClauseChecks.no_owner_no_assumptions
#print axioms Ash.OneShot.ContextualClauseChecks.outward_closed
#print axioms Ash.OneShot.ContextualClauseChecks.around_invocation
#print axioms Ash.OneShot.ContextualClauseChecks.around_invocation_checked
#print axioms Ash.OneShot.ContextualClauseChecks.around_invocation_bound
#print axioms Ash.OneShot.ContextualClauseChecks.outward_around_invocation
