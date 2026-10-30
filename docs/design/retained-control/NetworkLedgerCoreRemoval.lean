import NetworkLedgerChecker
import NetworkLedgerAllocation

/-
A first operational correspondence for the restricted RemoveById body. The
construct relation records successful selected-default queries and allocation
steps; a refusal has no normal construction result. The return relation tracks
actual whole entries and status values, and recursive evaluation uses the
actual constructor tail. This is not yet a proof that Rust reconstructed these
premises from every linked Effect Core node or that a caller cannot intercept
the default provider. Those are required before a product fact may be issued.
-/
namespace Ash.NetworkLedger.CoreRemoval

open Ash.NetworkLedger
open Ash.NetworkLedger.Checker
open Ash.NetworkLedger.Allocation

/-- A source allocator label represented in the existing natural-number model. -/
def sourceId : Id → (Bool × Int × Int)
  | .root => (true, 0, 0)
  | .work allocator serial => (false, Int.ofNat allocator, serial)

theorem sourceId_injective : Function.Injective sourceId := by
  intro x y equal
  cases x <;> cases y <;> simp_all [sourceId] <;> omega

/-- The nominal-case comparator used by the ordinary linked helper. -/
def compareId : Id → Id → Bool
  | .root, .root => true
  | .work a s, .work b t => decide (a = b) && decide (s = t)
  | _, _ => false

theorem compareId_correct (a b : Id) : compareId a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [compareId]

/-- One actual context query: it preserves state and returns the selected owner. -/
inductive Query : Selection → State → Selection → State → Prop where
  | host (state : State) : Query .hostDefault state .hostDefault state

/-- The emitted query, owner-targeted allocation, and construction on success. -/
inductive Construct {Value : Type} (value : Value) (fields : Nat) :
    State → Value → State → Prop where
  | host (before after : State) (selected : Selection) (queried : State) (location : Nat)
      (query : Query .hostDefault before selected queried)
      (success : execute selected queried true = .returned location after) :
      Construct value fields before value after

/-- Every successful construction preserves the protocol state. -/
theorem construct_preserves {Value : Type} {value : Value} {fields : Nat}
    {before after : State} {actual : Value} (construction : Construct value fields before actual after) :
    actual = value ∧ after.protocolVersion = before.protocolVersion := by
  cases construction with
  | host after selected queried location query success =>
    cases query
    have result := accepted_success .hostDefault before true location after rfl success
    exact ⟨rfl, result.2.2.1⟩

variable {Entry : Type} (key : Entry → Id)

/--
Normal returns of the restricted linked removal body. Each construction
premise stands for the corresponding emitted default query/allocate/construct
sequence, including the recursive call's argument and the constructor closure.
The relation records no normal return when one of those operations refuses.
-/
inductive Returns (q : Id) : Nat → List Entry → State → (List Entry × Status) → State → Prop where
  | empty (fuel : Nat) (s s₁ s₂ s₃ : State)
      (emptyValue : Construct ([] : List Entry) 1 s [] s₁)
      (missingValue : Construct Status.missing 1 s₁ .missing s₂)
      (result : Construct (([] : List Entry), Status.missing) 2 s₂ ([], .missing) s₃) :
      Returns q (fuel + 1) [] s ([], .missing) s₃
  | hit (fuel : Nat) (head : Entry) (tail : List Entry) (s s₁ s₂ s₃ s₄ : State)
      (arguments : Construct (key head, q) 2 s (key head, q) s₁)
      (comparisonScrutinee : Construct (key head, q) 2 s₁ (key head, q) s₂)
      (comparison : compareId (key head) q = true)
      (foundValue : Construct Status.found 1 s₂ .found s₃)
      (result : Construct (tail, Status.found) 2 s₃ (tail, .found) s₄) :
      Returns q (fuel + 1) (head :: tail) s (tail, .found) s₄
  | miss (fuel : Nat) (head : Entry) (tail remaining : List Entry) (status : Status)
      (s s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : State)
      (arguments : Construct (key head, q) 2 s (key head, q) s₁)
      (comparisonScrutinee : Construct (key head, q) 2 s₁ (key head, q) s₂)
      (comparison : compareId (key head) q = false)
      (recursiveArguments : Construct (q, tail) 2 s₂ (q, tail) s₃)
      (recursive : Returns q fuel tail s₃ (remaining, status) s₄)
      (closure : Construct Unit.unit 1 s₄ () s₅)
      (constructorArguments : Construct (head, remaining) 2 s₅ (head, remaining) s₆)
      (wholeEntry : Construct (head :: remaining) 2 s₆ (head :: remaining) s₇)
      (result : Construct (head :: remaining, status) 2 s₇ (head :: remaining, status) s₈) :
      Returns q (fuel + 1) (head :: tail) s (head :: remaining, status) s₈

/-- Restricted operational returns simulate the previously checked body. -/
theorem returns_simulates (q : Id) {fuel : Nat} {xs : List Entry} {start finish : State}
    {result : List Entry × Status} (returns : Returns key q fuel xs start result finish) :
    Checker.eval key Checker.acceptedBody q fuel xs = some result := by
  induction returns with
  | empty fuel s s₁ s₂ s₃ emptyValue missingValue result =>
    simp [Checker.eval, Checker.acceptedBody]
  | hit fuel head tail s s₁ s₂ s₃ s₄ arguments comparisonScrutinee comparison foundValue result =>
    have equal := (compareId_correct (key head) q).mp comparison
    simp [Checker.eval, Checker.acceptedBody, Checker.compare, equal]
  | miss fuel head tail remaining status s s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ arguments comparisonScrutinee comparison recursiveArguments recursive closure constructorArguments wholeEntry result ih =>
    have unequal : key head ≠ q := by
      intro equal
      have yes := (compareId_correct (key head) q).mpr equal
      rw [comparison] at yes
      contradiction
    simp [Checker.eval, Checker.acceptedBody, Checker.compare, unequal]
    exact ih

/-- Every such normal return has the checked whole-entry removal result. -/
theorem returns_remove (q : Id) {fuel : Nat} {xs : List Entry} {start finish : State}
    {result : List Entry × Status} (returns : Returns key q fuel xs start result finish) :
    result = remove key q xs := by
  exact Checker.eval_accepted key q fuel xs result (returns_simulates key q returns)

end Ash.NetworkLedger.CoreRemoval
