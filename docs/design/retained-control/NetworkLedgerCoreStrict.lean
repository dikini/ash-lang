import NetworkLedgerCoreRemoval

/-
The restricted generated tuple result evaluates its context query before its
field expressions, then obtains storage and initializes the result. This layer
records that order explicitly. It models only the recognized default provider;
actual linked nodes, caller selection and nonreentry still require an independent
reconstruction theorem before any product fact is issued.
-/
namespace Ash.NetworkLedger.CoreStrict

open Ash.NetworkLedger
open Ash.NetworkLedger.Allocation
open Ash.NetworkLedger.CoreRemoval

/-- Complete a previously queried construction after its fields have run. -/
inductive Finish : Selection → State → State → Prop where
  | host (before after : State) (location : Nat)
      (success : execute .hostDefault before true = .returned location after) :
      Finish .hostDefault before after

/-- Once the selected default is known, finishing is a projected construction. -/
theorem finish_projects {Value : Type} (value : Value) (fields : Nat)
    {before after : State} (finish : Finish .hostDefault before after) :
    Construct value fields before value after := by
  cases finish with
  | host before after location success =>
    exact Construct.host before after .hostDefault before location (Query.host before) success

variable {Entry : Type} (key : Entry → Id)

/--
Returns for the recognized body with the outer tuple's selection query ordered
before its fields. The selected host context is stable during these fields;
that property is established only by the separately checked control path.
-/
inductive StrictReturns (q : Id) : Nat → List Entry → State → (List Entry × Status) → State → Prop where
  | empty (fuel : Nat) (s queried s₁ s₂ s₃ : State) (selected : Selection)
      (outerQuery : Query .hostDefault s selected queried)
      (emptyValue : Construct ([] : List Entry) 1 queried [] s₁)
      (missingValue : Construct Status.missing 1 s₁ .missing s₂)
      (outerFinish : Finish selected s₂ s₃) :
      StrictReturns q (fuel + 1) [] s ([], .missing) s₃
  | hit (fuel : Nat) (head : Entry) (tail : List Entry)
      (s s₁ s₂ queried s₃ s₄ : State) (selected : Selection)
      (arguments : Construct (key head, q) 2 s (key head, q) s₁)
      (comparisonScrutinee : Construct (key head, q) 2 s₁ (key head, q) s₂)
      (comparison : compareId (key head) q = true)
      (outerQuery : Query .hostDefault s₂ selected queried)
      (foundValue : Construct Status.found 1 queried .found s₃)
      (outerFinish : Finish selected s₃ s₄) :
      StrictReturns q (fuel + 1) (head :: tail) s (tail, .found) s₄
  | miss (fuel : Nat) (head : Entry) (tail remaining : List Entry) (status : Status)
      (s s₁ s₂ s₃ s₄ queried s₅ s₆ s₇ s₈ : State) (selected : Selection)
      (arguments : Construct (key head, q) 2 s (key head, q) s₁)
      (comparisonScrutinee : Construct (key head, q) 2 s₁ (key head, q) s₂)
      (comparison : compareId (key head) q = false)
      (recursiveArguments : Construct (q, tail) 2 s₂ (q, tail) s₃)
      (recursive : StrictReturns q fuel tail s₃ (remaining, status) s₄)
      (outerQuery : Query .hostDefault s₄ selected queried)
      (closure : Construct Unit.unit 1 queried () s₅)
      (constructorArguments : Construct (head, remaining) 2 s₅ (head, remaining) s₆)
      (wholeEntry : Construct (head :: remaining) 2 s₆ (head :: remaining) s₇)
      (outerFinish : Finish selected s₇ s₈) :
      StrictReturns q (fuel + 1) (head :: tail) s (head :: remaining, status) s₈

/-- Strict result construction projects to the prior allocation relation. -/
theorem strict_projects (q : Id) {fuel : Nat} {xs : List Entry} {start finish : State}
    {result : List Entry × Status} (execution : StrictReturns key q fuel xs start result finish) :
    Returns key q fuel xs start result finish := by
  induction execution with
  | empty fuel s queried s₁ s₂ s₃ selected outerQuery emptyValue missingValue outerFinish =>
    cases outerQuery
    exact Returns.empty fuel s s₁ s₂ s₃ emptyValue missingValue
      (finish_projects ([], Status.missing) 2 outerFinish)
  | hit fuel head tail s s₁ s₂ queried s₃ s₄ selected arguments comparisonScrutinee comparison outerQuery foundValue outerFinish =>
    cases outerQuery
    exact Returns.hit fuel head tail s s₁ s₂ s₃ s₄ arguments comparisonScrutinee comparison foundValue
      (finish_projects (tail, Status.found) 2 outerFinish)
  | miss fuel head tail remaining status s s₁ s₂ s₃ s₄ queried s₅ s₆ s₇ s₈ selected arguments comparisonScrutinee comparison recursiveArguments recursive outerQuery closure constructorArguments wholeEntry outerFinish ih =>
    cases outerQuery
    exact Returns.miss fuel head tail remaining status s s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈
      arguments comparisonScrutinee comparison recursiveArguments ih closure constructorArguments wholeEntry
      (finish_projects (head :: remaining, status) 2 outerFinish)

/-- Under the stated successful host execution, strict returns remove exactly. -/
theorem strict_returns_remove (q : Id) {fuel : Nat} {xs : List Entry} {start finish : State}
    {result : List Entry × Status} (execution : StrictReturns key q fuel xs start result finish) :
    result = remove key q xs := by
  exact returns_remove key q (strict_projects key q execution)

end Ash.NetworkLedger.CoreStrict
