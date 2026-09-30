import SourceDeclarationPlans

/-! Explicit continuation-bound data are available to consuming source syntax,
before its admission judgment. No runtime success evidence is stored. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (ModePlans ClausePlans)
open SourceContextualHints (Requirement)

structure Bounds where
  resume : List Requirement
  close : List Requirement
  deriving DecidableEq

inductive ModeBounds : {family : Option (Nat → SourceDependencyAnnotations.Dependencies)} →
    ModePlans family → Type where
  | unavailable : ModeBounds .unavailable
  | available (bounds : Bounds) : ModeBounds (.available plans)

def ModeBounds.value {plans : ModePlans family} : ModeBounds plans → Option Bounds
  | .unavailable => none
  | .available bounds => some bounds

inductive ClauseBounds : {clauses : ScopedExpressions.Clauses} →
    {families : SourceDependencyAnnotations.ClauseDependencies} → ClausePlans clauses families → Type where
  | nil : ClauseBounds .nil
  | cons : ModeBounds ordinary → ModeBounds protectedMode → ClauseBounds rest →
      ClauseBounds (.cons (operation := operation) (body := body) ordinary protectedMode rest)

/-- Matching a clause selects its offered mode, including absence. Lookup
never falls through a matching unavailable mode to a later duplicate clause. -/
def ClauseBounds.lookup {plans : ClausePlans clauses families}
    (bounds : ClauseBounds plans) (operation : Nat) (held : Bool) : Option Bounds :=
  match bounds with
  | .nil => none
  | .cons (operation := other) ordinary protectedMode rest =>
      if operation = other then (if held then protectedMode.value else ordinary.value)
      else rest.lookup operation held

/-- Actual clause witnesses may change while the offered dependency families
remain fixed. Reindexing retains the recorded bound data for every offer. -/
def ModeBounds.reindex {before : ModePlans family} (bounds : ModeBounds before)
    (after : ModePlans family) : ModeBounds after :=
  match bounds, after with
  | .unavailable, .unavailable => .unavailable
  | .available bound, .available _ => .available bound

def ClauseBounds.reindex {before : ClausePlans clauses families} (bounds : ClauseBounds before)
    (after : ClausePlans nextClauses families) : ClauseBounds after :=
  match bounds, after with
  | .nil, .nil => .nil
  | .cons ordinary protectedMode rest, .cons nextOrdinary nextProtected nextRest =>
      .cons (ordinary.reindex nextOrdinary) (protectedMode.reindex nextProtected) (rest.reindex nextRest)

theorem ModeBounds.value_reindex {before : ModePlans family} (bounds : ModeBounds before)
    (after : ModePlans family) : (bounds.reindex after).value = bounds.value := by
  cases bounds <;> cases after <;> rfl

/-- Rewriting cannot replace a bound or switch the ordinary/protected offer.
This is data preservation; admission of rewritten code is a separate proof. -/
theorem ClauseBounds.lookup_reindex {before : ClausePlans clauses families} (bounds : ClauseBounds before)
    (after : ClausePlans nextClauses families) :
    (bounds.reindex after).lookup operation held = bounds.lookup operation held := by
  induction bounds generalizing nextClauses with
  | nil => cases after; rfl
  | cons ordinary protectedMode rest ih => cases after with
    | cons nextOrdinary nextProtected nextRest =>
        simp only [ClauseBounds.reindex, ClauseBounds.lookup, ModeBounds.value_reindex, ih]

/-- Installation checks every offered mode against the same finite envelope.
An unavailable mode has no continuation contract to check. This condition
concerns resumptive interception; disposal keeps its independent close bound. -/
def ModeBounds.acceptsResume {plans : ModePlans family} (bounds : ModeBounds plans)
    (required : List Requirement) : Bool :=
  match bounds with
  | .unavailable => true
  | .available bounds => decide (required ⊆ bounds.resume)

def ClauseBounds.acceptsResume {plans : ClausePlans clauses families} (bounds : ClauseBounds plans)
    (required : List Requirement) : Bool :=
  match bounds with
  | .nil => true
  | .cons ordinary protectedMode rest =>
      ordinary.acceptsResume required && protectedMode.acceptsResume required && rest.acceptsResume required

private theorem ModeBounds.acceptsResume_lookup {bounds : ModeBounds plans}
    (checked : bounds.acceptsResume required = true) (found : bounds.value = some selected) :
    required ⊆ selected.resume := by
  cases bounds with
  | unavailable => cases found
  | available actual =>
      cases found
      exact of_decide_eq_true checked

/-- The installation check covers the exact mode chosen by ordered lookup.
Duplicate clauses and unavailable matching modes retain their usual behavior. -/
theorem ClauseBounds.acceptsResume_lookup {plans : ClausePlans clauses families}
    (bounds : ClauseBounds plans) (checked : bounds.acceptsResume required = true)
    (found : bounds.lookup operation held = some selected) : required ⊆ selected.resume := by
  induction bounds with
  | nil => cases found
  | cons ordinary protectedMode rest ih =>
      simp only [ClauseBounds.acceptsResume, Bool.and_eq_true] at checked
      simp only [ClauseBounds.lookup] at found
      split at found
      · cases held with
        | false => exact ModeBounds.acceptsResume_lookup checked.1.1 found
        | true => exact ModeBounds.acceptsResume_lookup checked.1.2 found
      · exact ih checked.2 found

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ClauseBounds.acceptsResume_lookup
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ModeBounds.value_reindex
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ClauseBounds.lookup_reindex
