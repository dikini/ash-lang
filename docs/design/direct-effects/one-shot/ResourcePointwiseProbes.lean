import CoreCallablePlanSubstitution
namespace Ash.OneShot.ResourcePointwiseProbes
open ScopedExpressions SourceDeclarationPlans
open CoreCallablePlanSubstitution

def arms : Clauses := .cons 0 99 100 (.variable 0) .nil
def body : Code := .handle (.cell (.bound 17)) .unit arms
def family (identity : Nat) : Plan (.handler (.cell identity) [] [(0,none,none)] .pure) :=
  .handler [] (.cons (operation := 0) (parameter := 99) (binder := 100)
    (body := .variable 0) .unavailable .unavailable .nil) .pure
def original : Plan (.sequence .pure (.resource (fun identity => .handler (.cell identity) [] [(0,none,none)] .pure))) :=
  .sequence .pure (.resource family)

def firstClause : Plan dependencies → Option Code
  | .sequence _ second => firstClause second
  | .handler _ declarations _ =>
      match declarations with
      | .nil => none
      | @ClausePlans.cons _ _ _ _ _ _ _ code _ _ _ => some code
  | _ => none

def resourceClause (source : Plan dependencies) (identity : Nat) : Option Code :=
  match source with
  | .sequence _ (.resource bodies) => firstClause (bodies identity)
  | _ => none

def transformed := plan (.resource 17 (.integer 3) body) original 0 (.integer 8)

theorem original_member (identity : Nat) : resourceClause original identity = some (.variable 0) := rfl
/-- Every opened member traverses the SAME visible ordinary substitution.
The preceding resource-free plan function leaves this clause as variable0. -/
theorem pointwise_member (identity : Nat) : resourceClause transformed identity = some (.integer 8) := rfl

def effectOf : Plan dependencies → Option Instance
  | .handler (effect := effect) _ _ _ => some effect
  | _ => none

def resourceEffect (source : Plan dependencies) (identity : Nat) : Option Instance :=
  match source with
  | .sequence _ (.resource bodies) => effectOf (bodies identity)
  | _ => none

theorem varying_family_preserved (identity : Nat) : resourceEffect transformed identity = some (.cell identity) := rfl

theorem not_constantized : resourceEffect transformed 0 ≠ resourceEffect transformed 1 := by
  decide

#print axioms original_member
#print axioms pointwise_member
#print axioms varying_family_preserved
#print axioms not_constantized
end Ash.OneShot.ResourcePointwiseProbes
