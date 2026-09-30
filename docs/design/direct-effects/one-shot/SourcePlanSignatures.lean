import SourceDeclarationPlans

/-! Stable annotations for function types. Actual plans still retain clause
syntax for source authentication; signatures retain its required continuation
actions instead of variable names or literal clause code. -/
namespace Ash.OneShot.SourcePlanSignatures
open ScopedExpressions
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceContextualHints (Requirement)

mutual
inductive Signature : Dependencies → Type where
  | pure : Signature .pure
  | request : Signature (.request effect operation)
  | invoke : Signature (.invoke key)
  | sequence : Signature first → Signature second → Signature (.sequence first second)
  | choice : Signature first → Signature second → Signature (.choice first second)
  | handler (required : List Requirement) (declarations : ClauseSignatures families)
      (body : Signature dependencies) : Signature (.handler effect table families dependencies)
  | cleanup : Signature callback → Signature body → Signature (.cleanup needs callback body)
  | resource : (∀ identity, Signature (family identity)) → Signature (.resource family)

inductive ModeSignatures : Option (Nat → Dependencies) → Type where
  | unavailable : ModeSignatures none
  | available : (∀ owner, Signature (family owner)) → ModeSignatures (some family)

inductive ClauseSignatures : ClauseDependencies → Type where
  | nil : ClauseSignatures []
  | cons : Syntax.OneShotRights → ModeSignatures ordinary → ModeSignatures protectedMode →
      ClauseSignatures families → ClauseSignatures ((operation, ordinary, protectedMode) :: families)
end

mutual
def signature : Plan dependencies → Signature dependencies
  | .pure => .pure
  | .request => .request
  | .invoke => .invoke
  | .sequence first second => .sequence (signature first) (signature second)
  | .choice first second => .choice (signature first) (signature second)
  | .handler required declarations body => .handler required (clauseSignatures declarations) (signature body)
  | .cleanup callback body => .cleanup (signature callback) (signature body)
  | .resource body => .resource (fun identity => signature (body identity))

def modeSignatures : ModePlans family → ModeSignatures family
  | .unavailable => .unavailable
  | .available body => .available (fun owner => signature (body owner))

def clauseSignatures : ClausePlans clauses families → ClauseSignatures families
  | @ClausePlans.nil => .nil
  | @ClausePlans.cons _ _ _ _ _ _ _ body ordinary protectedMode rest =>
      .cons body.requiredActions (modeSignatures ordinary) (modeSignatures protectedMode) (clauseSignatures rest)
end

/-- Changing clause variables preserves its signature. Nested plans are
retained here; their own substitution witnesses are checked independently. -/
def substituteClauses (plans : ClausePlans clauses families) (name : Nat) (value : Code) :
    ClausePlans (clauses.subst name value) families :=
  match plans with
  | .nil => .nil
  | .cons ordinary protectedMode rest => .cons ordinary protectedMode (substituteClauses rest name value)

theorem substitution_signature (plans : ClausePlans clauses families) (isValue : value.IsValue) :
    clauseSignatures (substituteClauses plans name value) = clauseSignatures plans := by
  cases plans with
  | nil => rfl
  | cons ordinary protectedMode rest =>
      simp only [substituteClauses, clauseSignatures, Clauses.subst]
      split <;> simp only [Code.substitution_required_actions _ _ isValue, substitution_signature rest isValue]
termination_by structural plans

namespace Examples

def clauses : Clauses := .cons 0 1 9 (.resume 9 (.variable 2)) .nil
def families : ClauseDependencies := [(0, some (fun owner => .invoke ⟨owner, .resume⟩), none)]
def plans : ClausePlans clauses families := .cons (.available (fun _ => .invoke)) .unavailable .nil

theorem substituted_clause_changes : clauses.subst 2 .unit ≠ clauses := by
  intro same
  cases same

theorem substituted_signature_retained :
    clauseSignatures (substituteClauses plans 2 .unit) = clauseSignatures plans :=
  substitution_signature plans trivial

def disposingClauses : Clauses := .cons 0 1 9 (.discard 9) .nil
def disposingPlans : ClausePlans disposingClauses families := .cons (.available (fun _ => .invoke)) .unavailable .nil

/-- Keeping dependency indices alone cannot conceal a change in the clause's
required actions. Source typing must independently authenticate its code. -/
theorem altered_actions_rejected : clauseSignatures plans ≠ clauseSignatures disposingPlans := by
  intro same
  have actions := (ClauseSignatures.cons.inj same).1
  cases actions

end Examples

end Ash.OneShot.SourcePlanSignatures

#print axioms Ash.OneShot.SourcePlanSignatures.substitution_signature

#print axioms Ash.OneShot.SourcePlanSignatures.Examples.substituted_clause_changes
#print axioms Ash.OneShot.SourcePlanSignatures.Examples.substituted_signature_retained
#print axioms Ash.OneShot.SourcePlanSignatures.Examples.altered_actions_rejected
