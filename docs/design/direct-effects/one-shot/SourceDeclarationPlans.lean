import SourceContextualHints

/-! Recursive checking annotations for declarations that source code can
install later. The existing dependency tree remains the index; these plans
retain actual clause syntax and annotations for both offered clause families.
They are data, not a new computation grammar or an admission proof. -/
namespace Ash.OneShot.SourceDeclarationPlans
open ScopedExpressions
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourceContextualHints (Requirement Hints)

mutual
inductive Plan : Dependencies → Type where
  | pure : Plan .pure
  | request : Plan (.request effect operation)
  | invoke : Plan (.invoke key)
  | sequence : Plan first → Plan second → Plan (.sequence first second)
  | choice : Plan first → Plan second → Plan (.choice first second)
  | handler (required : List Requirement) (declarations : ClausePlans clauses families)
      (body : Plan dependencies) : Plan (.handler effect table families dependencies)
  | cleanup : Plan callback → Plan body → Plan (.cleanup needs callback body)
  | resource : (∀ identity, Plan (family identity)) → Plan (.resource family)

inductive ModePlans : Option (Nat → Dependencies) → Type where
  | unavailable : ModePlans none
  | available : (∀ owner, Plan (family owner)) → ModePlans (some family)

inductive ClausePlans : Clauses → ClauseDependencies → Type where
  | nil : ClausePlans .nil []
  | cons : ModePlans ordinary → ModePlans protectedMode → ClausePlans clauses families →
      ClausePlans (.cons operation parameter binder body clauses)
        ((operation, ordinary, protectedMode) :: families)
end

/- An internally handled operation whose clause disposes its own capture.
The surrounding continuation is outside this handler's body. -/
namespace HandledRequest

def family (owner : Nat) : Dependencies := .invoke ⟨owner, .dispose⟩
def families (operation : Nat) : ClauseDependencies := [(operation, some family, none)]
def table (operation : Nat) : List (Nat × ProtectionContracts.ClauseContract) :=
  [(operation, ⟨true, some [], none⟩)]
def clauses (operation : Nat) : ScopedExpressions.Clauses :=
  .cons operation 0 1 (.discard 1) .nil
def declarations (operation : Nat) : ClausePlans (clauses operation) (families operation) :=
  .cons (.available (fun _ => .invoke)) .unavailable .nil
def dependencies (effect : Instance) (operation : Nat) : Dependencies :=
  .handler effect (table operation) (families operation) (.sequence .pure (.request effect operation))
def plan (effect : Instance) (operation : Nat) : Plan (dependencies effect operation) :=
  .handler [] (declarations operation) (.sequence .pure .request)

end HandledRequest

/-- Split the existing annotations at a given source-scope boundary. Handler
requirements are retained exactly, including inside dormant branches. -/
theorem splitHints (hints : Hints (first.append second)) :
    ∃ front : Hints first, ∃ tail : Hints second, hints = front.append tail := by
  induction first with
  | nil => exact ⟨.nil, hints, rfl⟩
  | plain dependencies rest ih => cases hints with
    | plain rest => obtain ⟨front, tail, rfl⟩ := ih rest; exact ⟨.plain front, tail, rfl⟩
  | handler effect table families rest ih => cases hints with
    | handler required rest => obtain ⟨front, tail, rfl⟩ := ih rest; exact ⟨.handler required front, tail, rfl⟩
  | cell identity rest ih => cases hints with
    | cell rest => obtain ⟨front, tail, rfl⟩ := ih rest; exact ⟨.cell front, tail, rfl⟩
  | cleanup needs callback rest ih => cases hints with
    | cleanup rest => obtain ⟨front, tail, rfl⟩ := ih rest; exact ⟨.cleanup front, tail, rfl⟩
  | running rest ih => cases hints with
    | running rest => obtain ⟨front, tail, rfl⟩ := ih rest; exact ⟨.running front, tail, rfl⟩
  | live owner saved rest ihSaved ihRest => cases hints with
    | live saved rest => obtain ⟨front, tail, rfl⟩ := ihRest rest; exact ⟨.live saved front, tail, rfl⟩
  | spent owner rest ih => cases hints with
    | spent rest => obtain ⟨front, tail, rfl⟩ := ih rest; exact ⟨.spent front, tail, rfl⟩

end Ash.OneShot.SourceDeclarationPlans

#print axioms Ash.OneShot.SourceDeclarationPlans.splitHints
