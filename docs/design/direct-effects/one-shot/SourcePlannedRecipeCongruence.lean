import SourcePlannedRecipeDeclarations
import SourcePlanSignatureChecking

/-! Transport consuming recipes through their authenticated source signatures.
The transport does not require literal equality of plans or clause syntax;
scoped plans can retain distinct source witnesses with the same signature. -/
namespace Ash.OneShot.SourcePlannedClauseRecipes
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures

theorem silent_unique {first second : Plan dependencies}
    (empty : dependencies.Silent) : first = second := by
  induction empty with
  | pure => cases first; cases second; rfl
  | sequence left right ihLeft ihRight =>
      cases first; cases second
      exact congr (congrArg Plan.sequence ihLeft) ihRight

/-- Recipe transport follows the checked signature. This is the interface
needed by scope-bearing plans, whose dependency index does not fix their
handler requirements or nested clause witnesses. -/
theorem Recipe.signature_congr
    {family : Nat → SourceDependencyAnnotations.Dependencies}
    {plans next : ∀ owner, Plan (family owner)}
    (recipe : Recipe rights required plans provided)
    (same : ∀ owner, signature (plans owner) = signature (next owner)) :
    Recipe rights required next provided := by
  induction recipe with
  | resume permission =>
      have identical : next = (fun owner => .invoke (key := ⟨owner, .resume⟩)) := by
        funext owner
        cases next owner
        rfl
      rw [identical]
      exact .resume permission
  | dispose permission =>
      have identical : next = (fun owner => .invoke (key := ⟨owner, .dispose⟩)) := by
        funext owner
        cases next owner
        rfl
      rw [identical]
      exact .dispose permission
  | silent empty rest ih =>
      rename_i initialDependencies required restFamily restPlans provided initial
      let first (owner : Nat) : Plan initialDependencies := match next owner with | .sequence before _ => before
      let second (owner : Nat) : Plan (restFamily owner) := match next owner with | .sequence _ after => after
      have firstSame (owner : Nat) : first owner = initial := (silent_unique empty).symm
      have nextSame : next = (fun owner => .sequence initial (second owner)) := by
        funext owner
        have original := firstSame owner
        cases actual : next owner with
        | sequence before after => simpa only [first, second, actual] using congrArg (fun plan => Plan.sequence plan after) original
      rw [nextSame]
      apply Recipe.silent empty
      apply ih
      intro owner
      have equal := same owner
      rw [nextSame] at equal
      exact (Signature.sequence.inj equal).2
  | request rest ih =>
      rename_i required restFamily restPlans provided effect operation
      let second (owner : Nat) : Plan (restFamily owner) := match next owner with | .sequence _ after => after
      have nextSame : next = (fun owner => .sequence (.sequence .pure (.request (effect := effect) (operation := operation))) (second owner)) := by
        funext owner
        dsimp only [second]
        cases actual : next owner with
        | sequence before after => cases before with
          | sequence initial request => cases initial; cases request; rfl
      rw [nextSame]
      apply Recipe.request
      apply ih
      intro owner
      have equal := same owner
      rw [nextSame] at equal
      exact (Signature.sequence.inj equal).2
  | localRequest member rest ih =>
      rename_i provided identity required restFamily restPlans operation
      let second (owner : Nat) : Plan (restFamily owner) := match next owner with | .sequence _ after => after
      have nextSame : next = (fun owner => .sequence (.sequence .pure (.request (effect := .cell identity) (operation := operation))) (second owner)) := by
        funext owner
        dsimp only [second]
        cases next owner with
        | sequence before after => cases before with
          | sequence initial request => cases initial; cases request; rfl
      rw [nextSame]
      apply Recipe.localRequest member
      apply ih
      intro owner
      have equal := same owner
      rw [nextSame] at equal
      exact (Signature.sequence.inj equal).2
  | handledRequest shape rest ih =>
      rename_i effect operation required restFamily restPlans provided initial
      let first (owner : Nat) : Plan (SourceDeclarationPlans.HandledRequest.dependencies effect operation) :=
        match next owner with | .sequence before _ => before
      let second (owner : Nat) : Plan (restFamily owner) := match next owner with | .sequence _ after => after
      have nextSame : next = (fun owner => .sequence (first owner) (second owner)) := by
        funext owner
        dsimp only [first, second]
        cases next owner
        rfl
      rw [nextSame]
      apply Recipe.handledRequest
      · intro owner
        have equal := same owner
        rw [nextSame] at equal
        exact (Signature.sequence.inj equal).1.symm.trans (shape owner)
      · apply ih
        intro owner
        have equal := same owner
        rw [nextSame] at equal
        exact (Signature.sequence.inj equal).2
  | resource body ih =>
      let bodies (owner identity : Nat) := match next owner with | .resource plans => plans identity
      have nextSame : next = (fun owner => .resource (bodies owner)) := by
        funext owner
        dsimp only [bodies]
        cases next owner
        rfl
      rw [nextSame]
      apply Recipe.resource
      intro identity
      apply ih identity
      intro owner
      have equal := same owner
      rw [nextSame] at equal
      exact congrFun (Signature.resource.inj equal) identity
  | cleanup rest ih =>
      rename_i required restFamily restPlans provided
      let second (owner : Nat) : Plan (restFamily owner) := match next owner with | .cleanup _ body => body
      have nextSame : next = (fun owner => .cleanup (needs := []) .pure (second owner)) := by
        funext owner
        dsimp only [second]
        cases next owner with
        | cleanup callback body => cases callback; rfl
      rw [nextSame]
      apply Recipe.cleanup
      apply ih
      intro owner
      have equal := same owner
      rw [nextSame] at equal
      exact (Signature.cleanup.inj equal).2
  | choice left right ihLeft ihRight =>
      rename_i firstRequired firstFamily firstPlans provided secondRequired secondFamily secondPlans
      let first (owner : Nat) : Plan (firstFamily owner) := match next owner with | .choice before _ => before
      let second (owner : Nat) : Plan (secondFamily owner) := match next owner with | .choice _ after => after
      have nextSame : next = (fun owner => .choice (first owner) (second owner)) := by
        funext owner
        dsimp only [first, second]
        cases next owner
        rfl
      rw [nextSame]
      apply Recipe.choice
      · apply ihLeft
        intro owner
        have equal := same owner
        rw [nextSame] at equal
        exact (Signature.choice.inj equal).1
      · apply ihRight
        intro owner
        have equal := same owner
        rw [nextSame] at equal
        exact (Signature.choice.inj equal).2

end Ash.OneShot.SourcePlannedClauseRecipes

namespace Ash.OneShot.SourcePlannedRecipeDeclarations
open SourceDeclarationPlans (ModePlans ClausePlans)
open SourcePlanSignatures

theorem Modes.congr {first second : ModePlans family}
    (recipe : Modes rights required first)
    (same : modeSignatures first = modeSignatures second) : Modes rights required second := by
  cases recipe with
  | unavailable => cases second; exact .unavailable
  | available body => cases second with
    | available next =>
      exact .available (body.signature_congr (fun owner => congrFun (ModeSignatures.available.inj same) owner))

theorem Declarations.signature_congr {first : ClausePlans before families} {second : ClausePlans after families}
    (recipes : Declarations required first)
    (same : clauseSignatures first = clauseSignatures second) :
    Declarations required second := by
  induction recipes generalizing after with
  | nil => cases second; exact .nil
  | cons ordinary protectedMode rest ih => cases second with
    | cons nextOrdinary nextProtected nextRest =>
      obtain ⟨actions, ordinarySame, protectedSame, tail⟩ := ClauseSignatures.cons.inj same
      exact .cons (actions ▸ ordinary.congr ordinarySame) (actions ▸ protectedMode.congr protectedSame) (ih tail)


namespace Examples
open ScopedExpressions
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures.Examples (clauses families plans)

def first : Plan (.handler (.user 92 []) [] families .pure) := .handler [] plans .pure
def second : Plan (.handler (.user 92 []) [] families .pure) :=
  .handler [] (substituteClauses plans 2 .unit) .pure

theorem scoped_signatures_equal : signature first = signature second := by
  simp only [first, second, signature, substitution_signature plans (value := .unit) trivial]

/-- Equal signatures preserve checking data, not literal clause witnesses. -/
theorem scoped_plans_distinct : first ≠ second := by
  intro same
  change Plan.handler [] plans Plan.pure = Plan.handler [] (substituteClauses plans 2 .unit) Plan.pure at same
  have clauseSame : clauses = clauses.subst 2 .unit := by injection same
  exact SourcePlanSignatures.Examples.substituted_clause_changes clauseSame.symm

/-- The same dependency index cannot conceal a changed handler requirement. -/
theorem altered_requirement_rejected :
    signature first ≠ signature (Plan.handler (effect := .user 92 []) (table := []) [(.user 93 [], 0)] plans .pure) := by
  intro same
  have requirements := (Signature.handler.inj same).1
  cases requirements

theorem substituted_recipe_retained : Declarations [] (substituteClauses plans 2 .unit) := by
  have recipe : Declarations [] plans := .cons (.available (.resume rfl)) .unavailable .nil
  exact recipe.signature_congr SourcePlanSignatures.Examples.substituted_signature_retained.symm

end Examples

end Ash.OneShot.SourcePlannedRecipeDeclarations

#print axioms Ash.OneShot.SourcePlannedClauseRecipes.silent_unique
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Modes.congr
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Declarations.signature_congr

#print axioms Ash.OneShot.SourcePlannedClauseRecipes.Recipe.signature_congr

#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Examples.scoped_signatures_equal
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Examples.scoped_plans_distinct
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Examples.altered_requirement_rejected
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Examples.substituted_recipe_retained
