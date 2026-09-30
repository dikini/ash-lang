import SourcePlanRequirementSites
import SourcePlannedClauseRecipes

/-! Declaration annotations retain structural consuming recipes for both
offered modes. Selection follows the existing clause order and authenticates
the actual selected plan, rather than merely its dependency family. -/
namespace Ash.OneShot.SourcePlannedRecipeDeclarations
open ScopedExpressions
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceDependencyAnnotations (Dependencies)
open SourceContextualHints (Hints Requirement checkRequirements)
open SourcePlannedClauseRecipes (Recipe)
open SourcePlannedChecks (Local Pending)
open SourceContextualHintChecking (Compatible)
open OwnerPhaseTransitions (introduce)

inductive Modes (rights : Syntax.OneShotRights) :
    List Requirement → {family : Option (Nat → Dependencies)} → ModePlans family → Prop where
  | unavailable : Modes rights [] .unavailable
  | available (recipe : Recipe rights required plans) : Modes rights required (.available plans)

inductive Declarations : List Requirement → {clauses : Clauses} →
    {families : SourceDependencyAnnotations.ClauseDependencies} → ClausePlans clauses families → Prop where
  | nil : Declarations [] .nil
  | cons (ordinary : Modes body.requiredActions ordinaryRequired ordinaryPlan)
      (protectedMode : Modes body.requiredActions protectedRequired protectedPlan)
      (rest : Declarations restRequired restPlan) :
      Declarations (ordinaryRequired ++ protectedRequired ++ restRequired)
        (.cons (body := body) ordinaryPlan protectedPlan restPlan)

/-- Strong declaration evidence for the internally handled request pattern. -/
theorem handled_request_declarations :
    Declarations [] (SourceDeclarationPlans.HandledRequest.declarations operation) :=
  .cons (.available (.dispose rfl)) .unavailable .nil

theorem Modes.erase {plan : ModePlans family} (recipe : Modes rights required plan) :
    SourceContextualRequirements.ModeRecipe outward rights required family := by
  cases recipe with
  | unavailable => exact .unavailable
  | available body => exact .available body.erase

theorem Declarations.erase {plans : ClausePlans clauses families} (recipes : Declarations required plans) :
    SourceContextualRequirements.DeclarationRecipes outward clauses families required := by
  induction recipes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih => exact .cons ordinary.erase protectedMode.erase ih

theorem Modes.certified {plan : ModePlans family} (recipe : Modes rights required plan) :
    SourcePlannedChecks.CertifiedModes outward world plan := by
  cases recipe with
  | unavailable => exact .unavailable
  | available body => exact .available (fun _ => body.certified)

theorem Declarations.certified {plans : ClausePlans clauses families} (recipes : Declarations required plans) :
    SourcePlannedChecks.CertifiedClauses outward world plans := by
  induction recipes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih => exact .cons ordinary.certified protectedMode.certified ih

/-- The stronger declaration annotation supplies both existing handler-entry
premises, so callers do not need a second independent declaration proof. -/
theorem Declarations.handler {plans : ClausePlans clauses families} {hints : Hints scope}
    (recipes : Declarations required plans)
    (supplied : checkRequirements scope required = true)
    (body : Local outward actions phases world code
      (.handler (effect := effect) (table := table) (families := families) required hints)) :
    Local outward actions phases world
      (.handler (effect := effect) (table := table) required plans code) hints :=
  .handler recipes.erase recipes.certified supplied body

theorem Declarations.selected {declarations : ClausePlans clauses families}
    (recipes : Declarations required declarations)
    (selected : Selected operation held declarations parameter binder body plans) :
    ∃ needed, Recipe body.requiredActions needed plans ∧ needed ⊆ required := by
  induction selected generalizing required with
  | ordinary => cases recipes with
    | cons ordinary protectedMode rest => cases ordinary with
      | available recipe =>
          exact ⟨_, recipe, fun item member => List.mem_append_left _ (List.mem_append_left _ member)⟩
  | protectedMode => cases recipes with
    | cons ordinary protectedMode rest => cases protectedMode with
      | available recipe =>
          exact ⟨_, recipe, fun item member => List.mem_append_left _ (List.mem_append_right _ member)⟩
  | pass different next ih => cases recipes with
    | cons ordinary protectedMode rest =>
        obtain ⟨needed, recipe, included⟩ := ih rest
        exact ⟨needed, recipe, fun item member => List.mem_append_right _ (included member)⟩

/-- Declaration selection and pre-capture checks suffice for the selected
actual clause plan. Both offered modes use the same independent rights. -/
theorem Declarations.capture {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    {declarations : ClausePlans clauses families}
    {hints : Hints scope} {saved : Hints captured} {waiting : Hints tail}
    (recipes : Declarations required declarations)
    (selected : Selected operation captured.held declarations parameter binder body plans)
    (declared : SourceDependencyCapture.lookupDependencies operation families = some modes)
    (cut : SourcePlannedCuts.Cut effect operation contract modes hints saved waiting)
    (request : Local outward actions phases world (.request (effect := effect) (operation := operation)) hints)
    (retained : Pending outward actions phases world hints .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (permission : body.requiredActions.dispose = true → contract.dispose = true)
    (supplied : checkRequirements tail required = true) :
    SourceDependencyCapture.modeDependencies captured.held modes = some family ∧
    Local outward (actions.insert owner body.requiredActions) (introduce phases owner) world (plans owner)
      (.live (owner := owner) saved waiting) ∧
    Pending outward (actions.insert owner body.requiredActions) (introduce phases owner) world
      (.live (owner := owner) saved waiting) .nil := by
  obtain ⟨needed, recipe, included⟩ := recipes.selected selected
  refine ⟨?_, recipe.capture cut request retained compatible fresh consumed permission
    (SourceContextualRequirements.check_requirements_subset included supplied)⟩
  simpa only [declared, Option.bind_some] using selected.lookup

namespace Examples
open SourceDependencyHandlerGap (effect clauses dependencies)
open SourcePlannedChecks.Examples (clausePlans installPlan)
open SourceContextualHintChecking.Examples (tailHints)

/-- Reuse the existing source example which needs an outer interpretation.
Its actual plans admit structural recipes and handler entry, while the earlier
uniform declaration rule still rejects it. -/
theorem contextual_declaration :
    Declarations [(effect, 0)] clausePlans ∧
    Local outward actions phases world installPlan tailHints ∧
    ¬ SourceDependencySchemes.DeclarationSchemes outward clauses dependencies := by
  have recipes : Declarations [(effect, 0)] clausePlans :=
    .cons (.available (.request (.silent .pure (.resume rfl)))) .unavailable .nil
  exact ⟨recipes, recipes.handler (by decide) .pure,
    SourceDependencyHandlerGap.no_uniform_declarations outward⟩

end Examples
end Ash.OneShot.SourcePlannedRecipeDeclarations

#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Modes.erase
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Declarations.erase
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Modes.certified
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Declarations.certified
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Declarations.handler
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Declarations.selected
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Declarations.capture
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Examples.contextual_declaration

#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.handled_request_declarations
