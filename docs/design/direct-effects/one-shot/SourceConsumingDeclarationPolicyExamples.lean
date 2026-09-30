import SourceConsumingPolicyInstallation

/-! A handler-wrapped consuming declaration accepted by the concrete policy and
rejected by the recipe-only policy. This tests declaration admission and static
certification; it is not a complete initial-program admission theorem. -/
namespace Ash.OneShot.SourceConsumingDeclarationPolicies.Examples
open SourceDeclarationPlans (ClausePlans)
open SourceConsumingClauseAnnotations (Body Declarations Bounded ClauseBounds)
open SourceConsumingClauseAnnotations.CongruenceExamples (first body)

private def code : ScopedExpressions.Code :=
  .handle (Instantiation.freezeEffect (.user 92 [])) (.resume 9 .unit)
    SourcePlanSignatures.Examples.clauses

private def clauses : ScopedExpressions.Clauses := .cons 0 1 9 code .nil

private def families : SourceDependencyAnnotations.ClauseDependencies :=
  [(0, some (fun owner => .handler (.user 92 []) [] SourcePlanSignatures.Examples.families
    (.invoke ⟨owner, .resume⟩)), none)]

def plans : ClausePlans clauses families := .cons (.available first) .unavailable .nil

def annotation : Declarations [] plans := .cons (.available body) .unavailable .nil

def bounds : ClauseBounds plans := .cons (.available ⟨[], []⟩) .unavailable .nil

theorem bounded_source : Bounded bounds annotation [] := by
  apply Bounded.cons (ordinaryRequired := []) (protectedRequired := []) (restRequired := [])
  · apply SourceConsumingClauseAnnotations.BoundedMode.available
    · exact .available (fun owner => SourceConsumingClauseAnnotations.CongruenceExamples.nested_admitted owner)
    · intro owner
      exact .handler SourceConsumingClauseAnnotations.CongruenceExamples.annotation
        SourceConsumingClauseAnnotations.CongruenceExamples.admitted .resume
  · exact .unavailable
  · exact .nil

theorem admitted : (capability 1).accepts [] plans :=
  bounded_admitted (depth := 0) ⟨bounds, annotation, bounded_source⟩

theorem certified (world : List Nat) (outward : List Instance) :
    SourcePlannedChecks.CertifiedClauses (evidence := certification 1) outward world plans :=
  (laws 1 outward).certified admitted

private theorem recipe_no_handler {family : Nat → SourceDependencyAnnotations.Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)}
    (recipe : SourcePlannedClauseRecipes.Recipe rights required bodies provided) :
    ∀ owner, match family owner with
      | .handler _ _ _ _ => False
      | _ => True := by
  cases recipe <;> intro owner <;> trivial

theorem recipe_rejected : ¬ (capability 0).accepts required plans := by
  intro checked
  cases checked with
  | cons ordinary protectedMode rest => cases ordinary with
    | available recipe => exact recipe_no_handler recipe 0

/-- Inherited structural evidence remains admitted at the next layer. -/
theorem inherited : (capability 2).accepts [] plans := capability_inclusion admitted

/-- The broader declaration also enters the existing source scheduler. The
checking syntax remains a handler followed by the ordinary pure computation. -/
def handlerPlan : SourceDeclarationPlans.Plan
    (.handler (.user 93 []) [(0, ⟨false, some [], none⟩)] families .pure) :=
  .handler [] plans .pure

def handlerAnnotation : SourceScheduledCapabilityAnnotations.Code
    (declarationPolicy := capability 1) [] handlerPlan SourceRetainedPlans.Forest.nil := by
  letI := capability 1
  exact .handler admitted (.operations [] .pure .pure) (some bounds)

theorem handler_scheduled :
    SourceScheduledChecks.Local (admission := admission 1) (certification := certification 1)
      [] (fun _ => none) OwnerPhaseTransitions.empty [] handlerPlan SourceRetainedPlans.Forest.nil := by
  letI := capability 1
  letI := admission 1
  letI := certification 1
  exact handlerAnnotation.compile_with (laws 1 []) ⟨rfl, rfl⟩

theorem same_bounds_at_runtime (world : List Nat) :
    ∃ actual : Declarations (declarations := capability 1) world plans,
      Bounded (declarations := capability 1) bounds actual [] :=
  bounded_at_world (depth := 0) bounded_source world

end Ash.OneShot.SourceConsumingDeclarationPolicies.Examples

#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.Examples.bounded_source
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.Examples.admitted
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.Examples.certified
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.Examples.recipe_rejected
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.Examples.inherited

#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.Examples.handler_scheduled
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.Examples.same_bounds_at_runtime
