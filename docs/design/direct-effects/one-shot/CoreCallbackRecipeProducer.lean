import CoreCallbackAdmissionProducer
import SourcePlannedRecipeDeclarations

/-! Retained structural annotations certify exact literal plans. Producing and
validating these annotations from exported Core metadata remains separate. -/
namespace Ash.OneShot.CoreCallbackRecipeProducer
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open SourceDeclarationPlans (Plan ClausePlans ModePlans)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission

inductive Recipes : {dependencies : Dependencies} → Plan dependencies → Prop where
  | pure : Recipes .pure
  | request : Recipes .request
  | invoke : Recipes .invoke
  | sequence (first : Recipes initial) (second : Recipes continuation) : Recipes (.sequence initial continuation)
  | choice (left : Recipes first) (right : Recipes second) : Recipes (.choice first second)
  | handler (declarations : SourcePlannedRecipeDeclarations.Declarations required plans)
      (body : Recipes code) : Recipes (.handler required plans code)
  | cleanup (callback : Recipes first) (body : Recipes second) : Recipes (.cleanup first second)
  | resource (body : ∀ identity, Recipes (plans identity)) : Recipes (.resource plans)

theorem Recipes.certified_existing (recipes : Recipes plan) :
    SourcePlannedChecks.Certified outward world plan := by
  induction recipes generalizing world with
  | pure => exact .pure
  | request => exact .request
  | invoke => exact .invoke
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond
  | choice left right ihLeft ihRight => exact .choice ihLeft ihRight
  | handler declarations body ih => exact .handler declarations.erase declarations.certified ih
  | cleanup callback body ihCallback ihBody => exact .cleanup ihCallback ihBody
  | resource body ih => exact .resource (fun identity _ => ih identity)

theorem Recipes.certified (recipes : Recipes plan) :
    SourcePlannedChecks.Certified (evidence := declarationPolicy) outward world plan :=
  certified_from_existing recipes.certified_existing

theorem handler_certified
    (declarations : SourcePlannedRecipeDeclarations.Declarations required plans) (body : Recipes code) :
    SourcePlannedChecks.Certified (evidence := declarationPolicy) outward world
      (.handler (effect := effect) (table := table) required plans code) :=
  (Recipes.handler declarations body).certified

/-- The current clause continues with an effectful write after consumption.
The retained suffix is an exact Plan, not an inferred signature replacement. -/
inductive ClauseRecipes (rights : Syntax.OneShotRights) :
    List SourceContextualHints.Requirement → {family : Nat → Dependencies} →
    (∀ owner, Plan (family owner)) → (provided : List Nat := []) → Prop where
  | existing (recipe : SourcePlannedClauseRecipes.Recipe rights required plans provided) :
      ClauseRecipes rights required plans provided
  | purePrefix (body : ClauseRecipes rights required plans provided) :
      ClauseRecipes rights required (fun owner => .sequence .pure (plans owner)) provided
  | choice (left : ClauseRecipes rights firstRequired first provided)
      (right : ClauseRecipes rights secondRequired second provided) :
      ClauseRecipes rights (firstRequired ++ secondRequired)
        (fun owner => .choice (first owner) (second owner)) provided
  | suffix (body : ClauseRecipes rights required plans provided)
      (footprint : SourceRequestFootprints.Footprint (signature continuation) needed)
      (continuationRecipe : Recipes continuation) :
      ClauseRecipes rights (required ++ externalRequirements provided needed)
        (fun owner => .sequence (plans owner) continuation) provided

theorem ClauseRecipes.erase {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    (recipe : ClauseRecipes rights required plans provided) :
    ClauseRecipe outward rights required family provided := by
  induction recipe with
  | existing recipe => exact .existing recipe.erase
  | purePrefix body ih => exact .sequence .pure ih
  | choice left right ihLeft ihRight => exact .choice ihLeft ihRight
  | suffix body footprint continuationRecipe ih => exact .suffix ih footprint

theorem ClauseRecipes.certified (recipe : ClauseRecipes rights required plans provided) :
    SourcePlannedChecks.Certified (evidence := declarationPolicy) outward world (plans owner) := by
  letI : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
  induction recipe with
  | existing recipe => exact certified_from_existing recipe.certified
  | purePrefix body ih => exact .sequence .pure ih
  | choice left right ihLeft ihRight => exact .choice ihLeft ihRight
  | suffix body footprint continuationRecipe ih => exact .sequence ih continuationRecipe.certified

inductive Modes (rights : Syntax.OneShotRights) :
    List SourceContextualHints.Requirement → {family : Option (Nat → Dependencies)} → ModePlans family → Prop where
  | unavailable : Modes rights [] .unavailable
  | available (recipe : ClauseRecipes rights required plans) : Modes rights required (.available plans)

inductive Declarations : List SourceContextualHints.Requirement → {clauses : Clauses} →
    {families : SourceDependencyAnnotations.ClauseDependencies} → ClausePlans clauses families → Prop where
  | nil : Declarations [] .nil
  | cons (ordinary : Modes body.requiredActions ordinaryRequired ordinaryPlan)
      (protectedMode : Modes body.requiredActions protectedRequired protectedPlan)
      (rest : Declarations restRequired restPlan) :
      Declarations (ordinaryRequired ++ protectedRequired ++ restRequired)
        (.cons (body := body) ordinaryPlan protectedPlan restPlan)

theorem Modes.erase {family : Option (Nat → Dependencies)} {plan : ModePlans family}
    (recipe : Modes rights required plan) :
    DeclarationModes outward rights required family := by
  cases recipe with
  | unavailable => exact .unavailable
  | available recipe => exact .available recipe.erase

theorem Declarations.erase {plans : ClausePlans clauses families} (recipes : Declarations required plans) :
    ClauseDeclarations outward clauses families required := by
  induction recipes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih => exact .cons ordinary.erase protectedMode.erase ih

theorem Modes.certified (recipe : Modes rights required plan) :
    SourcePlannedChecks.CertifiedModes (evidence := declarationPolicy) outward world plan := by
  letI : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
  cases recipe with
  | unavailable => exact .unavailable
  | available recipe => exact .available (fun _ => recipe.certified)

theorem Declarations.certified (recipes : Declarations required plans) :
    SourcePlannedChecks.CertifiedClauses (evidence := declarationPolicy) outward world plans := by
  letI : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
  induction recipes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih => exact .cons ordinary.certified protectedMode.certified ih

theorem suffix_handler_certified
    (declarations : Declarations required plans) (body : Recipes code) :
    SourcePlannedChecks.Certified (evidence := declarationPolicy) outward world
      (.handler (effect := effect) (table := table) required plans code) :=
  by
  letI : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
  exact .handler declarations.erase declarations.certified body.certified

/-- Reconstruct the existing exported clause's annotation from its exact
literal private family, including the effectful write after resume. -/
theorem current_clause_recipes :
    ClauseRecipes ⟨true, true⟩ [(.cell identity, 1)] (Clause.plan identity) := by
  apply ClauseRecipes.purePrefix
  apply ClauseRecipes.choice (firstRequired := [(.cell identity, 1)]) (secondRequired := [])
  · have consuming : ClauseRecipes ⟨true, true⟩ [] (Clause.resumePlan) :=
      .existing (.silent .pure (.resume rfl))
    have writes : Recipes (Writes.plan identity) :=
      .sequence .pure (.sequence (.sequence .pure .pure) (.sequence .pure .request))
    have footprint : SourceRequestFootprints.Footprint (signature (Writes.plan identity)) [(.cell identity, 1)] :=
      .sequence .pure (.sequence (.sequence .pure .pure) (.sequence .pure .request))
    change ClauseRecipes ⟨true, true⟩ [(.cell identity, 1)]
      (fun owner => .sequence (Clause.resumePlan owner) (Writes.plan identity))
    simpa [externalRequirements, SourceContextualRequirements.providerScope,
      SourceHandlerRequirements.outwardRequirements, SourceHandlerRequirements.reaches]
      using ClauseRecipes.suffix consuming footprint writes
  · exact .existing (.dispose rfl)

theorem current_declaration_recipes :
    Declarations [(.cell identity, 1)] (Handler.declarationPlans identity) := by
  unfold Handler.declarationPlans
  apply Declarations.cons (ordinaryRequired := [(.cell identity, 1)]) (protectedRequired := []) (restRequired := [])
  · exact .available current_clause_recipes
  · exact .unavailable
  · exact .nil

theorem current_handler_certified (body : Recipes (Guarded.plan identity)) :
    SourcePlannedChecks.Certified (evidence := declarationPolicy) outward world (Handler.plan identity) :=
  suffix_handler_certified current_declaration_recipes body

/-- Construct the same graph lambda and stored callback together from its
source-owned literal body plan, complete rows and retained structural recipe.
Exported Core metadata does not yet produce this body annotation. -/
theorem callback_lambda {dependencies : Dependencies} {bodyPlan : Plan dependencies}
    {bodyRows : Rows (signature bodyPlan)}
    (sameAction : action.action = .lambda binder.id code)
    (known : graph.node index = some node) (kind : node.kind = .function binder bodyIndex)
    (inputType : TypeAgreement resources binder.type .unit)
    (body : Checked graph operations policy ports resources contracts owners world ownerMap action.requests .none
      (SourcePlannedTyping.Environment.extend (fun _ => none) binder.id .unit) (emptyRows.extend binder.id .unit)
      fuel bodyIndex code .unit bodyDemand bodyRequirements bodyPlan .unit bodyRows bodyEffects)
    (bodyBound : bodyEffects ⊆ allowanceEffects action.requests)
    (bodyOutward : RecursiveOutward.Outward bodyRequirements (some latent))
    (captured : LambdaPortCaptureSupport.captures (fun _ => none) binder.id code .unit .unit action.requests)
    (formed : ScopedPorts.InWorld world (Value.function .unit .unit action.requests latent (signature bodyPlan)).erase.erase.port)
    (latentBound : ∀ request ∈ latent, request.effect ∈ action.requests)
    (metadata : Metadata resources node (.function .unit .unit action.requests latent (signature bodyPlan)) [])
    (recipes : Recipes bodyPlan) :
    Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
      (fun _ => none) emptyRows (fuel + 1) index (.lambda binder.id code)
      (.function .unit .unit action.requests latent (signature bodyPlan))
      [] Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.empty .pure (.function .unit .unit bodyRows) .pure [] ∧
    ∃ stored : CoreCallbackRequestRoutes.StoredCallback operations policy contracts ports owners emptyRows world outward action,
      stored.dependencies = dependencies ∧ HEq stored.plan bodyPlan ∧ HEq stored.rows bodyRows ∧
      (∃ raw, CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok raw ∧
        raw.instantiate resources = action.action) ∧
      ScopedPorts.EffectConfigurationTyped operations.erase.erase.ports contracts.erase.erase.ports world
        ⟨.app action.action .unit, .none, .nil⟩ .unit action.requests ∧
      CoreCallbackRequestRoutes.CallbackCurrent stored contracts.erase.erase.ports world
        ⟨.app action.action .unit, .none, .nil⟩ := by
  have checked := Checked.lambda (allowed := allowed) (scope := scope)
    known kind inputType body bodyBound bodyOutward captured formed latentBound metadata
  refine ⟨checked, ?_⟩
  cases action with
  | mk identity actionCode closed actionScope answer requests =>
    dsimp only at sameAction
    subst actionCode
    obtain ⟨source, authenticated⟩ := body.sourceAuth
    let annotation : CoreCallbackAdmissionProducer.CallbackAnnotation operations policy contracts ports owners emptyRows world
        ⟨identity, .lambda binder.id code, closed, actionScope, answer, requests⟩ bodyPlan bodyRows latent := {
      callback := .lambda source bodyOutward formed latentBound,
      authenticated := .lambda authenticated captured (outward := bodyOutward)
        (formed := formed) (latentBound := latentBound) }
    let stored : CoreCallbackRequestRoutes.StoredCallback operations policy contracts ports owners emptyRows world outward
        ⟨identity, .lambda binder.id code, closed, actionScope, answer, requests⟩ := {
      latent := latent, dependencies := dependencies, plan := bodyPlan, rows := bodyRows,
      callback := annotation.callback, authenticated := annotation.authenticated,
      certified := recipes.certified }
    obtain ⟨raw, translated, instantiated, _, _⟩ := checked.compiled
    exact ⟨stored, rfl, HEq.rfl, HEq.rfl, ⟨raw, translated, instantiated⟩,
      stored.start.typed, stored.start⟩

end Ash.OneShot.CoreCallbackRecipeProducer

#print axioms Ash.OneShot.CoreCallbackRecipeProducer.Recipes.certified_existing
#print axioms Ash.OneShot.CoreCallbackRecipeProducer.Recipes.certified
#print axioms Ash.OneShot.CoreCallbackRecipeProducer.handler_certified
#print axioms Ash.OneShot.CoreCallbackRecipeProducer.ClauseRecipes.erase
#print axioms Ash.OneShot.CoreCallbackRecipeProducer.ClauseRecipes.certified
#print axioms Ash.OneShot.CoreCallbackRecipeProducer.Declarations.erase
#print axioms Ash.OneShot.CoreCallbackRecipeProducer.Declarations.certified
#print axioms Ash.OneShot.CoreCallbackRecipeProducer.suffix_handler_certified

#print axioms Ash.OneShot.CoreCallbackRecipeProducer.current_clause_recipes
#print axioms Ash.OneShot.CoreCallbackRecipeProducer.current_declaration_recipes
#print axioms Ash.OneShot.CoreCallbackRecipeProducer.current_handler_certified

#print axioms Ash.OneShot.CoreCallbackRecipeProducer.callback_lambda
