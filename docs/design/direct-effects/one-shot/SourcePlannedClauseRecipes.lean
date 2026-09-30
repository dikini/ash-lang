import SourcePlannedCapturePrep
import SourcePlannedProviders
import SourcePlanSignatureChecking

/-! Structural consuming-clause recipes retain actual plans and reconstruct
the stronger checks from pre-capture source judgments. These rules cover
consumption, resource scopes and local requests, pure cleanup, silent and
external request prefixes, internally handled request prefixes, and choice.
General handler-bearing clauses still require further structural rules; no opaque uniform-proof rule is added. -/
namespace Ash.OneShot.SourcePlannedClauseRecipes
open ScopedExpressions
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceContextualHintChecking (Compatible)
open SourcePlannedChecks (Local Pending)
open SourceContextualClauses (RequestCapability)
open OwnerPhaseTransitions (introduce spend)
open SourcePlannedProviders (providerHints provider_local request_from_capability)
open SourceContextualRequirements (providerScope provider_capability provider_member capability_plain capability_live)

theorem silent {plan : Plan dependencies} {hints : Hints scope}
    (empty : dependencies.Silent) : Local outward actions phases world plan hints := by
  induction empty generalizing scope with
  | pure => cases plan; exact .pure
  | sequence first second ihFirst ihSecond =>
      cases plan with
      | sequence left right => exact .sequence (ihFirst) (ihSecond)

open SourceDeclarationPlans
open SourcePlanSignatures (signature)

/-- The internal disposer uses the already established disposal family. -/
theorem handled_request_recipes :
    SourceContextualRequirements.DeclarationRecipes outward
      (HandledRequest.clauses operation) (HandledRequest.families operation) [] :=
  .cons (.available (.dispose rfl)) .unavailable .nil

theorem handled_request_certified :
    SourcePlannedChecks.Certified outward world (HandledRequest.plan effect operation) :=
  .handler handled_request_recipes (.cons (.available (fun _ => .invoke)) .unavailable .nil)
    (.sequence .pure .request)

/-- No continuation demand escapes this internal handler. Only its own empty
captured prefix is disposed; the original receiving suffix is unchanged. -/
theorem handled_request_local {hints : Hints scope} :
    Local outward actions phases world (HandledRequest.plan effect operation) hints := by
  refine .handler handled_request_recipes
    (.cons (.available (fun _ => .invoke)) .unavailable .nil) rfl (.sequence .pure (.request ?_ ?_))
  · have lower := SourceContextualRequirements.handled_request_checked
      (outward := outward) (actions := actions) (phases := phases) (world := world)
      (effect := effect) (operation := operation) (scope := scope)
    cases lower with
    | handler body => cases body with | sequence initial request => exact request
  · intro captured tail saved waiting contract modes same found disposes
    have selected : SourceDependencyCapture.select effect operation
        (.handler effect (HandledRequest.table operation) (HandledRequest.families operation) scope) =
        some (.handler (.handler effect (HandledRequest.table operation) (HandledRequest.families operation) .nil)
          scope ⟨true, some [], none⟩ (some HandledRequest.family, none)) := by
      simp [SourceDependencyCapture.select, HandledRequest.table, HandledRequest.families,
        ProtectionContracts.lookup, SourceDependencyCapture.lookupDependencies]
    cases Option.some.inj (selected.symm.trans found)
    cases saved with | handler required rest => cases rest; exact .nil

/-- A recipe describes the existing plan constructors. The owner is a parameter,
and action permission is independent of operation requirements. -/
inductive Recipe (rights : Syntax.OneShotRights) :
    List Requirement → {family : Nat → Dependencies} → (∀ owner, Plan (family owner)) → (provided : List Nat := []) → Prop where
  | resume (permission : rights.resume = true) :
      Recipe rights [] (fun owner => .invoke (key := ⟨owner, .resume⟩)) provided
  | dispose (permission : rights.dispose = true) :
      Recipe rights [] (fun owner => .invoke (key := ⟨owner, .dispose⟩)) provided
  | silent {initial : Plan dependencies} (empty : dependencies.Silent)
      (rest : Recipe rights required plans provided) :
      Recipe rights required (fun owner => .sequence initial (plans owner)) provided
  | request (rest : Recipe rights required plans provided) :
      Recipe rights ((effect, operation) :: required)
        (fun owner => .sequence (.sequence .pure (.request (effect := effect) (operation := operation))) (plans owner)) provided
  | localRequest (member : identity ∈ provided) (rest : Recipe rights required plans provided) :
      Recipe rights required
        (fun owner => .sequence (.sequence .pure (.request (effect := .cell identity) (operation := operation))) (plans owner)) provided
  | handledRequest {initial : Nat → Plan (HandledRequest.dependencies effect operation)}
      (shape : ∀ owner, signature (initial owner) = signature (HandledRequest.plan effect operation))
      (rest : Recipe rights required plans provided) :
      Recipe rights required (fun owner => .sequence (initial owner) (plans owner)) provided
  | resource {family : Nat → Nat → Dependencies} {plans : ∀ owner identity, Plan (family owner identity)}
      (body : ∀ identity, Recipe rights required (fun owner => plans owner identity) (identity :: provided)) :
      Recipe rights required (fun owner => .resource (plans owner)) provided
  | cleanup (rest : Recipe rights required plans provided) :
      Recipe rights required (fun owner => .cleanup (needs := []) .pure (plans owner)) provided
  | choice (left : Recipe rights firstRequired first provided) (right : Recipe rights secondRequired second provided) :
      Recipe rights (firstRequired ++ secondRequired) (fun owner => .choice (first owner) (second owner)) provided

/-- Erasure reuses the established contextual recipe rules. -/
theorem Recipe.erase {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    (recipe : Recipe rights required plans provided) :
    SourceContextualRequirements.Recipe outward rights required family provided := by
  induction recipe with
  | resume permission => exact .resume permission
  | dispose permission => exact .dispose permission
  | silent empty rest ih => exact .silent ih empty
  | request rest ih => exact .request ih
  | localRequest member rest ih => exact .localRequest member ih
  | handledRequest shape rest ih => exact .handledRequest ih
  | resource body ih => exact .resource ih
  | cleanup rest ih => exact .cleanup ih
  | choice left right ihLeft ihRight => exact .choice ihLeft ihRight

theorem Recipe.certified {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    (recipe : Recipe rights required plans provided) :
    SourcePlannedChecks.Certified outward world (plans owner) := by
  induction recipe generalizing world with
  | resume | dispose => exact .invoke
  | silent empty rest ih =>
      exact .sequence ((SourcePlannedClauseRecipes.silent (outward := outward) (world := world)
        (actions := fun _ => none) (phases := fun _ => .consumed) (hints := .nil) empty).certified) ih
  | request rest ih => exact .sequence (.sequence .pure .request) ih
  | localRequest member rest ih => exact .sequence (.sequence .pure .request) ih
  | handledRequest shape rest ih =>
      exact .sequence (SourcePlanSignatureChecking.certified_congr handled_request_certified (shape owner).symm) ih
  | resource body ih => exact .resource (fun identity fresh => ih identity)
  | cleanup rest ih => exact .cleanup .pure ih
  | choice left right ihLeft ihRight => exact .choice ihLeft ihRight

/-- Recomposition checks each constructor against the retained pieces. These
premises are derived from pre-capture checks by `Recipe.capture` below. -/
theorem Recipe.compile_providers {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    {saved : Hints captured} {waiting : Hints tail}
    (recipe : Recipe rights required plans provided)
    (known : actions owner = some rights) (available : phases owner = .available)
    (inside : Pending outward actions (spend phases owner) world saved (.spent (owner := owner) waiting))
    (outside : Pending outward actions (spend phases owner) world waiting .nil)
    (disposal : rights.dispose = true → captured.held = false ∧
      SourceRecursiveRoutes.Closing outward captured.shape [] [] ∧
      Pending outward actions (spend phases owner) world
        (SourceContextualInvocationHints.forClosing saved) (.running (.spent (owner := owner) waiting)))
    (compatible : Compatible (.live (owner := owner) saved waiting) .nil)
    (tailCompatible : Compatible waiting .nil)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    Local outward actions phases world (plans owner) (providerHints provided (.live (owner := owner) saved waiting)) := by
  induction recipe generalizing world with
  | resume permission =>
      exact provider_local _ (SourcePlannedRecomposition.resume_clause known permission available inside outside compatible)
  | dispose permission =>
      obtain ⟨unprotected, route, closing⟩ := disposal permission
      exact provider_local _ (SourcePlannedRecomposition.dispose_clause known permission available unprotected route closing outside tailCompatible)
  | silent empty rest ih => exact .sequence (SourcePlannedClauseRecipes.silent empty) (ih inside outside disposal supplied)
  | request rest ih =>
      exact .sequence (.sequence .pure (request_from_capability (capability_plain
        (provider_capability _ (capability_live (supplied _ List.mem_cons_self))))))
        (ih inside outside disposal (fun request member => supplied request (List.mem_cons_of_mem _ member)))
  | localRequest member rest ih =>
      exact .sequence (.sequence .pure (request_from_capability (capability_plain (provider_member member))))
        (ih inside outside disposal supplied)
  | handledRequest shape rest ih =>
      exact .sequence (SourcePlanSignatureChecking.local_congr handled_request_local (shape owner).symm)
        (ih inside outside disposal supplied)
  | resource body ih =>
      apply Local.resource
      intro identity fresh
      apply ih identity
      · exact SourcePlannedPhases.pending_transport_world inside
          (fun _ ready => ready) (fun _ _ known => known) (List.subset_append_left _ _)
      · exact SourcePlannedPhases.pending_transport_world outside
          (fun _ ready => ready) (fun _ _ known => known) (List.subset_append_left _ _)
      · intro permitted
        obtain ⟨held, route, closing⟩ := disposal permitted
        exact ⟨held, route, SourcePlannedPhases.pending_transport_world closing
          (fun _ ready => ready) (fun _ _ known => known) (List.subset_append_left _ _)⟩
      · exact supplied
  | cleanup rest ih => exact SourcePlannedNeutralChecks.pure_cleanup (ih inside outside disposal supplied)
  | choice left right ihLeft ihRight =>
      exact .choice (ihLeft inside outside disposal (fun request member => supplied request (List.mem_append_left _ member)))
        (ihRight inside outside disposal (fun request member => supplied request (List.mem_append_right _ member)))

theorem Recipe.compile {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    {saved : Hints captured} {waiting : Hints tail}
    (recipe : Recipe rights required plans)
    (known : actions owner = some rights) (available : phases owner = .available)
    (inside : Pending outward actions (spend phases owner) world saved (.spent (owner := owner) waiting))
    (outside : Pending outward actions (spend phases owner) world waiting .nil)
    (disposal : rights.dispose = true → captured.held = false ∧
      SourceRecursiveRoutes.Closing outward captured.shape [] [] ∧
      Pending outward actions (spend phases owner) world
        (SourceContextualInvocationHints.forClosing saved) (.running (.spent (owner := owner) waiting)))
    (compatible : Compatible (.live (owner := owner) saved waiting) .nil)
    (tailCompatible : Compatible waiting .nil)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    Local outward actions phases world (plans owner) (.live (owner := owner) saved waiting) :=
  recipe.compile_providers known available inside outside disposal compatible tailCompatible supplied

/-- The actual clause plan is checked using only judgments before capture,
fresh-owner facts and the declaration's finite operation requirements. -/
theorem Recipe.capture {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    {hints : Hints scope} {saved : Hints captured} {waiting : Hints tail}
    (recipe : Recipe rights required plans)
    (cut : SourcePlannedCuts.Cut effect operation contract modes hints saved waiting)
    (request : Local outward actions phases world (.request (effect := effect) (operation := operation)) hints)
    (retained : Pending outward actions phases world hints .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (permission : rights.dispose = true → contract.dispose = true)
    (supplied : checkRequirements tail required = true) :
    Local outward (actions.insert owner rights) (introduce phases owner) world (plans owner)
      (.live (owner := owner) saved waiting) ∧
    Pending outward (actions.insert owner rights) (introduce phases owner) world
      (.live (owner := owner) saved waiting) .nil := by
  obtain ⟨live, inside, outside, disposal⟩ := SourcePlannedCapturePrep.captured_checks cut request retained fresh consumed
  obtain ⟨liveCompatible, tailCompatible⟩ := SourcePlannedCapturePrep.cut_compatible (owner := owner) cut compatible
  exact ⟨recipe.compile (by simp [Syntax.UsageTickets.insert]) (by simp [introduce]) inside outside
    (fun permitted => disposal (permission permitted)) liveCompatible tailCompatible
    (SourceContextualRequirements.check_requirements_iff.mp supplied), live⟩

end Ash.OneShot.SourcePlannedClauseRecipes

#print axioms Ash.OneShot.SourcePlannedClauseRecipes.silent
#print axioms Ash.OneShot.SourcePlannedClauseRecipes.Recipe.erase
#print axioms Ash.OneShot.SourcePlannedClauseRecipes.Recipe.certified
#print axioms Ash.OneShot.SourcePlannedClauseRecipes.Recipe.compile
#print axioms Ash.OneShot.SourcePlannedClauseRecipes.Recipe.capture

#print axioms Ash.OneShot.SourcePlannedClauseRecipes.Recipe.compile_providers

#print axioms Ash.OneShot.SourcePlannedClauseRecipes.handled_request_recipes

#print axioms Ash.OneShot.SourcePlannedClauseRecipes.handled_request_certified

#print axioms Ash.OneShot.SourcePlannedClauseRecipes.handled_request_local
