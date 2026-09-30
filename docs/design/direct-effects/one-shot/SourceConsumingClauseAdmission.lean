import SourceConsumingClauseContracts

/-! Structural source admission for consuming clauses. The rules infer finite
outer operation requirements from syntax and declared continuation interfaces.
They do not quantify over future captured code or assume a checked clause body. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceContextualHints (Hints Requirement checkRequirements checkCapability)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)
open SourceScheduledAdaptationCompilation (requirements_prefix requirements_handler requirements_cell)
open SourceHandlerRequirements (outwardRequirements intercepted)

section
variable [declarations : DeclarationPolicy]

/-- The source rules mirror operation footprints, with distinct continuation
leaves. The declared continuation interfaces are ordinary reusable operation
requirements; the leaf separately checks the right to consume its owner. -/
inductive Admitted [declarations : DeclarationPolicy] (rights : Syntax.OneShotRights)
    (resumeRequired closeRequired : List Requirement) :
    {world : List Nat} → {owner : Nat} → {dependencies : SourceDependencyAnnotations.Dependencies} →
      {plan : Plan dependencies} → Body world owner plan → List Requirement → Prop where
  | resume (permission : rights.resume = true) : Admitted rights resumeRequired closeRequired .resume resumeRequired
  | dispose (permission : rights.dispose = true) : Admitted rights resumeRequired closeRequired .dispose closeRequired
  | sequence (rest : Admitted rights resumeRequired closeRequired body bodyRequired) :
      Admitted rights resumeRequired closeRequired (.sequence required footprint declared body) (required ++ bodyRequired)
  | choice (first : Admitted rights resumeRequired closeRequired left firstRequired)
      (second : Admitted rights resumeRequired closeRequired right secondRequired) :
      Admitted rights resumeRequired closeRequired (.choice left right) (firstRequired ++ secondRequired)
  | handler (body : Admitted rights resumeRequired closeRequired code bodyRequired)
      (internal : checkRequirements (.handler effect table families .nil) (intercepted effect bodyRequired) = true)
      (coverage : bounds.acceptsResume
        (required ++ outwardRequirements (.handler effect table families .nil) bodyRequired) = true) :
      Admitted rights resumeRequired closeRequired
        (.handler (effect := effect) (table := table) (families := families) (required := required) bounds evidence code)
        (required ++ outwardRequirements (.handler effect table families .nil) bodyRequired)
  | cleanup (body : Admitted rights resumeRequired closeRequired code bodyRequired) :
      Admitted rights resumeRequired closeRequired (.cleanup required footprint declared code) (required ++ bodyRequired)
  | resource (body : ∀ identity fresh, Admitted rights resumeRequired closeRequired (code identity fresh)
      ([(Instance.cell identity, 0), (.cell identity, 1)] ++ required)) :
      Admitted rights resumeRequired closeRequired (.resource code) required
  | weaken (body : Admitted rights resumeRequired closeRequired code first) (included : first ⊆ second) :
      Admitted rights resumeRequired closeRequired code second

/-- Weakening cannot hide the requirements of a resume leaf. -/
theorem Admitted.resume_requirements {plan : Plan dependencies} {body : Body world owner plan}
    (admitted : Admitted rights resumeRequired closeRequired body required) :
    match world, owner, dependencies, plan, body with
    | _, _, _, _, .resume => resumeRequired ⊆ required
    | _, _, _, _, _ => True := by
  induction admitted with
  | resume permission => exact List.Subset.refl _
  | @weaken world owner dependencies plan code first second source included ih =>
      cases code with
      | resume => exact ih.trans included
      | _ => trivial
  | _ => trivial

/-- Handler admission retains the actual nested bounds, even after outer
requirement weakening. Its body derivation supplies the finite envelope. -/
theorem Admitted.handler_bounds {plan : Plan dependencies} {body : Body world owner plan}
    (admitted : Admitted rights resumeRequired closeRequired body required) :
    match world, owner, dependencies, plan, body with
    | _, _, _, _, .handler (effect := effect) (table := table) (families := families)
        (required := handlerRequired) bounds _ code =>
        ∃ bodyRequired, Admitted rights resumeRequired closeRequired code bodyRequired ∧
          bounds.acceptsResume
            (handlerRequired ++ outwardRequirements (.handler effect table families .nil) bodyRequired) = true
    | _, _, _, _, _ => True := by
  induction admitted with
  | handler source internal coverage ih => exact ⟨_, source, coverage⟩
  | @weaken world owner dependencies plan code first second source included ih =>
      cases code <;> exact ih
  | _ => trivial

omit declarations in
/-- Operation lookup passes both live and spent owner markers. The ordered
caller prefix is retained and may still intercept a request. -/
private theorem requirements_live_spent (front : Scope) :
    checkRequirements (front.append (.live owner saved tail)) required = true ↔
      checkRequirements (front.append (.spent owner tail)) required = true := by
  apply Iff.of_eq
  congr 1
  unfold checkRequirements
  congr 1
  funext request
  rw [SourceHandlerRequirements.capability_append, SourceHandlerRequirements.capability_append]
  rw [SourceHandlerRequirements.capability_prepend
      (first := .live owner saved tail) (second := tail) rfl,
    SourceHandlerRequirements.capability_prepend
      (first := .spent owner tail) (second := tail) rfl]

/-- Structural admission derives all clause-local contract checks from a
finite outer requirement check. The saved continuation's code is unknown here.
Caller checks are an induction invariant, initially the empty caller. -/
theorem Admitted.bound_check {body : Body world owner plan}
    (admitted : Admitted rights resumeRequired closeRequired body required)
    {frontHints : Hints frontScope} {front : Forest frontHints} (before : Interfaces world front)
    (known : actions owner = some rights) (available : phases owner = .available)
    (caller : before.check (.spent owner waiting) = true)
    (supplied : checkRequirements (frontScope.append (.live owner captured waiting)) required = true) :
    body.BoundCheck resumeRequired closeRequired actions phases
      (frontScope.append (.live owner captured waiting)) waiting before := by
  induction admitted generalizing frontScope with
  | resume permission =>
      exact ⟨by simp only [known, Option.any_some, permission], available,
        (requirements_live_spent frontScope).mp supplied, caller⟩
  | dispose permission =>
      exact ⟨by simp only [known, Option.any_some, permission], available,
        requirements_prefix (front := .running .nil) (fun _ => rfl)
          ((requirements_live_spent frontScope).mp supplied), caller⟩
  | sequence rest ih =>
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨first, rest⟩ := supplied
      exact ⟨requirements_prefix (front := .plain _ .nil) (fun _ => rfl) first,
        ih before known available caller rest⟩
  | choice first second ihFirst ihSecond =>
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨left, right⟩ := supplied
      exact ⟨ihFirst before known available caller left, ihSecond before known available caller right⟩
  | handler body internal coverage ih =>
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨installed, rest⟩ := supplied
      exact ⟨installed, ih (.handler front before) known available
        (Bool.and_eq_true_iff.mpr ⟨(requirements_live_spent frontScope).mp installed, caller⟩)
        (requirements_handler internal rest)⟩
  | cleanup body ih =>
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨callback, rest⟩ := supplied
      exact ⟨ih (.cleanup front _ _ _ before) known available
          (Bool.and_eq_true_iff.mpr ⟨requirements_prefix (front := .running .nil) (fun _ => rfl)
            ((requirements_live_spent frontScope).mp callback), caller⟩)
          (requirements_prefix (front := .cleanup _ _ .nil) (fun _ => rfl) rest),
        requirements_prefix (front := .running .nil) (fun _ => rfl) callback⟩
  | resource body ih =>
      intro identity fresh
      exact ih identity fresh (.cell (before.world_weaken (List.subset_append_left _ _))) known available
        (by simpa only [Interfaces.check, Interfaces.check_world_weaken] using caller)
        (requirements_cell identity supplied)
  | weaken body included ih =>
      exact ih before known available caller (SourceContextualRequirements.check_requirements_subset included supplied)

/-- At handler installation the outer requirements are checked against the
waiting scope. Any later captured prefix may be inserted at the live boundary. -/
theorem Admitted.at_capture {body : Body world owner plan}
    (admitted : Admitted rights resumeRequired closeRequired body required)
    (known : actions owner = some rights) (available : phases owner = .available)
    (supplied : checkRequirements waiting required = true) :
    body.BoundCheck resumeRequired closeRequired actions phases (.live owner captured waiting) waiting .nil :=
  admitted.bound_check .nil known available rfl
    (requirements_prefix (front := .live owner captured .nil) (fun _ => rfl) supplied)

/-- The admitted source clause compiles at an actual live capture using only
original retained checks, finite interface bounds and independent owner facts. -/
theorem Admitted.schedule [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws declarations admission certification outward)
    {body : Body world owner plan} (admitted : Admitted rights resumeRequired closeRequired body required)
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing) (after : Interfaces world tail)
    (known : actions owner = some rights) (available : phases owner = .available)
    (supplied : checkRequirements tailScope required = true)
    (resumeBound : (actions owner).any (fun rights => rights.resume) = true → inside.exposed ⊆ resumeRequired)
    (closeBound : (actions owner).any (fun rights => rights.dispose) = true → closing.exposed ⊆ closeRequired)
    (resumeReady : (actions owner).any (fun rights => rights.resume) = true → inside.check resumeOutside = true)
    (closeReady : (actions owner).any (fun rights => rights.dispose) = true → closing.check closeOutside = true)
    (disposal : (actions owner).any (fun rights => rights.dispose) = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.check .nil = true) :
    SourceScheduledChecks.Local outward actions phases world plan (.live (owner := owner) saved tail) :=
  body.compile laws inside closing after
    (body.check_from_contract (admitted.at_capture known available supplied)
      resumeBound closeBound resumeReady closeReady disposal tailReady)

/-- Independent resource allocation keeps the structural source derivation. -/
theorem Admitted.world_weaken {body : Body world owner plan}
    (admitted : Admitted rights resumeRequired closeRequired body required) (larger : world ⊆ next) :
    Admitted rights resumeRequired closeRequired (body.world_weaken larger) required := by
  induction admitted generalizing next with
  | resume permission => exact .resume permission
  | dispose permission => exact .dispose permission
  | sequence rest ih => exact .sequence (ih larger)
  | choice first second ihFirst ihSecond => exact .choice (ihFirst larger) (ihSecond larger)
  | handler body internal coverage ih => exact .handler (ih larger) internal coverage
  | cleanup body ih => exact .cleanup (ih larger)
  | resource body ih =>
      exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member))
        (ScopedExpressions.append_subset larger (List.Subset.refl _)))
  | weaken body included ih => exact .weaken (ih larger) included

/-- Each offered mode records its declared resume and close operation bounds.
Unavailable modes have no source body or operation requirement. -/
inductive ModeAdmitted [declarations : DeclarationPolicy] (rights : Syntax.OneShotRights) :
    List Requirement → List Requirement → List Requirement → {world : List Nat} →
      {family : Option (Nat → SourceDependencyAnnotations.Dependencies)} →
      {plans : ModePlans family} → Modes world plans → Prop where
  | unavailable : ModeAdmitted rights [] [] [] .unavailable
  | available (source : ∀ owner, Admitted rights resumeRequired closeRequired (bodies owner) required) :
      ModeAdmitted rights resumeRequired closeRequired required (.available bodies)

/-- A structural declaration judgment aggregates the outer requirements of
all actual clauses and both modes. Source typing supplies the clause rights. -/
inductive DeclarationAdmitted [declarations : DeclarationPolicy] : List Requirement → {world : List Nat} →
    {clauses : ScopedExpressions.Clauses} → {families : SourceDependencyAnnotations.ClauseDependencies} →
      {plans : ClausePlans clauses families} → Declarations world plans → Prop where
  | nil : DeclarationAdmitted [] .nil
  | cons {body : ScopedExpressions.Code} (ordinary : ModeAdmitted body.requiredActions resumeOrdinary closeOrdinary ordinaryRequired ordinaryAnnotation)
      (protectedMode : ModeAdmitted body.requiredActions resumeProtected closeProtected protectedRequired protectedAnnotation)
      (rest : DeclarationAdmitted restRequired restAnnotation) :
      DeclarationAdmitted (ordinaryRequired ++ protectedRequired ++ restRequired)
        (Declarations.cons (body := body) ordinaryAnnotation protectedAnnotation restAnnotation)

/-- Ordered selection extracts the admitted actual body, its own interface
bounds and its share of the declaration's external operation requirements. -/
theorem DeclarationAdmitted.selected {plans : ClausePlans clauses families} {annotated : Declarations world plans}
    (admitted : DeclarationAdmitted required annotated)
    (selected : SourcePlannedRecipeDeclarations.Selected operation held plans parameter binder code bodies) :
    ∃ resumeRequired closeRequired needed, ∃ body : Body world owner (bodies owner),
      Admitted code.requiredActions resumeRequired closeRequired body needed ∧ needed ⊆ required := by
  induction selected generalizing required with
  | ordinary => cases admitted with
    | cons ordinary protectedMode rest => cases ordinary with
      | available source =>
          exact ⟨_, _, _, _, source owner,
            fun item member => List.mem_append_left _ (List.mem_append_left _ member)⟩
  | protectedMode => cases admitted with
    | cons ordinary protectedMode rest => cases protectedMode with
      | available source =>
          exact ⟨_, _, _, _, source owner,
            fun item member => List.mem_append_left _ (List.mem_append_right _ member)⟩
  | pass different next ih => cases admitted with
    | cons ordinary protectedMode rest =>
        obtain ⟨resumeRequired, closeRequired, needed, body, source, included⟩ := ih rest
        exact ⟨resumeRequired, closeRequired, needed, body, source,
          fun item member => List.mem_append_right _ (included member)⟩


theorem ModeAdmitted.world_weaken {modes : Modes world plans}
    (admitted : ModeAdmitted rights resumeRequired closeRequired required modes) (larger : world ⊆ next) :
    ModeAdmitted rights resumeRequired closeRequired required (modes.world_weaken larger) := by
  cases admitted with
  | unavailable => exact .unavailable
  | available source => exact .available (fun owner => (source owner).world_weaken larger)

theorem DeclarationAdmitted.world_weaken {annotated : Declarations world plans}
    (admitted : DeclarationAdmitted required annotated) (larger : world ⊆ next) :
    DeclarationAdmitted required (annotated.world_weaken larger) := by
  induction admitted with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      exact .cons (ordinary.world_weaken larger) (protectedMode.world_weaken larger) (ih larger)

end

namespace AdmissionExamples
open SourceScheduledClauseHandlers.Examples (code noActions bodies requesting waiting)
open SourceDependencyCapture.Examples (effectF)

/-- The source derivation has no actual capture, world-state check or future
body-success premise. F is supplied by the clause's own installed handler. -/
theorem admitted_body (owner : Nat) :
    Admitted code.requiredActions [(effectF, 0)] [] (Examples.body owner) [] :=
  .handler (bodyRequired := [(effectF, 0), (effectF, 0), (effectF, 0)])
    (.sequence (.sequence (.sequence (.resume rfl)))) rfl rfl

theorem admitted_declarations : DeclarationAdmitted [] Examples.declarations :=
  .cons (.available admitted_body) (.available admitted_body) .nil

/-- The source declaration derives checking at every later live capture, not
only at the concrete example used to discover this rule. -/
theorem any_capture (known : actions owner = some code.requiredActions) (available : phases owner = .available) :
    (Examples.body owner).BoundCheck [(effectF, 0)] [] actions phases (.live owner captured waitingScope) waitingScope .nil :=
  (admitted_body owner).at_capture known available rfl

/-- Derive the actual post-capture schedule from source admission and the
original retained interfaces, reusing the existing scheduling kernel. -/
theorem source_restored_schedule :
    SourceScheduledChecks.Local [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (bodies 19) (.live (owner := 19) requesting waiting) :=
  (admitted_body 19).schedule (SourceScheduledCapabilityAnnotations.recipeLaws [])
    (resumeOutside := ContractExamples.waitingScope) (closeOutside := .nil)
    ContractExamples.retained .nil (.handler .nil .nil) rfl rfl rfl
    (fun _ => List.Subset.refl _) (fun _ => List.Subset.refl _) (fun _ => rfl) (fun _ => rfl)
    (by intro impossible; cases impossible) rfl

/-- Resource admission discharges local builtin requests by membership. -/
theorem admitted_resource (owner : Nat) :
    Admitted code.requiredActions [] [] (Examples.resourceBody owner) [] := by
  apply Admitted.resource
  intro identity fresh
  apply Admitted.weaken (.cleanup (.sequence (.resume rfl)))
  intro request member
  exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp member))

/-- A missing captured requirement is rejected already by source admission. -/
theorem missing_operation_rejected :
    ¬ Admitted code.requiredActions [(.user 93 [], 0)] [] (Examples.body 19) [] := by
  intro admitted
  exact ContractExamples.missing_captured_operation (admitted.at_capture rfl rfl rfl)

end AdmissionExamples

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.bound_check

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.at_capture
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.world_weaken
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DeclarationAdmitted.selected

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.schedule
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ModeAdmitted.world_weaken
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DeclarationAdmitted.world_weaken
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.AdmissionExamples.admitted_body
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.AdmissionExamples.admitted_declarations
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.AdmissionExamples.any_capture
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.AdmissionExamples.source_restored_schedule
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.AdmissionExamples.admitted_resource
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.AdmissionExamples.missing_operation_rejected

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.resume_requirements
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.handler_bounds
