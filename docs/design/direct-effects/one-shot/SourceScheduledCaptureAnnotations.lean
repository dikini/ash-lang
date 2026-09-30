import SourceScheduledCapabilityAnnotations
import SourceScheduledClauseHandlers

/-! A structural certificate for one actual clause capture. The exact cut,
selected offered plans and recursive code annotation replace a universal
successful-body premise at the allocation boundary. -/
namespace Ash.OneShot.SourceScheduledCaptureAnnotations
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code)
open SourcePlannedRecipeDeclarations (Selected)

section
variable [declarationPolicy : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- Generate request-prefix annotations from source syntax. The continuation
annotation is retained unchanged; each new request gets its own operation leaf. -/
def requestPrefixAnnotation {hints : Hints scope} {forest : Forest hints} {rest : Plan dependencies}
    (requests : List SourceContextualHints.Requirement) (annotation : Code world rest forest) :
    Code world (SourceScheduledClauseHandlers.requestPrefix requests rest) forest :=
  match requests with
  | [] => annotation
  | request :: remaining =>
      .sequence (.operations [request] (.sequence .pure .request) (.sequence .pure .request))
        (requestPrefixAnnotation remaining annotation)

theorem requestPrefix_valid {hints : Hints scope} {forest : Forest hints} {rest : Plan dependencies}
    (annotation : Code world rest forest) (validated : annotation.Valid outward actions phases)
    (supplied : SourceContextualHints.checkRequirements scope requests = true) :
    (requestPrefixAnnotation requests annotation).Valid outward actions phases := by
  induction requests with
  | nil => exact validated
  | cons request remaining ih =>
      apply And.intro
      · exact SourceScheduledAdaptationCompilation.requirements_prefix (front := .plain _ .nil) (fun _ => rfl)
          (SourceContextualRequirements.check_requirements_subset
            (fun item member => List.mem_cons.mpr (Or.inl (List.mem_singleton.mp member))) supplied)
      · exact ih (SourceContextualRequirements.check_requirements_subset
          (fun _ member => List.mem_cons.mpr (Or.inr member)) supplied)

/-- Capture data carry no successful scheduling or body-validity field.
Independent validation supplies permissions and phases for this actual owner. -/
inductive Capture [declarationPolicy : SourceScheduledCapabilityAnnotations.DeclarationPolicy] (world : List Nat) (owner : Nat) (effect : Instance) (operation : Nat)
    (offered : ProtectionContracts.ClauseContract) (modes : SourcePlannedCuts.Modes)
    {clauses : ScopedExpressions.Clauses} {families : SourceDependencyAnnotations.ClauseDependencies}
    (plans : ClausePlans clauses families) (parameter binder : Nat) (body : ScopedExpressions.Code)
    {scope : SourceDependencyCapture.Scope} {hints : Hints scope} (forest : Forest hints) : Type where
  | site {savedHints : Hints captured} {waitingHints : Hints tail}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)}
      (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved waiting)
      (selected : Selected operation captured.held plans parameter binder body bodies)
      (annotation : Code world (bodies owner) (.live (owner := owner) saved waiting)) :
      Capture world owner effect operation offered modes plans parameter binder body forest

def Capture.Valid {hints : Hints scope} {forest : Forest hints}
    (admission : Capture world owner effect operation offered modes plans parameter binder body forest)
    (outward : List Instance) (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases) : Prop :=
  match admission with
  | .site _ _ annotation =>
      annotation.Valid outward (actions.insert owner body.requiredActions) (OwnerPhaseTransitions.introduce phases owner)

/-- Exact cut and clause uniqueness derive the allocator's former universal
requirement from this single annotation. No additional future-body proof is
assumed, and no specific consuming-clause recipe shape is required. -/
theorem Capture.requirements_with
    [admissionPolicy : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws declarationPolicy admissionPolicy certification outward)
    {hints : Hints scope} {forest : Forest hints}
    (admission : Capture world owner effect operation offered modes plans parameter binder body forest)
    (validated : admission.Valid outward actions phases)
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved waiting)
    {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)}
    (selected : Selected operation captured.held plans parameter binder body bodies) :
    SourceScheduledRequirements.Satisfied outward (actions.insert owner body.requiredActions)
      (OwnerPhaseTransitions.introduce phases owner) world (bodies owner) (.live (owner := owner) saved waiting) := by
  cases admission with
  | site annotatedCut annotatedSelection annotation =>
      cases Option.some.inj (annotatedCut.erase.lookup.symm.trans cut.erase.lookup)
      obtain ⟨rfl, rfl⟩ := annotatedCut.erase.unique cut.erase.hints
      obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (annotatedCut.forest.symm.trans cut.forest))
      obtain ⟨rfl, same⟩ := SourceScheduledClauseHandlers.selected_unique annotatedSelection selected
      cases same
      exact SourceScheduledRequirements.necessary (annotation.compile_with laws validated)

end

theorem Capture.requirements {hints : Hints scope} {forest : Forest hints}
    (admission : Capture world owner effect operation offered modes plans parameter binder body forest)
    (validated : admission.Valid outward actions phases)
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved waiting)
    {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)}
    (selected : Selected operation captured.held plans parameter binder body bodies) :
    SourceScheduledRequirements.Satisfied outward (actions.insert owner body.requiredActions)
      (OwnerPhaseTransitions.introduce phases owner) world (bodies owner) (.live (owner := owner) saved waiting) :=
  admission.requirements_with (SourceScheduledCapabilityAnnotations.recipeLaws outward) validated cut selected

namespace Examples
open SourceScheduledClauseHandlers.Examples
  (code bodies outerPlans saved noActions inner_declarations requests innerFamilies resumeFamily)
open SourceDependencyCapture.Examples (effectE effectF resumeTable)

/-- The actual selected plan installs a handler, performs two newly supplied
operations and resumes. Annotation construction uses no old consumer recipe. -/
def bodyAnnotation : Code [] (bodies 19) (.live (owner := 19) saved .nil) :=
  .handler inner_declarations
    (requestPrefixAnnotation requests
      (.sequence (.operations [] .pure .pure)
        (.resume (.handler .hit)
          (.operations (.handler .nil .nil)) (.operations (.handler .nil .nil)) (.operations .nil))))
    (some (.cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil))

def admission : Capture [] 19 effectE 0 ⟨false, some [], some []⟩
    (some (fun owner => .handler effectF resumeTable innerFamilies
      (SourceScheduledClauseHandlers.prefixDependencies requests (resumeFamily owner))),
     some (fun owner => .handler effectF resumeTable innerFamilies
      (SourceScheduledClauseHandlers.prefixDependencies requests (resumeFamily owner))))
    outerPlans 1 9 code saved :=
  .site (.hit rfl rfl) .ordinary bodyAnnotation

theorem admitted : admission.Valid [] noActions OwnerPhaseTransitions.empty := by
  change bodyAnnotation.Valid [] (noActions.insert 19 code.requiredActions)
    (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19)
  apply And.intro rfl
  apply requestPrefix_valid
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rfl

/-- The certificate is genuinely beyond the old declaration grammar; its
admission does not depend on pretending that grammar already accepts it. -/
theorem old_recipes_reject : ¬ SourcePlannedRecipeDeclarations.Declarations required outerPlans :=
  SourceScheduledClauseHandlers.Examples.old_declaration_recipe_rejects_wrapper

end Examples

end Ash.OneShot.SourceScheduledCaptureAnnotations

#print axioms Ash.OneShot.SourceScheduledCaptureAnnotations.Capture.requirements
#print axioms Ash.OneShot.SourceScheduledCaptureAnnotations.requestPrefix_valid
#print axioms Ash.OneShot.SourceScheduledCaptureAnnotations.Examples.admitted
#print axioms Ash.OneShot.SourceScheduledCaptureAnnotations.Examples.old_recipes_reject

#print axioms Ash.OneShot.SourceScheduledCaptureAnnotations.Capture.requirements_with
