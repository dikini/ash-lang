import SourceBoundAdmission

/-! A recursively admitted consuming clause generates admitted bound metadata
for the exact annotation used at capture. The projection is independent of the
captured forest; saved-source validity remains a separate obligation. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation ofCode)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledNeutral (OwnerCut)

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

def Body.boundAnnotation {plan : Plan dependencies} (body : Body world owner plan) : Annotation world plan :=
  match body with
  | .resume | .dispose => .absent
  | .sequence _ _ _ rest => .sequence .absent rest.boundAnnotation
  | .choice first second => .choice first.boundAnnotation second.boundAnnotation
  | .handler bounds _ body => .handler (some bounds) body.boundAnnotation
  | .cleanup _ _ _ body => .cleanup body.boundAnnotation .absent
  | .resource body => .resource (fun identity fresh => (body identity fresh).boundAnnotation)

theorem Body.Nested.boundAnnotation_admitted {body : Body world owner plan} (checked : body.Nested) :
    body.boundAnnotation.Admitted := by
  induction body with
  | resume | dispose => exact .absent .invoke
  | sequence required footprint declared rest ih =>
      cases checked with | sequence rest => exact .sequence (.absent declared) (ih rest)
  | choice first second ihFirst ihSecond =>
      cases checked with | choice first second => exact .choice (ihFirst first) (ihSecond second)
  | handler bounds evidence body ih =>
      cases checked with | handler source admitted body => exact .bounded source admitted (ih body)
  | cleanup required footprint declared body ih =>
      cases checked with | cleanup body => exact .cleanup (ih body) (.absent declared)
  | resource body ih =>
      cases checked with | resource body => exact .resource (fun identity fresh => ih identity fresh (body identity fresh))

/-- Capture instantiation retains exactly the source's recorded bounds. -/
theorem Body.ofCode_annotate {plan : Plan dependencies} (body : Body world owner plan)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail)
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing)
    (before : Interfaces world front) (after : Interfaces world tail) :
    ofCode (body.annotate cut inside closing before after) = body.boundAnnotation := by
  induction body generalizing wholeScope frontScope with
  | resume | dispose => rfl
  | sequence required footprint declared rest ih =>
      simp only [Body.annotate, ofCode, Body.boundAnnotation, ih cut inside closing before after]
  | choice first second ihFirst ihSecond =>
      simp only [Body.annotate, ofCode, Body.boundAnnotation,
        ihFirst cut inside closing before after, ihSecond cut inside closing before after]
  | handler bounds evidence body ih =>
      simp only [Body.annotate, ofCode, Body.boundAnnotation, ih (.handler cut) inside closing (.handler _ before) after]
  | cleanup required footprint declared body ih =>
      simp only [Body.annotate, ofCode, Body.boundAnnotation,
        ih (.cleanup cut) inside closing (.cleanup _ required footprint declared before) after]
  | resource body ih =>
      simp only [Body.annotate, ofCode, Body.boundAnnotation]
      congr 1
      funext identity fresh
      exact ih identity fresh (.cell cut)
        (inside.world_weaken (List.subset_append_left _ _))
        (closing.world_weaken (List.subset_append_left _ _))
        (.cell (before.world_weaken (List.subset_append_left _ _)))
        (after.world_weaken (List.subset_append_left _ _))

theorem Body.Nested.annotate_admitted {body : Body world owner plan} (checked : body.Nested)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail)
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing)
    (before : Interfaces world front) (after : Interfaces world tail) :
    (ofCode (body.annotate cut inside closing before after)).Admitted := by
  rw [body.ofCode_annotate cut inside closing before after]
  exact checked.boundAnnotation_admitted

end

/-- Recursive saved chains affect continuation annotations, but retain the
same bounds at every constructor of the selected clause. -/
theorem Body.ofCode_annotateRecursive {plan : Plan dependencies} (body : Body world owner plan)
    (owners : List Nat) {terminalHints : Hints terminalScope} {terminal : Forest terminalHints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix)
    (closing : Interfaces world ((SourceConsumingRecursiveBounds.chain owners terminal).append suffix).forClosing)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front ((SourceConsumingRecursiveBounds.chain owners terminal).append suffix) tail)
    (before : Interfaces world front) (after : Interfaces world tail) :
    ofCode (body.annotateRecursive owners source retained closing cut before after) = body.boundAnnotation := by
  induction body generalizing wholeScope frontScope with
  | resume | dispose => rfl
  | sequence required footprint declared rest ih =>
      simp only [Body.annotateRecursive, ofCode, Body.boundAnnotation, ih source retained closing cut before after]
  | choice first second ihFirst ihSecond =>
      simp only [Body.annotateRecursive, ofCode, Body.boundAnnotation,
        ihFirst source retained closing cut before after, ihSecond source retained closing cut before after]
  | handler bounds evidence body ih =>
      simp only [Body.annotateRecursive, ofCode, Body.boundAnnotation,
        ih source retained closing (.handler cut) (.handler _ before) after]
  | cleanup required footprint declared body ih =>
      simp only [Body.annotateRecursive, ofCode, Body.boundAnnotation,
        ih source retained closing (.cleanup cut) (.cleanup _ required footprint declared before) after]
  | resource body ih =>
      simp only [Body.annotateRecursive, ofCode, Body.boundAnnotation]
      congr 1
      funext identity fresh
      exact ih identity fresh
        (source.world_weaken (List.subset_append_left _ _))
        (retained.world_weaken (List.subset_append_left _ _))
        (closing.world_weaken (List.subset_append_left _ _)) (.cell cut)
        (.cell (before.world_weaken (List.subset_append_left _ _)))
        (after.world_weaken (List.subset_append_left _ _))

/-- Scheduling and recursive bound admission concern the same generated code
at the actual selected clause plan. No successor-admission premise is needed. -/
theorem Bounded.capture_annotation_admitted {actions : Syntax.UsageTickets}
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies)
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing) (after : Interfaces world tail)
    (checked : bounds.check operation savedScope.held code.requiredActions inside.exposed closing.exposed = true)
    (supplied : SourceContextualHints.checkRequirements tailScope required = true)
    (resumeReady : code.requiredActions.resume = true → inside.check resumeOutside = true)
    (closeReady : code.requiredActions.dispose = true → closing.check closeOutside = true)
    (disposal : code.requiredActions.dispose = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.check .nil = true) :
    ∃ annotation : SourceScheduledCapabilityAnnotations.Code world (bodies owner) (.live (owner := owner) saved tail),
      annotation.Valid outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce phases owner) ∧ (ofCode annotation).Admitted := by
  obtain ⟨body, nested, valid⟩ := admitted.capture_body_nested (owner := owner) (actions := actions) (phases := phases) cut selected inside closing after checked supplied
    resumeReady closeReady disposal tailReady
  exact ⟨body.annotate .hit inside closing .nil after, valid,
    nested.annotate_admitted .hit inside closing .nil after⟩

open SourceConsumingRecursiveBounds (chain annotateSuffix)
open SourceContextualHints (checkRequirements)

theorem Bounded.recursive_capture_annotation_admitted
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    (owners : List Nat) {terminalHints : Hints terminalScope} {terminal : Forest terminalHints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix)
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints} (after : Interfaces world waiting)
    {originalHints : Hints originalScope} {original : Forest originalHints}
    (oldReceiver : Interfaces world original)
    (originalReady : code.requiredActions.resume = true →
      (annotateSuffix owners source retained oldReceiver).Valid outward actions phases)
    (fresh : owner ∉ owners)
    {wholeHints : Hints wholeScope} {whole : Forest wholeHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole ((chain owners terminal).append suffix) waiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held
      plans parameter binder code bodies)
    (checked : bounds.check operation
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held code.requiredActions
      (source.append retained).exposed (SourceConsumingRecursiveBounds.closingSuffix owners source retained).exposed = true)
    (supplied : checkRequirements waitingScope required = true)
    (closeReady : code.requiredActions.dispose = true →
      (SourceConsumingRecursiveBounds.closingSuffix owners source retained).check closeOutside = true)
    (disposal : code.requiredActions.dispose = true →
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held = false ∧
        SourceDependencyCapture.checkClosing outward
          ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).shape [] [] = true)
    (tailReady : after.check .nil = true) :
    ∃ annotation : SourceScheduledCapabilityAnnotations.Code world (bodies owner)
        (.live (owner := owner) ((chain owners terminal).append suffix) waiting),
      annotation.Valid outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce phases owner) ∧ (ofCode annotation).Admitted := by
  obtain ⟨body, nested, valid⟩ := admitted.recursive_capture_body_nested owners source retained after oldReceiver
    originalReady fresh cut selected checked supplied closeReady disposal tailReady
  refine ⟨body.annotateRecursive owners source retained
    (SourceConsumingRecursiveBounds.closingSuffix owners source retained) .hit .nil after, valid, ?_⟩
  rw [body.ofCode_annotateRecursive]
  exact nested.boundAnnotation_admitted

namespace GenerationExamples
open CongruenceExamples (first annotation admitted)
open SourcePlanBounds.AdmissionExamples (missingRequirement)

def uncheckedNested (owner : Nat) : Body [] owner (first owner) :=
  .handler missingRequirement (.cons (.available (.resume rfl)) .unavailable .nil) .resume

/-- Outer consumption alone does not validate the installed declaration. -/
theorem outer_admitted (owner : Nat) : Admitted ⟨true, false⟩ [] [] (uncheckedNested owner) [] :=
  .handler (.resume rfl) rfl rfl

theorem unchecked_nested_rejected (owner : Nat) : ¬ (uncheckedNested owner).Nested := by
  intro checked
  cases checked with
  | handler source admitted body =>
      obtain ⟨contract, needed, body, found, sourceChecked, included⟩ := admitted.selected (owner := 9) .ordinary
      change some ⟨[(.user 93 [], 0)], []⟩ = some contract at found
      cases Option.some.inj found
      cases body
      have impossible : [(Instance.user 93 [], 0)] ⊆ [] := sourceChecked.resume_requirements.trans included
      exact List.not_mem_nil (impossible List.mem_cons_self)

theorem valid_nested (owner : Nat) : (CongruenceExamples.body owner).Nested :=
  .handler annotation admitted .resume

end GenerationExamples

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Nested.boundAnnotation_admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.ofCode_annotate
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Nested.annotate_admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.capture_annotation_admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.GenerationExamples.outer_admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.GenerationExamples.unchecked_nested_rejected
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.GenerationExamples.valid_nested

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.ofCode_annotateRecursive
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.recursive_capture_annotation_admitted

namespace Ash.OneShot.SourceConsumingCaptureInput
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceConsumingClauseAnnotations (ClauseBounds Bounded Declarations)

/-- Both existing captured-source shapes generate the same selected-plan
annotation with independent validity and recursive bound admission. -/
theorem Source.capture_annotation_admitted
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    {hints : Hints scope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (input : Source world whole saved waiting)
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies)
    (checked : input.Check outward actions phases owner bounds code.requiredActions cut closeOutside)
    (supplied : checkRequirements waitingScope required = true) :
    ∃ annotation : SourceScheduledCapabilityAnnotations.Code world (bodies owner) (.live (owner := owner) saved waiting),
      annotation.Valid outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce phases owner) ∧ (SourcePlanBounds.ofCode annotation).Admitted := by
  cases input with
  | operations source =>
      have parts := Bool.and_eq_true_iff.mp ((source.check_atCut cut).symm.trans checked.1)
      apply admitted.capture_annotation_admitted (closeOutside := closeOutside) cut selected
        (source.atCut cut).1 (source.atCut cut).1.forClosing (source.atCut cut).2 checked.2.1 supplied
        (fun _ => parts.1) _ checked.2.2.2 parts.2
      intro permission
      rw [SourceScheduledRetainedInterfaces.Interfaces.check_forClosing]
      exact checked.2.2.1 permission
  | recursive owners source retained after oldReceiver =>
      exact admitted.recursive_capture_annotation_admitted owners source retained after oldReceiver checked.1 checked.2.1
        cut selected checked.2.2.1 supplied checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2

end Ash.OneShot.SourceConsumingCaptureInput

#print axioms Ash.OneShot.SourceConsumingCaptureInput.Source.capture_annotation_admitted
