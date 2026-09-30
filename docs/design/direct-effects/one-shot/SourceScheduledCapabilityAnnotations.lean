import SourceScheduledInvocationInterfaces
import SourceDeclarationPolicyTransport
import SourceConsumingBoundData

/-! Source scheduling annotations with recursive continuation uses. Annotations
retain actual code and cuts, independently of the action and phase maps. Their
validation checks permissions separately and descends through actual restored
or closing source after consumption. No Local/Pending proof is stored. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourceScheduledNeutral (OwnerCut)
open SourceDependencyOwners (PendingWithin owners)
open SourceScheduledChecks (Local Pending)
open OwnerPhaseTransitions (Phases spend)

/-- Static declaration evidence carried by source annotations. -/
class DeclarationPolicy where
  accepts : ∀ (_required : List Requirement) {clauses : ScopedExpressions.Clauses}
    {families : SourceDependencyAnnotations.ClauseDependencies}, ClausePlans clauses families → Prop

instance recipePolicy : DeclarationPolicy where
  accepts := fun required {_ _} plans => SourcePlannedRecipeDeclarations.Declarations required plans

/-- These laws concern declaration evidence only. They contain no current or
future Local/Pending check, execution step or successful clause-body premise. -/
structure DeclarationLaws (declarationPolicy : DeclarationPolicy)
    (admission : SourceScheduledChecks.DeclarationPolicy)
    (certification : SourcePlannedChecks.DeclarationPolicy) (outward : List Instance) : Prop where
  admitted : ∀ {clauses families required} {plans : ClausePlans clauses families},
    declarationPolicy.accepts required plans → admission.accepts outward required plans
  certified : ∀ {world clauses families required} {plans : ClausePlans clauses families},
    declarationPolicy.accepts required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) outward world plans
  projected : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → certification.accepts outward required plans
  legacyAdmission : ∀ {clauses families required} {plans : ClausePlans clauses families},
    SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans
  legacyCertification : ∀ {clauses families required} {plans : ClausePlans clauses families},
    SourceContextualRequirements.DeclarationRecipes outward clauses families required →
      certification.accepts outward required plans

theorem recipeLaws (outward : List Instance) :
    DeclarationLaws recipePolicy SourceScheduledChecks.recipePolicy SourcePlannedChecks.contextualPolicy outward :=
  ⟨(fun checked => checked), (fun checked => SourcePlannedRecipeDeclarations.Declarations.certified checked),
    (fun checked => SourcePlannedRecipeDeclarations.Declarations.erase checked),
    (fun checked => checked), (fun checked => checked)⟩

section
variable [declarationPolicy : DeclarationPolicy]

mutual
/-- Structural source data. Recursive invocation branches are annotations of
the actual retained plans, not assumptions that those plans check successfully. -/
inductive Code [declarationPolicy : DeclarationPolicy] : List Nat → {dependencies : Dependencies} →
    {scope : Scope} → {hints : Hints scope} → Plan dependencies → Forest hints → Type where
  | operations (required : List Requirement) (footprint : RequestFootprint plan required)
      (declared : Declared world (signature plan)) : Code world plan forest
  | selected {hints : Hints scope} {forest : Forest hints}
      {savedHints : Hints captured} {waitingHints : Hints tail}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
      (bounded : contract.dispose = true → PendingWithin world (owners captured) captured)
      (closing : contract.dispose = true → Retained world saved.forClosing (.running waiting)) :
      Code world (.request (effect := effect) (operation := operation)) forest
  | resume {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
      {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
      (cut : OwnerCut owner forest front saved tail)
      (inside : Retained world saved (front.append (.spent (owner := owner) tail)))
      (before : Retained world front (.spent (owner := owner) tail))
      (after : Retained world tail .nil) :
      Code world (.invoke (key := ⟨owner, .resume⟩)) forest
  | dispose {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
      {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
      (cut : OwnerCut owner forest front saved tail)
      (closing : Retained world saved.forClosing (.running (front.append (.spent (owner := owner) tail))))
      (before : Retained world front (.spent (owner := owner) tail))
      (after : Retained world tail .nil) :
      Code world (.invoke (key := ⟨owner, .dispose⟩)) forest
  | sequence (first : Code world before (.plain after forest)) (second : Code world after forest) :
      Code world (.sequence before after) forest
  | choice : Code world first forest → Code world second forest → Code world (.choice first second) forest
  | handler {plans : ClausePlans clauses families}
      (declarations : declarationPolicy.accepts required plans)
      (body : Code world code
        (.handler (effect := effect) (table := table) (families := families) (required := required) forest))
      (bounds : Option (SourceConsumingClauseAnnotations.ClauseBounds plans) := none) :
      Code world (.handler (effect := effect) (table := table) required plans code) forest
  | cleanup (body : Code world code (.cleanup (needs := needs) callback forest))
      (completion : Code world callback (.running forest)) :
      Code world (.cleanup (needs := needs) callback code) forest
  | resource (body : ∀ identity, identity ∉ world →
      Code (world ++ [identity]) (code identity) (.cell (identity := identity) forest)) :
      Code world (.resource code) forest

/-- Retained annotations can now contain free continuation uses at ordinary
code and callback positions, including recursively dormant branches. -/
inductive Retained [declarationPolicy : DeclarationPolicy] : List Nat → {scope outside : Scope} →
    {hints : Hints scope} → {outsideHints : Hints outside} → Forest hints → Forest outsideHints → Type where
  | operations (interfaces : SourceScheduledRetainedInterfaces.Interfaces world forest) :
      Retained world forest outside
  | plain (code : Code world plan (rest.append outside)) (tail : Retained world rest outside) :
      Retained world (.plain plan rest) outside
  | handler {restHints : Hints restScope} {rest : Forest restHints} : Retained world rest outside →
      Retained world (.handler (effect := effect) (table := table) (families := families) (required := required) rest) outside
  | cell : Retained world rest outside → Retained world (.cell (identity := identity) rest) outside
  | cleanup (completion : Code world plan (.running (rest.append outside)))
      (tail : Retained world rest outside) : Retained world (.cleanup (needs := needs) plan rest) outside
  | running : Retained world rest outside → Retained world (.running rest) outside
  | live : Retained world saved (rest.append outside) → Retained world rest outside →
      Retained world (.live (owner := owner) saved rest) outside
  | spent : Retained world rest outside → Retained world (.spent (owner := owner) rest) outside
end

/-- An explicitly annotated installation carries bounds for its actual plans.
Operation-only annotations may omit this metadata; they cannot manufacture a
bounded packet by reading this field. -/
def Code.handlerBounds {world dependencies scope} {hints : Hints scope}
    {plans : ClausePlans clauses families} {code : Plan dependencies} {forest : Forest hints}
    (annotation : Code world (.handler (effect := effect) (table := table) required plans code) forest) :
    Option (SourceConsumingClauseAnnotations.ClauseBounds plans) :=
  match annotation with
  | .operations _ _ _ => none
  | .handler _ _ bounds => bounds

mutual
/-- Validation uses finite primitive checks. Fresh resource binders retain the
existing universal source rule; no claim of an executable whole-program decision
procedure is made for arbitrary resource families. -/
def Code.Valid (outward : List Instance) (actions : Syntax.UsageTickets)
    {world dependencies scope} {hints : Hints scope} {plan : Plan dependencies} {forest : Forest hints}
    (annotation : Code world plan forest) (phases : Phases) : Prop :=
  match annotation with
  | .operations required _ _ => checkRequirements scope required = true
  | .selected (effect := effect) (operation := operation) _ _ closing =>
      SourceDependencyCapture.checkCapture outward scope effect operation = true ∧
      ∀ disposes, (closing disposes).Valid outward actions phases
  | .resume (owner := owner) _ inside before after =>
      (actions owner).any (fun rights => rights.resume) = true ∧ phases owner = .available ∧
      inside.Valid outward actions (spend phases owner) ∧
      before.Valid outward actions (spend phases owner) ∧ after.Valid outward actions (spend phases owner)
  | .dispose (owner := owner) (savedScope := savedScope) _ closing before after =>
      (actions owner).any (fun rights => rights.dispose) = true ∧ phases owner = .available ∧
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true ∧
      closing.Valid outward actions (spend phases owner) ∧
      before.Valid outward actions (spend phases owner) ∧ after.Valid outward actions (spend phases owner)
  | .sequence first second | .choice first second =>
      first.Valid outward actions phases ∧ second.Valid outward actions phases
  | .handler (required := required) _ body _ =>
      checkRequirements scope required = true ∧ body.Valid outward actions phases
  | .cleanup body completion => body.Valid outward actions phases ∧ completion.Valid outward actions phases
  | .resource body => ∀ identity fresh, (body identity fresh).Valid outward actions phases

def Retained.Valid (outward : List Instance) (actions : Syntax.UsageTickets)
    {world scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (phases : Phases) : Prop :=
  match annotation with
  | .operations interfaces => interfaces.check outsideScope = true
  | .plain code tail => code.Valid outward actions phases ∧ tail.Valid outward actions phases
  | .handler (restScope := restScope) (required := required) tail =>
      checkRequirements (restScope.append outsideScope) required = true ∧ tail.Valid outward actions phases
  | .cell tail | .running tail | .spent tail => tail.Valid outward actions phases
  | .cleanup completion tail => completion.Valid outward actions phases ∧ tail.Valid outward actions phases
  | .live saved tail => saved.Valid outward actions phases ∧ tail.Valid outward actions phases
end

omit declarationPolicy in
private theorem permission_of_check {actions : Syntax.UsageTickets} (permission : Syntax.OneShotRights → Bool)
    (checked : (actions owner).any permission = true) :
    ∃ rights, actions owner = some rights ∧ permission rights = true := by
  cases known : actions owner with
  | none => simp [known] at checked
  | some rights => exact ⟨rights, rfl, by simpa only [known, Option.any_some] using checked⟩

section
variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Mutual structural induction compiles every recursive source annotation.
Execution and ownership consequences reuse the established scheduling kernel. -/
theorem compile_all_with (outward : List Instance) (actions : Syntax.UsageTickets)
    (laws : DeclarationLaws declarationPolicy admission certification outward) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (annotation : Code world plan forest) phases,
      annotation.Valid outward actions phases → Local outward actions phases world plan forest) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (annotation : Retained world forest outside) phases,
      annotation.Valid outward actions phases → Pending outward actions phases world forest outside) := by
  constructor
  all_goals first
    | (intro world dependencies scope hints plan forest annotation
       apply Code.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ phases, annotation.Valid outward actions phases → Local outward actions phases world plan forest)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ phases, annotation.Valid outward actions phases → Pending outward actions phases world forest outside)
         (t := annotation))
    | (intro world scope outsideScope hints outsideHints forest outside annotation
       apply Retained.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ phases, annotation.Valid outward actions phases → Local outward actions phases world plan forest)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ phases, annotation.Valid outward actions phases → Pending outward actions phases world forest outside)
         (t := annotation))
  all_goals intros
  all_goals first
    | (rename_i required footprint declared phases checked
       exact (SourceDeclarationPolicyTransport.scheduled_all SourceScheduledChecks.recipePolicy admission
         SourcePlannedChecks.contextualPolicy certification outward actions laws.legacyAdmission laws.legacyCertification).1
         phases _ _ _ (SourceScheduledSourceInterfaces.compile footprint declared checked))
    | (rename_i interfaces phases checked
       exact (SourceDeclarationPolicyTransport.scheduled_all SourceScheduledChecks.recipePolicy admission
         SourcePlannedChecks.contextualPolicy certification outward actions laws.legacyAdmission laws.legacyCertification).2
         phases _ _ _ (interfaces.compile checked))
    | (rename_i cut bounded closing ih phases checked
       exact SourceScheduledFreshRequests.request_from_schedule laws.projected cut
         (SourceDependencyCapture.check_capture_iff.mp checked.1) bounded
         (fun disposes => ih disposes phases (checked.2 disposes)))
    | (rename_i cut inside before after ihInside ihBefore ihAfter phases checked
       obtain ⟨allowed, available, savedOK, frontOK, tailOK⟩ := checked
       obtain ⟨rights, known, permission⟩ := permission_of_check _ allowed
       have savedSchedule := ihInside _ savedOK
       have frontSchedule := ihBefore _ frontOK
       have tailSchedule := ihAfter _ tailOK
       exact SourceScheduledScopedInvocations.resume_from_parts cut known permission available
         savedSchedule frontSchedule tailSchedule
         (SourceScheduledScopedInvocations.pending_resume_iff.mpr
           ⟨savedSchedule, frontSchedule, tailSchedule⟩).compatible)
    | (rename_i cut closing before after ihClosing ihBefore ihAfter phases checked
       obtain ⟨allowed, available, unprotected, route, closingOK, frontOK, tailOK⟩ := checked
       obtain ⟨rights, known, permission⟩ := permission_of_check _ allowed
       have closingSchedule := ihClosing _ closingOK
       have frontSchedule := ihBefore _ frontOK
       have tailSchedule := ihAfter _ tailOK
       exact SourceScheduledScopedInvocations.dispose_from_parts cut known permission available unprotected
         (SourceDependencyCapture.check_closing_iff.mp route) closingSchedule frontSchedule tailSchedule
         (SourceScheduledScopedInvocations.pending_dispose_iff.mpr
           ⟨closingSchedule, frontSchedule, tailSchedule⟩).compatible)
    | (rename_i first second ihFirst ihSecond phases checked
       exact Local.sequence (ihFirst _ checked.1) (ihSecond _ checked.2))
    | (rename_i first second ihFirst ihSecond phases checked
       exact Local.choice (ihFirst _ checked.1) (ihSecond _ checked.2))
    | (rename_i declarations body bounds ih phases checked
       exact Local.handler (laws.admitted declarations) (laws.certified declarations) checked.1 (ih _ checked.2))
    | (rename_i body completion ihBody ihCompletion phases checked
       exact Local.cleanup (ihBody _ checked.1) (ihCompletion _ checked.2))
    | (rename_i body ih phases checked
       exact Local.resource (fun identity fresh => ih identity fresh phases (checked identity fresh)))
    | (rename_i code tail ihCode ihTail phases checked
       exact Pending.plain (ihCode _ checked.1) (ihTail _ checked.2))
    | (rename_i tail ih phases checked
       exact Pending.handler checked.1 (ih _ checked.2))
    | (rename_i tail ih phases checked
       exact Pending.cell (ih _ checked))
    | (rename_i completion tail ihCompletion ihTail phases checked
       exact Pending.cleanup (ihCompletion _ checked.1) (ihTail _ checked.2))
    | (rename_i tail ih phases checked
       exact Pending.running (ih _ checked))
    | (rename_i saved tail ihSaved ihTail phases checked
       exact Pending.live (ihSaved _ checked.1) (ihTail _ checked.2))
    | (rename_i tail ih phases checked
       exact Pending.spent (ih _ checked))

theorem Code.compile_with (laws : DeclarationLaws declarationPolicy admission certification outward) {world dependencies scope} {hints : Hints scope}
    {plan : Plan dependencies} {forest : Forest hints}
    (annotation : Code world plan forest) (checked : annotation.Valid outward actions phases) :
    Local outward actions phases world plan forest :=
  (compile_all_with outward actions laws).1 world plan forest annotation phases checked

theorem Retained.compile_with (laws : DeclarationLaws declarationPolicy admission certification outward) {world scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (checked : annotation.Valid outward actions phases) :
    Pending outward actions phases world forest outside :=
  (compile_all_with outward actions laws).2 world forest outside annotation phases checked

end
end

theorem compile_all (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (annotation : Code world plan forest) phases,
      annotation.Valid outward actions phases → Local outward actions phases world plan forest) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (annotation : Retained world forest outside) phases,
      annotation.Valid outward actions phases → Pending outward actions phases world forest outside) :=
  compile_all_with (declarationPolicy := recipePolicy) (admission := SourceScheduledChecks.recipePolicy)
    (certification := SourcePlannedChecks.contextualPolicy) outward actions (recipeLaws outward)

theorem Code.compile {world dependencies scope} {hints : Hints scope}
    {plan : Plan dependencies} {forest : Forest hints}
    (annotation : Code world plan forest) (checked : annotation.Valid outward actions phases) :
    Local outward actions phases world plan forest :=
  (compile_all outward actions).1 world plan forest annotation phases checked

theorem Retained.compile {world scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (checked : annotation.Valid outward actions phases) :
    Pending outward actions phases world forest outside :=
  (compile_all outward actions).2 world forest outside annotation phases checked

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.compile_all
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.compile
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.compile

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.recipeLaws
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.compile_all_with
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.compile_with
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.compile_with
