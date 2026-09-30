import SourceScheduledCapabilityAnnotations

/-! Separate the recursive interpretation obligations from permissions and
one-shot phases. These are projections of the existing structural source, not
new syntax, target-validity premises, or a replacement admission criterion. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open OwnerPhaseTransitions (Phases spend)

variable [declarationPolicy : DeclarationPolicy]

mutual
/-- Interpretation selection, operation availability and cleanup effects. This
projection takes neither an action map nor a phase map. -/
def Code.InterpretationChecks (outward : List Instance)
    {world dependencies scope} {hints : Hints scope} {plan : Plan dependencies} {forest : Forest hints}
    (source : Code world plan forest) : Prop :=
  match source with
  | .operations required _ _ => checkRequirements scope required = true
  | .selected (effect := effect) (operation := operation) _ _ closing =>
      SourceDependencyCapture.checkCapture outward scope effect operation = true ∧
      ∀ disposes, (closing disposes).InterpretationChecks outward
  | .resume _ inside before after =>
      inside.InterpretationChecks outward ∧ before.InterpretationChecks outward ∧ after.InterpretationChecks outward
  | .dispose (savedScope := savedScope) _ closing before after =>
      SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true ∧
      closing.InterpretationChecks outward ∧ before.InterpretationChecks outward ∧ after.InterpretationChecks outward
  | .sequence first second | .choice first second =>
      first.InterpretationChecks outward ∧ second.InterpretationChecks outward
  | .handler (required := required) _ body _ =>
      checkRequirements scope required = true ∧ body.InterpretationChecks outward
  | .cleanup body completion => body.InterpretationChecks outward ∧ completion.InterpretationChecks outward
  | .resource body => ∀ identity fresh, (body identity fresh).InterpretationChecks outward

def Retained.InterpretationChecks (outward : List Instance)
    {world scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (source : Retained world forest outside) : Prop :=
  match source with
  | .operations interfaces => interfaces.check outsideScope = true
  | .plain code tail => code.InterpretationChecks outward ∧ tail.InterpretationChecks outward
  | .handler (restScope := restScope) (required := required) tail =>
      checkRequirements (restScope.append outsideScope) required = true ∧ tail.InterpretationChecks outward
  | .cell tail | .running tail | .spent tail => tail.InterpretationChecks outward
  | .cleanup completion tail => completion.InterpretationChecks outward ∧ tail.InterpretationChecks outward
  | .live saved tail => saved.InterpretationChecks outward ∧ tail.InterpretationChecks outward
end

mutual
/-- The same source's independent action and consumption check. Each invocation
checks availability before spending its owner in all actual continuation children.
Disposal also requires an unprotected saved capture. -/
def Code.ContinuationChecks (actions : Syntax.UsageTickets)
    {world dependencies scope} {hints : Hints scope} {plan : Plan dependencies} {forest : Forest hints}
    (source : Code world plan forest) (phases : Phases) : Prop :=
  match source with
  | .operations _ _ _ => True
  | .selected _ _ closing => ∀ disposes, (closing disposes).ContinuationChecks actions phases
  | .resume (owner := owner) _ inside before after =>
      (actions owner).any (fun rights => rights.resume) = true ∧ phases owner = .available ∧
      inside.ContinuationChecks actions (spend phases owner) ∧
      before.ContinuationChecks actions (spend phases owner) ∧ after.ContinuationChecks actions (spend phases owner)
  | .dispose (owner := owner) (savedScope := savedScope) _ closing before after =>
      (actions owner).any (fun rights => rights.dispose) = true ∧ phases owner = .available ∧
      savedScope.held = false ∧ closing.ContinuationChecks actions (spend phases owner) ∧
      before.ContinuationChecks actions (spend phases owner) ∧ after.ContinuationChecks actions (spend phases owner)
  | .sequence first second | .choice first second =>
      first.ContinuationChecks actions phases ∧ second.ContinuationChecks actions phases
  | .handler _ body _ => body.ContinuationChecks actions phases
  | .cleanup body completion => body.ContinuationChecks actions phases ∧ completion.ContinuationChecks actions phases
  | .resource body => ∀ identity fresh, (body identity fresh).ContinuationChecks actions phases

def Retained.ContinuationChecks (actions : Syntax.UsageTickets)
    {world scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Retained world forest outside) (phases : Phases) : Prop :=
  match source with
  | .operations _ => True
  | .plain code tail => code.ContinuationChecks actions phases ∧ tail.ContinuationChecks actions phases
  | .handler tail | .cell tail | .running tail | .spent tail => tail.ContinuationChecks actions phases
  | .cleanup completion tail => completion.ContinuationChecks actions phases ∧ tail.ContinuationChecks actions phases
  | .live saved tail => saved.ContinuationChecks actions phases ∧ tail.ContinuationChecks actions phases
end

/-- The two independent projections are exactly the existing validator, for
all source constructors, dormant branches, selected closing families and fresh
resource families. In particular this does not assume any target source check. -/
theorem admission_factors (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (source : Code world plan forest) phases,
      source.Valid outward actions phases ↔ source.InterpretationChecks outward ∧ source.ContinuationChecks actions phases) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (source : Retained world forest outside) phases,
      source.Valid outward actions phases ↔ source.InterpretationChecks outward ∧ source.ContinuationChecks actions phases) := by
  constructor
  all_goals first
    | (intro world dependencies scope hints plan forest source
       apply Code.rec
         (motive_1 := fun world {dependencies scope hints} plan forest source => ∀ phases,
           source.Valid outward actions phases ↔ source.InterpretationChecks outward ∧ source.ContinuationChecks actions phases)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside source => ∀ phases,
           source.Valid outward actions phases ↔ source.InterpretationChecks outward ∧ source.ContinuationChecks actions phases)
         (t := source))
    | (intro world scope outsideScope hints outsideHints forest outside source
       apply Retained.rec
         (motive_1 := fun world {dependencies scope hints} plan forest source => ∀ phases,
           source.Valid outward actions phases ↔ source.InterpretationChecks outward ∧ source.ContinuationChecks actions phases)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside source => ∀ phases,
           source.Valid outward actions phases ↔ source.InterpretationChecks outward ∧ source.ContinuationChecks actions phases)
         (t := source))
  all_goals intros
  all_goals simp_all [Code.Valid, Retained.Valid, Code.InterpretationChecks, Retained.InterpretationChecks,
    Code.ContinuationChecks, Retained.ContinuationChecks, forall_and, and_assoc, and_left_comm, and_comm]

theorem Code.valid_iff_factors {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (source : Code world plan forest) :
    source.Valid outward actions phases ↔ source.InterpretationChecks outward ∧ source.ContinuationChecks actions phases :=
  (admission_factors outward actions).1 _ _ _ source phases

theorem Retained.valid_iff_factors {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (source : Retained world forest outside) :
    source.Valid outward actions phases ↔ source.InterpretationChecks outward ∧ source.ContinuationChecks actions phases :=
  (admission_factors outward actions).2 _ _ _ source phases

section
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Reuse the original compiler after independently checking interpretations
and the recursive one-shot uses. No target Local judgment is an input. -/
theorem Code.compile_factors
    (laws : DeclarationLaws declarationPolicy admission certification outward)
    {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (source : Code world plan forest)
    (interpretations : source.InterpretationChecks outward)
    (continuations : source.ContinuationChecks actions phases) :
    SourceScheduledChecks.Local outward actions phases world plan forest :=
  source.compile_with laws (source.valid_iff_factors.mpr ⟨interpretations, continuations⟩)

theorem Retained.compile_factors
    (laws : DeclarationLaws declarationPolicy admission certification outward)
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Retained world forest outside)
    (interpretations : source.InterpretationChecks outward)
    (continuations : source.ContinuationChecks actions phases) :
    SourceScheduledChecks.Pending outward actions phases world forest outside :=
  source.compile_with laws (source.valid_iff_factors.mpr ⟨interpretations, continuations⟩)
end

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.admission_factors
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.valid_iff_factors
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.valid_iff_factors
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.compile_factors
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.compile_factors
