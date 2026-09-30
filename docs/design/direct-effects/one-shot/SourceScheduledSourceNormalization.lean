import SourceScheduledOperationExpansion

/-! Normalize source annotation spines before contextual rechecking. The
actual plans, forests, declaration bounds, owner rights and phases stay fixed.
Only compact absent metadata is expanded along its existing syntax. -/
namespace Ash.OneShot.SourceBoundSnapshots

def Retained.normalize {world scope} {hints : SourceContextualHints.Hints scope}
    {forest : SourceRetainedPlans.Forest hints} (bounds : Retained world forest) : Retained world forest :=
  match bounds with
  | .nil => .nil
  | .plain code tail => .plain code.normalize tail.normalize
  | .handler tail => .handler tail.normalize
  | .cell tail => .cell tail.normalize
  | .cleanup code tail => .cleanup code.normalize tail.normalize
  | .running tail => .running tail.normalize
  | .live saved tail => .live saved.normalize tail.normalize
  | .spent tail => .spent tail.normalize

theorem Retained.normalize_idempotent {bounds : Retained world forest} :
    bounds.normalize.normalize = bounds.normalize := by
  induction bounds <;> simp_all only [Retained.normalize, SourcePlanBounds.Annotation.normalize_idempotent]

variable [SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem Retained.Admitted.normalize {bounds : Retained world forest}
    (ready : bounds.Admitted) : bounds.normalize.Admitted := by
  induction ready with
  | nil => exact .nil
  | plain code tail ih => exact .plain code.normalize ih
  | handler tail ih => exact .handler ih
  | cell tail ih => exact .cell ih
  | cleanup code tail ih => exact .cleanup code.normalize ih
  | running tail ih => exact .running ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourcePlanBounds (ofCode)
open SourceBoundSnapshots.Retained (ofCapability)

variable [declarations : DeclarationPolicy]

/-- Expand compact retained interfaces using their existing positional finite
checks. Each current plan uses the operation expansion proved above. -/
theorem expand_retained_interfaces
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (interfaces : Interfaces world forest) (ready : interfaces.check outsideScope = true) :
    ∃ annotation : Retained world forest outside,
      annotation.Valid outward actions phases ∧
      ofCapability annotation = (SourceBoundSnapshots.Retained.absent forest).normalize ∧ annotation.Expanded := by
  induction interfaces generalizing outsideScope with
  | nil => exact ⟨.operations .nil, rfl, rfl, True.intro⟩
  | plain rest required footprint declared tail ih =>
      obtain ⟨currentReady, tailReady⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨code, codeReady, codeBounds, codeExpanded⟩ := expand_operations_signature legacy footprint rfl declared currentReady
      obtain ⟨remaining, remainingReady, remainingBounds, remainingExpanded⟩ := ih tailReady
      exact ⟨.plain code remaining, ⟨codeReady, remainingReady⟩,
        (congrArg (fun bounds => SourceBoundSnapshots.Retained.plain bounds (ofCapability remaining)) codeBounds).trans
          (congrArg (SourceBoundSnapshots.Retained.plain _) remainingBounds), ⟨codeExpanded, remainingExpanded⟩⟩
  | handler rest tail ih =>
      obtain ⟨supplied, tailReady⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨remaining, remainingReady, remainingBounds, remainingExpanded⟩ := ih tailReady
      exact ⟨.handler remaining, ⟨supplied, remainingReady⟩,
        congrArg SourceBoundSnapshots.Retained.handler remainingBounds, remainingExpanded⟩
  | cell tail ih =>
      obtain ⟨remaining, remainingReady, remainingBounds, remainingExpanded⟩ := ih ready
      exact ⟨.cell remaining, remainingReady, congrArg SourceBoundSnapshots.Retained.cell remainingBounds, remainingExpanded⟩
  | cleanup rest required footprint declared tail ih =>
      obtain ⟨currentReady, tailReady⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨code, codeReady, codeBounds, codeExpanded⟩ := expand_operations_signature legacy footprint rfl declared currentReady
      obtain ⟨remaining, remainingReady, remainingBounds, remainingExpanded⟩ := ih tailReady
      exact ⟨.cleanup code remaining, ⟨codeReady, remainingReady⟩,
        (congrArg (fun bounds => SourceBoundSnapshots.Retained.cleanup bounds (ofCapability remaining)) codeBounds).trans
          (congrArg (SourceBoundSnapshots.Retained.cleanup _) remainingBounds), ⟨codeExpanded, remainingExpanded⟩⟩
  | running tail ih =>
      obtain ⟨remaining, remainingReady, remainingBounds, remainingExpanded⟩ := ih ready
      exact ⟨.running remaining, remainingReady, congrArg SourceBoundSnapshots.Retained.running remainingBounds, remainingExpanded⟩
  | live rest saved tail ihSaved ihTail =>
      obtain ⟨savedReady, tailReady⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨inside, insideReady, insideBounds, insideExpanded⟩ := ihSaved savedReady
      obtain ⟨remaining, remainingReady, remainingBounds, remainingExpanded⟩ := ihTail tailReady
      exact ⟨.live inside remaining, ⟨insideReady, remainingReady⟩,
        (congrArg (fun bounds => SourceBoundSnapshots.Retained.live bounds (ofCapability remaining)) insideBounds).trans
          (congrArg (SourceBoundSnapshots.Retained.live _) remainingBounds), ⟨insideExpanded, remainingExpanded⟩⟩
  | spent tail ih =>
      obtain ⟨remaining, remainingReady, remainingBounds, remainingExpanded⟩ := ih ready
      exact ⟨.spent remaining, remainingReady, congrArg SourceBoundSnapshots.Retained.spent remainingBounds, remainingExpanded⟩

/-- Mutual normalization follows the existing Code/Retained grammar. The
original validity supplies each permission and each phase after consumption;
normalization neither creates a use nor moves a control delimiter. -/
theorem normalize_all (outward : List Instance) (actions : Syntax.UsageTickets)
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (source : Code world plan forest) phases, source.Valid outward actions phases →
      ∃ annotation : Code world plan forest, annotation.Valid outward actions phases ∧
        ofCode annotation = (ofCode source).normalize ∧ annotation.Expanded) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (source : Retained world forest outside) phases,
      source.Valid outward actions phases →
      ∃ annotation : Retained world forest outside, annotation.Valid outward actions phases ∧
        ofCapability annotation = (ofCapability source).normalize ∧ annotation.Expanded) := by
  constructor
  all_goals first
    | (intro world dependencies scope hints plan forest source
       apply Code.rec
         (motive_1 := fun world {dependencies scope hints} plan forest source =>
           ∀ phases, source.Valid outward actions phases →
             ∃ annotation : Code world plan forest, annotation.Valid outward actions phases ∧
               ofCode annotation = (ofCode source).normalize ∧ annotation.Expanded)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside source =>
           ∀ phases, source.Valid outward actions phases →
             ∃ annotation : Retained world forest outside, annotation.Valid outward actions phases ∧
               ofCapability annotation = (ofCapability source).normalize ∧ annotation.Expanded)
         (t := source))
    | (intro world scope outsideScope hints outsideHints forest outside source
       apply Retained.rec
         (motive_1 := fun world {dependencies scope hints} plan forest source =>
           ∀ phases, source.Valid outward actions phases →
             ∃ annotation : Code world plan forest, annotation.Valid outward actions phases ∧
               ofCode annotation = (ofCode source).normalize ∧ annotation.Expanded)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside source =>
           ∀ phases, source.Valid outward actions phases →
             ∃ annotation : Retained world forest outside, annotation.Valid outward actions phases ∧
               ofCapability annotation = (ofCapability source).normalize ∧ annotation.Expanded)
         (t := source))
  all_goals intros
  all_goals first
    | (rename_i required footprint declared phases ready
       exact expand_operations_signature legacy footprint rfl declared ready)
    | (rename_i interfaces phases ready
       exact expand_retained_interfaces legacy interfaces ready)
    | (rename_i cut bounded closing ih phases ready
       have generated := fun disposes => ih disposes phases (ready.2 disposes)
       exact ⟨.selected cut bounded (fun disposes => Classical.choose (generated disposes)),
         ⟨ready.1, fun disposes => (Classical.choose_spec (generated disposes)).1⟩, rfl,
         fun disposes => (Classical.choose_spec (generated disposes)).2.2⟩)
    | (rename_i cut inside before after ihInside ihBefore ihAfter phases ready
       obtain ⟨inside, insideReady, _, insideExpanded⟩ := ihInside _ ready.2.2.1
       obtain ⟨before, beforeReady, _, beforeExpanded⟩ := ihBefore _ ready.2.2.2.1
       obtain ⟨after, afterReady, _, afterExpanded⟩ := ihAfter _ ready.2.2.2.2
       exact ⟨.resume cut inside before after, ⟨ready.1, ready.2.1, insideReady, beforeReady, afterReady⟩, rfl,
         ⟨insideExpanded, beforeExpanded, afterExpanded⟩⟩)
    | (rename_i cut closing before after ihClosing ihBefore ihAfter phases ready
       obtain ⟨closing, closingReady, _, closingExpanded⟩ := ihClosing _ ready.2.2.2.2.1
       obtain ⟨before, beforeReady, _, beforeExpanded⟩ := ihBefore _ ready.2.2.2.2.2.1
       obtain ⟨after, afterReady, _, afterExpanded⟩ := ihAfter _ ready.2.2.2.2.2.2
       exact ⟨.dispose cut closing before after,
         ⟨ready.1, ready.2.1, ready.2.2.1, ready.2.2.2.1, closingReady, beforeReady, afterReady⟩, rfl,
         ⟨closingExpanded, beforeExpanded, afterExpanded⟩⟩)
    | (rename_i first second ihFirst ihSecond phases ready
       obtain ⟨first, firstReady, firstBounds, firstExpanded⟩ := ihFirst _ ready.1
       obtain ⟨second, secondReady, secondBounds, secondExpanded⟩ := ihSecond _ ready.2
       refine ⟨.sequence first second, ⟨firstReady, secondReady⟩, ?_, ⟨firstExpanded, secondExpanded⟩⟩
       exact (congrArg (fun bounds => SourcePlanBounds.Annotation.sequence bounds (ofCode second)) firstBounds).trans
         (congrArg (SourcePlanBounds.Annotation.sequence _) secondBounds))
    | (rename_i first second ihFirst ihSecond phases ready
       obtain ⟨first, firstReady, firstBounds, firstExpanded⟩ := ihFirst _ ready.1
       obtain ⟨second, secondReady, secondBounds, secondExpanded⟩ := ihSecond _ ready.2
       refine ⟨.choice first second, ⟨firstReady, secondReady⟩, ?_, ⟨firstExpanded, secondExpanded⟩⟩
       exact (congrArg (fun bounds => SourcePlanBounds.Annotation.choice bounds (ofCode second)) firstBounds).trans
         (congrArg (SourcePlanBounds.Annotation.choice _) secondBounds))
    | (rename_i declared body bounds ih phases ready
       obtain ⟨body, bodyReady, bodyBounds, bodyExpanded⟩ := ih _ ready.2
       exact ⟨.handler declared body bounds, ⟨ready.1, bodyReady⟩,
         congrArg (SourcePlanBounds.Annotation.handler bounds) bodyBounds, bodyExpanded⟩)
    | (rename_i body completion ihBody ihCompletion phases ready
       obtain ⟨body, bodyReady, bodyBounds, bodyExpanded⟩ := ihBody _ ready.1
       obtain ⟨completion, completionReady, completionBounds, completionExpanded⟩ := ihCompletion _ ready.2
       refine ⟨.cleanup body completion, ⟨bodyReady, completionReady⟩, ?_, ⟨bodyExpanded, completionExpanded⟩⟩
       exact (congrArg (fun bounds => SourcePlanBounds.Annotation.cleanup bounds (ofCode completion)) bodyBounds).trans
         (congrArg (SourcePlanBounds.Annotation.cleanup _) completionBounds))
    | (rename_i body ih phases ready
       have generated := fun identity fresh => ih identity fresh phases (ready identity fresh)
       refine ⟨.resource (fun identity fresh => Classical.choose (generated identity fresh)),
         (fun identity fresh => (Classical.choose_spec (generated identity fresh)).1), ?_,
         (fun identity fresh => (Classical.choose_spec (generated identity fresh)).2.2)⟩
       simp only [ofCode, SourcePlanBounds.Annotation.normalize]
       congr 1
       funext identity fresh
       exact (Classical.choose_spec (generated identity fresh)).2.1)
    | (rename_i code tail ihCode ihTail phases ready
       obtain ⟨code, codeReady, codeBounds, codeExpanded⟩ := ihCode _ ready.1
       obtain ⟨tail, tailReady, tailBounds, tailExpanded⟩ := ihTail _ ready.2
       refine ⟨.plain code tail, ⟨codeReady, tailReady⟩, ?_, ⟨codeExpanded, tailExpanded⟩⟩
       exact (congrArg (fun bounds => SourceBoundSnapshots.Retained.plain bounds (ofCapability tail)) codeBounds).trans
         (congrArg (SourceBoundSnapshots.Retained.plain _) tailBounds))
    | (rename_i tail ih phases ready
       obtain ⟨tail, tailReady, tailBounds, tailExpanded⟩ := ih _ ready.2
       exact ⟨.handler tail, ⟨ready.1, tailReady⟩, congrArg SourceBoundSnapshots.Retained.handler tailBounds, tailExpanded⟩)
    | (rename_i tail ih phases ready
       obtain ⟨tail, tailReady, tailBounds, tailExpanded⟩ := ih _ ready
       exact ⟨.cell tail, tailReady, congrArg SourceBoundSnapshots.Retained.cell tailBounds, tailExpanded⟩)
    | (rename_i completion tail ihCompletion ihTail phases ready
       obtain ⟨completion, completionReady, completionBounds, completionExpanded⟩ := ihCompletion _ ready.1
       obtain ⟨tail, tailReady, tailBounds, tailExpanded⟩ := ihTail _ ready.2
       refine ⟨.cleanup completion tail, ⟨completionReady, tailReady⟩, ?_, ⟨completionExpanded, tailExpanded⟩⟩
       exact (congrArg (fun bounds => SourceBoundSnapshots.Retained.cleanup bounds (ofCapability tail)) completionBounds).trans
         (congrArg (SourceBoundSnapshots.Retained.cleanup _) tailBounds))
    | (rename_i tail ih phases ready
       obtain ⟨tail, tailReady, tailBounds, tailExpanded⟩ := ih _ ready
       exact ⟨.running tail, tailReady, congrArg SourceBoundSnapshots.Retained.running tailBounds, tailExpanded⟩)
    | (rename_i saved tail ihSaved ihTail phases ready
       obtain ⟨saved, savedReady, savedBounds, savedExpanded⟩ := ihSaved _ ready.1
       obtain ⟨tail, tailReady, tailBounds, tailExpanded⟩ := ihTail _ ready.2
       refine ⟨.live saved tail, ⟨savedReady, tailReady⟩, ?_, ⟨savedExpanded, tailExpanded⟩⟩
       exact (congrArg (fun bounds => SourceBoundSnapshots.Retained.live bounds (ofCapability tail)) savedBounds).trans
         (congrArg (SourceBoundSnapshots.Retained.live _) tailBounds))
    | (rename_i tail ih phases ready
       obtain ⟨tail, tailReady, tailBounds, tailExpanded⟩ := ih _ ready
       exact ⟨.spent tail, tailReady, congrArg SourceBoundSnapshots.Retained.spent tailBounds, tailExpanded⟩)

theorem Code.normalize
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    {source : Code world plan forest} (ready : source.Valid outward actions phases) :
    ∃ annotation : Code world plan forest, annotation.Valid outward actions phases ∧
      ofCode annotation = (ofCode source).normalize ∧ annotation.Expanded :=
  (normalize_all outward actions legacy).1 _ _ _ _ _ ready

theorem Retained.normalize
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    {source : Retained world forest outside} (ready : source.Valid outward actions phases) :
    ∃ annotation : Retained world forest outside, annotation.Valid outward actions phases ∧
      ofCapability annotation = (ofCapability source).normalize ∧ annotation.Expanded :=
  (normalize_all outward actions legacy).2 _ _ _ _ _ ready

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Admitted.normalize
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.expand_retained_interfaces
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.normalize_all
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.normalize
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.normalize

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.normalize_idempotent
