import SourceScheduledCapabilityAnnotations
import SourceScheduledInterfaceWorld
import SourceBoundResources

/-! Structural resource-world extension of exact capability annotations.
Existing declaration, interface and pending-owner weakening supply the atomic
cases. All code, cuts, clause bounds and physical forests retain their identity. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)

variable [DeclarationPolicy]

mutual
/-- Extend the declaration world without reconstructing source annotations from
successful scheduling. Future resource bodies use the existing subset law. -/
def Code.world_weaken {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (annotation : Code world plan forest) (larger : world ⊆ next) : Code next plan forest :=
  match annotation with
  | .operations required footprint declared => .operations required footprint (declared.world_weaken larger)
  | .selected cut bounded closing =>
      .selected cut (fun disposes => (bounded disposes).world_weaken larger)
        (fun disposes => (closing disposes).world_weaken larger)
  | .resume cut inside before after =>
      .resume cut (inside.world_weaken larger) (before.world_weaken larger) (after.world_weaken larger)
  | .dispose cut closing before after =>
      .dispose cut (closing.world_weaken larger) (before.world_weaken larger) (after.world_weaken larger)
  | .sequence first second => .sequence (first.world_weaken larger) (second.world_weaken larger)
  | .choice first second => .choice (first.world_weaken larger) (second.world_weaken larger)
  | .handler declared body bounds => .handler declared (body.world_weaken larger) bounds
  | .cleanup body completion => .cleanup (body.world_weaken larger) (completion.world_weaken larger)
  | .resource body => .resource (fun identity fresh =>
      (body identity (fun member => fresh (larger member))).world_weaken
        (ScopedExpressions.append_subset larger (List.Subset.refl _)))

def Retained.world_weaken {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (larger : world ⊆ next) : Retained next forest outside :=
  match annotation with
  | .operations interfaces => .operations (interfaces.world_weaken larger)
  | .plain code tail => .plain (code.world_weaken larger) (tail.world_weaken larger)
  | .handler tail => .handler (tail.world_weaken larger)
  | .cell tail => .cell (tail.world_weaken larger)
  | .cleanup completion tail => .cleanup (completion.world_weaken larger) (tail.world_weaken larger)
  | .running tail => .running (tail.world_weaken larger)
  | .live saved tail => .live (saved.world_weaken larger) (tail.world_weaken larger)
  | .spent tail => .spent (tail.world_weaken larger)
end

/-- Validity follows the same annotations into a larger world. No target check
or operation capability is added as a premise. -/
theorem weaken_annotation_world (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (annotation : Code world plan forest) next (larger : world ⊆ next) phases,
      annotation.Valid outward actions phases → (annotation.world_weaken larger).Valid outward actions phases) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (annotation : Retained world forest outside)
      next (larger : world ⊆ next) phases,
      annotation.Valid outward actions phases → (annotation.world_weaken larger).Valid outward actions phases) := by
  constructor
  all_goals first
    | (intro world dependencies scope hints plan forest annotation
       apply Code.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ next (larger : world ⊆ next) phases, annotation.Valid outward actions phases →
             (annotation.world_weaken larger).Valid outward actions phases)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ next (larger : world ⊆ next) phases, annotation.Valid outward actions phases →
             (annotation.world_weaken larger).Valid outward actions phases)
         (t := annotation))
    | (intro world scope outsideScope hints outsideHints forest outside annotation
       apply Retained.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ next (larger : world ⊆ next) phases, annotation.Valid outward actions phases →
             (annotation.world_weaken larger).Valid outward actions phases)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ next (larger : world ⊆ next) phases, annotation.Valid outward actions phases →
             (annotation.world_weaken larger).Valid outward actions phases)
         (t := annotation))
  all_goals intros
  all_goals first
    | (rename_i required footprint declared next larger phases checked; exact checked)
    | (rename_i interfaces next larger phases checked
       simpa only [Retained.world_weaken, Retained.Valid,
         SourceScheduledRetainedInterfaces.Interfaces.check_world_weaken] using checked)
    | (rename_i cut bounded closing ih next larger phases checked
       exact ⟨checked.1, fun disposes => ih disposes next larger phases (checked.2 disposes)⟩)
    | (rename_i cut inside before after ihInside ihBefore ihAfter next larger phases checked
       exact ⟨checked.1, checked.2.1, ihInside _ larger _ checked.2.2.1,
         ihBefore _ larger _ checked.2.2.2.1, ihAfter _ larger _ checked.2.2.2.2⟩)
    | (rename_i cut closing before after ihClosing ihBefore ihAfter next larger phases checked
       exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1,
         ihClosing _ larger _ checked.2.2.2.2.1,
         ihBefore _ larger _ checked.2.2.2.2.2.1, ihAfter _ larger _ checked.2.2.2.2.2.2⟩)
    | (rename_i first second ihFirst ihSecond next larger phases checked
       exact ⟨ihFirst _ larger _ checked.1, ihSecond _ larger _ checked.2⟩)
    | (rename_i declared body bounds ih next larger phases checked
       exact ⟨checked.1, ih _ larger _ checked.2⟩)
    | (rename_i body ih next larger phases checked
       exact fun identity fresh => ih identity (fun member => fresh (larger member)) _
         (ScopedExpressions.append_subset larger (List.Subset.refl _)) phases
         (checked identity (fun member => fresh (larger member))))
    | (rename_i tail ih next larger phases checked; exact ⟨checked.1, ih _ larger _ checked.2⟩)
    | (rename_i tail ih next larger phases checked; exact ih _ larger _ checked)

theorem Code.world_weaken_valid {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (annotation : Code world plan forest) (larger : world ⊆ next) (checked : annotation.Valid outward actions phases) :
    (annotation.world_weaken larger).Valid outward actions phases :=
  (weaken_annotation_world outward actions).1 _ _ _ annotation _ larger phases checked

theorem Retained.world_weaken_valid {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (larger : world ⊆ next) (checked : annotation.Valid outward actions phases) :
    (annotation.world_weaken larger).Valid outward actions phases :=
  (weaken_annotation_world outward actions).2 _ _ _ annotation _ larger phases checked

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.weaken_annotation_world
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.world_weaken_valid
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.world_weaken_valid
