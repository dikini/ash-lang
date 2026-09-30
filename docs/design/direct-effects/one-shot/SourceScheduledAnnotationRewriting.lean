import SourcePlanRewriting
import SourceScheduledCapabilityAnnotations

/-! Retain source scheduling annotations through signature-preserving changes
of literal clause witnesses. Permission and phase validation are unchanged. -/
namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourcePlanRewriting (ClauseMap)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

def Interfaces.rewrite (change : ClauseMap) {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) : Interfaces world (change.forest forest) :=
  match interfaces with
  | .nil => .nil
  | .plain rest required footprint declared next =>
      .plain (change.forest rest) required (footprint.congr (change.plan_signature _).symm)
        (declared.congr (change.plan_signature _).symm) (next.rewrite change)
  | .handler rest next => .handler (change.forest rest) (next.rewrite change)
  | .cell next => .cell (next.rewrite change)
  | .cleanup rest required footprint declared next =>
      .cleanup (change.forest rest) required (footprint.congr (change.plan_signature _).symm)
        (declared.congr (change.plan_signature _).symm) (next.rewrite change)
  | .running next => .running (next.rewrite change)
  | .live rest saved next => .live (change.forest rest) (saved.rewrite change) (next.rewrite change)
  | .spent next => .spent (next.rewrite change)

theorem Interfaces.check_rewrite (change : ClauseMap) {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) :
    (interfaces.rewrite change).check outside = interfaces.check outside := by
  induction interfaces generalizing outside <;> simp_all [Interfaces.rewrite, Interfaces.check] <;> rfl

end Ash.OneShot.SourceScheduledRetainedInterfaces

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourcePlanRewriting (ClauseMap)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)

def Code.cast {first second : Plan dependencies} {hints : Hints scope} {before after : Forest hints}
    (planSame : first = second) (forestSame : before = after) (annotation : Code world first before) :
    Code world second after := planSame ▸ forestSame ▸ annotation

def Retained.cast {hints : Hints scope} {outsideHints : Hints outsideScope}
    {first second : Forest hints} {before after : Forest outsideHints}
    (forestSame : first = second) (outsideSame : before = after) (annotation : Retained world first before) :
    Retained world second after := forestSame ▸ outsideSame ▸ annotation

theorem Code.valid_cast {first second : Plan dependencies} {hints : Hints scope} {before after : Forest hints}
    (planSame : first = second) (forestSame : before = after) (annotation : Code world first before) :
    (annotation.cast planSame forestSame).Valid outward actions phases ↔ annotation.Valid outward actions phases := by
  cases planSame; cases forestSame; rfl

theorem Retained.valid_cast {hints : Hints scope} {outsideHints : Hints outsideScope}
    {first second : Forest hints} {before after : Forest outsideHints}
    (forestSame : first = second) (outsideSame : before = after) (annotation : Retained world first before) :
    (annotation.cast forestSame outsideSame).Valid outward actions phases ↔ annotation.Valid outward actions phases := by
  cases forestSame; cases outsideSame; rfl

mutual
def Code.rewrite (change : ClauseMap) {world dependencies scope} {hints : Hints scope}
    {plan : Plan dependencies} {forest : Forest hints} (annotation : Code world plan forest) :
    Code world (change.plan plan) (change.forest forest) :=
  match annotation with
  | .operations required footprint declared =>
      .operations required (footprint.congr (change.plan_signature _).symm)
        (declared.congr (change.plan_signature _).symm)
  | .selected (saved := saved) cut bounded closing =>
      .selected (change.cut cut) bounded
        (fun disposes => (closing disposes |>.rewrite change).cast (change.forest_closing saved) rfl)
  | .resume (front := front) cut inside before after =>
      .resume (change.owner_cut cut)
        ((inside.rewrite change).cast rfl (change.forest_append front _))
        (before.rewrite change) (after.rewrite change)
  | .dispose (front := front) (saved := saved) cut closing before after =>
      .dispose (change.owner_cut cut)
        ((closing.rewrite change).cast (change.forest_closing saved)
          (congrArg Forest.running (change.forest_append front _)))
        (before.rewrite change) (after.rewrite change)
  | .sequence first second => .sequence (first.rewrite change) (second.rewrite change)
  | .choice first second => .choice (first.rewrite change) (second.rewrite change)
  | .handler (plans := plans) declarations body bounds =>
      .handler (declarations.signature_congr (change.preserves plans).symm) (body.rewrite change)
        (bounds.map (fun recorded => recorded.reindex (change.apply plans).2))
  | .cleanup body completion => .cleanup (body.rewrite change) (completion.rewrite change)
  | .resource body => .resource (fun identity fresh => (body identity fresh).rewrite change)

def Retained.rewrite (change : ClauseMap) {world scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (annotation : Retained world forest outside) :
    Retained world (change.forest forest) (change.forest outside) :=
  match annotation with
  | .operations interfaces => .operations (interfaces.rewrite change)
  | .plain (rest := rest) code tail =>
      .plain ((code.rewrite change).cast rfl (change.forest_append rest outside)) (tail.rewrite change)
  | .handler tail => .handler (tail.rewrite change)
  | .cell tail => .cell (tail.rewrite change)
  | .cleanup (rest := rest) completion tail =>
      .cleanup ((completion.rewrite change).cast rfl (congrArg Forest.running (change.forest_append rest outside)))
        (tail.rewrite change)
  | .running tail => .running (tail.rewrite change)
  | .live (rest := rest) saved tail =>
      .live ((saved.rewrite change).cast rfl (change.forest_append rest outside)) (tail.rewrite change)
  | .spent tail => .spent (tail.rewrite change)
end

/-- Validation is invariant under rewriting, including recursive outside-owner
uses. The equivalence preserves rejection as well as successful admission. -/
theorem rewrite_valid_all (change : ClauseMap) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (annotation : Code world plan forest) outward actions phases,
      (annotation.rewrite change).Valid outward actions phases ↔ annotation.Valid outward actions phases) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (annotation : Retained world forest outside) outward actions phases,
      (annotation.rewrite change).Valid outward actions phases ↔ annotation.Valid outward actions phases) := by
  constructor
  all_goals first
    | (intro world dependencies scope hints plan forest annotation
       apply Code.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ outward actions phases, (annotation.rewrite change).Valid outward actions phases ↔ annotation.Valid outward actions phases)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ outward actions phases, (annotation.rewrite change).Valid outward actions phases ↔ annotation.Valid outward actions phases)
         (t := annotation))
    | (intro world scope outsideScope hints outsideHints forest outside annotation
       apply Retained.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ outward actions phases, (annotation.rewrite change).Valid outward actions phases ↔ annotation.Valid outward actions phases)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ outward actions phases, (annotation.rewrite change).Valid outward actions phases ↔ annotation.Valid outward actions phases)
         (t := annotation))
  all_goals intros
  all_goals simp only [Code.rewrite, Retained.rewrite, Code.Valid, Retained.Valid]
  all_goals simp_all only [Code.valid_cast, Retained.valid_cast,
    SourceScheduledRetainedInterfaces.Interfaces.check_rewrite]

theorem Code.valid_rewrite (change : ClauseMap) {hints : Hints scope} {plan : Plan dependencies} {forest : Forest hints}
    (annotation : Code world plan forest) :
    (annotation.rewrite change).Valid outward actions phases ↔ annotation.Valid outward actions phases :=
  (rewrite_valid_all change).1 world plan forest annotation outward actions phases

theorem Retained.valid_rewrite (change : ClauseMap) {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (annotation : Retained world forest outside) :
    (annotation.rewrite change).Valid outward actions phases ↔ annotation.Valid outward actions phases :=
  (rewrite_valid_all change).2 world forest outside annotation outward actions phases

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_rewrite
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.valid_cast
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.valid_cast
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.rewrite_valid_all
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.valid_rewrite
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.valid_rewrite
