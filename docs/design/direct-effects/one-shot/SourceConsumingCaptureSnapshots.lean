import SourceConsumingBoundGeneration
import SourceBoundCapture

/-! Construct capture bound metadata independently of continuation scheduling.
The selected declaration supplies current-plan bounds; the actual cut moves
existing pending bounds. No restriction on the captured source shape is needed. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot Captured)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- The actual selected declaration yields admitted current-plan metadata.
This uses its recorded nested bounds, without projecting a reconstructed
capability annotation or inspecting any captured continuation. -/
theorem Bounded.selected_plan_bounds
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
    (selected : SourcePlannedRecipeDeclarations.Selected operation held plans parameter binder code bodies) :
    ∃ current : Annotation world (bodies owner), current.Admitted := by
  induction selected generalizing required with
  | ordinary => cases bounded with
    | cons ordinary protectedMode rest => cases ordinary with
      | available source nested => exact ⟨_, (nested owner).boundAnnotation_admitted⟩
  | protectedMode => cases bounded with
    | cons ordinary protectedMode rest => cases protectedMode with
      | available source nested => exact ⟨_, (nested owner).boundAnnotation_admitted⟩
  | pass different next ih => cases bounded with
    | cons ordinary protectedMode rest => exact ih rest

/-- Arbitrary captured forests retain their actual bound data. The result
has the exact selected clause plan and exact saved/waiting source pieces.
Scheduling validity remains an independent obligation. -/
theorem Bounded.capture_snapshot
    (before : Snapshot world) (beforeAdmitted : before.Admitted)
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes before.forest saved waiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies) :
    ∃ current : Annotation world (bodies owner),
    ∃ pending : SourceBoundSnapshots.Retained world (.live (owner := owner) saved waiting),
      Captured owner before ⟨_, bodies owner, current, _, _, .live (owner := owner) saved waiting, pending⟩ ∧
      (⟨_, bodies owner, current, _, _, .live (owner := owner) saved waiting, pending⟩ : Snapshot world).Admitted := by
  obtain ⟨current, currentAdmitted⟩ := bounded.selected_plan_bounds (owner := owner) selected
  obtain ⟨pending, moved⟩ := SourceBoundSnapshots.capture_snapshot before cut current (owner := owner)
  exact ⟨current, pending, moved, moved.admitted beforeAdmitted currentAdmitted⟩

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.selected_plan_bounds
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.capture_snapshot
