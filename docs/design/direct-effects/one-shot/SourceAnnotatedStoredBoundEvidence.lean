import SourceAnnotatedStoredRuntimeCapture
import SourceConsumingBoundGeneration
import SourceBoundCapture

/-! A checked bounded capture generates its actual clause annotation and the
admitted snapshot carried through allocation. Exact cut uniqueness reuses the
single supplied finite capture check for the allocator's selected witness. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)


/-- Evidence about the selected clause plan and forest, independent of its
later contract refinement or payload substitution. -/
def GeneratedCapture (before : Snapshot world) (owner : Nat) : SourceAnnotatedAllocationData.ClauseEvidence :=
  fun plan forest =>
    ∃ annotation : SourceScheduledCapabilityAnnotations.Code world plan forest,
    ∃ pending : Retained world forest,
      Captured owner before ⟨_, plan, SourcePlanBounds.ofCode annotation, _, _, forest, pending⟩ ∧
      (⟨_, plan, SourcePlanBounds.ofCode annotation, _, _, forest, pending⟩ : Snapshot world).Admitted

/-- Generate annotation and requirements for the same selected plan. The
existing finite check and exact cut determine every witness used below. -/
theorem bounded_capture_requirements
    (snapshot : Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : SourceConsumingClauseAnnotations.Declarations world plans}
    {bounds : SourceConsumingClauseAnnotations.ClauseBounds plans}
    (bounded : SourceConsumingClauseAnnotations.Bounded bounds annotations required)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (source : SourceConsumingCaptureInput.Source world snapshot.forest saved waiting)
    (sourceCut : SourceScheduledNeutral.Cut requested operation offered modes snapshot.forest saved waiting)
    (checked : source.Check outward actions phases owner bounds code.requiredActions sourceCut closeOutside)
    (supplied : SourceContextualHints.checkRequirements waitingScope required = true)
    {actualSavedHints : Hints actualSavedScope} {actualWaitingHints : Hints actualWaitingScope}
    {actualSaved : Forest actualSavedHints} {actualWaiting : Forest actualWaitingHints}
    (actualCut : SourceScheduledNeutral.Cut requested operation offered modes snapshot.forest actualSaved actualWaiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation actualSavedScope.held plans parameter binder code bodies) :
    SourceScheduledRequirements.Satisfied outward (actions.insert owner code.requiredActions)
      (OwnerPhaseTransitions.introduce phases owner) world (bodies owner) (.live (owner := owner) actualSaved actualWaiting) ∧
    GeneratedCapture snapshot owner (bodies owner) (.live (owner := owner) actualSaved actualWaiting) := by
  cases Option.some.inj (sourceCut.erase.lookup.symm.trans actualCut.erase.lookup)
  obtain ⟨rfl, rfl⟩ := sourceCut.erase.unique actualCut.erase.hints
  obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (sourceCut.forest.symm.trans actualCut.forest))
  obtain ⟨annotation, valid, admitted⟩ := source.capture_annotation_admitted bounded actualCut selected checked supplied
  obtain ⟨pending, moved⟩ := capture_snapshot snapshot actualCut (SourcePlanBounds.ofCode annotation) (owner := owner)
  exact ⟨SourceScheduledRequirements.necessary (annotation.compile valid),
    annotation, pending, moved, moved.admitted snapshotAdmitted admitted⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.bounded_capture_requirements
