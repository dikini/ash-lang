import SourceConsumingContextualCapture
import SourceScheduledNeutralBoundRetention

/-! Generate source annotations after a structural neutral receiver change.
Original contextual admission and finite checks suffice; target admission is
not assumed. The selected-source bridge retains an admitted capture snapshot. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Declarations ClauseBounds Bounded SelectedSource)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)
open SourceScheduledNeutral (Expansion)
open OwnerPhaseTransitions (introduce)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {wholeScope frontScope savedScope waitingScope : Scope}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}

/-- Generate at the changed receiver while retaining every bound recorded in
the current body. The original finite checks are not target scheduling evidence. -/
theorem At.generate_expanding {body : Body world owner plan}
    {context : Context world owner outward actions phases whole front saved waiting}
    (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    {nextHints : Hints nextScope} {next : Forest nextHints} (changed : Expansion whole next) :
    ∃ annotation : Code world plan next, annotation.Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = body.boundAnnotation := by
  obtain ⟨original, ready, bounds⟩ := admitted.generate_retaining checked
  obtain ⟨annotation, valid, same⟩ := original.expand_retaining laws project ready changed
  exact ⟨annotation, valid, same.trans bounds⟩

/-- Preserve nested-bound admission through the exact current-code equality. -/
theorem At.generate_expanding_admitted {body : Body world owner plan}
    {context : Context world owner outward actions phases whole front saved waiting}
    (admitted : At laws project body context) (nested : body.Nested)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    {nextHints : Hints nextScope} {next : Forest nextHints} (changed : Expansion whole next) :
    ∃ annotation : Code world plan next, annotation.Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = body.boundAnnotation ∧ (SourcePlanBounds.ofCode annotation).Admitted := by
  obtain ⟨annotation, valid, same⟩ := admitted.generate_expanding checked changed
  exact ⟨annotation, valid, same, same.symm ▸ nested.boundAnnotation_admitted⟩

/-- Authenticate the body at the actual selected clause, generate it from an
original admitted receiver and its neutral expansion, and reuse capture_snapshot.
This yields the existing allocator's certificate validity and admitted snapshot;
it does not assert that arbitrary execution preserves the original admission. -/
theorem SelectedSource.capture_expanding
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
    {nextSavedHints : Hints nextSavedScope} {nextWaitingHints : Hints nextWaitingScope}
    {nextSaved : Forest nextSavedHints} {nextWaiting : Forest nextWaitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes snapshot.forest nextSaved nextWaiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation nextSavedScope.held plans parameter binder code bodies)
    {body : Body world owner (bodies owner)}
    (selectedSource : SelectedSource owner annotations selected body)
    {context : Context world owner outward (actions.insert owner code.requiredActions) (introduce phases owner)
      whole front saved waiting}
    (original : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired (actions.insert owner code.requiredActions)
      (introduce phases owner) wholeScope waitingScope context.before)
    (changed : Expansion whole (.live (owner := owner) nextSaved nextWaiting)) :
    ∃ annotation : Code world (bodies owner) (.live (owner := owner) nextSaved nextWaiting),
      (SourceScheduledCaptureAnnotations.Capture.site cut selected annotation).Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = body.boundAnnotation ∧
      (SourcePlanBounds.ofCode annotation).Admitted ∧
      SourceBoundSnapshots.CapturedBounds snapshot owner (bodies owner) (.live (owner := owner) nextSaved nextWaiting) := by
  obtain ⟨_, _, _, _, _, nested⟩ := selectedSource.admitted bounded
  obtain ⟨annotation, valid, same, admitted⟩ := original.generate_expanding_admitted nested checked changed
  obtain ⟨pending, moved⟩ := SourceBoundSnapshots.capture_snapshot snapshot cut (SourcePlanBounds.ofCode annotation)
  exact ⟨annotation, valid, same, admitted, ⟨_, pending, moved, moved.admitted snapshotAdmitted admitted⟩⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_expanding
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_expanding_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_expanding
