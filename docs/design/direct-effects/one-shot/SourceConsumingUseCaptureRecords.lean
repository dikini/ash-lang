import SourceConsumingUseCapture
import SourceConsumingUseReceiver

/-! The selected clause's structural source record is retained beside its
capture certificate and exact bound snapshot. Source evidence at this request
is still an input; it is not inferred from successful future execution. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Declarations ClauseBounds Bounded SelectedSource Generated)
open SourceScheduledCapabilityAnnotations (Code Retained CaptureSource DeclarationPolicy DeclarationLaws)
open SourceDependencyOwners (owners)
open SourcePlannedRecipeDeclarations (Selected)
open OwnerPhaseTransitions (introduce)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- The same selected bound supplies the record's independent clause checks.
The generated annotation, captured metadata and canonical disposal snapshots
are exactly those of the existing capture theorem. -/
theorem SelectedSource.capture_record_at_use
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes snapshot.forest saved waiting)
    (selected : Selected operation savedScope.held plans parameter binder code bodies)
    {body : Body world owner (bodies owner)}
    (selectedSource : SelectedSource owner annotations selected body)
    (source : Retained world snapshot.forest .nil)
    (captureSource : CaptureSource outward actions phases cut source code.requiredActions)
    (permits : code.requiredActions.dispose = true → offered.dispose = true)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none) (absent : owner ∉ owners snapshot.scope)
    (atUse : AtUse outward (actions.insert owner code.requiredActions) (introduce phases owner)
      (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent) body .nil)
    (aligned : SourceBoundSnapshots.Retained.ofCapability source = snapshot.pending) :
    let context := Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent
    ∃ contract : SourceConsumingClauseAnnotations.Bounds,
      bounds.lookup operation savedScope.held = some contract ∧
    ∃ annotation : Code world (bodies owner) (.live (owner := owner) saved waiting),
    ∃ record : UseQueuedBody contract.resume contract.close context SourceScheduledNeutral.OwnerCut.hit
      SourceScheduledRetainedInterfaces.Interfaces.nil (SourcePlanBounds.ofCode annotation),
      record.body = body ∧
      (SourceScheduledCaptureAnnotations.Capture.site cut selected annotation).Valid outward actions phases ∧
      Generated (actions.insert owner code.requiredActions) context.continuationBounds body annotation ∧
      ∃ savedBounds : SourceBoundSnapshots.Retained world saved,
        let captured : SourceBoundSnapshots.Snapshot world :=
          ⟨_, bodies owner, SourcePlanBounds.ofCode annotation, _, _, .live (owner := owner) saved waiting,
            .live savedBounds (SourceBoundSnapshots.Retained.ofCapability context.after)⟩
        SourceBoundSnapshots.Captured owner snapshot captured ∧ captured.Admitted ∧
        (∀ permission, context.continuationBounds.resumption permission = savedBounds) ∧
        ∀ permission,
          let closed := SourceBoundSnapshots.Snapshot.value
            ((SourceBoundSnapshots.Retained.ofCapability (context.closing permission).val).append
              (.running (.spent (owner := owner) (SourceBoundSnapshots.Retained.ofCapability context.after))))
          SourceBoundSnapshots.Discarded owner captured closed ∧ closed.Admitted := by
  obtain ⟨contract, needed, found, admitted, included, nested⟩ := selectedSource.admitted bounded
  obtain ⟨annotation, ready, generated, retained⟩ :=
    SelectedSource.capture_at_use laws project snapshot snapshotAdmitted bounded cut selected selectedSource
      source captureSource permits supplied fresh absent atUse aligned
  let record : UseQueuedBody contract.resume contract.close
      (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent)
      SourceScheduledNeutral.OwnerCut.hit SourceScheduledRetainedInterfaces.Interfaces.nil
      (SourcePlanBounds.ofCode annotation) :=
    ⟨body, generated.current_bounds, atUse, nested,
      admitted.at_capture (by simp [Syntax.UsageTickets.insert]) (by simp [introduce])
        (SourceContextualRequirements.check_requirements_subset included supplied)⟩
  exact ⟨contract, found, annotation, record, rfl, ready, generated, retained⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_record_at_use
