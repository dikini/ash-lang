import SourceConsumingUseAdmission
import SourceConsumingContextualCapture

/-! Capture from selected stored clauses with structural rechecking at the
actual consuming leaves. Rich saved/closing annotations use the existing source
compiler; capture and canonical disposal reuse the established snapshot laws. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Declarations ClauseBounds Bounds Bounded SelectedSource Generated)
open SourceScheduledCapabilityAnnotations (Code Retained CaptureSource DeclarationPolicy DeclarationLaws)
open SourceDependencyOwners (owners)
open SourcePlannedRecipeDeclarations (Selected)
open OwnerPhaseTransitions (introduce)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Initial clause admission and the separate structural leaf derivation
construct the capture certificate and canonical snapshots. This does not assume
future target validity, nor derive leaf rechecking at every reachable request. -/
theorem SelectedSource.capture_at_use
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
    ∃ annotation : Code world (bodies owner) (.live (owner := owner) saved waiting),
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
  obtain ⟨contract, needed, _, admitted, included, nested⟩ := selectedSource.admitted bounded
  obtain ⟨annotation, ready, generated⟩ := atUse.initial_source laws project admitted
    (by simp [Syntax.UsageTickets.insert]) (by simp [introduce])
    (SourceContextualRequirements.check_requirements_subset included supplied)
  have boundsAdmitted := generated.current_bounds.symm ▸ nested.boundAnnotation_admitted
  obtain ⟨savedBounds, moved, valid, kept, closing⟩ := Context.of_request_snapshot laws project snapshot snapshotAdmitted
    cut source code.requiredActions captureSource permits fresh absent aligned
    (SourcePlanBounds.ofCode annotation) boundsAdmitted
  exact ⟨annotation, ready, generated, savedBounds, moved, valid, kept, closing⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_at_use
