import SourceConsumingLeafInterfaces
import SourceConsumingContextualCapture

/-! Selected stored source reaches the existing capture/snapshot boundary by
consuming-leaf interface generation. The stored mode supplies the contract;
original-source views and finite inclusion checks replace future At admission. -/
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

/-- The actual selected declaration, original continuation views and its stored
finite bounds construct the capture annotation. Existing snapshot laws derive
canonical capture and every permitted disposal; no target Valid or At premise
is supplied. This still requires views of the actual saved and closing sources. -/
theorem SelectedSource.capture_leaf_interfaces
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
    (interfaces : (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent).OperationSources)
    (contract : Bounds) (found : bounds.lookup operation savedScope.held = some contract)
    (resumeBound : ∀ permission, (interfaces.resumption permission).exposed ⊆ contract.resume)
    (closeBound : ∀ permission, (interfaces.closing permission).exposed ⊆ contract.close)
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
  obtain ⟨actual, needed, actualFound, admitted, included, nested⟩ := selectedSource.admitted bounded
  have same : actual = contract := Option.some.inj (actualFound.symm.trans found)
  subst actual
  obtain ⟨annotation, ready, generated⟩ := interfaces.initial_source admitted
    (by simp [Syntax.UsageTickets.insert]) (by simp [introduce])
    (SourceContextualRequirements.check_requirements_subset included supplied) resumeBound closeBound
  have boundsAdmitted := generated.current_bounds.symm ▸ nested.boundAnnotation_admitted
  obtain ⟨savedBounds, moved, valid, kept, closing⟩ := Context.of_request_snapshot laws project snapshot snapshotAdmitted
    cut source code.requiredActions captureSource permits fresh absent aligned
    (SourcePlanBounds.ofCode annotation) boundsAdmitted
  exact ⟨annotation, ready, generated, savedBounds, moved, valid, kept, closing⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_leaf_interfaces
