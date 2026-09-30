import SourceConsumingUseAligned
import SourceConsumingUseCaptureRecords

/-! Initialize the combined source/metadata record from actual capture and
preserve it at boundary-entry snapshots. The source transition and metadata
transition share the same pending data, rather than separate witnesses. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Declarations ClauseBounds Bounded SelectedSource Generated)
open SourceScheduledCapabilityAnnotations (Code Retained CaptureSource DeclarationPolicy DeclarationLaws)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)
open SourcePlanBounds (Annotation ofCode)
open SourceBoundSnapshots (Snapshot EnteredHandler EnteredCleanup EnteredResource)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceDependencyOwners (owners)
open SourcePlannedRecipeDeclarations (Selected)
open OwnerPhaseTransitions (introduce)

variable [declarations : DeclarationPolicy]
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {original : Context world owner outward actions phases base baseFront saved waiting}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {cut : OwnerCut owner whole front saved waiting} {before : Interfaces world front}
    {targetHints : Hints targetScope} {target : Forest targetHints}
    {pending : SourceBoundSnapshots.Retained world target}

theorem UseAlignedBody.handler_entered
    {plans : ClausePlans clauses families} {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    {next : Snapshot world}
    (entered : EnteredHandler effect table required plans ⟨_, plan, bounds, _, _, target, pending⟩ next) :
    ∃ child : UseAlignedBody resumeRequired closeRequired original
      (.handler (effect := effect) (table := table) (families := families) (required := required) cut)
      (.handler _ before) next.current
      (.handler (effect := effect) (table := table) (families := families) (required := required) pending),
      next = ⟨_, next.plan, child.source.body.boundAnnotation, _, _,
        .handler (effect := effect) (table := table) (families := families) (required := required) target,
        .handler pending⟩ := by
  cases entered
  refine ⟨record.handler_body, ?_⟩
  rw [← record.handler_body.source.origin]

theorem UseAlignedBody.cleanup_entered
    {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    {next : Snapshot world}
    (entered : EnteredCleanup ⟨_, plan, bounds, _, _, target, pending⟩ next) :
    ∃ needs callbackDependencies, ∃ callback : Plan callbackDependencies,
    ∃ required, ∃ footprint : RequestFootprint callback required, ∃ declared : Declared world (signature callback),
    ∃ child : UseAlignedBody resumeRequired closeRequired original
      (.cleanup (needs := needs) (plan := callback) cut)
      (.cleanup front required footprint declared before) next.current
      (.cleanup (needs := needs) (.absent (plan := callback)) pending),
      next = ⟨_, next.plan, child.source.body.boundAnnotation, _, _, .cleanup (needs := needs) callback target,
        .cleanup Annotation.absent pending⟩ ∧
      (Code.operations (forest := .running target) required footprint declared).Valid outward actions phases ∧
      (∀ request ∈ required, request.1 ∈ needs) := by
  cases entered
  obtain ⟨required, footprint, declared, child, ready, callbackBounds, covered⟩ := record.sequence_rest.cleanup_body
  refine ⟨_, _, _, required, footprint, declared, child, ?_, ready, covered⟩
  rw [callbackBounds, ← child.source.origin]

theorem UseAlignedBody.resource_entered
    {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    (fresh : identity ∉ world) {next : Snapshot (world ++ [identity])}
    (entered : EnteredResource identity ⟨_, plan, bounds, _, _, target, pending⟩ next) :
    ∃ child : UseAlignedBody resumeRequired closeRequired (original.world_weaken (List.subset_append_left _ [identity]))
      (.cell (identity := identity) cut) (.cell (before.world_weaken (List.subset_append_left _ [identity])))
      next.current (.cell (identity := identity) (pending.world_weaken (List.subset_append_left _ [identity]))),
      next = ⟨_, next.plan, child.source.body.boundAnnotation, _, _, .cell (identity := identity) target,
        .cell (pending.world_weaken (List.subset_append_left _ [identity]))⟩ := by
  cases entered
  refine ⟨record.sequence_rest.resource_body fresh, ?_⟩
  rw [← (record.sequence_rest.resource_body fresh).source.origin]

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- The original source split determines both saved and canonical closing
metadata. The new record is tied to the same actual capture snapshot. The
AtUse derivation at this request is still an input. -/
theorem SelectedSource.capture_aligned_at_use
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (snapshot : Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
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
    (aligned : ofCapability source = snapshot.pending) :
    let context := Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent
    ∃ contract : SourceConsumingClauseAnnotations.Bounds,
      bounds.lookup operation savedScope.held = some contract ∧
    ∃ annotation : Code world (bodies owner) (.live (owner := owner) saved waiting),
    ∃ savedBounds : SourceBoundSnapshots.Retained world saved,
    ∃ record : UseAlignedBody contract.resume contract.close context OwnerCut.hit Interfaces.nil
      (ofCode annotation) (.live (owner := owner) savedBounds (ofCapability context.after)),
      record.source.body = body ∧ record.metadata.captured = savedBounds ∧
      (SourceScheduledCaptureAnnotations.Capture.site cut selected annotation).Valid outward actions phases ∧
      Generated (actions.insert owner code.requiredActions) context.continuationBounds body annotation ∧
      let captured : Snapshot world :=
        ⟨_, bodies owner, ofCode annotation, _, _, .live (owner := owner) saved waiting,
          .live savedBounds (ofCapability context.after)⟩
      SourceBoundSnapshots.Captured owner snapshot captured ∧ captured.Admitted := by
  obtain ⟨contract, found, annotation, sourceRecord, bodySame, ready, generated, _retained⟩ :=
    SelectedSource.capture_record_at_use laws project snapshot snapshotAdmitted bounded cut selected selectedSource
      source captureSource permits supplied fresh absent atUse aligned
  obtain ⟨savedBounds, kept, resumption, closing⟩ :=
    Context.of_request_bounds laws project cut source code.requiredActions captureSource permits fresh absent
  let context := Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent
  have captured := SourceScheduledCapabilityAnnotations.capture_snapshot_from_parts (owner := owner)
    snapshot cut savedBounds (ofCapability context.after) (kept.trans (heq_of_eq aligned)) (ofCode annotation)
  have currentReady : (ofCode annotation).Admitted := sourceRecord.origin.symm ▸ sourceRecord.nested.boundAnnotation_admitted
  exact ⟨contract, found, annotation, savedBounds,
    ⟨sourceRecord, UseMetadata.captured_root savedBounds resumption closing⟩,
    bodySame, rfl, ready, generated, captured, captured.admitted snapshotAdmitted currentReady⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.handler_entered
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.cleanup_entered
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.resource_entered
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_aligned_at_use
