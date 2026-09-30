import SourceConsumingUseMetadata
import SourceConsumingUseTransitions
import SourceConsumingUseHandlerEntry

/-! Keep consuming source and actual pending metadata together. The receiver
expansion is derived from metadata provenance, not separately assumed. This
record follows one consuming body; it does not assert whole-program coverage. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints Requirement)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)
open SourceScheduledNeutral (OwnerCut Expansion)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot Computed Returned)

variable [declarations : DeclarationPolicy]

structure UseAlignedBody (resumeRequired closeRequired : List Requirement)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (original : Context world owner outward actions phases base baseFront saved waiting)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    (cut : OwnerCut owner whole front saved waiting) (before : Interfaces world front)
    {targetHints : Hints targetScope} {target : Forest targetHints}
    {plan : Plan dependencies} (bounds : Annotation world plan)
    (pending : SourceBoundSnapshots.Retained world target) where
  source : UseQueuedBody resumeRequired closeRequired original cut before bounds
  metadata : UseMetadata original front pending

variable {baseHints : Hints baseScope} {base : Forest baseHints}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {original : Context world owner outward actions phases base baseFront saved waiting}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {cut : OwnerCut owner whole front saved waiting} {before : Interfaces world front}
    {targetHints : Hints targetScope} {target : Forest targetHints}
    {pending : SourceBoundSnapshots.Retained world target}

/-- The owner cut identifies the original whole forest; metadata movement
already contains the actual receiver's structural expansion. -/
theorem UseMetadata.receiver (metadata : UseMetadata original front pending)
    (cut : OwnerCut owner whole front saved waiting) : Expansion whole target :=
  (SourceScheduledRecomposition.predicate_congr
    (SourceContextualInvocationHints.selected_cut cut.found).reconstruct
    cut.hints cut.forest (fun source => Expansion source target)).mpr metadata.movement.forest

def UseAlignedBody.at_receiver {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending) :
    UseReceiverBody resumeRequired closeRequired original cut before target bounds :=
  ⟨record.source, record.metadata.receiver cut⟩

def UseAlignedBody.plug {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    (position : SourceAnnotatedCode.Context) :
    UseAlignedBody resumeRequired closeRequired original cut before (bounds.plug position).2.2 pending :=
  ⟨record.source.plug position, record.metadata⟩

/-- Computation keeps the same pending metadata and selects an admitted child.
Both pieces of the successor record are obtained from the predecessor. -/
theorem UseAlignedBody.computed {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    {next : Snapshot world}
    (step : Computed rule ⟨_, plan, bounds, _, _, target, pending⟩ next) :
    ∃ child : UseAlignedBody resumeRequired closeRequired original cut before next.current pending,
      record.source.body.Reduction rule child.source.body ∧
      next = ⟨_, next.plan, child.source.body.boundAnnotation, _, _, target, pending⟩ := by
  obtain ⟨child, reduced, same⟩ := record.at_receiver.computed pending step
  exact ⟨⟨child.source, record.metadata⟩, reduced, same⟩

theorem UseAlignedBody.returned {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    (position : SourceAnnotatedCode.Context)
    {currentPlan : Plan currentDependencies} (current : Annotation world currentPlan)
    {next : Snapshot world}
    (step : Returned position
      ⟨_, currentPlan, current, _, _, .plain plan target, .plain bounds pending⟩ next) :
    ∃ child : UseAlignedBody resumeRequired closeRequired original cut before (bounds.plug position).2.2 pending,
      next = ⟨_, _, child.source.body.boundAnnotation, _, _, target, pending⟩ := by
  obtain ⟨child, same⟩ := record.at_receiver.returned position current pending step
  exact ⟨⟨child.source, record.metadata⟩, same⟩

def UseAlignedBody.sequence_rest {first : Plan firstDependencies} {rest : Plan restDependencies}
    {bounds : Annotation world (.sequence first rest)}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending) :
    UseAlignedBody resumeRequired closeRequired original cut before bounds.second pending :=
  ⟨record.source.sequence_rest, record.metadata⟩

def UseAlignedBody.handler_body
    {plans : ClausePlans clauses families} {bodyPlan : Plan dependencies}
    {bounds : Annotation world (.handler (effect := effect) (table := table) required plans bodyPlan)}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending) :
    UseAlignedBody resumeRequired closeRequired original
      (.handler (effect := effect) (table := table) (families := families) (required := required) cut)
      (.handler _ before) bounds.handlerBody
      (.handler (effect := effect) (table := table) (families := families) (required := required) pending) :=
  ⟨record.source.handler_body, record.metadata.handler⟩

theorem UseAlignedBody.cleanup_body {callback : Plan callbackDependencies} {bodyPlan : Plan dependencies}
    {bounds : Annotation world (.cleanup (needs := needs) callback bodyPlan)}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending) :
    ∃ required, ∃ footprint : RequestFootprint callback required, ∃ declared : Declared world (signature callback),
    ∃ _child : UseAlignedBody resumeRequired closeRequired original
      (.cleanup (needs := needs) (plan := callback) cut)
      (.cleanup front required footprint declared before) bounds.cleanupBody
      (.cleanup (needs := needs) (.absent (plan := callback)) pending),
      (Code.operations (forest := .running target) required footprint declared).Valid outward actions phases ∧
      bounds.cleanupCallback = Annotation.absent ∧
      (∀ request ∈ required, request.1 ∈ needs) := by
  obtain ⟨required, footprint, declared, child, ready, origin, covered⟩ := record.at_receiver.cleanup_body
  exact ⟨required, footprint, declared, ⟨child.source, record.metadata.cleanup⟩, ready, origin, covered⟩

def UseAlignedBody.resource_body
    {families : Nat → SourceDependencyAnnotations.Dependencies} {plans : ∀ identity, Plan (families identity)}
    {bounds : Annotation world (.resource plans)}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    (fresh : identity ∉ world) :
    UseAlignedBody resumeRequired closeRequired (original.world_weaken (List.subset_append_left _ [identity]))
      (.cell (identity := identity) cut) (.cell (before.world_weaken (List.subset_append_left _ [identity])))
      (bounds.resourceBody fresh) (.cell (identity := identity) (pending.world_weaken (List.subset_append_left _ [identity]))) :=
  ⟨record.source.resource_body fresh, (record.metadata.world_weaken (List.subset_append_left _ [identity])).cell⟩

/-- Source and metadata use the same derived rights equality. -/
def UseAlignedBody.extend_permissions {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    (permissions : Syntax.UsageExtension actions nextActions) :
    UseAlignedBody resumeRequired closeRequired
      (original.extend_permissions permissions (by
        obtain ⟨rights, known⟩ := (record.source.body.boundCheck_owner record.source.checked).1
        exact known.trans (permissions owner rights known).symm)) cut before bounds pending :=
  ⟨record.source.extend_permissions permissions, record.metadata.extend_permissions permissions (by
    obtain ⟨rights, known⟩ := (record.source.body.boundCheck_owner record.source.checked).1
    exact known.trans (permissions owner rights known).symm)⟩

def UseAlignedBody.restrict_phases {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    (extension : SourceScheduledPhaseRestriction.AvailableOn (SourceDependencyOwners.owners baseScope) phases nextPhases) :
    UseAlignedBody resumeRequired closeRequired (original.restrict_phases extension) cut before bounds pending :=
  ⟨record.source.restrict_phases extension, record.metadata.restrict_phases extension⟩

def UseAlignedBody.world_weaken {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    (larger : world ⊆ nextWorld) :
    UseAlignedBody resumeRequired closeRequired (original.world_weaken larger) cut (before.world_weaken larger)
      (bounds.world_weaken larger) (pending.world_weaken larger) :=
  ⟨record.source.world_weaken larger, record.metadata.world_weaken larger⟩

/-- Focus retains source for either the pending consuming remainder or the
current consuming child. Operation-prefix source remains in the existing split. -/
structure UseAlignedFocused (resumeRequired closeRequired : List Requirement)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (original : Context world owner outward actions phases base baseFront saved waiting)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    (cut : OwnerCut owner whole front saved waiting) (before : Interfaces world front)
    {targetHints : Hints targetScope} {target : Forest targetHints}
    {child : Plan childDependencies} {rest : Plan restDependencies}
    (childBounds : Annotation world child) (restBounds : Annotation world rest)
    (pending : SourceBoundSnapshots.Retained world target) where
  source : UseFocusedSource resumeRequired closeRequired original cut before childBounds restBounds
  metadata : UseMetadata original front pending

def UseAlignedBody.focused {bounds : Annotation world plan}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds pending)
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (step : SourcePlanBounds.Focused world bounds childBounds restBounds) :
    UseAlignedFocused resumeRequired closeRequired original cut before childBounds restBounds pending :=
  ⟨record.source.focused step, record.metadata⟩

theorem UseAlignedFocused.queued_body
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (focused : UseAlignedFocused resumeRequired closeRequired original cut before childBounds restBounds pending)
    (restBody : Body world owner rest) :
    Nonempty (UseAlignedBody resumeRequired closeRequired original cut before restBounds pending) := by
  obtain ⟨source⟩ := focused.source.queued_body restBody
  exact ⟨source, focused.metadata⟩

theorem UseAlignedFocused.current_body
    {child : Plan childDependencies} {childBounds : Annotation world child}
    (focused : UseAlignedFocused resumeRequired closeRequired original cut before
      childBounds (.absent (plan := .pure)) pending) :
    Nonempty (UseAlignedBody resumeRequired closeRequired original cut before childBounds
      (.plain (.absent (plan := .pure)) pending)) := by
  obtain ⟨source⟩ := focused.source.current_body
  exact ⟨source, focused.metadata.extra⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.receiver
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.at_receiver
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.plug
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.computed
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.returned
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.sequence_rest
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.handler_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.cleanup_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.resource_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.extend_permissions
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.restrict_phases
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.world_weaken
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.focused
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedFocused.queued_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedFocused.current_body
