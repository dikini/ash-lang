import SourceConsumingUseQueued
import SourceConsumingAdmissionPermissions
import SourceConsumingQueuedTransport

/-! Permission and phase transport for consumption-time source evidence.
The original source determines which live owners must remain available;
the actual caller may contain intermediate masking handlers. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy resumed_phases disposed_phases)
open SourceScheduledPhaseRestriction (AvailableOn)
open SourceDependencyOwners (owners)

variable [DeclarationPolicy]
  {baseHints : Hints baseScope} {base : Forest baseHints}

/-- These maps change independent fields. The retained annotation values are
identical, including permission-indexed saved and closing annotations. -/
theorem Context.world_weaken_extend_permissions
    (context : Context world owner outward actions phases base baseFront saved waiting)
    (larger : world ⊆ nextWorld)
    (permissions : Syntax.UsageExtension actions nextActions) (same : actions owner = nextActions owner) :
    (context.world_weaken larger).extend_permissions permissions same =
      (context.extend_permissions permissions same).world_weaken larger := by
  cases context
  rfl

theorem Context.world_weaken_restrict_phases
    (context : Context world owner outward actions phases base baseFront saved waiting)
    (larger : world ⊆ nextWorld)
    (extension : AvailableOn (owners baseScope) phases nextPhases) :
    (context.world_weaken larger).restrict_phases extension =
      (context.restrict_phases extension).world_weaken larger := by
  cases context
  rfl

/-- Extension preserves existing rights. Equality at the selected owner
prevents extension from inventing saved-source evidence for a new right. -/
theorem AtUse.extend_permissions
    {context : Context world owner outward actions phases base baseFront saved waiting}
    {body : Body world owner plan} {front : Forest frontHints}
    (source : AtUse outward actions phases context body front)
    (permissions : Syntax.UsageExtension actions nextActions) (same : actions owner = nextActions owner) :
    AtUse outward nextActions phases (context.extend_permissions permissions same) body front := by
  induction source with
  | resume resumption =>
      exact .resume (fun permission =>
        (resumption (by simpa only [same] using permission)).transport permissions (fun _ _ ready => ready))
  | dispose closing =>
      exact .dispose (fun permission =>
        (closing (by simpa only [same] using permission)).transport permissions (fun _ _ ready => ready))
  | sequence source ih => exact .sequence (ih same)
  | choice left right ihLeft ihRight => exact .choice (ihLeft same) (ihRight same)
  | handler source ih => exact .handler (ih same)
  | cleanup covered source ih => exact .cleanup covered (ih same)
  | resource each ih =>
      apply AtUse.resource
      intro identity fresh
      simpa only [Context.world_weaken_extend_permissions] using ih identity fresh same

/-- Availability is restricted using the original source's owner cut. A
different intermediate caller does not impose an eager source check. -/
theorem AtUse.restrict_phases
    {context : Context world owner outward actions phases base baseFront saved waiting}
    {body : Body world owner plan} {front : Forest frontHints}
    (source : AtUse outward actions phases context body front)
    (extension : AvailableOn (owners baseScope) phases nextPhases) :
    AtUse outward actions nextPhases (context.restrict_phases extension) body front := by
  induction source with
  | resume resumption =>
      rename_i current
      exact .resume (fun permission =>
        (resumption permission).restrict_phases (resumed_phases current.cut extension))
  | dispose closing =>
      rename_i current
      exact .dispose (fun permission =>
        (closing permission).restrict_phases (disposed_phases current.cut extension))
  | sequence source ih => exact .sequence (ih extension)
  | choice left right ihLeft ihRight => exact .choice (ihLeft extension) (ihRight extension)
  | handler source ih => exact .handler (ih extension)
  | cleanup covered source ih => exact .cleanup covered (ih extension)
  | resource each ih =>
      apply AtUse.resource
      intro identity fresh
      simpa only [Context.world_weaken_restrict_phases] using ih identity fresh extension

/-- The finite clause check already establishes a known permission entry, so
queued source needs no extra equality assumption when the registry grows. -/
def UseQueuedBody.extend_permissions
    {original : Context world owner outward actions phases base baseFront saved waiting}
    (queued : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    (permissions : Syntax.UsageExtension actions nextActions) :
    UseQueuedBody resumeRequired closeRequired
      (original.extend_permissions permissions (by
        obtain ⟨rights, known⟩ := (queued.body.boundCheck_owner queued.checked).1
        exact known.trans (permissions owner rights known).symm)) cut before bounds := by
  have same : actions owner = nextActions owner := by
    obtain ⟨rights, known⟩ := (queued.body.boundCheck_owner queued.checked).1
    exact known.trans (permissions owner rights known).symm
  exact ⟨queued.body, queued.origin, queued.source.extend_permissions permissions same,
    queued.nested, queued.body.boundCheck_owner_transport queued.checked same (fun ready => ready)⟩

/-- Transport both the structural source and its independent finite check.
The owner's availability follows from the original cut; callers supply only
the availability inclusion for owners reachable in that original source. -/
def UseQueuedBody.restrict_phases
    {original : Context world owner outward actions phases base baseFront saved waiting}
    (queued : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    (extension : AvailableOn (owners baseScope) phases nextPhases) :
    UseQueuedBody resumeRequired closeRequired (original.restrict_phases extension) cut before bounds :=
  ⟨queued.body, queued.origin, queued.source.restrict_phases extension, queued.nested,
    queued.body.boundCheck_owner_transport queued.checked rfl
      (extension owner (SourceScheduledPhaseRestriction.selected_owner
        (SourceContextualInvocationHints.selected_cut original.cut.found)))⟩

/-- Reuse the existing world maps for syntax, nested declarations and finite
checks. The queued index and the current caller's interface grow together. -/
def UseQueuedBody.world_weaken
    {original : Context world owner outward actions phases base baseFront saved waiting}
    (queued : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    (larger : world ⊆ nextWorld) :
    UseQueuedBody resumeRequired closeRequired (original.world_weaken larger)
      cut (before.world_weaken larger) (bounds.world_weaken larger) :=
  ⟨queued.body.world_weaken larger,
    (congrArg (fun bounds => bounds.world_weaken larger) queued.origin).trans
      (queued.body.boundAnnotation_world_weaken larger).symm,
    queued.source.world_weaken larger, queued.nested.world_weaken larger,
    queued.body.boundCheck_world_weaken larger queued.checked⟩

/-- All three independent changes compose on the same queued source record.
The result remains available to focus, return and generation at its exact
current cut; a different interpretation stack requires separate evidence. -/
def UseQueuedBody.transport
    {original : Context world owner outward actions phases base baseFront saved waiting}
    (queued : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    (permissions : Syntax.UsageExtension actions nextActions)
    (extension : AvailableOn (owners baseScope) phases nextPhases)
    (larger : world ⊆ nextWorld) :
    UseQueuedBody resumeRequired closeRequired
      (((original.extend_permissions permissions (by
        obtain ⟨rights, known⟩ := (queued.body.boundCheck_owner queued.checked).1
        exact known.trans (permissions owner rights known).symm)).restrict_phases extension).world_weaken larger)
      cut (before.world_weaken larger) (bounds.world_weaken larger) :=
  ((queued.extend_permissions permissions).restrict_phases extension).world_weaken larger

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.world_weaken_extend_permissions
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.world_weaken_restrict_phases
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.extend_permissions
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.restrict_phases
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.extend_permissions
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.restrict_phases
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.world_weaken
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.transport
