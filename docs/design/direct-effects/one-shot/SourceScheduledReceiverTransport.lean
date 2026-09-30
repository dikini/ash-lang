import SourceScheduledReceiverRechecking
import SourceScheduledRecheckingPhases
import SourceScheduledRecheckingWorld

/-! Receiver-only source rechecking survives permission, phase and world
transport. Expression cases reuse the established general transport proofs;
only the retained spine is traversed here. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy)
open SourceScheduledPhaseRestriction (AvailableOn)
open SourceDependencyOwners (owners)
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

variable [DeclarationPolicy]

/-- Changing capability availability does not authorize a change to retained
code positions. The original source determines the needed live-owner facts. -/
theorem ReceiverChange.transport
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} {source : Retained world forest outside}
    (changed : ReceiverChange outward actions phases source next)
    (permissions : Syntax.UsageExtension actions nextActions)
    (extension : AvailableOn (owners (scope.append outsideScope)) phases nextPhases) :
    ReceiverChange outward nextActions nextPhases source next := by
  induction changed with
  | same => exact .same
  | provide ready previous inserted ih =>
      exact .provide (Retained.valid_transport _ ready permissions extension) (ih extension) inserted
  | operations interfaces supplied => exact .operations interfaces supplied
  | plain code tail ih => exact .plain (code.transport permissions extension) (ih extension)
  | handler supplied tail ih => exact .handler supplied (ih extension)
  | cell tail ih => exact .cell (ih extension)
  | cleanup code tail ih => exact .cleanup (code.transport permissions extension) (ih extension)
  | running tail ih => exact .running (ih extension)
  | spent tail ih => exact .spent (ih extension)
  | live saved tail ihSaved ihTail =>
      apply ReceiverChange.live
      · apply ihSaved
        apply extension.weaken
        simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
        exact List.subset_cons_self _ _
      · apply ihTail
        apply extension.weaken
        simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
        intro name member
        exact List.mem_cons_of_mem _ (List.mem_append_right _ member)

theorem ReceiverChange.restrict_phases
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} {source : Retained world forest outside}
    (changed : ReceiverChange outward actions phases source next)
    (extension : AvailableOn (owners (scope.append outsideScope)) phases nextPhases) :
    ReceiverChange outward actions nextPhases source next :=
  changed.transport (fun _ _ known => known) extension

theorem ReceiverChange.world_weaken
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} {source : Retained world forest outside}
    (changed : ReceiverChange outward actions phases source next)
    (larger : world ⊆ nextWorld) :
    ReceiverChange outward actions phases (source.world_weaken larger) next := by
  induction changed with
  | same => exact .same
  | provide ready previous inserted ih =>
      exact .provide (Retained.world_weaken_valid _ larger ready) (ih larger) inserted
  | operations interfaces supplied =>
      exact .operations (interfaces.world_weaken larger)
        (by simpa only [SourceScheduledRetainedInterfaces.Interfaces.check_world_weaken] using supplied)
  | plain code tail ih => exact .plain (code.world_weaken larger) (ih larger)
  | handler supplied tail ih => exact .handler supplied (ih larger)
  | cell tail ih => exact .cell (ih larger)
  | cleanup code tail ih => exact .cleanup (code.world_weaken larger) (ih larger)
  | running tail ih => exact .running (ih larger)
  | live saved tail ihSaved ihTail => exact .live (ihSaved larger) (ihTail larger)
  | spent tail ih => exact .spent (ih larger)

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ReceiverChange.transport
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ReceiverChange.restrict_phases
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ReceiverChange.world_weaken
