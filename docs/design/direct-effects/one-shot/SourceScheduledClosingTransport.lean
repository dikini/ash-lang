import SourceScheduledClosingOwners
import SourceScheduledRecheckingPhases
import SourceScheduledRecheckingWorld

/-! Canonical source closing survives permission, phase and world
transport. Expression cases reuse the established general transport proofs;
only the closing traversal is handled here. -/
namespace Ash.OneShot.SourceScheduledPhaseRestriction
open OwnerPhaseTransitions (spendAll)

/-- Spending unrelated owners leaves the surviving availability facts intact.
Reuse the pointwise retirement equation; no source traversal is needed. -/
theorem retire_outside (separated : ∀ owner ∈ names, owner ∉ retired) :
    AvailableOn names phases (spendAll phases retired) := by
  intro owner member ready
  simpa only [OwnerPhaseTransitions.spendAll_at, if_neg (separated owner member)] using ready

end Ash.OneShot.SourceScheduledPhaseRestriction

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy DeclarationLaws)
open SourceScheduledPhaseRestriction (AvailableOn)
open SourceDependencyOwners (owners)
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

variable [DeclarationPolicy]

/-- Capability transport retains the canonical closing traversal. The original
source determines the needed live-owner availability facts. -/
theorem Closing.transport
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} {source : Retained world forest outside}
    (changed : Closing outward actions phases source next)
    (permissions : Syntax.UsageExtension actions nextActions)
    (extension : AvailableOn (owners (scope.append outsideScope)) phases nextPhases) :
    Closing outward nextActions nextPhases source next := by
  induction changed with
  | operations interfaces supplied => exact .operations interfaces supplied
  | plain tail ih => exact .plain (ih extension)
  | handler tail ih => exact .handler (ih extension)
  | cell tail ih => exact .cell (ih extension)
  | cleanup code tail ih => exact .cleanup (code.transport permissions extension) (ih extension)
  | running tail ih => exact .running (ih extension)
  | spent tail ih => exact .spent (ih extension)
  | live saved tail ihSaved ihTail =>
      apply Closing.live
      · apply ihSaved
        apply extension.weaken
        simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
        exact List.subset_cons_self _ _
      · apply ihTail
        apply extension.weaken
        simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
        intro name member
        exact List.mem_cons_of_mem _ (List.mem_append_right _ member)

theorem Closing.restrict_phases
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} {source : Retained world forest outside}
    (changed : Closing outward actions phases source next)
    (extension : AvailableOn (owners (scope.append outsideScope)) phases nextPhases) :
    Closing outward actions nextPhases source next :=
  changed.transport (fun _ _ known => known) extension

theorem Closing.world_weaken
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} {source : Retained world forest outside}
    (changed : Closing outward actions phases source next)
    (larger : world ⊆ nextWorld) :
    Closing outward actions phases (source.world_weaken larger) next := by
  induction changed with
  | operations interfaces supplied =>
      exact .operations (interfaces.world_weaken larger)
        (by simpa only [SourceScheduledRetainedInterfaces.Interfaces.check_world_weaken] using supplied)
  | plain tail ih => exact .plain (ih larger)
  | handler tail ih => exact .handler (ih larger)
  | cell tail ih => exact .cell (ih larger)
  | cleanup code tail ih => exact .cleanup (code.world_weaken larger) (ih larger)
  | running tail ih => exact .running (ih larger)
  | live saved tail ihSaved ihTail => exact .live (ihSaved larger) (ihTail larger)
  | spent tail ih => exact .spent (ih larger)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Compile the original closing source, then reuse annotation phase transport
at its actual surviving receiver. Retired owners need not remain available in
the discarded normal source. Exact callback metadata is retained unchanged. -/
theorem Closing.compile_retiring
    (laws : DeclarationLaws inferInstance admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → DeclarationPolicy.accepts required plans)
    {hints : Hints scope} {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {forest : Forest hints} {outside : Forest outsideHints} {next : Forest nextHints}
    {source : Retained world forest outside}
    (closing : Closing outward actions phases source next)
    (ready : source.Valid outward actions phases)
    (separated : ∀ owner ∈ owners nextScope, owner ∉ retired) :
    ∃ annotation : Retained world forest.forClosing next,
      annotation.Valid outward actions (OwnerPhaseTransitions.spendAll phases retired) ∧
      SourceBoundSnapshots.Retained.ofCapability annotation =
        (SourceBoundSnapshots.Retained.ofCapability source).forClosing := by
  obtain ⟨annotation, valid, kept⟩ := closing.compile_retaining laws project ready
  refine ⟨annotation, annotation.restrict_phases valid ?_, kept⟩
  simpa only [SourceScheduledPhaseRestriction.owners_append,
    SourceScheduledPhaseRestriction.owners_closing_empty, List.nil_append] using
      (SourceScheduledPhaseRestriction.retire_outside (phases := phases) separated)

end Ash.OneShot.SourceScheduledSourceRechecking

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyOwners (owners)
open SourceBoundSnapshots.Retained (ofCapability)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- At an authenticated capture, uniqueness supplies phase separation for any
retired subset of captured owners. The source, actual cut and original closing
derivation suffice; no valid successor annotation or future phase check is input. -/
theorem CaptureSource.compile_retiring
    (_laws : DeclarationLaws declarations admission certification outward)
    (_project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    {cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting}
    {source : Retained world whole .nil}
    (captured : CaptureSource outward actions phases cut source rights)
    (disposes : rights.dispose = true)
    (unique : (owners wholeScope).Nodup) (included : retired ⊆ owners savedScope) :
    ∃ annotation : Retained world saved.forClosing (.running waiting),
      annotation.Valid outward actions (OwnerPhaseTransitions.spendAll phases retired) ∧
      ofCapability annotation = (ofCapability captured.inside).forClosing := by
  have uniqueParts : (owners savedScope ++ owners waitingScope).Nodup := by
    simpa only [cut.erase.reconstruct_scope, SourceScheduledPhaseRestriction.owners_append] using unique
  have separate := (List.nodup_append.mp uniqueParts).2.2
  have separated : ∀ owner ∈ owners waitingScope, owner ∉ retired := by
    intro owner surviving spent
    exact separate owner (included spent) owner surviving rfl
  obtain ⟨annotation, ready, kept⟩ := captured.closing disposes
  refine ⟨annotation, annotation.restrict_phases ready ?_, kept⟩
  simpa only [SourceScheduledPhaseRestriction.owners_append,
    SourceScheduledPhaseRestriction.owners_closing_empty, owners, List.nil_append] using
      (SourceScheduledPhaseRestriction.retire_outside (phases := phases) separated)

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.transport
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.restrict_phases
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.world_weaken
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.retire_outside
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.compile_retiring
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.CaptureSource.compile_retiring
