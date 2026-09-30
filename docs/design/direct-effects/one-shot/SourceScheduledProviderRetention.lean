import SourceScheduledReceiverRetention
import SourceScheduledProviderChecks
import SourceScheduledAnnotationWorldLaws

/-! Provider insertion preserves exact metadata through the shared receiver
retention proof. Resource-world extension is performed structurally first;
existing scheduling transport is used only as the relation's proved law. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledProviders (Insertion)
open SourcePlanBounds (ofCode)
open SourceBoundSnapshots.Retained (ofCapability)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Existing provider scheduling and requirement preservation discharge the
same receiver laws used by neutral expansion. -/
theorem provider_receiver_laws
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans) :
    ReceiverLaws (Insertion identity) outward actions phases where
  requirements := fun changed ready => changed.erase.requirements ready
  transport := fun source ready changed =>
    (annotate_all_with outward actions project).1 _ _ _ _
      (SourceScheduledProviderChecks.local_transport (source.compile_with laws ready) changed)
  plain := Insertion.plain
  handler := Insertion.handler
  cell := Insertion.cell
  cleanup := Insertion.cleanup
  running := Insertion.running
  live := Insertion.live
  spent := Insertion.spent

theorem Code.provide_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints} {plan : Plan dependencies}
    (source : Code world plan before) (ready : source.Valid outward actions phases)
    (changed : Insertion identity before after) :
    ∃ annotation : Code world plan after, annotation.Valid outward actions phases ∧ ofCode annotation = ofCode source :=
  source.receiver_retaining (provider_receiver_laws laws project) ready changed

theorem Retained.provide_receiver_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {hints : Hints scope} {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {forest : Forest hints} {outside : Forest outsideHints} {next : Forest nextHints}
    (source : Retained world forest outside) (ready : source.Valid outward actions phases)
    (changed : Insertion identity outside next) :
    ∃ annotation : Retained world forest next, annotation.Valid outward actions phases ∧ ofCapability annotation = ofCapability source :=
  source.receiver_retaining (provider_receiver_laws laws project) ready changed

/-- This is the resource-entry combination: extend the source world, insert
the actual provider in the receiver, and retain the exact extended snapshot. -/
theorem Retained.provide_world_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {hints : Hints scope} {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {forest : Forest hints} {outside : Forest outsideHints} {next : Forest nextHints}
    (source : Retained world forest outside) (ready : source.Valid outward actions phases)
    (larger : world ⊆ nextWorld) (changed : Insertion identity outside next) :
    ∃ annotation : Retained nextWorld forest next, annotation.Valid outward actions phases ∧
      ofCapability annotation = (ofCapability source).world_weaken larger := by
  obtain ⟨annotation, valid, kept⟩ := (source.world_weaken larger).provide_receiver_retaining laws project
    (source.world_weaken_valid larger ready) changed
  exact ⟨annotation, valid, kept.trans (source.ofCapability_world_weaken larger)⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.provider_receiver_laws
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.provide_retaining
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.provide_receiver_retaining
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.provide_world_retaining
