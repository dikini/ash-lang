import SourceScheduledCapabilityTransport
import SourceScheduledProviderChecks

/-! Generate retained annotations after allocating a local resource. Existing
world and provider transport supply all scheduling obligations, including calls
to owners outside the retained forest. No target-source check is a premise. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (ClausePlans)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

theorem Retained.weaken_world_with
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (checked : annotation.Valid outward actions phases)
    (larger : world ⊆ nextWorld) :
    ∃ next : Retained nextWorld forest outside, next.Valid outward actions phases :=
  (annotate_all_with outward actions project).2 _ _ _ _
    (SourceScheduledTransport.pending_transport_world (annotation.compile_with laws checked)
      (fun _ ready => ready) (fun _ _ known => known) larger)

theorem Retained.provide_outside_with
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {hints : Hints scope} {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {forest : Forest hints} {outside : Forest outsideHints} {nextOutside : Forest nextHints}
    (annotation : Retained world forest outside) (checked : annotation.Valid outward actions phases)
    (larger : world ⊆ nextWorld) (changed : SourceScheduledProviders.Insertion identity outside nextOutside) :
    ∃ next : Retained nextWorld forest nextOutside, next.Valid outward actions phases :=
  (annotate_all_with outward actions project).2 _ _ _ _
    (SourceScheduledProviderChecks.pending_outside_transport
      (SourceScheduledTransport.pending_transport_world (annotation.compile_with laws checked)
        (fun _ ready => ready) (fun _ _ known => known) larger) changed)

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.weaken_world_with
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.provide_outside_with
