import SourceScheduledNeutralBoundRetention
import SourceBoundSnapshots

/-! Neutral changes to the outside receiver keep the exact retained snapshot.
The shared receiver laws and retention proof also serve Code.expand_retaining.
Operation-only interfaces reuse their exposed requirement law; invocation and
ownership arguments are unchanged. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledNeutral (Expansion)
open SourceBoundSnapshots.Retained (ofCapability)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- The fixed retained forest keeps its exact snapshot under neutral receiver
expansion, using the shared source retention proof. -/
theorem Retained.expand_receiver_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Retained world forest outside) (ready : source.Valid outward actions phases)
    {nextHints : Hints nextScope} {next : Forest nextHints} (changed : Expansion outside next) :
    ∃ annotation : Retained world forest next, annotation.Valid outward actions phases ∧
      ofCapability annotation = ofCapability source :=
  source.receiver_retaining (neutral_receiver_laws laws project) ready changed

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.expand_receiver_retaining
