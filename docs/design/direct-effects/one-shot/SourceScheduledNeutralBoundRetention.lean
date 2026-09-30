import SourceScheduledCapabilityTransport
import SourceScheduledReceiverRetention

/-! Neutral receiver expansion retains exact current-plan bound metadata.
Existing receiver transport handles atomic invocations and selected requests;
only current syntax is traversed to retain its recorded handler bounds. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledNeutral (Expansion)
open SourcePlanBounds (ofCode)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Existing neutral scheduling transport instantiates the shared retention laws. -/
theorem neutral_receiver_laws
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans) :
    ReceiverLaws Expansion outward actions phases where
  requirements := fun changed ready => changed.erase.requirements ▸ ready
  transport := fun source ready changed => source.expand_with laws project ready changed
  plain := Expansion.plain
  handler := Expansion.handler
  cell := Expansion.cell
  cleanup := Expansion.cleanup
  running := Expansion.running
  live := Expansion.live
  spent := Expansion.spent

/-- Neutral receiver expansion reuses the shared metadata retention proof. -/
theorem Code.expand_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {beforeHints : Hints beforeScope} {before : Forest beforeHints} {plan : Plan dependencies}
    (source : Code world plan before) (ready : source.Valid outward actions phases)
    {afterHints : Hints afterScope} {after : Forest afterHints} (changed : Expansion before after) :
    ∃ annotation : Code world plan after, annotation.Valid outward actions phases ∧
      ofCode annotation = ofCode source :=
  source.receiver_retaining (neutral_receiver_laws laws project) ready changed

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.neutral_receiver_laws
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.expand_retaining
