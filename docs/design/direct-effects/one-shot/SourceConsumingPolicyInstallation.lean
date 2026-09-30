import SourceConsumingDeclarationPolicies
import SourceConsumingDeclarationTransport
import SourceConsumingStoredBounds

/-! The concrete declaration policies retain the same actual bounds when
source evidence is moved to a broader policy and the runtime resource world.
The resulting packet admission is the premise used by generic raw capture. -/
namespace Ash.OneShot.SourceConsumingDeclarationEntry
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)
open SourceConsumingClauseAnnotations (PolicyTranslation)

theorem evidence_policy {source target : DeclarationPolicy}
    (translate : PolicyTranslation source target)
    (checked : evidence (nested := source) world required plans) :
    evidence (nested := target) world required plans := by
  obtain ⟨bounds, annotation, admitted⟩ := checked
  exact ⟨bounds, annotation.map_policy translate, admitted.map_policy translate⟩

end Ash.OneShot.SourceConsumingDeclarationEntry

namespace Ash.OneShot.SourceConsumingDeclarationPolicies
open SourceDeclarationPlans (ClausePlans)
open SourceConsumingClauseAnnotations (Declarations ClauseBounds Bounded)

/-- Policy inclusion and resource-world weakening preserve the exact recorded
bounds, not merely existence of some newly chosen interface. -/
theorem bounded_at_world {plans : ClausePlans clauses families} {bounds : ClauseBounds plans}
    {annotation : Declarations (declarations := capability depth) [] plans}
    (checked : Bounded (declarations := capability depth) bounds annotation required) (world : List Nat) :
    ∃ actual : Declarations (declarations := capability (depth + 1)) world plans,
      Bounded (declarations := capability (depth + 1)) bounds actual required :=
  ⟨(annotation.map_policy (fun old => capability_inclusion old)).world_weaken (declarations := capability (depth + 1)) (List.nil_subset world),
    (checked.map_policy (fun old => capability_inclusion old)).world_weaken (declarations := capability (depth + 1)) (List.nil_subset world)⟩

theorem bounded_evidence {plans : ClausePlans clauses families}
    (checked : bounded (capability depth) required plans) (world : List Nat) :
    SourceConsumingDeclarationEntry.evidence (nested := capability (depth + 1)) world required plans := by
  obtain ⟨bounds, annotation, admitted⟩ := checked
  obtain ⟨actual, preserved⟩ := bounded_at_world admitted world
  exact ⟨bounds, actual, preserved⟩

/-- Admit the actual installed packet under the same concrete policy used by
capture certificates. Its recorded bounds and selected plans are unchanged. -/
theorem handler_admitted {packet : SourceConsumingStoredBounds.HandlerBounds families handler}
    (route : packet.admission = .bounded)
    {annotation : Declarations (declarations := capability depth) [] packet.plans}
    (checked : Bounded (declarations := capability depth) packet.bounds annotation (required handler.erase)) (world : List Nat) :
    packet.Admitted (nested := capability (depth + 1)) world required := by
  obtain ⟨actual, preserved⟩ := bounded_at_world checked world
  exact SourceConsumingStoredBounds.HandlerBounds.Admitted.bounded
    (nested := capability (depth + 1)) route actual preserved

end Ash.OneShot.SourceConsumingDeclarationPolicies

#print axioms Ash.OneShot.SourceConsumingDeclarationEntry.evidence_policy
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.bounded_at_world
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.bounded_evidence
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.handler_admitted
