import SourceScheduledInterfaceRequirements
import SourceScheduledReceiverRechecking

/-! Finite operation admission before a caller prefix closes. Existing boundary
factorization identifies exactly the remaining uniform operation requirements;
a stronger outside bound supports arbitrary closing prefixes without storing a
successful target source judgment. Continuation permissions remain separate. -/
namespace Ash.OneShot.SourceHandlerRequirements
open SourceDependencyCapture (Scope)
open SourceContextualHints (Requirement checkRequirements)

/-- Uniform operation interfaces already require both modes. A running marker
therefore changes neither their finite check nor their selected contract. -/
theorem requirements_running (scope : Scope) :
    checkRequirements (.running scope) required = checkRequirements scope required := by
  simp only [checkRequirements, capability_prepend
    (first := .running scope) (second := scope) (effect := _) (operation := _) rfl]

/-- Requests supplied in the unchanged source prefix are discharged first;
surviving builtin cells then discharge requests inside the closing prefix. -/
def survivingRequirements (kept closing : Scope) (required : List Requirement) : List Requirement :=
  outwardRequirements closing.forClosing (outwardRequirements kept required)

/-- Given the original internal checks, this is an exact finite criterion at
the unchanged outside receiver. It is not validity of any target annotation. -/
theorem requirements_surviving_iff
    (checked : checkRequirements (kept.append before) required = true) :
    checkRequirements (kept.append (closing.forClosing.append (.running outside))) required = true ↔
      checkRequirements outside (survivingRequirements kept closing required) = true := by
  rw [requirements_replace_iff checked,
    SourceScheduledCallbackInterfaces.requirements_closing_iff, requirements_running]
  rfl

/-- A source operation bound checked at the surviving outside supports EVERY
closing prefix. Local builtin providers may discharge additional requirements. -/
theorem requirements_any_closing (closing : Scope)
    (supplied : checkRequirements outside required = true) :
    checkRequirements (closing.forClosing.append (.running outside)) required = true := by
  apply (SourceScheduledCallbackInterfaces.requirements_closing_iff closing).mpr
  rw [requirements_running]
  exact SourceContextualRequirements.check_requirements_subset (fun _ member => (List.mem_filter.mp member).1) supplied

end Ash.OneShot.SourceHandlerRequirements

namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceHandlerRequirements (outwardRequirements)

/-- The retained source already accounts for ordinary code, callbacks, internal
handlers and dormant bodies in its exposed interface. Factor only its changed
receiver; do not repeat the source traversal. -/
theorem Interfaces.check_closing_receiver_iff {closing outside : Scope} {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (checked : interfaces.check before = true) :
    interfaces.check (closing.forClosing.append (.running outside)) = true ↔
      checkRequirements outside (outwardRequirements closing.forClosing interfaces.exposed) = true := by
  rw [interfaces.check_replace_iff checked,
    SourceScheduledCallbackInterfaces.requirements_closing_iff, SourceHandlerRequirements.requirements_running]

/-- A finite source-bound check at the unchanged receiver suffices uniformly
for any caller closing prefix. No future per-body success is an assumption. -/
theorem Interfaces.check_any_closing {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (checked : interfaces.check before = true)
    (bounded : interfaces.exposed ⊆ required)
    (supplied : checkRequirements outside required = true) (closing : Scope) :
    interfaces.check (closing.forClosing.append (.running outside)) = true :=
  interfaces.check_transport checked (SourceHandlerRequirements.requirements_any_closing closing
    (SourceContextualRequirements.check_requirements_subset bounded supplied))

end Ash.OneShot.SourceScheduledRetainedInterfaces

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceHandlerRequirements (survivingRequirements)

variable [DeclarationPolicy]

/-- Narrow an original conservative interface using a footprint of the same
source. Rechecking follows from its original internal check and a finite
surviving outside requirement, not a target guard or successful target source. -/
theorem Expression.surviving_operations
    {keptHints : Hints keptScope} {closingHints : Hints closingScope}
    {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
    {kept : Forest keptHints} (closing : Forest closingHints)
    {before : Forest beforeHints} (outside : Forest outsideHints)
    {oldFootprint : RequestFootprint plan oldRequired}
    {declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature plan)}
    (footprint : RequestFootprint plan required) (included : required ⊆ oldRequired)
    (ready : (Code.operations (forest := kept.append before) oldRequired oldFootprint declared).Valid outward actions phases)
    (supplied : checkRequirements outsideScope (survivingRequirements keptScope closingScope required) = true) :
    Expression outward actions phases (Code.operations (forest := kept.append before) oldRequired oldFootprint declared)
      (kept.append (closing.forClosing.append (.running outside))) := by
  apply Expression.reinterface footprint
  exact (SourceHandlerRequirements.requirements_surviving_iff
    (SourceContextualRequirements.check_requirements_subset included ready)).mpr supplied

/-- An original retained operation annotation receives the same source-directed
check. Its saved forest and metadata positions are unchanged. -/
theorem ReceiverChange.surviving_operations
    {hints : Hints scope} {forest : Forest hints}
    {beforeHints : Hints beforeScope} {before : Forest beforeHints}
    {closingHints : Hints closingScope} (closing : Forest closingHints)
    {outsideHints : Hints outsideScope} (outside : Forest outsideHints)
    (interfaces : SourceScheduledRetainedInterfaces.Interfaces world forest)
    (ready : (Retained.operations (outside := before) interfaces).Valid outward actions phases)
    (supplied : checkRequirements outsideScope
      (SourceHandlerRequirements.outwardRequirements closingScope.forClosing interfaces.exposed) = true) :
    ReceiverChange outward actions phases (Retained.operations (outside := before) interfaces)
      (closing.forClosing.append (.running outside)) :=
  .operations interfaces ((interfaces.check_closing_receiver_iff ready).mpr supplied)

/-- A saved atomic request may have either original annotation form. Reuse its
existing receiver reconstruction; a surviving outside capability supplies the
new request regardless of conservative requirements stored in the old source. -/
theorem ReceiverChange.request_any_closing
    {beforeHints : Hints beforeScope} {before : Forest beforeHints}
    {source : Retained world (.plain (.request (effect := effect) (operation := operation)) .nil) before}
    {closingHints : Hints closingScope} (closing : Forest closingHints)
    {outsideHints : Hints outsideScope} (outside : Forest outsideHints)
    (supplied : SourceContextualClauses.RequestCapability effect operation outsideScope) :
    ReceiverChange outward actions phases source (closing.forClosing.append (.running outside)) := by
  apply ReceiverChange.request
  apply SourceContextualRequirements.check_requirements_iff.mp
    (SourceHandlerRequirements.requirements_any_closing closingScope (required := [(effect, operation)]) ?_)
    (effect, operation) List.mem_cons_self
  apply SourceContextualRequirements.check_requirements_iff.mpr
  intro request member
  cases List.mem_singleton.mp member
  exact supplied

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceHandlerRequirements.requirements_running
#print axioms Ash.OneShot.SourceHandlerRequirements.requirements_surviving_iff
#print axioms Ash.OneShot.SourceHandlerRequirements.requirements_any_closing
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_closing_receiver_iff
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_any_closing
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.surviving_operations
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ReceiverChange.surviving_operations
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ReceiverChange.request_any_closing
