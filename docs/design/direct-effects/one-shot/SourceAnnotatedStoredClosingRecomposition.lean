import SourceAnnotatedStoredResumption
import SourceConsumingBoundDisposal
import SourceAnnotatedClosingData

/-! Materialize closing control with its exact packet data. Closing plans
contain only resource, callback and retirement frames; their existing source
and scheduling proof therefore constructs the joint judgment directly. -/
namespace Ash.OneShot.SourceConsumingStoredBounds
open SourceAnnotatedRuntime (Stack CloseEntry)
variable {families : SourceDependencyCapture.Families} {front capture tail : Stack}

theorem StackBounds.discard_parts
    (stored : StackBounds families (front.append (.live owner input answer capture caller tail)))
    (scope : Execution.Scope) (identity : Nat) (plan : List CloseEntry) :
    (StackBounds.closing scope plan).append (.push (.closing (identity := identity)) stored.resumeWaiting) =
      stored.discard scope identity plan := by
  unfold StackBounds.resumeWaiting StackBounds.discard
  generalize stored.splitAt front (.live owner input answer capture caller tail) = parts
  rcases parts with ⟨first, second⟩
  cases second
  rfl

end Ash.OneShot.SourceConsumingStoredBounds

namespace Ash.OneShot.SourceAnnotatedClosingPlans
open ScopedExpressions ProtectionContracts
open SourceAnnotatedRuntime (CloseEntry closeControl closeControl_erase)
open SourceAnnotatedStoredTyping (Segment)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest closingForest)
open RecursiveRequirements (Requirements evaluate)
open OwnerClosingSource (retirements)

theorem Template.scheduled_stored_source
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy] {plans : Plans plan hints} {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints}
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (checked : SourceScheduledChecks.Pending outward actions phases world (closingForest plans.erase) outside)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world closing (plan.map CloseEntry.erase))
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      (closeControl caller plan) .unit .unit (retirements (plan.map CloseEntry.erase)) requirements [] (closingForest plans.erase) outside
      (ScopedPorts.planProvides (plan.map CloseEntry.erase) ++ closing) closing (SourceConsumingStoredBounds.StackBounds.closing caller plan) := by
  have scopeTypes := ScopedPorts.effect_scope_known_has_types scope
  induction template with
  | nil => exact .nil (List.Subset.refl _)
  | release rest ih => cases typed with | release typed => cases checked with | cell next =>
      exact .push ⟨.cell scopeTypes (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl
        (.cell scope (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources])), .cell⟩ (ih next typed) (List.Subset.refl _)
  | retire known rest ih => cases typed with | retire typed => cases checked with | running next =>
      exact .push ⟨.retiring known (.retiring (CoherentSourceTypes.Owners.ports_lookup
        (SourceDependencyAnnotations.contract_erase_known (SourcePlannedSources.contract_erase_known known)))), .retiring⟩
        (ih next typed) (List.Subset.refl _)
  | @invoke dependencies tail receiving hints latent raw requirements action callbackPlan plans callback rest ih =>
    cases typed with | invoke callable effects typed => cases checked with | cleanup localCheck next =>
      exact .push ⟨.armed (action := { action with scope := caller, answer := .unit }) scopeTypes callback rfl
        (.armed scope callable effects) localCheck, .armed⟩ (ih next typed) (List.Subset.refl _)

end Ash.OneShot.SourceAnnotatedClosingPlans

namespace Ash.OneShot.SourceAnnotatedClosingData
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceAnnotatedStoredTyping (Segment)
open SourceConsumingStoredBounds (StackBounds)
open OwnerClosingSource (retirements)

theorem Certificate.materialize_packets
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy] {hints : Hints captured} {saved : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (certificate : Certificate operations policy contracts tables world capture plan saved raw requirements)
    (checked : SourceScheduledChecks.Pending outward actions phases world saved.forClosing outside)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world closing plan)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller) :
    ∃ annotated, SourceAnnotatedRuntime.makePlan capture = some annotated ∧
      (SourceAnnotatedRuntime.closeControl caller annotated).erase = closeControl caller plan ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        (SourceAnnotatedRuntime.closeControl caller annotated) .unit .unit (retirements plan) requirements [] saved.forClosing outside
        (ScopedPorts.planProvides plan ++ closing) closing (StackBounds.closing caller annotated) := by
  cases certificate with
  | checked built template same =>
      rw [← same] at checked
      have source := (template.scope (second := caller)).scheduled_stored_source
        (evidence := evidence) (families := families) (required := required) checked typed scope
      rw [same] at source
      exact ⟨_, built, SourceAnnotatedRuntime.closeControl_erase _ _, source⟩

end Ash.OneShot.SourceAnnotatedClosingData

#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.discard_parts
#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Template.scheduled_stored_source
#print axioms Ash.OneShot.SourceAnnotatedClosingData.Certificate.materialize_packets
