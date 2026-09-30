import SourceScheduledRechecking
import SourcePlannedClosingRecomposition

/-! Materialize the stored closing template at its exact retained callback
plans. The disposal schedule supplies their checks at the new receiving suffix;
source and requirement bodies remain those of the selected record. -/
namespace Ash.OneShot.SourcePlannedClosingPlans
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest closingForest)
open RecursiveRequirements (Requirements evaluate)
open OwnerClosingSource (retirements)

/-- Construct typed closing frames from the exact selected template and its
scheduled forest, retaining all callback plans and requirement bodies. -/
theorem Template.scheduled_source {plans : Plans plan hints} {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints}
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (checked : SourceScheduledChecks.Pending outward actions phases world (closingForest plans) outside)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world closing plan)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller) :
    SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      (closeControl caller plan) .unit .unit (retirements plan) requirements [] (closingForest plans) outside
      (ScopedPorts.planProvides plan ++ closing) closing := by
  have scopeTypes := ScopedPorts.effect_scope_known_has_types scope
  induction template with
  | nil => exact .nil (List.Subset.refl _)
  | release rest ih => cases typed with | release typed => cases checked with | cell next =>
      exact .push (.cell scopeTypes (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl
        (.cell scope (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]))) (ih next typed) (List.Subset.refl _)
  | retire known rest ih => cases typed with | retire typed => cases checked with | running next =>
      exact .push (.retiring known (.retiring (CoherentSourceTypes.Owners.ports_lookup
        (SourceDependencyAnnotations.contract_erase_known (SourcePlannedSources.contract_erase_known known))))) (ih next typed) (List.Subset.refl _)
  | @invoke dependencies tail receiving hints latent raw requirements action callbackPlan plans callback rest ih =>
    cases typed with | invoke callable effects typed => cases checked with | cleanup localCheck next =>
      exact .push (.armed (action := { action with scope := caller, answer := .unit }) scopeTypes callback rfl
        (.armed scope callable effects) localCheck) (ih next typed) (List.Subset.refl _)

/-- Closing execution and the waiting computation retain one shared forest and
the requirement-evaluation equation of the existing append theorem. -/
theorem Template.scheduled_recompose {plans : Plans plan hints} {waitingHints : Hints waitingScope}
    {waitingForest : Forest waitingHints} {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (checked : SourceScheduledChecks.Pending outward actions phases world (closingForest plans) (waitingForest.append outside))
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world closing plan)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
    (waiting : SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      tail .unit output tailDemand tailRequirements tailRecords waitingForest outside closing outgoing) :
    ∃ combined : Requirements (retirements plan ++ tailDemand),
      SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        ((closeControl caller plan).append tail) .unit output (retirements plan ++ tailDemand) combined tailRecords
        ((closingForest plans).append waitingForest) outside (ScopedPorts.planProvides plan ++ closing) outgoing ∧
      ∀ store receiving before, evaluate store receiving before combined =
        ProtectionResiduals.merge
          (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before requirements)
          (evaluate store receiving (OwnerPhaseTransitions.spendAll before (retirements plan)) tailRequirements) := by
  exact SourceScheduledFrames.segment_append (template.scheduled_source checked typed scope) waiting rfl HEq.rfl HEq.rfl

end Ash.OneShot.SourcePlannedClosingPlans

#print axioms Ash.OneShot.SourcePlannedClosingPlans.Template.scheduled_source
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Template.scheduled_recompose
