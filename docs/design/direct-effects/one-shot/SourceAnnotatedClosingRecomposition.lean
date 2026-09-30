import SourceAnnotatedClosingPlans
import SourceAnnotatedRuntimeSegments

/-! Materialize the stored annotated cleanup sources and recompose them with
the waiting segment. The existing schedule and plan typing check the exact
erased plan; rich callback source is retained by the same template. -/
namespace Ash.OneShot.SourceAnnotatedClosingPlans
open ScopedExpressions ProtectionContracts
open SourceAnnotatedRuntime (CloseEntry closeControl closeControl_erase)
open SourceAnnotatedRuntimeTyping (Segment)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest closingForest)
open RecursiveRequirements (Requirements evaluate)
open OwnerClosingSource (retirements)

theorem Template.scope
    (template : Template operations policy contracts tables world first plans raw requirements) :
    Template operations policy contracts tables world second plans raw requirements := by
  have same : ∀ plan, OwnerPhases.ofStack tables (closeControl first plan).erase =
      OwnerPhases.ofStack tables (closeControl second plan).erase := by
    intro plan
    rw [closeControl_erase, closeControl_erase]
    exact RecursiveRecords.plan_context_scope tables _
  induction template with
  | nil => exact .nil
  | release rest ih => rw [same]; exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => rw [same]; exact .invoke callback ih

/-- The template's actual annotated callbacks become armed runtime frames.
No annotated successor source or callback reannotation is a premise. -/
theorem Template.scheduled_source
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy] {plans : Plans plan hints} {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints}
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (checked : SourceScheduledChecks.Pending outward actions phases world (closingForest plans.erase) outside)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world closing (plan.map CloseEntry.erase))
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      (closeControl caller plan) .unit .unit (retirements (plan.map CloseEntry.erase)) requirements [] (closingForest plans.erase) outside
      (ScopedPorts.planProvides (plan.map CloseEntry.erase) ++ closing) closing := by
  have scopeTypes := ScopedPorts.effect_scope_known_has_types scope
  induction template with
  | nil => exact .nil (List.Subset.refl _)
  | release rest ih => cases typed with | release typed => cases checked with | cell next =>
      exact .push (.cell scopeTypes (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl
        (.cell scope (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]))) (ih next typed) (List.Subset.refl _)
  | retire known rest ih => cases typed with | retire typed => cases checked with | running next =>
      exact .push (.retiring known (.retiring (CoherentSourceTypes.Owners.ports_lookup
        (SourceDependencyAnnotations.contract_erase_known (SourcePlannedSources.contract_erase_known known)))))
        (ih next typed) (List.Subset.refl _)
  | @invoke dependencies tail receiving hints latent raw requirements action callbackPlan plans callback rest ih =>
    cases typed with | invoke callable effects typed => cases checked with | cleanup localCheck next =>
      exact .push (.armed (action := { action with scope := caller, answer := .unit }) scopeTypes callback rfl
        (.armed scope callable effects) localCheck) (ih next typed) (List.Subset.refl _)

/-- Reuse segment append, preserving its exact retirement list and requirement
evaluation equation under the waiting stack's ordered interpretations. -/
theorem Template.scheduled_recompose
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification] {plans : Plans plan hints} {waitingHints : Hints waitingScope}
    {waitingForest : Forest waitingHints} {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (checked : SourceScheduledChecks.Pending outward actions phases world (closingForest plans.erase) (waitingForest.append outside))
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world closing (plan.map CloseEntry.erase))
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
    (waiting : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      tail .unit output tailDemand tailRequirements tailRecords waitingForest outside closing outgoing) :
    ∃ combined : Requirements (retirements (plan.map CloseEntry.erase) ++ tailDemand),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        ((closeControl caller plan).append tail) .unit output (retirements (plan.map CloseEntry.erase) ++ tailDemand) combined tailRecords
        ((closingForest plans.erase).append waitingForest) outside (ScopedPorts.planProvides (plan.map CloseEntry.erase) ++ closing) outgoing ∧
      ∀ store receiving before, evaluate store receiving before combined =
        ProtectionResiduals.merge
          (evaluate store (OwnerPhases.ofStack tables tail.erase ++ receiving) before requirements)
          (evaluate store receiving (OwnerPhaseTransitions.spendAll before (retirements (plan.map CloseEntry.erase))) tailRequirements) := by
  exact SourceAnnotatedRuntimeTyping.segment_append (template.scheduled_source checked typed scope) waiting rfl HEq.rfl HEq.rfl

end Ash.OneShot.SourceAnnotatedClosingPlans

#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Template.scheduled_source
#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Template.scheduled_recompose

#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Template.scope
