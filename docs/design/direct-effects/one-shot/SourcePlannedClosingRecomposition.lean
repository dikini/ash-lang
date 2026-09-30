import SourcePlannedClosingPlans

/-! Closing checks and source compose at the same actual annotations. Registry
extension retains those annotations; materialization and stack concatenation
reuse the established joint segment theorem and its requirement equation. -/
namespace Ash.OneShot.SourcePlannedClosingPlans
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourcePlannedRecomposition (running_append_assoc)
open RecursiveRequirements (Requirements evaluate)
open OwnerClosingSource (retirements)

/-- Split or join checks of the annotated close plan without replacing a
callback plan by another witness at the same dependency index. -/
theorem Checked.append_iff {first : Plans before firstHints} {second : Plans after secondHints}
    (outside : Hints outsideScope) :
    Checked outward actions phases world outside (first.append second) ↔
      Checked outward actions phases world (secondHints.append outside) first ∧
      Checked outward actions phases world outside second := by
  induction first with
  | nil => exact ⟨fun checked => ⟨.nil, checked⟩, fun ⟨_, checked⟩ => checked⟩
  | release rest ih =>
      constructor
      · intro checked; cases checked with | release next =>
          obtain ⟨inside, remaining⟩ := ih.mp next
          exact ⟨.release inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with | release next => exact .release (ih.mpr ⟨next, remaining⟩)
  | retire rest ih =>
      constructor
      · intro checked; cases checked with | retire next =>
          obtain ⟨inside, remaining⟩ := ih.mp next
          exact ⟨.retire inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with | retire next => exact .retire (ih.mpr ⟨next, remaining⟩)
  | invoke callback rest ih =>
      constructor
      · intro checked; cases checked with | invoke localCheck next =>
          obtain ⟨inside, remaining⟩ := ih.mp next
          exact ⟨.invoke ((running_append_assoc _ _ _).mp localCheck) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with | invoke localCheck next =>
          exact .invoke ((running_append_assoc _ _ _).mpr localCheck) (ih.mpr ⟨next, remaining⟩)

theorem Template.scope
    (template : Template operations policy contracts tables world first plans raw requirements) :
    Template operations policy contracts tables world second plans raw requirements := by
  induction template with
  | nil => exact .nil
  | release rest ih =>
      simpa only [RecursiveRecords.plan_context_scope (first := first) (second := second)] using Template.release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih =>
      simpa only [RecursiveRecords.plan_context_scope (first := first) (second := second)] using Template.invoke callback ih

theorem Template.transport
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (extension : contracts.Extends nextContracts) :
    Template operations policy nextContracts tables world caller plans raw requirements := by
  induction template with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire (extension _ _ known) ih
  | invoke callback rest ih => exact .invoke (SourcePlannedSources.expression_extension callback extension) ih

/-- Materialize the stored template and join the actual waiting stack. Both
source and callback checks retain their plans, and the accounting equation is
the existing joint-segment recomposition result. -/
theorem Template.recompose {plans : Plans plan hints} {waitingHints : Hints waitingScope}
    {outside : Hints outsideScope}
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (checked : Checked outward actions phases world (waitingHints.append outside) plans)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world closing plan)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
    (waiting : SourcePlannedCheckedFrames.Segment operations policy contracts tables families required actions outward phases world
      tail .unit output tailDemand tailRequirements tailRecords waitingHints outside closing outgoing) :
    ∃ combined : Requirements (retirements plan ++ tailDemand),
      SourcePlannedCheckedFrames.Segment operations policy contracts tables families required actions outward phases world
        ((closeControl caller plan).append tail) .unit output (retirements plan ++ tailDemand) combined tailRecords
        (hints.append waitingHints) outside (ScopedPorts.planProvides plan ++ closing) outgoing ∧
      ∀ store receiving before, evaluate store receiving before combined =
        ProtectionResiduals.merge
          (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before requirements)
          (evaluate store receiving (OwnerPhaseTransitions.spendAll before (retirements plan)) tailRequirements) := by
  exact SourcePlannedCheckedFrames.segment_append (template.source checked typed scope) waiting rfl HEq.rfl

end Ash.OneShot.SourcePlannedClosingPlans

#print axioms Ash.OneShot.SourcePlannedClosingPlans.Checked.append_iff
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Template.scope
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Template.transport
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Template.recompose
