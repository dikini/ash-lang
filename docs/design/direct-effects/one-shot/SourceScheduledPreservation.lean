import SourceScheduledPreservationStable
import SourceScheduledPreservationAllocating

/-! Combined constructive preservation for the current one-shot state.
A request contains operational premises only. Stable steps specify their exact
successor; allocating requests leave source-dependent metadata to the existing
M1 constructions. No request or realization contains successor validity. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

/-- The complete transition interface combines fixed successors with the seven
families whose source-selected witnesses are constructed by M1. -/
inductive Request (before : Snapshot operations) : Type where
  | stable (after : Snapshot operations) (step : Stable.Step operations before after)
  | allocating (request : Allocating.Request before)

/-- Operational agreement with the supplied request, independently of validity. -/
def Realizes {operations : SourcePlannedTyping.Operations} {before : Snapshot operations}
    (request : Request before) (after : Snapshot operations) : Prop :=
  match request with
  | .stable expected _ => after = expected
  | .allocating request => Allocating.Realizes request after

/-- Every applicable transition request has an actual preserving realization.
This theorem neither assumes successor evidence nor asserts preservation for
arbitrary raw annotation choices. Availability of requests is the separate
progress obligation. -/
theorem preservation
    {operations : SourcePlannedTyping.Operations} {before : Snapshot operations}
    {ports : OperationRows operations}
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows before)
    (request : Request before) :
    ∃ after : Snapshot operations,
      LexicalUnwind.Event before.run.execution after.run.execution ∧
      Realizes request after ∧
      Valid policy outward ambient budget ports emptyRows output outputRows after := by
  cases request with
  | stable after step =>
    obtain ⟨event, next⟩ := step.preserve valid
    exact ⟨after, event, rfl, next⟩
  | allocating request =>
    exact request.preserve valid

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.preservation
