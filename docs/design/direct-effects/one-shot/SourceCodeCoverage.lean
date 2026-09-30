import SourceCodeDecomposition
import SourceCodeRecordPositions

/-! Complete current and retained code coverage at an actual bound snapshot.
Computation, focus and plain return derive their successor code from the source
already present. This invariant does not assert contextual AtUse admission. -/
namespace Ash.OneShot.SourceScheduledSavedPlans
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

theorem saved_append_nil {hints : Hints scope} (forest : Forest hints) :
    (⟨_, _, forest.append .nil⟩ : Saved) = ⟨_, _, forest⟩ :=
  (SourceScheduledRecomposition.predicate_congr
    (SourceDependencyProjection.scope_append_nil _)
    (SourcePlannedRecomposition.hints_append_nil _)
    (SourceScheduledRecomposition.forest_append_nil forest)
    (fun target => (⟨_, _, target⟩ : Saved) = ⟨_, _, forest⟩)).mpr rfl

end Ash.OneShot.SourceScheduledSavedPlans

namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)
open SourcePlanBounds (ofCode)
open SourceScheduledSavedPlans (saved_append_nil)

variable [declarations : DeclarationPolicy]

structure Snapshot.CodeCoverage (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (snapshot : Snapshot world) where
  current : Code world snapshot.plan snapshot.forest
  ready : current.Valid outward actions phases
  origin : ofCode current = snapshot.current
  pending : snapshot.pending.Records (CodeRecord outward actions phases)
  located : Retained.Records.AtReceivers outward actions phases pending .nil

theorem Snapshot.CodeCoverage.computed {before after : Snapshot world}
    (covered : before.CodeCoverage outward actions phases) (step : Computed rule before after) :
    Nonempty (after.CodeCoverage outward actions phases) := by
  cases step with
  | step before bounds selected =>
      obtain ⟨source, ready, origin⟩ := covered.current.reduced covered.ready (covered.origin.symm ▸ selected)
      exact ⟨⟨source, ready, origin, covered.pending, covered.located⟩⟩

/-- Return consumes the actual head record, reconstructing code from its
authenticated receiver rather than asking for a new queued-source judgment. -/
theorem Snapshot.CodeCoverage.returned {before after : Snapshot world}
    (covered : before.CodeCoverage outward actions phases) (step : Returned position before after) :
    Nonempty (after.CodeCoverage outward actions phases) := by
  cases step with
  | plain currentBounds queued remaining =>
      rcases covered with ⟨current, currentReady, currentOrigin, pending, located⟩
      cases pending with
      | plain record tail =>
        cases located with
        | plain located rest =>
          obtain ⟨source, ready, origin⟩ := record.at_receiver (located.trans (saved_append_nil _))
          cases origin
          exact ⟨⟨source.plug position, source.plug_valid position ready, source.plug_bounds position, tail, rest⟩⟩

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Focus stores the derived queued code and carries all old records intact.
The four metadata cases cover the existing ten expression focus forms. -/
theorem Snapshot.CodeCoverage.focused
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {before after : Snapshot world}
    (covered : before.CodeCoverage outward actions phases) (step : Focused before after) :
    Nonempty (after.CodeCoverage outward actions phases) := by
  cases step with
  | step before childBounds restBounds selected =>
      obtain ⟨current, queued, currentReady, queuedReady, currentOrigin, queuedOrigin⟩ :=
        covered.current.focused laws project covered.ready (covered.origin.symm ▸ selected)
      let record : CodeRecord outward actions phases restBounds :=
        ⟨⟨_, _, before.forest⟩, queued, queuedOrigin, queuedReady⟩
      exact ⟨⟨current, currentReady, currentOrigin, .plain record covered.pending,
        .plain (saved_append_nil before.forest).symm covered.located⟩⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceScheduledSavedPlans.saved_append_nil
#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.CodeCoverage.computed
#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.CodeCoverage.returned
#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.CodeCoverage.focused
