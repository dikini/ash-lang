import SourceConsumingAdmissionPhases
import SourceConsumingHandlerAdmissionExamples
import SourceConsumingStructuralCleanupExamples
import SourceScheduledSourceRecheckingExamples

/-! Retiring an unrelated owner preserves actual structural admission, including
outside-owner invocations and rich callbacks. Retiring a retained owner fails
the independently checked availability premise. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples
open SourceScheduledPhaseRestriction (AvailableOn)
open SourceScheduledCapabilityAnnotations (recipeLaws)
open OwnerPhaseTransitions (available spend)
open SourceDependencyOwners (owners)
open SourceDependencyCapture (Scope)
open SourceScheduledSourceRechecking

private theorem extended (names : List Nat) :
    AvailableOn names phases (available (names ++ [88])) := by
  intro name member _
  exact if_pos (List.mem_append_left _ member)

def structuralScope := Scope.live 19 (.plain (.invoke ⟨37, .resume⟩) .nil) (.live 37 .nil (.cell 4 .nil))
def extraPhases := available ([19, 37] ++ [88])

theorem structural_extension : AvailableOn (owners structuralScope) StructuralExamples.phases extraPhases :=
  extended [19, 37]

theorem retire_unrelated : AvailableOn (owners structuralScope) extraPhases (spend extraPhases 88) :=
  absent_available (by decide)

/-- The start phase really includes an available owner that the final phase
consumes. This is not an equality of phase maps disguised as transport. -/
theorem phase_changed : extraPhases 88 = .available ∧ (spend extraPhases 88) 88 = .consumed := ⟨rfl, rfl⟩

theorem structural_source_preserved :
    At (recipeLaws []) (fun evidence => evidence) StructuralExamples.body
      ((StructuralExamples.context.restrict_phases structural_extension).restrict_phases retire_unrelated) :=
  (StructuralExamples.admitted.restrict_phases structural_extension).restrict_phases retire_unrelated

theorem structural_schedule_preserved :
    SourceScheduledChecks.Local [] StructuralExamples.actions (spend extraPhases 88) [4]
      StructuralExamples.clause StructuralExamples.whole := by
  apply StructuralExamples.admitted.scheduled_restrict StructuralExamples.checked
  intro name member ready
  exact retire_unrelated name member (structural_extension name member ready)

/-- Handler rewriting and fresh resources use existentially generated saved
annotations. Admission transport reconciles those witnesses while retaining
both nested handler scopes and their source bodies. -/
theorem nested_source_preserved :
    At (recipeLaws []) (fun evidence => evidence) HandlerExamples.wrappedBody
      ((Examples.context Examples.phases).restrict_phases
        (show AvailableOn [19] Examples.phases (available [19, 88]) from extended [19])) :=
  HandlerExamples.wrapped_admitted.restrict_phases (extended [19])

/-- Preserve the freshRich rule's original callback proof and its recursive
closing derivation at the changed phases. The callback still uses owner 37. -/
theorem rich_callback_preserved :
    Expression [] SourceScheduledSourceRechecking.Examples.actions
      (spend (available [37, 88]) 88) SourceScheduledSourceRechecking.Examples.request
      SourceScheduledSourceRechecking.Examples.after := by
  apply SourceScheduledSourceRechecking.Examples.rechecked.restrict_phases
  intro name member _
  change name ∈ [37] at member
  have same := List.mem_singleton.mp member
  subst name
  rfl

/-- The phase condition detects the outside invocation saved by owner 19.
Checking only owner 19, as the finite bound check does, would miss this. -/
theorem retained_owner_cannot_retire :
    ¬ AvailableOn (owners structuralScope) StructuralExamples.phases (spend StructuralExamples.phases 37) := by
  intro extension
  have impossible := extension 37 (by decide) rfl
  change Syntax.UseState.consumed = .available at impossible
  cases impossible

end Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples.structural_extension
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples.retire_unrelated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples.phase_changed
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples.structural_source_preserved
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples.structural_schedule_preserved
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples.nested_source_preserved
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples.rich_callback_preserved
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PhaseExamples.retained_owner_cannot_retire
