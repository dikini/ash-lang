import SourceBoundAdmission
import SourceAnnotatedBoundFocus

/-! Existing snapshot relations preserve the structural admission of their
exact data. These proofs compose with the existing runtime preservation
theorems; they do not repeat ownership or evaluation arguments. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan)
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem Reduced.admitted {source : Annotation world first} {next : Annotation world second}
    (step : Reduced world rule source next) (admitted : source.Admitted) : next.Admitted := by
  cases step with
  | bind => exact admitted.second
  | beta => exact admitted.second.second
  | ifTrue => exact admitted.second.left
  | ifFalse => exact admitted.second.right

theorem Focused.admitted {source : Annotation world whole}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (step : Focused world source childBounds restBounds) (admitted : source.Admitted) :
    childBounds.Admitted ∧ restBounds.Admitted := by
  cases step with
  | pure => exact ⟨.absent .pure, .absent .pure⟩
  | sequence => exact ⟨admitted.first, admitted.second⟩
  | pairRight => exact ⟨admitted.second, .absent .pure⟩
  | appArgument => exact ⟨admitted.second.first, admitted.second.second⟩

theorem Annotation.Admitted.plug {plan : Plan dependencies} {bounds : Annotation world plan}
    (admitted : bounds.Admitted) (position : SourceAnnotatedCode.Context) :
    (bounds.plug position).2.2.Admitted := by
  cases position <;> first
    | exact .sequence (.absent .pure) admitted
    | exact .sequence (.absent .pure) (.sequence (.absent .pure) admitted)

end Ash.OneShot.SourcePlanBounds

namespace Ash.OneShot.SourceBoundSnapshots
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem Snapshot.value_admitted {hints : SourceContextualHints.Hints receiving}
    {forest : SourceRetainedPlans.Forest hints} {pending : Retained world forest} (admitted : pending.Admitted) :
    (Snapshot.value pending).Admitted := ⟨.absent .pure, admitted⟩

theorem Computed.admitted {before after : Snapshot world}
    (step : Computed rule before after) (admitted : before.Admitted) : after.Admitted := by
  cases step with
  | step source bounds selected => exact ⟨selected.admitted admitted.1, admitted.2⟩

theorem Focused.admitted {before after : Snapshot world}
    (step : Focused before after) (admitted : before.Admitted) : after.Admitted := by
  cases step with
  | step source child rest selected =>
      obtain ⟨childChecked, restChecked⟩ := selected.admitted admitted.1
      exact ⟨childChecked, .plain restChecked admitted.2⟩

theorem Returned.admitted {before after : Snapshot world}
    (step : Returned position before after) (admitted : before.Admitted) : after.Admitted := by
  cases step
  cases admitted.2 with
  | plain code rest => exact ⟨code.plug position, rest⟩

theorem Exited.admitted {before after : Snapshot world}
    (step : Exited boundary before after) (admitted : before.Admitted) : after.Admitted := by
  cases step
  all_goals cases admitted.2
  all_goals exact ⟨.absent .pure, ‹_›⟩

theorem StartedCleanup.admitted {before after : Snapshot world}
    (step : StartedCleanup before after) (admitted : before.Admitted) : after.Admitted := by
  cases step
  cases admitted.2 with
  | cleanup code rest => exact ⟨.sequence (.absent .pure) (.sequence (.absent .pure) code), .running rest⟩

theorem EnteredCleanup.admitted {before after : Snapshot world}
    (step : EnteredCleanup before after) (admitted : before.Admitted) : after.Admitted := by
  cases step
  exact ⟨admitted.1.second.cleanup_body, .cleanup admitted.1.second.cleanup_callback admitted.2⟩

theorem EnteredResource.admitted {before : Snapshot world} {after : Snapshot (world ++ [identity])}
    (step : EnteredResource identity before after) (admitted : before.Admitted) : after.Admitted := by
  cases step with
  | step bounds remaining fresh =>
      exact ⟨admitted.1.second.resource_body fresh,
        .cell (admitted.2.world_weaken (List.subset_append_left _ _))⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourcePlanBounds.Reduced.admitted
#print axioms Ash.OneShot.SourcePlanBounds.Focused.admitted
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.plug
#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.value_admitted
#print axioms Ash.OneShot.SourceBoundSnapshots.Computed.admitted
#print axioms Ash.OneShot.SourceBoundSnapshots.Focused.admitted
#print axioms Ash.OneShot.SourceBoundSnapshots.Returned.admitted
#print axioms Ash.OneShot.SourceBoundSnapshots.Exited.admitted
#print axioms Ash.OneShot.SourceBoundSnapshots.StartedCleanup.admitted
#print axioms Ash.OneShot.SourceBoundSnapshots.EnteredCleanup.admitted
#print axioms Ash.OneShot.SourceBoundSnapshots.EnteredResource.admitted
