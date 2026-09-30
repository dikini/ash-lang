import SourceScheduledInterceptSource
import SourceScheduledFreshClosingExamples

/-! Recover a nonempty original callback prefix from whole source at fresh
disposal. No separate normal-prefix annotation is an input to rechecking. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceDependencyCapture.Examples
  (effectE resumeTable resumeDependencies disposeTable disposeDependencies)

def callbackEffect : Instance := .user 701 []
def outward : List Instance := [callbackEffect]
def actions : Syntax.UsageTickets := fun _ => none
def phases : OwnerPhaseTransitions.Phases := OwnerPhaseTransitions.available []
def waiting : Forest (Hints.handler (effect := callbackEffect) (table := resumeTable)
    (families := resumeDependencies) []
    (.handler (effect := effectE) (table := resumeTable) (families := resumeDependencies) [] .nil)) :=
  .handler (.handler .nil)
def front := Forest.cleanup (needs := [callbackEffect])
  (.request (effect := callbackEffect) (operation := 0)) .nil
def target := front.append (.handler (effect := effectE) (table := disposeTable)
  (families := disposeDependencies) (required := []) waiting)
def captured := front.append (.handler (effect := effectE) (table := disposeTable)
  (families := disposeDependencies) (required := []) .nil)
def wholeSource : Retained [] (front.append waiting) .nil :=
  .cleanup (.operations [(callbackEffect, 0)] .request .request)
    (.handler (.handler (.operations .nil)))
def request : Code [] (.request (effect := effectE) (operation := 0)) (front.append waiting) :=
  .operations [(effectE, 0)] .request .request

theorem whole_ready : wholeSource.Valid outward actions phases := ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩
theorem request_ready : request.Valid outward actions phases := rfl

theorem intercepted : SourceScheduledHandlerSelection.Intercept effectE 0 ⟨true, some [], none⟩
    (some SourceDependencyCapture.Examples.disposeFamily, none)
    disposeTable disposeDependencies [] (front.append waiting) target captured waiting :=
  .cleanup (.hit rfl rfl)

noncomputable def recovered := InterceptSource.recoverAt front rfl intercepted wholeSource whole_ready

/-- The waiting suffix and the actual callback snapshot remain those split
from the whole original annotation, even though recovery uses existence proofs. -/
theorem source_retained : HEq
    ((SourceBoundSnapshots.Retained.ofCapability recovered.normal).append
      (SourceBoundSnapshots.Retained.ofCapability recovered.tail))
    (SourceBoundSnapshots.Retained.ofCapability wholeSource) := recovered.original

theorem callback_closing : Closing outward actions phases recovered.normal (.running waiting) :=
  .request_callback (SourceContextualRequirements.check_capability_iff.mp rfl)

theorem rechecked : Expression outward actions phases request target :=
  recovered.rechecking (by decide) (fun _ => .cleanup (.handler .nil)) (fun _ => callback_closing)

theorem generated : ∃ annotation : Code [] (.request (effect := effectE) (operation := 0)) target,
    annotation.Valid outward actions phases ∧
    SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode request :=
  rechecked.compile_retaining (recipeLaws outward) (fun evidence => evidence) request_ready

/-- Original source validity does not manufacture a capability for executing
the same callback with an empty outside receiver. -/
theorem missing_callback_capability :
    ¬ SourceContextualClauses.RequestCapability callbackEffect 0 (.running .nil) := by
  intro capability
  have impossible := SourceContextualRequirements.check_capability_iff.mpr capability
  change false = true at impossible
  cases impossible

end Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples

namespace Ash.OneShot.SourceScheduledSourceRechecking.InterceptJoinedExamples
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open FreshClosingExamples
open SourceScheduledSourceRechecking.Examples (actions phases)
open SourceDependencyCapture.Examples (effectE)

def suffix : Retained [4] waiting .nil :=
  .live (.operations .nil) (.cell (.handler (.operations .nil)))
def wholeSource := original.joinSource suffix

theorem whole_ready : wholeSource.Valid outward actions phases :=
  (original.joinSource_valid suffix).mpr ⟨original_valid, ⟨rfl, ⟨rfl, rfl⟩⟩⟩

def recovered := InterceptSource.recoverJoined (by decide) intercepted original suffix whole_ready

/-- Unlike an existential split, source-directed join recovery retains the
actual callback annotation. Its existing outside-owner closing proof applies. -/
theorem original_retained : recovered.normal = original :=
  eq_of_heq (InterceptSource.recoverJoined_normal (by decide) intercepted original suffix whole_ready)

theorem closing_reused : Closing outward actions phases recovered.normal (.running waiting) :=
  original_retained.symm ▸ closing

theorem rechecked : Expression outward actions phases request target :=
  recovered.rechecking (by decide)
    (fun _ => .cleanup (.cleanup (.handler (.handler .nil)))) (fun _ => closing_reused)

theorem generated : ∃ annotation : Code [4]
    (.request (effect := effectE) (operation := 0)) target,
    annotation.Valid outward actions phases ∧
    SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode request :=
  rechecked.compile_retaining (recipeLaws outward) (fun evidence => evidence) request_valid

/-- Recovery cannot start from this whole source after its outside owner has
been consumed. This follows from the existing original-source counterexample. -/
theorem consumed_whole_rejected :
    ¬ wholeSource.Valid outward actions (OwnerPhaseTransitions.spend phases 37) :=
  fun ready => consumed_owner_rejected ((original.joinSource_valid suffix).mp ready).1

end Ash.OneShot.SourceScheduledSourceRechecking.InterceptJoinedExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples.whole_ready
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples.request_ready
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples.intercepted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples.source_retained
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples.callback_closing
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSourceExamples.missing_callback_capability

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptJoinedExamples.whole_ready
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptJoinedExamples.original_retained
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptJoinedExamples.closing_reused
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptJoinedExamples.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptJoinedExamples.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptJoinedExamples.consumed_whole_rejected
