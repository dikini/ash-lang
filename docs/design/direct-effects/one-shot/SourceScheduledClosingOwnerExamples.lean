import SourceScheduledClosingTransport
import SourceScheduledFreshClosingExamples

/-! A fresh disposer can pass the operation guard and ordinary pending-owner
bound while its callback refers to a captured owner that closing retires.
This is a source/context obstruction, not an unsafe typed execution claim. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceDependencyOwners (CallbacksWithin PendingWithin owners)
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies disposeTable disposeDependencies)

def actions : Syntax.UsageTickets := fun owner => if owner = 37 then some ⟨true, false⟩ else none
def phases := OwnerPhaseTransitions.available [37]
def invocation := Plan.invoke (key := ⟨37, .resume⟩)
def waiting : Forest (Hints.handler (effect := effectE) (table := resumeTable)
    (families := resumeDependencies) [] .nil) := .handler .nil
def front := Forest.cleanup (needs := []) invocation (.live (owner := 37) .nil .nil)
def callback : Code [] invocation (.running ((Forest.live (owner := 37) .nil .nil).append waiting)) :=
  .resume (.running .hit) (.operations .nil) (.running (.operations .nil)) (.handler (.operations .nil))
def original : Retained [] front waiting :=
  .cleanup callback (.live (.operations .nil) (.operations .nil))
def request : Code [] (.request (effect := effectE) (operation := 0)) (front.append waiting) :=
  .operations [(effectE, 0)] .request .request

def target := front.append (.handler (effect := effectE) (table := disposeTable)
  (families := disposeDependencies) (required := []) waiting)
def captured := front.append (.handler (effect := effectE) (table := disposeTable)
  (families := disposeDependencies) (required := []) .nil)

theorem original_valid : original.Valid [] actions phases := ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
theorem request_valid : request.Valid [] actions phases := rfl

theorem intercepted : SourceScheduledHandlerSelection.Intercept effectE 0 ⟨true, some [], none⟩
    (some SourceDependencyCapture.Examples.disposeFamily, none) disposeTable disposeDependencies []
    (front.append waiting) target captured waiting := .cleanup (.live (.hit rfl rfl))

theorem guard_passes : SourceDependencyCapture.checkCapture []
    (.cleanup [] (.invoke ⟨37, .resume⟩) (.live 37 .nil
      (.handler effectE disposeTable disposeDependencies (.handler effectE resumeTable resumeDependencies .nil))))
    effectE 0 = true := by decide

theorem pending_owners_pass : PendingWithin [] [37]
    (.cleanup [] (.invoke ⟨37, .resume⟩) (.live 37 .nil (.handler effectE disposeTable disposeDependencies .nil))) :=
  .cleanup (.live .nil (.handler .nil))

/-- The callback's only owner is inside the capture, not the surviving tail. -/
theorem callback_owner_rejected : ¬ CallbacksWithin [] []
    (.cleanup [] (.invoke ⟨37, .resume⟩) (.live 37 .nil (.handler effectE disposeTable disposeDependencies .nil))) := by
  intro bound
  cases bound with
  | cleanup code tail => cases code with
    | invoke included => cases included

/-- Reuse the necessary bound from a checked closing schedule. Every candidate
target annotation is excluded; this is not just failure of a generator choice. -/
theorem no_target (annotation : Code [] (.request (effect := effectE) (operation := 0)) target) :
    ¬ annotation.Valid [] actions phases := by
  intro ready
  have checked := annotation.compile_with (recipeLaws []) ready
  have bounded := checked.disposal_owner_bounds (recipeLaws []).projected intercepted.cut rfl
  exact callback_owner_rejected bounded.2

theorem no_rechecking : ¬ Expression [] actions phases request target := by
  intro changed
  obtain ⟨annotation, valid, _⟩ := changed.compile_retaining (recipeLaws []) (fun evidence => evidence) request_valid
  exact no_target annotation valid

/-- The new bound still permits the previously checked mixed callbacks, whose
invocation names a live owner in the surviving waiting tail. -/
theorem outside_callback_permitted : CallbacksWithin [4] [37]
    (.cleanup [.cell 4] (.request (.cell 4) 0)
      (.cleanup [] (.invoke ⟨37, .resume⟩)
        (.handler FreshClosingExamples.shadow resumeTable resumeDependencies .nil))) := by
  have bound := FreshClosingExamples.closing.callback_owners
    (recipeLaws FreshClosingExamples.outward) (fun evidence => evidence) FreshClosingExamples.original_valid
  exact bound

end Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples

namespace Ash.OneShot.SourceScheduledSourceRechecking.ClosingRetirementExamples
open SourceDeclarationPlans (Plan)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceDependencyOwners (owners PendingWithin)
open OwnerPhaseTransitions (spendAll introduce)

def actions := Examples.actions.insert 19 ⟨true, true⟩
def phases := introduce Examples.phases 19
def invocation := Plan.invoke (key := ⟨19, .resume⟩)
def front := Forest.plain invocation (Forest.live (owner := 19) .nil FreshClosingExamples.front)

def fullTail : Retained [4]
    (FreshClosingExamples.front.append FreshClosingExamples.waiting) .nil :=
  .cleanup FreshClosingExamples.operationSource
    (.cleanup FreshClosingExamples.invokeSource
      (.handler (.live (.operations .nil) (.cell (.handler (.operations .nil))))))

def ordinary : Code [4] invocation
    (Forest.live (owner := 19) .nil (FreshClosingExamples.front.append FreshClosingExamples.waiting)) :=
  .resume .hit (.operations .nil) (.operations .nil) fullTail

def original : Retained [4] front FreshClosingExamples.waiting :=
  .plain ordinary (.live (.operations .nil) FreshClosingExamples.original)

theorem original_valid : original.Valid FreshClosingExamples.outward actions phases := by
  dsimp only [original, ordinary, fullTail, FreshClosingExamples.original,
    FreshClosingExamples.operationSource, FreshClosingExamples.invokeSource, Code.Valid, Retained.Valid]
  repeat' constructor

/-- The original normal source really uses the owner that disposal retires;
its validity cannot be transported unchanged through that retirement. -/
theorem normal_source_invalid_after_retirement :
    ¬ original.Valid FreshClosingExamples.outward actions (spendAll phases [19]) := by
  intro ready
  have unavailable := ready.1.2.1
  change Syntax.UseState.consumed = .available at unavailable
  cases unavailable

theorem closing : Closing FreshClosingExamples.outward actions phases original
    (.running FreshClosingExamples.waiting) := by
  apply Closing.plain
  apply Closing.live Closing.empty
  apply FreshClosingExamples.closing.transport
    (Syntax.fresh_usage_insert_extends (show Examples.actions 19 = none from rfl))
  intro owner _ ready
  by_cases same : owner = 19
  · subst owner; rfl
  · simpa only [phases, introduce, if_neg same] using ready

/-- Compilation drops ordinary owner-19 code and preserves the cell operation
and outside-owner-37 callback at the changed phases, with exact source metadata. -/
theorem generated_after_retirement :
    ∃ annotation : Retained [4] front.forClosing (.running FreshClosingExamples.waiting),
      annotation.Valid FreshClosingExamples.outward actions (spendAll phases [19]) ∧
      SourceBoundSnapshots.Retained.ofCapability annotation =
        (SourceBoundSnapshots.Retained.ofCapability original).forClosing := by
  apply closing.compile_retiring (recipeLaws FreshClosingExamples.outward) (fun checked => checked) original_valid
  intro owner member
  have same : owner = 37 := List.mem_singleton.mp member
  subst owner
  decide

end Ash.OneShot.SourceScheduledSourceRechecking.ClosingRetirementExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples.request_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples.intercepted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples.guard_passes
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples.pending_owners_pass
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples.callback_owner_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples.no_target
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples.no_rechecking
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingOwnerExamples.outside_callback_permitted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingRetirementExamples.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingRetirementExamples.normal_source_invalid_after_retirement
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingRetirementExamples.closing
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ClosingRetirementExamples.generated_after_retirement
