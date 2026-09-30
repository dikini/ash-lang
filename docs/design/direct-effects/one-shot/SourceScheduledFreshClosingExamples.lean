import SourceScheduledClosingOwners
import SourceScheduledSourceRecheckingExamples

/-! Fresh disposal reuses the original normal prefix and structural closing.
The prefix mixes an effectful callback with a callback invoking an outside
owner. Conservative operation annotations can be replaced by exact footprints. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies disposeTable disposeDependencies)
open SourceScheduledSourceRechecking.Examples (actions phases)

def shadow : Instance := .user 700 []
def outward : List Instance := [.cell 4]
def waiting : Forest (Hints.live (owner := 37) .nil
    (.cell (identity := 4) (.handler (effect := effectE) (table := resumeTable)
      (families := resumeDependencies) [] .nil))) := .live .nil (.cell (.handler .nil))
def delimiter : Forest (Hints.handler (effect := shadow) (table := resumeTable)
    (families := resumeDependencies) [] .nil) := .handler .nil
def invocation := Plan.invoke (key := ⟨37, .resume⟩)
def inner := Forest.cleanup (needs := []) invocation delimiter
def front := Forest.cleanup (needs := [.cell 4]) (.request (effect := .cell 4) (operation := 0)) inner

def invokeSource : Code [4] invocation (.running (delimiter.append waiting)) :=
  .resume (.running (.handler .hit)) (.operations .nil)
    (.running (.handler (.operations .nil))) (.cell (.handler (.operations .nil)))
def operationSource : Code [4] (.request (effect := .cell 4) (operation := 0))
    (.running (inner.append waiting)) :=
  .operations [(.cell 4, 0), (shadow, 0)] (.weaken .request (by simp)) .request
def original : Retained [4] front waiting :=
  .cleanup operationSource (.cleanup invokeSource (.handler (.operations .nil)))
def request : Code [4] (.request (effect := effectE) (operation := 0)) (front.append waiting) :=
  .operations [(effectE, 0)] .request .request

theorem original_valid : original.Valid outward actions phases :=
  ⟨rfl, ⟨⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ⟨rfl, rfl⟩⟩⟩

theorem request_valid : request.Valid outward actions phases := rfl

/-- The callback's actual cell request needs no capability from the handler
being erased. Its earlier annotation conservatively included that operation. -/
theorem old_requirement_unavailable : SourceContextualHints.checkRequirements
    (.running ((SourceDependencyCapture.Scope.cleanup [] (.invoke ⟨37, .resume⟩)
      (.handler shadow resumeTable resumeDependencies .nil)).forClosing.append
      (.running (.live 37 .nil (.cell 4 (.handler effectE resumeTable resumeDependencies .nil))))))
    [(.cell 4, 0), (shadow, 0)] = false := rfl

theorem closing : Closing outward actions phases original (.running waiting) := by
  apply Closing.cleanup
  · exact .reinterface .request rfl
  · apply Closing.cleanup
    · exact .resume (.running (SourceScheduledNeutral.OwnerCut.closing_prefix (.running .hit) delimiter)) .empty
        (.running (.protect (.dropHandler .empty))) .same
    · exact .handler .empty

def target := front.append (.handler (effect := effectE) (table := disposeTable)
  (families := disposeDependencies) (required := []) waiting)
def captured := front.append (.handler (effect := effectE) (table := disposeTable)
  (families := disposeDependencies) (required := []) .nil)

theorem intercepted : SourceScheduledHandlerSelection.Intercept effectE 0 ⟨true, some [], none⟩
    (some SourceDependencyCapture.Examples.disposeFamily, none)
    disposeTable disposeDependencies [] (front.append waiting) target captured waiting :=
  .cleanup (.cleanup (.handler (by decide) (.hit rfl rfl)))

/-- The delimiter is supplied by the actual interception. All callback
rechecking comes from the original prefix's structural closing derivation. -/
theorem rechecked : Expression outward actions phases request target :=
  .fresh_closing intercepted original (fun _ => original_valid) (by decide)
    (fun _ => .cleanup (.cleanup (.handler (.handler .nil)))) (fun _ => closing)

theorem generated : ∃ annotation : Code [4]
    (.request (effect := effectE) (operation := 0)) target,
    annotation.Valid outward actions phases ∧
    SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode request :=
  rechecked.compile_retaining (recipeLaws outward) (fun evidence => evidence) request_valid

/-- Closing preserves the original canonical callback metadata, including
both retained callbacks. It is not merely a validity-only reconstruction. -/
theorem closing_generated : ∃ annotation : Retained [4] front.forClosing (.running waiting),
    annotation.Valid outward actions phases ∧
    SourceBoundSnapshots.Retained.ofCapability annotation =
      (SourceBoundSnapshots.Retained.ofCapability original).forClosing :=
  closing.compile_retaining (recipeLaws outward) (fun evidence => evidence) original_valid

/-- A footprint cannot omit the callback's actual request. Reuse the existing
source compiler and its necessary request guard instead of a new induction. -/
theorem actual_request_cannot_be_omitted :
    ¬ SourceScheduledAdaptationCompilation.RequestFootprint
      (.request (effect := .cell 4) (operation := 0)) [] := by
  intro footprint
  have scheduled := SourceScheduledSourceInterfaces.compile
    (outward := []) (actions := fun _ => none) (phases := OwnerPhaseTransitions.available [])
    (world := []) (forest := Forest.nil) footprint .request rfl
  cases scheduled with
  | request guard closing =>
      have impossible := SourceDependencySchemes.checked_request guard
      change false = true at impossible
      cases impossible

/-- Changing an operation interface supplies no use of an already-consumed
outside continuation. The original source phase check still rejects it. -/
theorem consumed_owner_rejected :
    ¬ original.Valid outward actions (OwnerPhaseTransitions.spend phases 37) := by
  intro ready
  have available := ready.2.1.2.1
  simp [OwnerPhaseTransitions.spend] at available

end Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.request_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.old_requirement_unavailable
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.closing
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.intercepted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.closing_generated

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.actual_request_cannot_be_omitted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FreshClosingExamples.consumed_owner_rejected
