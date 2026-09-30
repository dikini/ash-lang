import SourceScheduledSourceRechecking

/-! A newly installed disposer closes a callback that invokes an outside owner.
This is beyond operation-only callback footprints. Original validity supplies
owner rights and phase; structural rechecking supplies the changed receivers. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.Examples
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceDependencyCapture.Examples
  (effectE resumeTable resumeDependencies disposeTable disposeDependencies)
open OwnerPhaseTransitions (Phases spend)

def actions : Syntax.UsageTickets := fun owner => if owner = 37 then some ⟨true, false⟩ else none
def phases : Phases := OwnerPhaseTransitions.available [37]
def waiting : Forest (Hints.live (owner := 37) .nil
    (.handler (effect := effectE) (table := resumeTable) (families := resumeDependencies) [] .nil)) :=
  .live .nil (.handler .nil)
def callback := Plan.invoke (key := ⟨37, .resume⟩)
def front := Forest.cleanup (needs := []) callback .nil
def after := front.append
  (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) waiting)
def saved := front.append
  (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) .nil)

def originalCallback : Code [] callback (.running waiting) :=
  .resume (.running .hit) (.operations .nil) (.operations (.running .nil)) (.handler (.operations .nil))
def original : Retained [] front waiting := .cleanup originalCallback (.operations .nil)
def request : Code [] (.request (effect := effectE) (operation := 0)) (front.append waiting) :=
  .operations [(effectE, 0)] .request .request

theorem original_valid : original.Valid [] actions phases :=
  ⟨⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩, rfl⟩
theorem request_valid : request.Valid [] actions phases := rfl

theorem rich_closing : RetainedChange [] actions phases original saved.forClosing (.running waiting) := by
  apply RetainedChange.cleanup
  · exact .resume (.running (.running .hit)) (.operations .nil rfl)
      (.operations (.running (.running .nil)) rfl) .same
  · exact .operations .nil rfl

theorem intercepted : SourceScheduledHandlerSelection.Intercept effectE 0 ⟨true, some [], none⟩
    (some SourceDependencyCapture.Examples.disposeFamily, none)
    disposeTable disposeDependencies [] (front.append waiting) after saved waiting :=
  .cleanup (.hit rfl rfl)

/-- The fresh closing annotation is generated from the original normal prefix
and recursive rules, not supplied as an already-valid target. -/
theorem rechecked : Expression [] actions phases request after :=
  .freshRich intercepted original (fun _ => original_valid) (by decide)
    (fun _ => .cleanup (.handler .nil)) (fun _ => rich_closing)

theorem generated : ∃ annotation : Code [] (.request (effect := effectE) (operation := 0)) after,
    annotation.Valid [] actions phases :=
  rechecked.compile (recipeLaws []) (fun evidence => evidence) request_valid

/-- This callback is outside the operation-only interface grammar. -/
theorem callback_not_footprint : ¬ SourceScheduledAdaptationCompilation.RequestFootprint callback required := by
  intro footprint
  exact footprint.no_invocation rfl

/-- Source validity cannot supply the already-consumed outside owner. -/
theorem consumed_original_rejected : ¬ original.Valid [] actions (spend phases 37) := by
  intro ready
  have available := ready.1.2.1
  simp [spend] at available

end Ash.OneShot.SourceScheduledSourceRechecking.Examples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Examples.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Examples.request_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Examples.rich_closing
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Examples.intercepted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Examples.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Examples.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Examples.callback_not_footprint
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Examples.consumed_original_rejected
