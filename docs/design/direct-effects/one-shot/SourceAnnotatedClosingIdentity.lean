import SourceAnnotatedClosingData
import SourceAnnotatedAdmission

/-! Equal erased closing plans need not retain the same checked annotations.
Reuse the two admitted binding choices to exhibit two closed cleanup callbacks
at the same rich type, requirement template and saved forest. This rules out
recovering exact annotated-plan identity from the existing raw indices alone. -/
namespace Ash.OneShot.SourceAnnotatedClosingIdentity
open SourceAnnotatedCode (Term)
open SourceAnnotatedCode.Examples (program functionHint)
open SourceAnnotatedSources (Expression ValueSummary)
open SourceAnnotatedSources.Examples (parameterHint program_source)
open SourceAnnotatedRuntime (Action CloseEntry closeControl)
open SourceAnnotatedClosingPlans (Plans Template)
open SourcePlanSignatures (signature)

def callback (integer : Bool) : Term :=
  .lambda (functionHint .unit) 4 (program (parameterHint integer))

theorem callback_source (integer : Bool) :
    ValueSummary operations policy contracts [] environment [] (callback integer)
      (.function .unit .unit [] [] (signature SourceFocusAnnotationGap.plan)) := by
  refine .checked (by change true = true; rfl) ?_ (.lambda (program_source integer) ?_ ?_ (by simp))
  · cases integer <;> decide
  · exact .sequence (.sequence (.request (layers := [])) (.request (layers := []))) (.request (layers := []))
  · simp [ScopedPorts.InWorld, SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase,
      CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]

def action (integer : Bool) : Action :=
  ⟨0, callback integer, ⟨trivial, rfl, by intro dependency member; cases member⟩, .none, .unit, []⟩

def plans (integer : Bool) : Plans [.invoke (action integer)]
    (.cleanup (needs := []) (callback := .sequence (.sequence .pure .pure) .pure) .nil) :=
  .invoke SourceFocusAnnotationGap.plan .nil

theorem template (integer : Bool) :
    Template operations policy contracts tables [] .none (plans integer) []
      (.sequence (.request [] []) (.request [] [])) := by
  exact Template.invoke (action := action integer) (callbackPlan := SourceFocusAnnotationGap.plan)
    (plans := .nil) (callback_source integer) .nil

theorem erased_plan_same :
    ([CloseEntry.invoke (action false)]).map CloseEntry.erase =
      ([CloseEntry.invoke (action true)]).map CloseEntry.erase := rfl

/-- Either annotated witness inhabits the same existing raw certificate index. -/
theorem certificate (integer : Bool) :
    SourceAnnotatedClosingData.ErasedCertificate operations policy contracts tables []
      (([CloseEntry.invoke (action false)]).map CloseEntry.erase)
      (SourceRetainedPlans.Forest.cleanup (needs := []) SourceFocusAnnotationGap.plan .nil) []
      (.sequence (.request [] []) (.request [] [])) :=
  .checked (annotated := [CloseEntry.invoke (action integer)]) (plans := plans integer) (template integer) rfl

theorem annotated_plan_different :
    [CloseEntry.invoke (action false)] ≠ [CloseEntry.invoke (action true)] := by
  intro same
  cases same

theorem closing_control_different :
    closeControl .none [CloseEntry.invoke (action false)] ≠
      closeControl .none [CloseEntry.invoke (action true)] := by
  intro same
  cases same

theorem erased_closing_control_same :
    (closeControl .none [CloseEntry.invoke (action false)]).erase =
      (closeControl .none [CloseEntry.invoke (action true)]).erase := rfl

end Ash.OneShot.SourceAnnotatedClosingIdentity

#print axioms Ash.OneShot.SourceAnnotatedClosingIdentity.callback_source
#print axioms Ash.OneShot.SourceAnnotatedClosingIdentity.template
#print axioms Ash.OneShot.SourceAnnotatedClosingIdentity.certificate
#print axioms Ash.OneShot.SourceAnnotatedClosingIdentity.erased_plan_same
#print axioms Ash.OneShot.SourceAnnotatedClosingIdentity.annotated_plan_different
#print axioms Ash.OneShot.SourceAnnotatedClosingIdentity.closing_control_different
#print axioms Ash.OneShot.SourceAnnotatedClosingIdentity.erased_closing_control_same
