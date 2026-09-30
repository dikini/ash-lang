import SourceAnnotatedRuntimeFocus
import SourceAnnotatedRuntimeReturnSteps
import SourceAnnotatedAdmission

/-! Initial admission and focusing retain the two distinct type choices of
the earlier erased-code ambiguity. The example constructs its initial invariant
and derives the successor from the finite guard. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeExamples
open SourceAnnotatedCode.Examples (unit initializer program)
open SourceAnnotatedSources.Examples (parameterHint)
open SourceAnnotatedRuntime (Plain)
open SourceAnnotatedRuntimeState (State)

def bindingFrame (integer : Bool) : Plain :=
  ⟨.bind .unit 0 unit, .none,
    (if integer then .function .integer .unit [] [] else .function .unit .unit [] []), .unit, [], rfl⟩

theorem frame_guard (integer : Bool) :
    SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty (initializer (parameterHint integer))
      .unit .nil (bindingFrame integer).erase = true := by
  cases integer <;> decide

theorem wrong_parameter_guard :
    SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty (initializer (parameterHint false))
      .unit .nil (bindingFrame true).erase = false := by decide

theorem initial (integer : Bool) :
    SourceAnnotatedRuntimeState.State operations policy (fun _ => none) tables families required (fun _ => none) (fun _ => none)
      [] [] [] .none (program (parameterHint integer)) .nil .nil .unit [] [] evidence := by
  apply SourceAnnotatedRuntimeState.initial (SourceAnnotatedSources.Examples.program_source integer) rfl
    SourceFocusAnnotationGap.scheduled
  · exact (SourceScheduledExecution.checkInitial_iff.mp SourceFocusAnnotationGap.admitted).1
  · rfl

/-- Binding focus chooses the type recorded by the actual initializer hint;
both annotations remain admitted, and their saved frame types differ. -/
theorem focused (integer : Bool) :
    ∃ (dependencies : SourceDependencyAnnotations.Dependencies) (plan : SourceDeclarationPlans.Plan dependencies),
      SourceAnnotatedRuntimeState.State operations policy (fun _ => none) tables families required (fun _ => none) (fun _ => none)
        [] [] [] .none (initializer (parameterHint integer)) (.push (.plain (bindingFrame integer)) .nil)
        (.plain plan .nil) .unit [] [] evidence := by
  obtain ⟨dependencies, plan, step, next⟩ := SourceAnnotatedRuntimeFocus.focus_preserves (plain := bindingFrame integer)
    (initial (operations := operations) (policy := policy) (tables := tables) (families := families)
      (required := required) (evidence := evidence) integer)
    (SourceAnnotatedCode.Examples.binding_focus (parameterHint integer)) (frame_guard integer)
  exact ⟨dependencies, plan, next⟩

/-- Ordinary computation preserves the same annotated saved frame after the
focus step. No independently assumed intermediate invariant is used. -/
theorem focused_bind (integer : Bool) :
    ∃ (dependencies : SourceDependencyAnnotations.Dependencies) (plan : SourceDeclarationPlans.Plan dependencies),
      SourceAnnotatedRuntimeState.State operations policy (fun _ => none) tables families required (fun _ => none) (fun _ => none)
        [] [] [] .none (SourceAnnotatedCode.Examples.constant (parameterHint integer))
        (.push (.plain (bindingFrame integer)) .nil) (.plain plan .nil) .unit [] [] evidence := by
  obtain ⟨dependencies, plan, focusedState⟩ := focused
    (operations := operations) (policy := policy) (tables := tables) (families := families)
    (required := required) (evidence := evidence) integer
  exact ⟨dependencies, plan, SourceAnnotatedRuntimeState.bind_preserves focusedState
    ⟨trivial, rfl, by intro dependency member; cases member⟩⟩

/-- Returning the computed initializer reconstructs the annotated binding
from the saved frame and its actual retained plan. -/
theorem returned (integer : Bool) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceAnnotatedRuntimeState.State operations policy (fun _ => none) tables families required (fun _ => none) (fun _ => none)
        [] [] [] .none (.bind .unit 0 (SourceAnnotatedCode.Examples.constant (parameterHint integer)) unit)
        .nil rest.forest .unit [] [] evidence := by
  obtain ⟨dependencies, plan, focusedState⟩ := focused_bind
    (operations := operations) (policy := policy) (tables := tables) (families := families)
    (required := required) (evidence := evidence) integer
  obtain ⟨rest, contextDependencies, contextPlan, same, next⟩ :=
    SourceAnnotatedRuntimeReturns.plug_preserves focusedState
      ⟨trivial, rfl, by intro dependency member; cases member⟩
  exact ⟨rest, next⟩

/-- Both formerly ambiguous source choices now reach the unit endpoint with
an empty runtime stack, through focus, computation, return and final binding. -/
theorem completed (integer : Bool) :
    ∃ rest : SourceScheduledSavedPlans.Saved,
      SourceAnnotatedRuntimeState.State operations policy (fun _ => none) tables families required (fun _ => none) (fun _ => none)
        [] [] [] .none unit .nil rest.forest .unit [] [] evidence := by
  obtain ⟨rest, returnedState⟩ := returned
    (operations := operations) (policy := policy) (tables := tables) (families := families)
    (required := required) (evidence := evidence) integer
  exact ⟨rest, SourceAnnotatedRuntimeState.bind_preserves returnedState
    ⟨trivial, rfl, by intro dependency member; cases member⟩⟩

end Ash.OneShot.SourceAnnotatedRuntimeExamples

#print axioms Ash.OneShot.SourceAnnotatedRuntimeExamples.frame_guard
#print axioms Ash.OneShot.SourceAnnotatedRuntimeExamples.wrong_parameter_guard
#print axioms Ash.OneShot.SourceAnnotatedRuntimeExamples.initial
#print axioms Ash.OneShot.SourceAnnotatedRuntimeExamples.focused
#print axioms Ash.OneShot.SourceAnnotatedRuntimeExamples.focused_bind

#print axioms Ash.OneShot.SourceAnnotatedRuntimeExamples.returned
#print axioms Ash.OneShot.SourceAnnotatedRuntimeExamples.completed
