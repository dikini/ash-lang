import SourceAnnotatedContexts

/-! Annotated initial source admission projects to the established scheduled
runtime theorem. Scheduling, completion and signature premises remain explicit;
this is not complete initial admission. Examples retain both formerly ambiguous
binding choices as distinct checked syntax. -/
namespace Ash.OneShot.SourceAnnotatedSources
open SourcePlannedTyping (Value)
open SourcePlanSignatures (signature)

/-- Reuse initial runtime construction with the very same source types and
requirements, forgetting only finite annotations. -/
theorem initial_run {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (contextual : SourceScheduledChecks.Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] plan .nil)
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (signature : operations.erase.erase.ports = DeclarationResults.signature declarations) :
    demand = [] ∧ SourceScheduledExecution.Run operations declarations policy (fun _ => none) (fun _ => none)
      tables families required (fun _ => none) ⟨⟨⟨code.erase, .none, .nil⟩, [], []⟩, []⟩
      .nil output [] [] resultBound :=
  SourceScheduledExecution.initial_run source.erase contextual admitted result signature

namespace Examples
open SourceAnnotatedCode
open SourceAnnotatedCode.Examples (unit constant initializer program)
open SourceFocusAnnotationGap (functionType requirements plan)

theorem unit_source : Expression operations policy contracts world allowed scope environment
    unit .unit [] (.request [] []) .pure :=
  .checked (by decide) (by decide) .unit

/-- A finite choice between two parameter types exercises the erased-code
ambiguity without imposing a canonical inferred type. -/
def parameterHint (integer : Bool) : Instantiation.ValueType := if integer then .integer else .unit
def parameterType (integer : Bool) : Value := if integer then .integer else .unit

theorem constant_source (integer : Bool) : Expression operations policy contracts [] [] scope environment
    (constant (parameterHint integer)) (functionType (parameterType integer)) [] (.request [] []) .pure := by
  refine .checked ?_ ?_ (.lambda unit_source (RecursiveOutward.Outward.request (layers := [])) ?_ (by simp))
  · cases integer <;> decide
  · cases integer <;> decide
  · cases integer <;> simp [parameterType, ScopedPorts.InWorld, ScopedPorts.Port.resources,
      CoherentSourceTypes.Value.port, SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase]

theorem initializer_source (integer : Bool) : Expression operations policy contracts [] [] scope environment
    (initializer (parameterHint integer)) (functionType (parameterType integer)) []
    (.sequence (.request [] []) (.request [] [])) (.sequence .pure .pure) := by
  refine .checked ?_ ?_ (.bind unit_source (constant_source integer))
  · cases integer <;> decide
  · cases integer <;> decide

theorem program_source (integer : Bool) : Expression operations policy contracts [] [] scope environment
    (program (parameterHint integer)) .unit [] requirements (signature plan) := by
  refine .checked (by change true = true; rfl) ?_ (.bind (initializer_source integer) unit_source)
  cases integer <;> decide

theorem admitted_program (integer : Bool) :
    SourceScheduledExecution.Run SourceScheduledExecution.InitialAdmissionExamples.operations (fun _ => none) policy (fun _ => none) (fun _ => none)
      tables families required (fun _ => none)
      ⟨⟨⟨(program (parameterHint integer)).erase, .none, .nil⟩, [], []⟩, []⟩ .nil .unit [] [] (.storage []) :=
  (initial_run (plan := plan) (program_source integer) SourceFocusAnnotationGap.scheduled
    SourceFocusAnnotationGap.admitted SourceFocusAnnotationGap.completion SourceScheduledExecution.InitialAdmissionExamples.signature_agreement).2

/-- The finite syntax that chooses a unit parameter cannot silently change to
an integer-parameter initializer under another rich source derivation. -/
theorem changed_initializer_rejected :
    ¬ Expression operations policy contracts world allowed scope environment
      (initializer (parameterHint false)) (functionType .integer) demand req checking := by
  intro source
  have checked := source.hint_checked
  change false = true at checked
  cases checked

/-- Resource names inside body hints are accepted under their local binder and
checked at every fresh opening; the body actually refers to the acquired cell. -/
theorem local_resource_source : Expression operations policy contracts [] [] scope environment
    (.resource .unit 7 (.integer .integer 0) SourceAnnotatedCode.Examples.localBody) .unit []
    (.sequence (.request [] []) (.sequence (.request [] []) (.request [] [])))
    (.sequence .pure (.resource (fun _ => .sequence .pure .pure))) := by
  refine .checked (by decide) (by decide) (.resource
    (bodyRequirements := fun _ => .sequence (.request [] []) (.request [] []))
    (residual := []) (.checked (by decide) (by decide) .integer) ?_ ?_ ?_ ?_ ?_)
  · intro identity fresh
    refine .checked (by change true = true; rfl) (by change true = true; rfl) (.bind (input := .reference identity) ?_ unit_source)
    refine .checked ?_ (by change true = true; rfl) (.reference (by simp))
    change decide (some (ScopedPorts.Port.reference identity) = some (.reference identity)) = true
    exact decide_eq_true rfl
  · simp [ScopedPorts.InWorld, ScopedPorts.Port.resources, SourcePlannedTyping.Value.erase,
      SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port]
  · simp
  · simp
  · intro identity fresh
    exact .sequence .request .request

end Examples
end Ash.OneShot.SourceAnnotatedSources

#print axioms Ash.OneShot.SourceAnnotatedSources.initial_run
#print axioms Ash.OneShot.SourceAnnotatedSources.Examples.unit_source
#print axioms Ash.OneShot.SourceAnnotatedSources.Examples.constant_source
#print axioms Ash.OneShot.SourceAnnotatedSources.Examples.initializer_source
#print axioms Ash.OneShot.SourceAnnotatedSources.Examples.program_source
#print axioms Ash.OneShot.SourceAnnotatedSources.Examples.admitted_program
#print axioms Ash.OneShot.SourceAnnotatedSources.Examples.changed_initializer_rejected

#print axioms Ash.OneShot.SourceAnnotatedSources.Examples.local_resource_source
