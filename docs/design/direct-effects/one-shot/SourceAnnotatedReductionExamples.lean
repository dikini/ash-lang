import SourceAnnotatedReduction
import SourceAnnotatedAdmission

/-! A closed function containing a local resource scope is bound, substituted
and called. Both reductions retain annotated source typing and the existing
requirement evaluation, including the fresh resource-body derivation. -/
namespace Ash.OneShot.SourceAnnotatedSources.ReductionExamples
open SourceAnnotatedCode (Term Reduction)
open SourceAnnotatedCode.Examples (unit functionHint localBody)
open RecursiveRequirements (Requirements evaluate)
open SourcePlannedTyping (Value)
open SourcePlanSignatures (Signature)
open SourceDependencyAnnotations (Dependencies)

abbrev empty : Requirements [] := .request [] []
def resourceBody : Term := .resource .unit 7 (.integer .integer 0) localBody
def bodyRequirements : Requirements [] := .sequence empty (.sequence empty empty)
def bodySignature : Signature (.sequence .pure (.resource (fun _ => .sequence .pure .pure))) :=
  .sequence .pure (.resource (fun _ => .sequence .pure .pure))
def localFunction : Term := .lambda (functionHint .unit) 3 resourceBody
def localType : Value := .function .unit .unit [] [] bodySignature
def call : Term := .app .unit localFunction unit
def program : Term := .bind .unit 5 localFunction (.app .unit (.variable (functionHint .unit) 5) unit)
def callRequirements : Requirements [] := .emitAfter (.sequence empty empty) [] []

theorem local_source : Expression operations policy contracts [] [] scope environment
    localFunction localType [] empty .pure := by
  refine .checked (by decide) (by decide) (.lambda Examples.local_resource_source ?_ ?_ (by simp))
  · exact .sequence (.request (layers := [])) (.sequence (.request (layers := [])) (.request (layers := [])))
  · simp [ScopedPorts.InWorld, Value.erase, SourceDependencyAnnotations.Value.erase,
      CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]

theorem local_closed : ScopedExpressions.ClosedValue localFunction.erase :=
  ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem unit_closed : ScopedExpressions.ClosedValue unit.erase :=
  ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem program_source : Expression operations policy contracts [] [] scope environment program .unit []
    (.sequence empty callRequirements) (.sequence .pure (.sequence .pure (.sequence .pure bodySignature))) := by
  refine .checked (by decide) (by decide) (.bind local_source ?_)
  refine .checked (by decide) (by decide)
    (.app (.checked (by decide) (by decide) (.variable rfl ?_)) Examples.unit_source (by simp))
  simp [Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port,
    ScopedPorts.InWorld, ScopedPorts.Port.resources]

theorem binding_step : Reduction program scope call scope :=
  .bind local_closed (by
    intro name member
    change Syntax.Dependency.variable name ∈ [Syntax.Dependency.variable 5] at member
    simpa using member)

theorem call_step : Reduction call scope resourceBody .none := .beta unit_closed local_closed

/-- The same locally scoped annotated function survives binding substitution
and beta reduction; beta changes to the established no-ticket evaluation scope. -/
theorem higher_order_preserves : ∃ first second,
    Expression operations policy contracts [] [] scope environment call .unit [] first
      (.sequence .pure (.sequence .pure bodySignature)) ∧
    Expression operations policy contracts [] [] .none environment resourceBody .unit [] second bodySignature ∧
    ∀ store receiving phases,
      evaluate store receiving phases first = evaluate store receiving phases (.sequence empty callRequirements) ∧
      evaluate store receiving phases second = evaluate store receiving phases first := by
  obtain ⟨first, bound, firstEvaluation⟩ := bind_expression
    (program_source (operations := operations) (policy := policy) (contracts := contracts) (scope := scope) (environment := environment)) local_closed
  obtain ⟨second, called, secondEvaluation⟩ := beta_expression bound unit_closed
  exact ⟨first, second, bound, called, fun store receiving phases =>
    ⟨firstEvaluation store receiving phases, secondEvaluation store receiving phases⟩⟩

end Ash.OneShot.SourceAnnotatedSources.ReductionExamples

#print axioms Ash.OneShot.SourceAnnotatedSources.ReductionExamples.local_source
#print axioms Ash.OneShot.SourceAnnotatedSources.ReductionExamples.local_closed
#print axioms Ash.OneShot.SourceAnnotatedSources.ReductionExamples.unit_closed
#print axioms Ash.OneShot.SourceAnnotatedSources.ReductionExamples.program_source
#print axioms Ash.OneShot.SourceAnnotatedSources.ReductionExamples.binding_step
#print axioms Ash.OneShot.SourceAnnotatedSources.ReductionExamples.call_step
#print axioms Ash.OneShot.SourceAnnotatedSources.ReductionExamples.higher_order_preserves
