import SourceCallableSubstitution

/-! Handler-bearing callable admission while the shared substitution and
    reduction interfaces are being integrated. No general safety claim. -/
namespace Ash.OneShot.SourceCallableExamples
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked)
open SourceTemplates (Expression ValueSummary)

def effect : Instance := .user 91 []
def operations : Operations := fun actual operation =>
  if actual = effect ∧ operation = 0 then some (.unit, .unit) else none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, false⟩
def contracts : Owners.Contracts := fun _ => none
def clauses : Clauses := .cons 0 1 9 (.resume 9 .unit) .nil
def table : List (Nat × ClauseContract) := [(0, ⟨false, some [], some []⟩)]
def body : Code := .handle (Instantiation.freezeEffect effect)
  (.perform (Instantiation.freezeEffect effect) 0 .unit) clauses
def function : Code := .lambda 0 body
def functionType : Value := .function .unit .unit [] []
def bodyRequirements : Requirements [] :=
  (Requirements.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]).prepend [.ordinary (.handler effect 0 table)]

theorem operation_known : operations effect 0 = some (.unit, .unit) := by decide

theorem body_source (environment : Environment) :
    Expression operations policy contracts [] [] .none environment body .unit [] bodyRequirements := by
  have clausePorts : ScopedPorts.ClausesTyped operations.ports [] environment.ports effect .unit [] clauses :=
    .cons (port_lookup operation_known)
      (.resume .unit (List.Subset.refl []) (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources])) .nil
  have coverage : ScopedPorts.Covers operations.ports effect clauses := by
    intro operation input output known
    by_cases same : operation = 0
    · simp [same, clauses, ScopedTyping.clauseKeys]
    · simp [Operations.ports, operations, same] at known
  exact .handler (.perform operation_known List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
    clausePorts (.cons (.resume rfl .unit) .nil) coverage (by decide) (List.Subset.refl []) table
    (.cons (by intro impossible; cases impossible) .nil)

theorem body_outward : RecursiveOutward.Outward bodyRequirements (some []) := by
  have inside : RecursiveOutward.Outward
      (.emitAfter (Requirements.request [] []) [] [⟨effect, 0, false⟩]) (some [⟨effect, 0, false⟩]) :=
    .emitAfter (layers := []) (.request (layers := []))
  have current := RecursiveOutward.prepend inside [.handler effect 0 table]
  have evaluated : residualize [.handler effect 0 table] [⟨effect, 0, false⟩] = some [] := by decide
  simpa only [Option.bind_some, evaluated, bodyRequirements, List.map_cons, List.map_nil] using current

theorem function_source : Expression operations policy contracts [] [] .none Environment.empty function functionType [] (.request [] []) :=
  .lambda (body_source _) body_outward (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem function_value_summary : ValueSummary operations policy contracts [] Environment.empty [] function functionType :=
  SourceTemplates.value_summary function_source trivial

theorem legacy_summary_rejects :
    ¬ CoherentSourceTypes.Summary operations [] Environment.empty [] function functionType [] := by
  intro summary
  cases summary with
  | lambda body formed => cases body

theorem application_source : Expression operations policy contracts [] [] .none Environment.empty (.app function .unit) .unit []
    (.emitAfter (.sequence (.request [] []) (.request [] [])) [] []) :=
  .app function_source (.stable .unit) (List.Subset.refl [])

theorem beta_step : RawStep ⟨.app function .unit, .none, .nil⟩ ⟨body, .none, .nil⟩ [] [] := by
  have closed := ScopedPorts.typed_value_closed (SourceTemplates.expression_ports function_source .none) trivial
  simpa only [function, body, clauses, Code.subst, Clauses.subst, ite_self] using
    (RawStep.beta 0 body .unit .none .nil ScopedExecution.Examples.unit_closed closed)

theorem body_checked : Checked [] [] OwnerPhaseTransitions.empty bodyRequirements [] := by
  apply RecursiveRequirements.evaluate_sound
  rw [RecursiveOutward.evaluation body_outward]
  rfl

/-- An old stable application accepts a variable with the new callable type;
    substitution must preserve the full handler body carried by its value. -/
theorem variable_application : Expression operations policy contracts [] [] .none
    (Environment.empty.extend 7 functionType) (.app (.variable 7) .unit) .unit [] (.request [] []) :=
  .stable (.app (.variable (by simp [Environment.extend, functionType])
    (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])) .unit (List.Subset.refl []))

theorem substituted_application : Expression operations policy contracts [] [] .none Environment.empty
    (.app function .unit) .unit [] (.request [] []) := by
  have closed := ScopedPorts.typed_value_closed (SourceTemplates.expression_ports function_source .none) trivial
  exact SourceCallableSubstitution.substitution variable_application function_value_summary closed

end Ash.OneShot.SourceCallableExamples
#print axioms Ash.OneShot.SourceCallableExamples.operation_known
#print axioms Ash.OneShot.SourceCallableExamples.body_source
#print axioms Ash.OneShot.SourceCallableExamples.body_outward
#print axioms Ash.OneShot.SourceCallableExamples.function_source
#print axioms Ash.OneShot.SourceCallableExamples.function_value_summary
#print axioms Ash.OneShot.SourceCallableExamples.legacy_summary_rejects
#print axioms Ash.OneShot.SourceCallableExamples.application_source
#print axioms Ash.OneShot.SourceCallableExamples.beta_step
#print axioms Ash.OneShot.SourceCallableExamples.body_checked
#print axioms Ash.OneShot.SourceCallableExamples.variable_application
#print axioms Ash.OneShot.SourceCallableExamples.substituted_application
