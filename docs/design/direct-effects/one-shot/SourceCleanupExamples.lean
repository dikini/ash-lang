import RecursiveEntries
import SourceCallableExamples

/-! A cleanup callback containing a direct effect handler crosses installation,
    invocation and beta reduction with the collected source invariant preserved.
    This example does not assert selected-clause admission or a complete run. -/
namespace Ash.OneShot.SourceCleanupExamples
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements)
open RecursiveRecords (CheckedState)
open SourceCallableExamples

def tables : CallableProtectionFrames.Tables := fun _ => []
def program : Code := .cleanup function .unit

theorem cleanup_step_callback {callback cleanupBody : Code}
    (step : RawStep first last added removed)
    (firstEq : first.expression = .cleanup callback cleanupBody)
    (lastEq : last.stack = .push (.armed action) tail)
    (addedEq : added = [.cleanup identity]) : action.action = callback := by
  cases step <;> cases addedEq
  cases firstEq
  cases lastEq
  rfl

theorem initial_checked : CheckedState operations policy contracts tables [] [] .none program .nil .unit [] [] := by
  have current : SourceTemplates.Expression operations policy contracts [] [] .none Environment.empty program .unit []
      (.emitAfter (.sequence (.request [] []) (.request [] [])) [] []) :=
    .cleanup function_source (.stable .unit) (List.Subset.refl [])
  exact RecursiveExecution.check_state (.checked current .none .nil) .nil (by decide)
    (by simp [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
      RecursiveRequirements.evaluate_emit, OwnerPhases.ofStack,
      RecursiveRecomposition.evaluate_empty, OwnerSource.exportAt, residual_empty,
      OwnerPhaseTransitions.spendAll, ProtectionResiduals.merge]) (by decide)

theorem install_invoke_beta : ∃ action : ActionData,
    action.identity = 73 ∧ action.action = function ∧
    RawTrace ⟨program, .none, .nil⟩
      ⟨body, .none, .push (.running action .unit ScopedExecution.Examples.unit_closed) .nil⟩ [.cleanup 73] [] ∧
    CheckedState operations policy contracts tables [] [] .none body
      (.push (.running action .unit ScopedExecution.Examples.unit_closed) .nil) .unit [] [] := by
  obtain ⟨action, identity, entered, installed, ownerTrace⟩ :=
    RecursiveEntries.cleanup_preserves initial_checked (by trivial) 73
  have same : action.action = function := cleanup_step_callback entered rfl rfl rfl
  have invoked := RecursiveExecution.start_cleanup installed ScopedExecution.Examples.unit_closed
  rw [same] at invoked
  have reduced := RecursiveExecution.beta_preserves invoked ScopedExecution.Examples.unit_closed
  have next : CheckedState operations policy contracts tables [] [] .none body
      (.push (.running action .unit ScopedExecution.Examples.unit_closed) .nil) .unit [] [] := by
    simpa only [function, body, clauses, Code.subst, Clauses.subst, ite_self] using reduced
  have started := RawStep.startCleanup action .unit ScopedExecution.Examples.unit_closed .none .nil
  rw [same] at started
  have closed := ScopedPorts.typed_value_closed (SourceTemplates.expression_ports function_source .none) trivial
  have beta : RawStep
      ⟨.app function .unit, .none, .push (.running action .unit ScopedExecution.Examples.unit_closed) .nil⟩
      ⟨body, .none, .push (.running action .unit ScopedExecution.Examples.unit_closed) .nil⟩ [] [] := by
    simpa only [function, body, clauses, Code.subst, Clauses.subst, ite_self] using
      (RawStep.beta 0 body .unit .none _ ScopedExecution.Examples.unit_closed closed)
  exact ⟨action, identity, same, .next entered (.next started (.next beta (.refl _))), next⟩

def action : ActionData :=
  ⟨73, function, ScopedPorts.typed_value_closed (SourceTemplates.expression_ports function_source .none) trivial,
    .none, .unit, []⟩

theorem closing_rows : SourceClosingRows.Rows operations policy contracts [] [.invoke action] [] := by
  exact .invoke (action := action) (latent := []) function_value_summary .nil

end Ash.OneShot.SourceCleanupExamples
#print axioms Ash.OneShot.SourceCleanupExamples.initial_checked
#print axioms Ash.OneShot.SourceCleanupExamples.install_invoke_beta
#print axioms Ash.OneShot.SourceCleanupExamples.closing_rows
#print axioms Ash.OneShot.SourceCleanupExamples.cleanup_step_callback
