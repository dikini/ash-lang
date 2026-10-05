import CoreCallableRichCaptureOrigin
import CaptureAnnotations

/-! Same-current capture location and clause alignment. Canonicalizing the
future lexical annotation preserves the actual Core state; full rich successor
Current and its original-root bookkeeping remain separate obligations. -/
namespace Ash.OneShot.CoreCallableRichCaptureCoreAlignment
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreGeneralCaptureResume
open CoreCallableGeneratedChronology CoreCallableGeneralHistory
open CoreCallableContractSource (Contract)
open CoreCallableContractExecution (Site runtimeType)
open CoreCallableRichAdmittedCurrentOrigins (Current)
open SourcePlannedChecks (DeclarationPolicy)
variable {graph : Graph} {endpoint : Endpoint graph}

/-- The current history, route and lookup produce the exact lexical cut. -/
theorem input_handler_cut (input : CaptureInput endpoint) :
    HandlerCut input.requested endpoint.lexical
      ((location endpoint input.index).front.append
        (.push (.handler (location endpoint input.index).data) .nil))
      (location endpoint input.index).tail (location endpoint input.index).data := by
  exact (handler_location_cut endpoint.history input.index input.same input.prefixScope
    input.route input.lookup).realizes.2.1

/-- Align any rich selection at this same handler with the actual producer. -/
theorem chosen_clause_alignment (input : CaptureInput endpoint)
    (selected : ClauseAt input.operation (location endpoint input.index).data.clauses
      parameter binder body) :
    parameter = (capture_data input).argument.id ∧
      binder = CoreTranslation.ticket graph input.selectedClause.owner ∧
      body = (capture_data input).body :=
  CaptureAnnotations.clause_selection_unique selected (capture_data input).clauseAt

/-- CaptureInput.result occurs in no current premise. Only this future lexical
annotation is replaced; the same index, source, operand and current guards remain. -/
def with_result (input : CaptureInput endpoint) (annotation : Ty) : CaptureInput endpoint :=
  { input with result := annotation }

/-- Use the complete current rich Contract, including higher-order contracts. -/
def canonical_input (input : CaptureInput endpoint) (result : Contract) : CaptureInput endpoint :=
  with_result input (runtimeType result)

/-- Choice of translated capture data cannot change the selected parameter. -/
theorem with_result_argument (input : CaptureInput endpoint) (annotation : Ty) :
    (capture_data input).argument.id = (capture_data (with_result input annotation)).argument.id := by
  exact (CaptureAnnotations.clause_selection_unique (capture_data input).clauseAt
    (capture_data (with_result input annotation)).clauseAt).1

/-- The actual Core capture has no result-annotation argument. Its lexical
endpoint may differ; only the actual Core state is asserted equal here. -/
theorem with_result_core_state (input : CaptureInput endpoint) (annotation : Ty) :
    (capture_result input).after.state = (capture_result (with_result input annotation)).after.state := by
  change captureAfter endpoint.state input.selectedClause (capture_data input).argument.id input.value
    (location endpoint input.index).installation.handler (location endpoint input.index).data.activation
    (location endpoint input.index).site (location endpoint input.index).environment
    (location endpoint input.index).inside (location endpoint input.index).outside =
    captureAfter endpoint.state input.selectedClause (capture_data (with_result input annotation)).argument.id input.value
      (location endpoint input.index).installation.handler (location endpoint input.index).data.activation
      (location endpoint input.index).site (location endpoint input.index).environment
      (location endpoint input.index).inside (location endpoint input.index).outside
  rw [with_result_argument input annotation]

theorem canonical_core_state (input : CaptureInput endpoint) (result : Contract) :
    (capture_result input).after.state = (capture_result (canonical_input input result)).after.state :=
  with_result_core_state input (runtimeType result)

/-- Concrete underdetermination: both incompatible annotations retain every
CaptureInput current guard. This does not claim a rich successor for either. -/
theorem annotation_underdetermined (input : CaptureInput endpoint) :
    (with_result input .unit).result ≠ (with_result input .boolean).result := by
  intro same
  cases same

section
variable [DeclarationPolicy]

/-- The same current relation identifies the Site's physical lexical stack;
no supplied cut or future correspondence witness is needed. -/
theorem current_handler_cut
    (input : CaptureInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope whole result final context root)
    (current : Current program endpoint site) :
    HandlerCut input.requested whole
      ((location endpoint input.index).front.append
        (.push (.handler (location endpoint input.index).data) .nil))
      (location endpoint input.index).tail (location endpoint input.index).data := by
  have same := current.related.machine
  simp only [Endpoint.point, input.focus, CoreCleanupRunFrames.attach, Stack.append] at same
  have stacks : endpoint.lexical = whole := by
    injection same with configurations
    exact congrArg Configuration.stack configurations
  rw [← stacks]
  exact input_handler_cut input

end
#check input_handler_cut
#check chosen_clause_alignment
#check with_result
#check canonical_input
#check with_result_argument
#check with_result_core_state
#check canonical_core_state
#check annotation_underdetermined
#check current_handler_cut
#print axioms input_handler_cut
#print axioms chosen_clause_alignment
#print axioms with_result_argument
#print axioms with_result_core_state
#print axioms canonical_core_state
#print axioms annotation_underdetermined
#print axioms current_handler_cut
end Ash.OneShot.CoreCallableRichCaptureCoreAlignment
