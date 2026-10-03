import CoreCallableRichBranchEventConsumers

namespace Ash.OneShot.RichBranchEventInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission CoreCallableContractExecution
open CoreCallableRichBranchCurrentOrigins CoreCallableRichBranchEventConsumers
open CoreCallableGeneratedChronology
open SourcePlanSignatures (signature)
open SourcePlannedChecks (DeclarationPolicy)

section
variable [DeclarationPolicy]
variable {graph : CoreSyntax.Graph} {endpoint : Endpoint graph}

theorem true_original_indices
    (condition : Source globals outward world allowed scope environment (.boolean true) .boolean cd cr cp cw)
    (left : Source globals outward world allowed scope environment yes output ld lr lp lw)
    (right : Source globals outward world allowed scope environment no output rd rr rp rw)
    (same : ld.Perm rd)
    (selected : Source globals outward world allowed scope environment chosen output sd sr sp sw)
    (arm : OriginalArm (IndexedSource.branch condition left right same) selected) :
    HEq selected left ∧ HEq sp lp ∧ HEq sw lw := by
  cases condition
  cases arm
  exact ⟨HEq.rfl,HEq.rfl,HEq.rfl⟩

theorem false_original_indices
    (condition : Source globals outward world allowed scope environment (.boolean false) .boolean cd cr cp cw)
    (left : Source globals outward world allowed scope environment yes output ld lr lp lw)
    (right : Source globals outward world allowed scope environment no output rd rr rp rw)
    (same : ld.Perm rd)
    (selected : Source globals outward world allowed scope environment chosen output sd sr sp sw)
    (arm : OriginalArm (IndexedSource.branch condition left right same) selected) :
    HEq selected right ∧ HEq sp rp ∧ HEq sw rw := by
  cases condition
  cases arm
  exact ⟨HEq.rfl,HEq.rfl,HEq.rfl⟩

theorem branch_original_authority (event : BranchEvent input site current) :
    OriginalArm site.current.source event.preserved.next.current.source ∧
    event.preserved.next.pending = site.pending ∧
    event.preserved.next.retained = site.retained :=
  ⟨event.preserved.original,event.preserved.pending,event.preserved.retained⟩

theorem branch_root_selection
    (input : DecisionInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean input.choice) input.yesCode input.noCode) input.plain.scope endpoint.lexical
      output final context root)
    (current : CoreCallableRichAdmittedCurrentOrigins.Current program endpoint site)
    (event : BranchEvent input site current) :
    RootSelection root event.preserved.selectedRoot := event.preserved.rootSelection

theorem branch_bookkeeping (event : BranchEvent input site current) :
    event.after.run.issued = current.run.issued ∧
    event.after.run.completed = current.run.completed ∧
    event.after.eventCount = current.eventCount + 1 :=
  ⟨event.issued,event.completed,event.count⟩

theorem branch_not_zero_events (event : BranchEvent input site current) :
    event.after.eventCount ≠ current.eventCount := by
  have count := event.count
  omega

theorem branch_no_extra_owner (event : BranchEvent input site current) (owner : Owner) :
    event.after.run.issued ≠ current.run.issued ++ [owner] := by
  intro same
  have lengths := congrArg List.length (event.issued.symm.trans same)
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega

omit [DeclarationPolicy] in
/-- Distinctness is only a negative-test premise; positive arms are unrestricted. -/
theorem wrong_arm_rejected (input : DecisionInput endpoint) (different : input.yesCode ≠ input.noCode) :
    (decision_result input).after.focus.expression ≠
      (if input.choice then input.noCode else input.yesCode) := by
  have focus := (decision_focus input).1
  rw [focus]
  cases input.choice
  · exact Ne.symm different
  · exact different

omit [DeclarationPolicy] in
theorem decision_original_history (input : DecisionInput endpoint) :
    HEq (decision_result input).after.history endpoint.history ∧
    (decision_result input).after.owners = endpoint.owners ∧
    (decision_result input).after.state.heap = endpoint.state.heap ∧
    (decision_result input).after.physical = endpoint.physical ∧
    (decision_result input).after.lexical = endpoint.lexical := by
  obtain ⟨focus,lexical,history,owners,heap,physical,maps⟩ := decision_focus input
  exact ⟨history,owners,heap,physical,lexical⟩

end
#print axioms true_original_indices
#print axioms false_original_indices
#print axioms branch_original_authority
#print axioms branch_root_selection
#print axioms branch_bookkeeping
#print axioms branch_not_zero_events
#print axioms branch_no_extra_owner
#print axioms wrong_arm_rejected
#print axioms decision_original_history
end Ash.OneShot.RichBranchEventInterfaces
