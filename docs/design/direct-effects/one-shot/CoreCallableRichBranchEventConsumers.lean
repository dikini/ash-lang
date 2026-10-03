import CoreCallableRichBranchCurrentOrigins

namespace Ash.OneShot.CoreCallableRichBranchEventConsumers
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableGeneratedChronology CoreCallableRichBranchCurrentOrigins
open CoreCallableRichAdmittedCurrentOrigins
open CoreCallableContractExecution (Site)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation (RawTrace)
open SourcePlannedChecks (DeclarationPolicy)

section
variable [DeclarationPolicy]
variable {graph : CoreSyntax.Graph} {endpoint : Endpoint graph}

omit [DeclarationPolicy] in
/-- Both actual Boolean decisions are positive nonallocating target events. -/
theorem decision_positive (input : DecisionInput endpoint) :
    CoreUnwindRelation.Positive endpoint.point.machine (decision_result input).after.point.machine [] [] := by
  obtain ⟨focus,lexical,history,owners,heap,physical,maps⟩ := decision_focus input
  simp only [Endpoint.point,input.focus,focus,lexical,CoreCleanupRunFrames.attach,Stack.append]
  cases input.choice
  · exact .one (.evaluate (.ifFalse _ _ _ _) (by trivial))
  · exact .one (.evaluate (.ifTrue _ _ _ _) (by trivial))

/-- Chosen rich authority is the output of current source projection, coupled
to the actual mapped decision result and its inherited target-event ledger. -/
structure BranchEvent
    (input : DecisionInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean input.choice) input.yesCode input.noCode) input.plain.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site) where
  preserved : BranchPreserved site
  after : Current program (decision_result input).after preserved.next
  event : LexicalUnwind.Event current.run after.run
  issued : after.run.issued = current.run.issued
  completed : after.run.completed = current.run.completed
  count : after.eventCount = current.eventCount + 1
  actual : CoreMachine.next graph endpoint.state = .stepped (decision_result input).after.state
  positive : CoreUnwindRelation.Positive endpoint.point.machine (decision_result input).after.point.machine [] []

theorem branch_event
    (input : DecisionInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean input.choice) input.yesCode input.noCode) input.plain.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site) : Nonempty (BranchEvent input site current) := by
  obtain ⟨preserved⟩ := branch_preserves site
  obtain ⟨focus,lexical,history,owners,heap,physical,maps⟩ := decision_focus input
  have related : CoreCallableRichBetaCore.Current (decision_result input).after preserved.next := by
    constructor
    simp only [Endpoint.point,focus,lexical,CoreCleanupRunFrames.attach,Stack.append]
  let run : LexicalUnwind.RunState :=
    ⟨(decision_result input).after.point.machine,current.run.issued,current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine run.machine [] [] := by
    change LexicalUnwind.Transition current.run.machine (decision_result input).after.point.machine [] []
    rw [current.machine,current.related.machine,related.machine]
    cases input.choice
    · exact .evaluate (.ifFalse _ _ _ _) (by trivial)
    · exact .evaluate (.ifTrue _ _ _ _) (by trivial)
  have event : LexicalUnwind.Event current.run run := by
    simpa only [List.append_nil,List.nil_append] using
      LexicalUnwind.Event.step transition current.nonallocating_fresh
  let after : Current program (decision_result input).after preserved.next := {
    input := current.input,related := related,run := run,machine := rfl,
    eventCount := current.eventCount + 1,past := .step current.past event,
    ledger := LexicalUnwind.event_preserves_ledger event current.ledger }
  exact ⟨⟨preserved,after,event,rfl,rfl,rfl,(decision_result input).core,decision_positive input⟩⟩

/-- Raw endpoint accounting consumes the actual appended past, separately from
whole rich validity and availability. -/
theorem BranchEvent.endpoint_accounting (event : BranchEvent input site current) :
    Ledger event.after.run.erase ∧ event.after.run.completed.Nodup ∧
      (∀ owner, owner ∈ event.after.run.machine.stack.erase.owners → owner ∉ event.after.run.completed) :=
  event.after.past.ownership ⟨List.Perm.refl [],List.nodup_nil⟩

end
#print axioms decision_positive
#print axioms branch_event
#print axioms BranchEvent.endpoint_accounting
end Ash.OneShot.CoreCallableRichBranchEventConsumers
