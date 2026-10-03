import CoreCallableRichAdmittedCurrentOrigins

namespace Ash.OneShot.CoreCallableRichAdmittedEventConsumers
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableGeneratedChronology CoreCallableRichAdmittedCurrentOrigins
open CoreCallableContractAdmission (SubstitutionPolicyStable)
open CoreCallableContractExecution (Site BetaPreserved)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation (RawTrace)
open SourcePlannedChecks (DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]
variable {graph : CoreSyntax.Graph} {endpoint : Endpoint graph}

/-- Every private-family, Source/Auth, exact Plan/Rows and actual root output is
retained in the existing BetaPreserved receipt. The target Event and inherited
ledger are computed from the SAME current causal receipt. -/
structure BetaEvent
    (input : BetaInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site) where
  preserved : BetaPreserved site
  after : Current program (beta_result input).after preserved.next
  event : LexicalUnwind.Event current.run after.run
  issued : after.run.issued = current.run.issued
  completed : after.run.completed = current.run.completed
  count : after.eventCount = current.eventCount + 1
  actual : CoreMachine.next graph endpoint.state = .stepped (beta_result input).after.state
  positive : CoreUnwindRelation.Positive endpoint.point.machine (beta_result input).after.point.machine [] []

/-- Consume current authority and the named actual beta producer. No desired
successor Site, Result, future Steps/chain or private identity equality is input. -/
theorem beta_event
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (input : BetaInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site) : Nonempty (BetaEvent input site current) := by
  obtain ⟨preserved,related,actual,matching,raw⟩ :=
    CoreCallableRichBetaCore.beta_preserves stable input site
  let run : LexicalUnwind.RunState :=
    ⟨(beta_result input).after.point.machine,current.run.issued,current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine run.machine [] [] := by
    change LexicalUnwind.Transition current.run.machine (beta_result input).after.point.machine [] []
    rw [current.machine,current.related.machine,related.machine]
    exact .evaluate raw (by trivial)
  have event : LexicalUnwind.Event current.run run := by
    simpa only [List.append_nil,List.nil_append] using
      LexicalUnwind.Event.step transition current.nonallocating_fresh
  let after : Current program (beta_result input).after preserved.next := {
    input := current.input
    related := related
    run := run
    machine := rfl
    eventCount := current.eventCount + 1
    past := .step current.past event
    ledger := LexicalUnwind.event_preserves_ledger event current.ledger }
  have positive : CoreUnwindRelation.Positive endpoint.point.machine (beta_result input).after.point.machine [] [] := by
    rw [current.related.machine,related.machine]
    exact .one (.evaluate raw (by trivial))
  exact ⟨⟨preserved,after,event,rfl,rfl,rfl,actual,positive⟩⟩

/-- The M4 endpoint is an actual RawTrace endpoint with its ledger. This is not
Snapshot.Valid, general availability, or a Core/M4 step-count equality. -/
theorem BetaEvent.endpoint_accounting (event : BetaEvent input site current) :
    Ledger event.after.run.erase ∧ event.after.run.completed.Nodup ∧
      (∀ owner, owner ∈ event.after.run.machine.stack.erase.owners → owner ∉ event.after.run.completed) :=
  event.after.past.ownership ⟨List.Perm.refl [],List.nodup_nil⟩

end
#print axioms beta_event
#print axioms BetaEvent.endpoint_accounting
end Ash.OneShot.CoreCallableRichAdmittedEventConsumers
