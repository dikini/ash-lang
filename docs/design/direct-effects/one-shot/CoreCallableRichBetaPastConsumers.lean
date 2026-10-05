import CoreCallableRichAdmittedEventConsumers
import CoreCallableRichHandlerFreshness

/-! Connect the existing actual beta Event to installation history at its SAME
computed rich endpoint. Current remains machine equality plus RawTrace ledger;
this does not produce a general current BetaInput or runtime registry relation. -/
namespace Ash.OneShot.CoreCallableRichBetaPastConsumers
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreCallableGeneratedChronology
open CoreCallableRichAdmittedCurrentOrigins CoreCallableRichAdmittedEventConsumers
open CoreCallableRichHandlerFreshness
open CoreCallableContractAdmission (SubstitutionPolicyStable)
open CoreCallableContractExecution (Site BetaPreserved)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]
variable {graph : Graph} {endpoint : Endpoint graph}

/-- Both outputs use the existing Event and full BetaPreserved private source.
The current typed input and original-root past are inputs, never a future Site. -/
theorem beta_event_with_past
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (input : BetaInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site)
    (past : InstallationsPast program current.input endpoint site) :
    ∃ event : BetaEvent input site current,
      event.after.input = current.input ∧
      InstallationsPast program current.input (beta_result input).after event.preserved.next ∧
      InstallationsPast program event.after.input (beta_result input).after event.preserved.next ∧
      (beta_result input).after.state.nextHandler ∉ installations := by
  obtain ⟨event⟩ := beta_event stable input site current
  obtain ⟨actual, membership⟩ := past.operation (.beta input)
  have retained : installations ⊆
      CoreHandlerHistory.enteredHandlers (beta_result input).after.state.observations := by
    simpa only [CoreCallableHandlerPastOrigins.Operation.added_handlers, List.append_nil]
      using membership
  have nextPast : InstallationsPast program current.input
      (beta_result input).after event.preserved.next := ⟨actual, retained⟩
  have consumerPast : InstallationsPast program event.after.input
      (beta_result input).after event.preserved.next := ⟨actual, retained⟩
  exact ⟨event, Subsingleton.elim _ _, nextPast, consumerPast, nextPast.fresh⟩

omit evidence in
/-- SAME already executed running history produces the continuation required
by handler_event. No future Generated, endpoint or successful edge is input. -/
noncomputable def beta_generated
    {start : CoreCallableRunningOccurrence.RunningStartPast graph cleanupOwners action environment data
      savedValue savedCode physical target}
    (run : Generated start endpoint count created discharged)
    (input : BetaInput endpoint) :
    Generated start (beta_result input).after (count + 1) created discharged := by
  simpa only [List.append_nil, List.nil_append] using Generated.next run (.beta input)

/-- Absence uses the actual endpoint's original-root counter history. -/
theorem beta_counter_membership_rejected
    (input : BetaInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site)
    (event : BetaEvent input site current)
    (past : InstallationsPast program event.after.input (beta_result input).after event.preserved.next)
    (member : (beta_result input).after.state.nextHandler ∈ installations) : False :=
  past.fresh member

/-- The existing positive Event increments the ledger once, never zero times. -/
theorem beta_zero_event_rejected
    (input : BetaInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site)
    (event : BetaEvent input site current)
    (same : event.after.eventCount = current.eventCount) : False := by
  have increment := event.count
  omega

end
#print axioms beta_event_with_past
#print axioms beta_generated
#print axioms beta_counter_membership_rejected
#print axioms beta_zero_event_rejected
end Ash.OneShot.CoreCallableRichBetaPastConsumers
