import CoreCallableRichCaptureCurrentEvents
import CoreCallableRichResumePastConsumers

/-! Source-only resume retention under DN-0033. Both existing full rich resume
producers retain their exact returned Current and add lifetime ticket provenance.
Capture dependency and this leaf require actual elaboration and integration.
No general C3, disposal/cleanup join, close freshness or M4 result is asserted. -/
namespace Ash.OneShot.CoreCallableRichResumeTicketOrigins
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreValueRelation CoreStrictStack CoreGeneralCaptureResume
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableGeneralHistory
open CoreCallableRunningOccurrence CoreCallableGeneratedChronology
open CoreCallableInitialAdmission CoreCallableInitialChronology CoreCallableGeneratedTicketBound
open CoreCallableRichAdmittedCurrentOrigins CoreCallableRichHandlerFreshness
open CoreCallableContractAdmission CoreCallableContractExecution CoreCallableResumeCorrespondence
open CoreCallableContractRegistries (OwnerContract)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation (RawTrace)
open SourcePlannedChecks (DeclarationPolicy)

open CoreCallableRichResumePastConsumers
open CoreCallableRichCaptureCurrentEvents (IssuedOrigin)
open CoreCallableRichRegistryOrigins (RegistryOrigin)

section
variable [evidence : DeclarationPolicy]
variable {graph : Graph} {endpoint : Endpoint graph}

omit evidence in
/-- The actual thirteen-case operation projection retains capture observations
through this SAME resume; the resumed observation is not a new capture. -/
private theorem resume_captured_tickets (input : ResumeInput endpoint) :
    CoreTicketHistory.capturedTickets (resume_result input).after.state.observations =
      CoreTicketHistory.capturedTickets endpoint.state.observations := by
  simpa only [issuedTickets, List.filterMap_nil, List.append_nil] using
    CoreCallableGeneratedTicketBound.Operation.ticket_events (.resume input)

/-- Full existing maps retain their origin through the actual computed resume.
The same contract/action values remain indexed; no lower-port replacement occurs. -/
private theorem registry_resume
    (origin : RegistryOrigin program initialInput endpoint owners actions)
    (input : ResumeInput endpoint) :
    RegistryOrigin program initialInput (resume_result input).after owners actions := by
  obtain ⟨count, steps⟩ := origin.actual
  refine ⟨⟨count + 1, .snoc steps (resume_result input).core⟩, ?_, ?_⟩
  · intro owner contract known
    rw [resume_captured_tickets input]
    exact origin.ownerIssued owner contract known
  · intro owner rights known
    rw [resume_captured_tickets input]
    exact origin.actionIssued owner rights known

/-- Exactly the existing full resume existential, with two current provenance
receipts appended for its same returned Current. This introduces no provider. -/
abbrev ResumeTicketOriginOutput
    {rootDemand : List Nat} {root : RecursiveRequirements.Requirements rootDemand}
    {program : Program programGlobals programActions programBudget programCode}
    {hints : ReturnHints receiving} {context : Context hints}
    (input : ResumeInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume input.binder input.code) input.plain.scope endpoint.lexical
      result final context root)
    (current : Current program endpoint site) : Prop :=
    ∃ contract : OwnerContract,
      globals.owners input.dynamicTicket = some contract ∧ result = contract.answer ∧
      ScopedPorts.eraseType input.result = contract.input.port ∧
      ScopedPorts.eraseType input.data.answer = contract.answer.port ∧
    ∃ nextDemand, ∃ nextRoot : RecursiveRequirements.Requirements nextDemand,
      rootDemand = input.dynamicTicket :: nextDemand ∧
    ∃ nextAllowed, ∃ restored : Packed,
    ∃ next : Site globals outward world nextAllowed actions
        (OwnerPhaseTransitions.spend phases input.dynamicTicket) budget ambient installations
        input.code input.plain.scope
        (input.capturedTarget.append (input.frontTarget.append
          (.spent input.dynamicTicket input.data.answer input.data.scope input.tail)))
        contract.input final restored.context nextRoot,
    ∃ after : Current program (resume_result input).after next,
      after.input = current.input ∧
      InstallationsPast program current.input (resume_result input).after next ∧
      LexicalUnwind.Transition current.run.machine after.run.machine [] [.ticket input.dynamicTicket] ∧
      LexicalUnwind.Event current.run after.run ∧
      after.run.issued = current.run.issued ∧
      after.run.completed = [.ticket input.dynamicTicket] ++ current.run.completed ∧
      after.eventCount = current.eventCount + 1 ∧
      after.eventCount ≠ current.eventCount ∧
      CoreMachine.next graph endpoint.state = .stepped (resume_result input).after.state ∧
      CoreUnwindRelation.Positive endpoint.point.machine (resume_result input).after.point.machine
        [] [.ticket input.dynamicTicket] ∧
      Matching graph endpoint (resume_result input).after [] [.ticket input.dynamicTicket] ∧
      IssuedOrigin after ∧
      RegistryOrigin program after.input (resume_result input).after globals.owners actions

private theorem retain_origins
    {rootDemand : List Nat} {root : RecursiveRequirements.Requirements rootDemand}
    {program : Program programGlobals programActions programBudget programCode}
    {hints : ReturnHints receiving} {context : Context hints}
    (input : ResumeInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume input.binder input.code) input.plain.scope endpoint.lexical
      result final context root)
    (current : Current program endpoint site)
    (issued : IssuedOrigin current)
    (origin : RegistryOrigin program current.input endpoint globals.owners actions)
    (output : ResumePastOutput input site current) :
    ResumeTicketOriginOutput input site current := by
  obtain ⟨contract, known, resultAnswer, inputPort, answerPort, nextDemand, nextRoot,
    rootSame, nextAllowed, restored, next, after, inputSame, past, transition, event,
    issuedSame, completedSame, countSame, nonzero, actual, positive, matching⟩ := output
  have afterIssued : IssuedOrigin after := by
    intro ticket member
    rw [resume_captured_tickets input]
    rw [issuedSame] at member
    exact issued ticket member
  have afterRegistry : RegistryOrigin program after.input (resume_result input).after
      globals.owners actions := by
    exact registry_resume origin input
  exact ⟨contract, known, resultAnswer, inputPort, answerPort, nextDemand, nextRoot,
    rootSame, nextAllowed, restored, next, after, inputSame, past, transition, event,
    issuedSame, completedSame, countSame, nonzero, actual, positive, matching,
    afterIssued, afterRegistry⟩

/-- Initial chronology supplies the existing cut uniqueness. Current provenance
is transported after calling the unchanged full resume producer. -/
theorem resume_from_initial_past_with_ticket_origins
    {rootDemand : List Nat} {root : RecursiveRequirements.Requirements rootDemand}
    {program : Program programGlobals programActions programBudget programCode}
    {hints : ReturnHints receiving} {context : Context hints}
    (input : ResumeInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume input.binder input.code) input.plain.scope endpoint.lexical
      result final context root)
    (current : Current program endpoint site)
    (issued : IssuedOrigin current)
    (origin : RegistryOrigin program current.input endpoint globals.owners actions)
    (past : InstallationsPast program current.input endpoint site)
    (chronology : InitialChronology current.input endpoint count created discharged) :
    ResumeTicketOriginOutput input site current := by
  exact retain_origins input site current issued origin
    (resume_from_initial_past input site current past chronology)

/-- The same causal cleanup history retains both its full resume existential
and Generated continuation; no future Current or success is a public premise. -/
theorem resume_from_causal_past_with_ticket_origins
    {rootDemand : List Nat} {root : RecursiveRequirements.Requirements rootDemand}
    {program : Program programGlobals programActions programBudget programCode}
    {hints : ReturnHints receiving} {context : Context hints}
    (input : ResumeInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume input.binder input.code) input.plain.scope endpoint.lexical
      result final context root)
    (current : Current program endpoint site)
    (issued : IssuedOrigin current)
    (origin : RegistryOrigin program current.input endpoint globals.owners actions)
    (past : InstallationsPast program current.input endpoint site)
    {registration : InitialChronology current.input registered count created discharged}
    {cleanup : CleanupInput registered}
    {body : OperationSegment (cleanup_result cleanup).after bodyEnd bodyCount bodyCreated bodyDischarged}
    {start : RunningStartPast graph registered.owners cleanup.action cleanup.environment cleanup.data
      savedValue savedCode registered.physical registered.lexical}
    (causal : CausalStart registration cleanup body start)
    (generated : Generated start endpoint laterCount laterCreated laterDischarged) :
    ResumeTicketOriginOutput input site current ∧
      Nonempty (Generated start (resume_result input).after (laterCount + 1)
        (laterCreated ++ []) ([.ticket input.dynamicTicket] ++ laterDischarged)) := by
  obtain ⟨output, generatedAfter⟩ :=
    resume_from_causal_past input site current past causal generated
  exact ⟨retain_origins input site current issued origin output, generatedAfter⟩

end
#check ResumeTicketOriginOutput
#check resume_from_initial_past_with_ticket_origins
#check resume_from_causal_past_with_ticket_origins
#print axioms resume_from_initial_past_with_ticket_origins
#print axioms resume_from_causal_past_with_ticket_origins
end Ash.OneShot.CoreCallableRichResumeTicketOrigins
