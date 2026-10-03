import CoreCallableRichHandlerFreshness
import CoreCallableRichAdmittedCurrentOrigins
import CoreCallableResumeCorrespondence
import CoreCallableGeneralStartedFrom

namespace Ash.OneShot
namespace CoreCallableRichResumePastConsumers
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

section
variable {graph : Graph} {endpoint : Endpoint graph}

/-- The existing current typed input fixes the complete actual raw resume edge. -/
theorem resume_raw (input : ResumeInput endpoint) :
    RawStep ⟨.resume input.binder input.code,input.plain.scope,endpoint.lexical⟩
      ⟨input.code,input.plain.scope,input.capturedTarget.append
        (input.frontTarget.append (.spent input.dynamicTicket input.data.answer input.data.scope input.tail))⟩
      [] [.ticket input.dynamicTicket] := by
  rw [input.lexical]
  exact .resume input.binder input.dynamicTicket input.plain.scope input.data.scope
    input.result input.data.answer input.frontTarget input.capturedTarget input.tail
    input.code input.operand.closed input.resolve

/-- This is the positive target edge of SAME resume_result, including saved caller. -/
theorem resume_transition (input : ResumeInput endpoint) :
    LexicalUnwind.Transition endpoint.point.machine (resume_result input).after.point.machine
      [] [.ticket input.dynamicTicket] := by
  have before : endpoint.point.machine =
      .eval ⟨.resume input.binder input.code,input.plain.scope,endpoint.lexical⟩ := by
    simp only [Endpoint.point,input.focus,CoreCleanupRunFrames.attach,Stack.append]
  rw [before]
  change LexicalUnwind.Transition
    (.eval ⟨.resume input.binder input.code,input.plain.scope,endpoint.lexical⟩)
    (.eval ⟨input.code,input.plain.scope,input.capturedTarget.append
      (input.frontTarget.append (.spent input.dynamicTicket input.data.answer input.data.scope input.tail))⟩)
    [] [.ticket input.dynamicTicket]
  exact .evaluate (resume_raw input) (by trivial)

variable [DeclarationPolicy]

/-- Only an existential conjunction of the EXISTING full Site, Current and past
judgments. No new relation or provider record is introduced. Program indices
remain independent of the current Site's globals, as in existing Current. -/
abbrev ResumePastOutput
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
      Matching graph endpoint (resume_result input).after [] [.ticket input.dynamicTicket]

/-- Names are PRIVATE intermediate evidence, derived by each public chronology
entry. All restoration and private checking rows come from existing Site.resume. -/
private theorem resume_with_names
    {rootDemand : List Nat} {root : RecursiveRequirements.Requirements rootDemand}
    {program : Program programGlobals programActions programBudget programCode}
    {hints : ReturnHints receiving} {context : Context hints}
    (input : ResumeInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume input.binder input.code) input.plain.scope endpoint.lexical
      result final context root)
    (current : Current program endpoint site)
    (past : InstallationsPast program current.input endpoint site)
    (names : endpoint.lexical.erase.ticketNames.Nodup) : ResumePastOutput input site current := by
  obtain ⟨owner,contract,front,cap,tail,inputType,answerType,caller,
    known,resolved,resultAnswer,shape,inputPort,answerPort,nextDemand,nextRoot,rootSame,
    nextAllowed,restored,next,_raw⟩ := site.resume input.operand.closed
  have ownerSame : owner = input.dynamicTicket := Option.some.inj (resolved.symm.trans input.resolve)
  subst owner
  have named : (front.append (.live input.dynamicTicket inputType answerType cap caller tail)).erase.ticketNames.Nodup := by
    rw [← shape]
    exact names
  obtain ⟨frontSame,inputSame,answerSame,capSame,callerSame,tailSame⟩ :=
    live_cut_unique named (shape.symm.trans input.lexical)
  subst front inputType answerType cap caller tail
  have related : CoreCallableRichBetaCore.Current (resume_result input).after next := ⟨rfl⟩
  have transported := past.operation (.resume input)
  have nextPast : InstallationsPast program current.input (resume_result input).after next :=
    ⟨transported.1,by simpa only [CoreCallableHandlerPastOrigins.Operation.added_handlers,List.append_nil] using transported.2⟩
  let nextRun : LexicalUnwind.RunState :=
    ⟨(resume_result input).after.point.machine,current.run.issued,
      [.ticket input.dynamicTicket] ++ current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine nextRun.machine [] [.ticket input.dynamicTicket] := by
    change LexicalUnwind.Transition current.run.machine (resume_result input).after.point.machine [] [.ticket input.dynamicTicket]
    rw [current.machine]
    exact resume_transition input
  have event : LexicalUnwind.Event current.run nextRun := by
    simpa only [List.append_nil] using LexicalUnwind.Event.step transition current.nonallocating_fresh
  let after : Current program (resume_result input).after next := {
    input := current.input,related := related,run := nextRun,machine := rfl,
    eventCount := current.eventCount + 1,past := .step current.past event,
    ledger := LexicalUnwind.event_preserves_ledger event current.ledger }
  have nonzero : after.eventCount ≠ current.eventCount := by
    change current.eventCount + 1 ≠ current.eventCount
    omega
  exact ⟨contract,known,resultAnswer,inputPort,answerPort,nextDemand,nextRoot,rootSame,
    nextAllowed,restored,next,after,rfl,nextPast,transition,event,rfl,rfl,rfl,nonzero,
    (resume_result input).core,.one (resume_transition input),(resume_result input).matching⟩

/-- SAME original-root typed initial chronology computes cut uniqueness. No
public names/Steps/success or future authority premise enters this producer. -/
theorem resume_from_initial_past
    {rootDemand : List Nat} {root : RecursiveRequirements.Requirements rootDemand}
    {program : Program programGlobals programActions programBudget programCode}
    {hints : ReturnHints receiving} {context : Context hints}
    (input : ResumeInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume input.binder input.code) input.plain.scope endpoint.lexical
      result final context root)
    (current : Current program endpoint site)
    (past : InstallationsPast program current.input endpoint site)
    (chronology : InitialChronology current.input endpoint count created discharged) :
    ResumePastOutput input site current := by
  have history := CoreTicketHistory.initial_steps_history graph chronology.actual_steps
  exact resume_with_names input site current past (chronology.lexical_ticket_bound.names history)

/-- SAME causal cleanup start and its already executed typed continuation supply
the bound; the actual resumed continuation is derived internally below. -/
theorem resume_from_causal_past
    {rootDemand : List Nat} {root : RecursiveRequirements.Requirements rootDemand}
    {program : Program programGlobals programActions programBudget programCode}
    {hints : ReturnHints receiving} {context : Context hints}
    (input : ResumeInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume input.binder input.code) input.plain.scope endpoint.lexical
      result final context root)
    (current : Current program endpoint site)
    (past : InstallationsPast program current.input endpoint site)
    {registration : InitialChronology current.input registered count created discharged}
    {cleanup : CleanupInput registered}
    {body : OperationSegment (cleanup_result cleanup).after bodyEnd bodyCount bodyCreated bodyDischarged}
    {start : RunningStartPast graph registered.owners cleanup.action cleanup.environment cleanup.data
      savedValue savedCode registered.physical registered.lexical}
    (causal : CausalStart registration cleanup body start)
    (generated : Generated start endpoint laterCount laterCreated laterDischarged) :
    ResumePastOutput input site current ∧
      Nonempty (Generated start (resume_result input).after (laterCount + 1)
        (laterCreated ++ []) ([.ticket input.dynamicTicket] ++ laterDischarged)) := by
  have actual := causal.generated_from_initial generated
  have history := CoreTicketHistory.initial_steps_history graph actual.1
  have bounded := Generated.lexical_ticket_bound generated causal.originalBound
  exact ⟨resume_with_names input site current past (bounded.names history),
    ⟨Generated.next generated (.resume input)⟩⟩

end

/-- The complete restored physical prefix and literal full history are the
existing resume_result fields, not erased-port or renamed-owner equalities. -/
theorem resume_full_physical (input : ResumeInput endpoint) :
    (resume_result input).after.physical = input.captured ++ (input.front ++
      .clauseBoundary input.handler input.owner input.occurrence input.dynamicTicket none :: input.outside) := rfl

theorem resume_full_history (input : ResumeInput endpoint) :
    (resume_result input).after.history = (resume_location input).restored_history := rfl

theorem resume_full_lexical (input : ResumeInput endpoint) :
    (resume_result input).after.lexical = input.capturedTarget.append
      (input.frontTarget.append (.spent input.dynamicTicket input.data.answer input.data.scope input.tail)) := rfl

/-- Exact runtime histories and owners, with only the consumed boundary changed. -/
theorem resume_runtime_preserved (input : ResumeInput endpoint) :
    (resume_result input).after.owners = endpoint.owners ∧
    (resume_result input).after.state.heap = endpoint.state.heap ∧
    (resume_result input).after.state.nextOwner = endpoint.state.nextOwner ∧
    (resume_result input).after.state.nextActivation = endpoint.state.nextActivation ∧
    (resume_result input).after.state.nextCleanup = endpoint.state.nextCleanup ∧
    (resume_result input).after.state.nextClose = endpoint.state.nextClose ∧
    (resume_result input).after.state.nextHandler = endpoint.state.nextHandler ∧
    (resume_result input).after.state.observations = endpoint.state.observations ++ [.resumed input.dynamicTicket] :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem resume_resolution_mismatch (input : ResumeInput endpoint)
    (different : input.plain.scope.resolve input.binder ≠ some input.dynamicTicket) : False :=
  different input.resolve

theorem resume_physical_mismatch (input : ResumeInput endpoint)
    (different : endpoint.physical ≠ input.front ++
      .clauseBoundary input.handler input.owner input.occurrence input.dynamicTicket (some input.captured) :: input.outside) : False :=
  different input.physical

theorem resume_lexical_mismatch (input : ResumeInput endpoint)
    (different : endpoint.lexical ≠ input.frontTarget.append
      (.live input.dynamicTicket input.result input.data.answer input.capturedTarget input.data.scope input.tail)) : False :=
  different input.lexical

/-- An already spent SAME installation blocks physical passage to any later
candidate cut. The original full captured data and owner header remain indexed. -/
theorem resume_spent_front_rejected
    (past : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data)
    (header : CoreRequestFrames.OwnerHeader graph owners heap handler owner occurrence data)
    (tail : GeneralHistory graph heap physical target) :
    ¬ PassFront handler owner (GeneralHistory.spent past header tail) :=
  matching_spent_blocks past header tail

end CoreCallableRichResumePastConsumers

#print axioms CoreCallableRichResumePastConsumers.resume_raw
#print axioms CoreCallableRichResumePastConsumers.resume_transition
#print axioms CoreCallableRichResumePastConsumers.resume_from_initial_past
#print axioms CoreCallableRichResumePastConsumers.resume_from_causal_past
#print axioms CoreCallableRichResumePastConsumers.resume_full_physical
#print axioms CoreCallableRichResumePastConsumers.resume_full_history
#print axioms CoreCallableRichResumePastConsumers.resume_full_lexical
#print axioms CoreCallableRichResumePastConsumers.resume_runtime_preserved
#print axioms CoreCallableRichResumePastConsumers.resume_resolution_mismatch
#print axioms CoreCallableRichResumePastConsumers.resume_physical_mismatch
#print axioms CoreCallableRichResumePastConsumers.resume_lexical_mismatch
#print axioms CoreCallableRichResumePastConsumers.resume_spent_front_rejected
end Ash.OneShot
