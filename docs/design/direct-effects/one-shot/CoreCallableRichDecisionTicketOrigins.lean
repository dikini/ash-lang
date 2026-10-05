import CoreCallableRichCaptureCurrentEvents
import CoreCallableRichBranchEventConsumers

/-! Decision provenance retention under DN-0033. The unchanged full rich
Boolean decision producer supplies the successor Current and original arm
selection. This leaf adds current ticket-origin retention; it does not establish
general C3, close-label freshness, cleanup restoration or M4. -/
namespace Ash.OneShot.CoreCallableRichDecisionTicketOrigins
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableGeneratedChronology CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreCallableRichBranchCurrentOrigins CoreCallableRichBranchEventConsumers
open CoreCallableRichAdmittedCurrentOrigins
open CoreCallableContractExecution (Site)
open CoreCallableInitialAdmission (Program)
open CoreCallableInitialChronology (InitialInput)
open CoreCallableRichCaptureCurrentEvents (IssuedOrigin)
open CoreCallableRichRegistryOrigins (RegistryOrigin)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]
variable {graph : CoreSyntax.Graph} {endpoint : Endpoint graph}

omit evidence in
/-- Actual Core.next determinism recovers the observation projection omitted
from decision_focus. Both Boolean choices retain the entire observation list. -/
theorem decision_observations (input : DecisionInput endpoint) :
    (decision_result input).after.state.observations = endpoint.state.observations := by
  have computed := (decision_result input).core
  rcases input with ⟨choice,frame,plain,yesCode,noCode,position,related,control,maps,focus⟩
  change FrameRel graph endpoint.owners endpoint.state.heap frame plain.context at related
  rw [position] at related
  cases related with
  | booleanMatch yesTranslated noTranslated yesSaved noSaved =>
    rename_i yesFuel yes rawYes noFuel no rawNo environment reversed
    have shape : endpoint.state.frames =
        .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: endpoint.physical := by
      simpa only [maps,framesOf,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using endpoint.frames
    have actual : CoreMachine.next graph endpoint.state = .stepped
        { endpoint.state with
          control := .evaluate (if choice then yes else no) environment
          frames := endpoint.physical } := by
      simp only [CoreMachine.next,control,shape,CoreStrictSteps.select_boolean]
    have same := CoreMachine.Outcome.stepped.inj (computed.symm.trans actual)
    have observationsSame := congrArg (fun state : CoreMachine.State => state.observations) same
    simpa only using observationsSame

/-- Registry receipts retain full current contracts/actions through this actual
nonallocating Core edge, independently of the target ledger projection. -/
private theorem registry_decision
    (origin : RegistryOrigin program initialInput endpoint owners actions)
    (input : DecisionInput endpoint) :
    RegistryOrigin program initialInput (decision_result input).after owners actions := by
  obtain ⟨count, steps⟩ := origin.actual
  refine ⟨⟨count + 1, .snoc steps (decision_result input).core⟩, ?_, ?_⟩
  · intro owner contract known
    rw [decision_observations input]
    exact origin.ownerIssued owner contract known
  · intro owner rights known
    rw [decision_observations input]
    exact origin.actionIssued owner rights known

/-- The full existing BranchEvent is retained as the same witness. Its original
arm Contract, private Plan/Rows/root, Current, ledger/event and actual positive
step are unchanged; only current input identity and origin receipts accompany it. -/
abbrev DecisionTicketOriginOutput
    (input : DecisionInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean input.choice) input.yesCode input.noCode) input.plain.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site) : Prop :=
    ∃ event : BranchEvent input site current,
      event.after.input = current.input ∧
      IssuedOrigin event.after ∧
      RegistryOrigin program event.after.input (decision_result input).after globals.owners actions ∧
      Matching graph endpoint (decision_result input).after [] []

/-- One existing full producer covers both Boolean decisions. Origin retention
uses its actual returned event and current receipts, without a future Current,
source, successful step, observation equality or freshness premise. -/
theorem decision_event_with_ticket_origins
    (input : DecisionInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean input.choice) input.yesCode input.noCode) input.plain.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site)
    (issued : IssuedOrigin current)
    (origin : RegistryOrigin program current.input endpoint globals.owners actions) :
    DecisionTicketOriginOutput input site current := by
  obtain ⟨event⟩ := branch_event input site current
  have inputSame : event.after.input = current.input := Subsingleton.elim _ _
  have afterIssued : IssuedOrigin event.after := by
    intro ticket member
    rw [decision_observations input]
    rw [event.issued] at member
    exact issued ticket member
  have afterRegistry : RegistryOrigin program event.after.input (decision_result input).after
      globals.owners actions := by
    exact registry_decision origin input
  exact ⟨event,inputSame,afterIssued,afterRegistry,(decision_result input).matching⟩

end
#check DecisionTicketOriginOutput
#check decision_observations
#check decision_event_with_ticket_origins
#print axioms decision_observations
#print axioms decision_event_with_ticket_origins
end Ash.OneShot.CoreCallableRichDecisionTicketOrigins
