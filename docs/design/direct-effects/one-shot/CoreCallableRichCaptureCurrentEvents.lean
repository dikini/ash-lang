import CoreCallableRichCaptureCoreAlignment

/-! UNCOMPILED source increment under DN-0033. The full accepted capture
consumer is synchronized with its computed canonical Core endpoint. Issued
provenance is retained CURRENT evidence, not a consequence of weak Current.
No general C3/M4 or whole-goal closure is asserted. -/
namespace Ash.OneShot.CoreCallableRichCaptureCurrentEvents
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreGeneralCaptureResume CoreCallableGeneralHistory
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation (RawTrace)
open SourceDependencyChecks.Lexical (ReturnHints)
open CoreCallableContractRegistries (OwnerContract)
open CoreCallableContractAdmission
open CoreCallableContractExecution (Site)
open CoreCallableGeneratedChronology CoreCallableInitialChronology
open CoreCallableRichAdmittedCurrentOrigins (Current)
open CoreCallableRichAdmittedEventConsumers (BetaEvent beta_event)
open CoreCallableRichRegistryOrigins (RegistryOrigin)
open CoreCallableRichCaptureCoreAlignment (canonical_input canonical_core_state)
open SourcePlannedChecks (DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]
variable {graph : Graph} {endpoint : Endpoint graph}

/-- Every lifetime-issued target ticket has an actual original-root Core
capture observation. Completed tickets remain covered because issued retains
its whole lifetime, rather than only owners in the current context. -/
def IssuedOrigin
    {site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root}
    (current : Current program endpoint site) : Prop :=
  ∀ ticket, Owner.ticket ticket ∈ current.run.issued →
    ticket ∈ CoreTicketHistory.capturedTickets endpoint.state.observations

/-- Literal initial issued history is empty, independently of the Program's
registry parameters. Full registry origin still needs its separate empty-map seed. -/
theorem initial_issued_origin
    (program : CoreCallableInitialAdmission.Program globals actions budget code)
    (input : InitialInput graph code) :
    IssuedOrigin (CoreCallableRichAdmittedCurrentOrigins.initial_from_input program input) := by
  intro ticket impossible
  cases impossible

omit evidence in
/-- Local list transport uses the existing thirteen-case actual operation
observation theorem. Cleanup/close identities are ignored only by this ticket
projection; the existing full ledger still retains every Owner constructor. -/
private theorem operation_issued_append
    {nextEndpoint : Endpoint graph}
    (operation : Operation endpoint nextEndpoint created discharged)
    (issued : ∀ ticket, Owner.ticket ticket ∈ oldIssued →
      ticket ∈ CoreTicketHistory.capturedTickets endpoint.state.observations) :
    ∀ ticket, Owner.ticket ticket ∈ oldIssued ++ created →
      ticket ∈ CoreTicketHistory.capturedTickets nextEndpoint.state.observations := by
  intro ticket member
  rw [CoreCallableGeneratedTicketBound.Operation.ticket_events operation]
  rcases List.mem_append.mp member with old | allocated
  · exact List.mem_append_left _ (issued ticket old)
  · apply List.mem_append_right
    exact List.mem_filterMap.mpr ⟨Owner.ticket ticket, allocated, rfl⟩

/-- Same named beta consumer changes neither issued tickets nor Core captures.
It outputs its full existing private-family BetaEvent and current provenance. -/
theorem beta_event_with_issued_origin
    (stable : SubstitutionPolicyStable outward)
    (input : BetaInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site)
    (issued : IssuedOrigin current) :
    ∃ event : BetaEvent input site current, IssuedOrigin event.after := by
  obtain ⟨event⟩ := beta_event stable input site current
  refine ⟨event, ?_⟩
  intro ticket member
  rw [event.issued] at member
  apply operation_issued_append (.beta input) issued ticket
  simpa only [List.append_nil] using member

/-- RegistryOrigin's actual history bounds every causal issued target ticket.
The allocating freshness needed by Event.step is derived, never supplied. -/
theorem allocating_fresh
    {site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root}
    (current : Current program endpoint site)
    (registry : RegistryOrigin program current.input endpoint globals.owners actions)
    (issued : IssuedOrigin current) :
    (current.run.issued ++ [Owner.ticket endpoint.state.nextOwner]).Nodup := by
  have unique : current.run.issued.Nodup := by
    simpa only [LexicalUnwind.RunState.erase] using current.ledger.2
  have absent : Owner.ticket endpoint.state.nextOwner ∉ current.run.issued := by
    intro member
    exact CoreTicketHistory.history_fresh endpoint.state registry.history
      (issued endpoint.state.nextOwner member)
  refine List.nodup_append.mpr ⟨unique, by simp, ?_⟩
  intro old member new inserted same
  have identity : new = Owner.ticket endpoint.state.nextOwner := by simpa using inserted
  apply absent
  simpa only [same, identity] using member

/-- Actual capture appends exactly its current counter to Core observations.
The matching target issued append preserves the whole lifetime provenance. -/
theorem capture_issued_origin
    (input : CaptureInput endpoint) (result : CoreCallableContractSource.Contract)
    {site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack output final context root}
    (current : Current program endpoint site)
    (issued : IssuedOrigin current) :
    ∀ ticket, Owner.ticket ticket ∈
        current.run.issued ++ [Owner.ticket endpoint.state.nextOwner] →
      ticket ∈ CoreTicketHistory.capturedTickets
        (capture_result (canonical_input input result)).after.state.observations :=
  operation_issued_append (.capture (canonical_input input result)) issued

omit evidence in
/-- ClauseAt uniqueness aligns the full rich selected body with the computed
canonical Core endpoint. No future Site, Source or equality is a premise. -/
theorem capture_point
    (input : CaptureInput endpoint) (result : CoreCallableContractSource.Contract)
    (selected : ClauseAt input.operation (location endpoint input.index).data.clauses
      parameter binder body) :
    (capture_result (canonical_input input result)).after.point.machine =
      .eval ⟨body.subst parameter input.code, .ticket binder endpoint.state.nextOwner,
        .live endpoint.state.nextOwner (CoreCallableContractExecution.runtimeType result)
          (location endpoint input.index).data.answer
          ((location endpoint input.index).front.append
            (.push (.handler (location endpoint input.index).data) .nil))
          (location endpoint input.index).data.scope (location endpoint input.index).tail⟩ := by
  obtain ⟨parameterSame, binderSame, bodySame⟩ :=
    CoreCallableRichCaptureCoreAlignment.chosen_clause_alignment
      (canonical_input input result) selected
  change LexicalUnwind.Machine.eval ⟨(capture_data (canonical_input input result)).body.subst
      (capture_data (canonical_input input result)).argument.id input.code,
      .ticket (CoreTranslation.ticket graph input.selectedClause.owner) endpoint.state.nextOwner,
      .live endpoint.state.nextOwner (CoreCallableContractExecution.runtimeType result)
        (location endpoint input.index).data.answer
        ((location endpoint input.index).front.append
          (.push (.handler (location endpoint input.index).data) .nil))
        (location endpoint input.index).data.scope (location endpoint input.index).tail⟩ = _
  rw [parameterSame, binderSame, bodySame]
  rfl

/-- Produce the full same-root allocating Current and actual positive event
from the existing rich capture consumer, current payload guards and retained
issued provenance. Every private family/Plan/Rows/root conjunct is retained. -/
theorem capture_event
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (stable : SubstitutionPolicyStable outward)
    (input : CaptureInput endpoint)
    (site : CoreCallableContractExecution.Site globals outward world allowed actions phases budget ambient installations
      (.perform (Instantiation.freezeEffect input.requested) input.operation input.code) input.plain.scope endpoint.lexical result final context root)
    (current : Current program endpoint site)
    (origin : RegistryOrigin program current.input endpoint globals.owners actions)
    (issued : IssuedOrigin current)
    (checkedRequest : CorePayloadReceiver.CheckedRequest requestTable requestPort)
    (origins : CorePayloadReceiver.ActivationOrigins)
    (dependencies : ∀ identity, identity ∈ ScopedPorts.Support.evaluate ScopedPorts.Support.empty input.code.dependencies →
      identity ∉ ambient → ∃ origin, CorePayloadReceiver.originAt origins identity = some origin ∧
        origin ∈ checkedRequest.record.dependencyOrigins)
    (crossed : CorePayloadReceiver.CapturedRealizes checkedRequest origins ((location endpoint input.index).front.append
      (.push (.handler (location endpoint input.index).data) .nil)) ambient)
    (resumeDemand : List Nat) (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ captured outside : Packed,
    ∃ answer residual parameter binder code resumeEffects closeEffects,
    ∃ family : Nat → Dependencies, ∃ bodies : ∀ localOwner, Plan (family localOwner),
    ∃ bodyRows : ∀ localOwner, Rows (signature (bodies localOwner)),
    let allocated : OwnerContract := ⟨result, answer, captured.scope.held, resumeDemand, resumeRow,
      resumeDemand, closeRow, resumeEffects, closeEffects⟩
    ∃ nextDemand, ∃ nextRoot : RecursiveRequirements.Requirements nextDemand,
    ∃ next : CoreCallableContractExecution.Site (globals.withOwner endpoint.state.nextOwner allocated) outward world residual
      (actions.insert endpoint.state.nextOwner code.requiredActions) (OwnerPhaseTransitions.introduce phases endpoint.state.nextOwner) budget ambient installations
      (code.subst parameter input.code) (.ticket binder endpoint.state.nextOwner)
      (.live endpoint.state.nextOwner (CoreCallableContractExecution.runtimeType result) (location endpoint input.index).data.answer ((location endpoint input.index).front.append
        (.push (.handler (location endpoint input.index).data) .nil))
        (location endpoint input.index).data.scope (location endpoint input.index).tail)
      answer final (Context.live (owner := endpoint.state.nextOwner) (resumeDemand := resumeDemand) captured.context outside.context) nextRoot,
      ClauseAt input.operation (location endpoint input.index).data.clauses parameter binder code ∧
      SourceDependencyChecks.Lexical.Capture receiving input.requested input.operation ∧
      RawStep ⟨.perform (Instantiation.freezeEffect input.requested) input.operation input.code, input.plain.scope, endpoint.lexical⟩
        ⟨code.subst parameter input.code, .ticket binder endpoint.state.nextOwner,
          .live endpoint.state.nextOwner (CoreCallableContractExecution.runtimeType result) (location endpoint input.index).data.answer ((location endpoint input.index).front.append
        (.push (.handler (location endpoint input.index).data) .nil))
        (location endpoint input.index).data.scope (location endpoint input.index).tail⟩ [.ticket endpoint.state.nextOwner] [] ∧
      next.dependencies = family endpoint.state.nextOwner ∧
      HEq next.plan (CoreCallablePlanSubstitution.plan code (bodies endpoint.state.nextOwner) parameter input.code) ∧
      HEq (signature next.plan) (signature (bodies endpoint.state.nextOwner)) ∧ HEq next.rows (bodyRows endpoint.state.nextOwner) ∧
      ∃ after : Current program (capture_result (canonical_input input result)).after next,
        after.input = current.input ∧
        LexicalUnwind.Event current.run after.run ∧
        after.run.issued = current.run.issued ++ [Owner.ticket endpoint.state.nextOwner] ∧
        after.run.completed = current.run.completed ∧
        after.eventCount = current.eventCount + 1 ∧
        IssuedOrigin after ∧
        RegistryOrigin program after.input (capture_result (canonical_input input result)).after
          (globals.owners.insert endpoint.state.nextOwner allocated)
          (actions.insert endpoint.state.nextOwner code.requiredActions) ∧
        (capture_result input).after.state =
          (capture_result (canonical_input input result)).after.state ∧
        CoreMachine.next graph endpoint.state = .stepped (capture_result input).after.state ∧
        Matching graph endpoint (capture_result (canonical_input input result)).after
          [Owner.ticket endpoint.state.nextOwner] [] ∧
        CoreUnwindRelation.Positive endpoint.point.machine
          (capture_result (canonical_input input result)).after.point.machine
          [Owner.ticket endpoint.state.nextOwner] [] := by
  have cut := CoreCallableRichCaptureCoreAlignment.input_handler_cut input
  obtain ⟨captured, outside, answer, residual, parameter, binder, code, resumeEffects,
    closeEffects, family, bodies, bodyRows, nextDemand, nextRoot, next, located, guarded,
    raw, exactDependencies, exactPlan, exactSignature, exactRows, registryAfter⟩ :=
    CoreCallableRichCaptureOrigin.capture_at_actual_counter stable site current origin
      input.operand.closed cut input.ready checkedRequest origins dependencies crossed
      resumeDemand resumeRow closeRow
  have related : CoreCallableRichBetaCore.Current
      (capture_result (canonical_input input result)).after next :=
    ⟨capture_point input result located⟩
  let run : LexicalUnwind.RunState :=
    ⟨(capture_result (canonical_input input result)).after.point.machine,
      current.run.issued ++ [Owner.ticket endpoint.state.nextOwner], current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine run.machine
      [Owner.ticket endpoint.state.nextOwner] [] := by
    change LexicalUnwind.Transition current.run.machine
      (capture_result (canonical_input input result)).after.point.machine
      [Owner.ticket endpoint.state.nextOwner] []
    rw [current.machine, current.related.machine, related.machine]
    exact .evaluate raw (by trivial)
  have event : LexicalUnwind.Event current.run run := by
    simpa only [List.nil_append] using
      LexicalUnwind.Event.step transition (allocating_fresh current origin issued)
  let after : Current program (capture_result (canonical_input input result)).after next := {
    input := current.input
    related := related
    run := run
    machine := rfl
    eventCount := current.eventCount + 1
    past := .step current.past event
    ledger := LexicalUnwind.event_preserves_ledger event current.ledger }
  have nextIssued : IssuedOrigin after := by
    exact capture_issued_origin input result current issued
  have nextRegistry : RegistryOrigin program after.input
      (capture_result (canonical_input input result)).after
      (globals.owners.insert endpoint.state.nextOwner
        ⟨result, answer, captured.scope.held, resumeDemand, resumeRow,
          resumeDemand, closeRow, resumeEffects, closeEffects⟩)
      (actions.insert endpoint.state.nextOwner code.requiredActions) :=
    registryAfter (canonical_input input result)
  have actual : CoreMachine.next graph endpoint.state =
      .stepped (capture_result input).after.state := by
    rw [canonical_core_state input result]
    exact (Operation.actual (.capture (canonical_input input result))).1
  have positive : CoreUnwindRelation.Positive endpoint.point.machine
      (capture_result (canonical_input input result)).after.point.machine
      [Owner.ticket endpoint.state.nextOwner] [] := by
    rw [current.related.machine, related.machine]
    exact .one (.evaluate raw (by trivial))
  exact ⟨captured, outside, answer, residual, parameter, binder, code, resumeEffects,
    closeEffects, family, bodies, bodyRows, nextDemand, nextRoot, next, located, guarded,
    raw, exactDependencies, exactPlan, exactSignature, exactRows, after, rfl, event,
    rfl, rfl, rfl, nextIssued, nextRegistry, canonical_core_state input result, actual,
    (Operation.actual (.capture (canonical_input input result))).2, positive⟩

end
#check IssuedOrigin
#check initial_issued_origin
#check beta_event_with_issued_origin
#check allocating_fresh
#check capture_issued_origin
#check capture_point
#check capture_event
#print axioms initial_issued_origin
#print axioms beta_event_with_issued_origin
#print axioms allocating_fresh
#print axioms capture_issued_origin
#print axioms capture_point
#print axioms capture_event
end Ash.OneShot.CoreCallableRichCaptureCurrentEvents
