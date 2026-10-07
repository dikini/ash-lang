import CoreCallableRichOriginalResultAuthorityInterface

/-! UNCOMPILED producers and nonallocating preservation for the separately frozen
original-result interface. Current armed inversion supplies all metadata. No
finish consumer or Generated Boolean claim is added. -/
namespace Ash.OneShot.CoreCallableRichOriginalResultAuthority
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreCallableGeneratedChronology
open CoreCallableInitialChronology CoreCallableGeneralHistory CoreCallableRunningOccurrence
open CoreCallableGeneratedCleanupCompletion CoreCallableReachableResume
open CoreCallableContractAdmission CoreCallableContractExecution
open CoreCallableContractSource (Contract Environment)
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (Certified DeclarationPolicy)
open CoreCallableRichNormalCleanupPhases
open CoreCallableInitialAdmission (Program)
open CoreCallableReceiverRefinement (LexicalBounds)

variable {graph : Graph} {originalEndpoint : Endpoint graph}
variable [evidence : DeclarationPolicy]

omit evidence in
private theorem original_closed_evaluation (closed : ClosedValue value)
    (first second : ScopedPorts.Support.Env) :
    ScopedPorts.Support.evaluate first value.dependencies =
      ScopedPorts.Support.evaluate second value.dependencies := by
  apply ScopedPorts.Support.evaluation_congr
  intro name member
  exact False.elim (ScopedTyping.closedValue_no_variable closed member)

/-- Invert the CURRENT armed constructor and retain its full callback package,
original typed tail and saved Source/Auth together with the derived callback Site.
No running-proof identity or desired after carrier supplies these fields. -/
theorem original_result_authority
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    {context : Context hints}
    {callbackDependencies : Dependencies}
    {callbackSignature : SourcePlanSignatures.Signature callbackDependencies}
    {callbackRows : Rows callbackSignature}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root)
    (related : CoreValueRelation.ValueRel graph originalEndpoint.owners
      originalEndpoint.state.heap runtimeValue value) :
    Nonempty (OriginalResultAuthority site related) := by
  let saved := site.saved_value related
  let savedAtScope := IndexedSource.value_allowed saved.source related.closed.1 allowed data.scope
  obtain ⟨savedLexical,savedEnvironment,savedAuth⟩ := saved.authentication
  have savedAtAuth : Authenticated globals.registry outward savedAtScope savedLexical
      (actualReceiver world receiving ambient) :=
    savedAuth.value_allowed related.closed.1 allowed data.scope
  cases pendingSame : site.pending with
  | original pending => cases pending
  | armed callback authenticated certified requestsSame answerSame tail =>
      obtain ⟨⟨callbackCertificate,callbackChecked⟩,⟨normalRetained,normalRetainedChecked⟩⟩ :=
        phase_cleanup_retained_parts site.retained site.retainedChecked
      have callbackRun := cleanup_wait_callback saved.waiting
      obtain ⟨callbackLexical,callbackAuth⟩ := authenticated
      have callbackReceived :
          ScopedPorts.Support.evaluate ScopedPorts.Support.empty data.action.dependencies ⊆
          actualReceiver world receiving ambient := by
        rw [original_closed_evaluation data.closed ScopedPorts.Support.empty
          callbackLexical.environment]
        exact SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp
          callbackAuth.current_support
      let summary := IndexedSource.value_summary callback data.closed.1
      have summaryAuth : Authenticated globals.registry outward summary ([] : LexicalBounds)
          (actualReceiver world receiving ambient) := by
        apply (callbackAuth.value_summary data.closed.1).value_reauthenticate data.closed
        exact callbackReceived
      obtain ⟨applicationSource,applicationAuth,applicationCertificate,
        applicationChecked,applicationRun⟩ :=
        normal_callback_application summary summaryAuth data.closed certified
          callbackCertificate callbackChecked callbackRun
      let running : PhasePending globals outward world requests ambient
          (.push (.running data value related.closed) stack) .unit final (Context.normal context) :=
        .running callback ⟨callbackLexical,callbackAuth⟩ certified requestsSame related.closed
          savedAtScope ⟨savedLexical,savedAtAuth⟩ answerSame tail
      let next : PhaseSite globals outward world requests actions phases budget
          ambient installations
          (.app data.action .unit) .none (.push (.running data value related.closed) stack)
          .unit final (Context.normal context) root := {
        sourceDemand := [], requirements := _, dependencies := _, plan := _, rows := _,
        bound := actualReceiver world receiving ambient,
        current := ⟨applicationSource,applicationAuth.current_support,actualReceiver.issued,
          ⟨[],rfl,applicationAuth⟩,actualReceiver.issued⟩,
        received := actualReceiver.received, certificate := applicationCertificate,
        certificateChecked := applicationChecked, pending := running,
        retained := normalRetained, retainedChecked := normalRetainedChecked,
        accounting := applicationRun,
        annotated := site.annotated, row := site.row, annotation := site.annotation,
        checked := site.checked, bounded := site.bounded }
      exact ⟨{
        original := saved, savedSource := savedAtScope, savedSame := rfl,
        savedAuthentication := ⟨savedLexical,savedAtAuth⟩,
        publicDependencies := _, publicPlan := _, publicRows := _,
        signatureSame := HEq.rfl, rowsSame := HEq.rfl,
        callbackDemand := _, callbackRequirements := _,
        privateDependencies := _, privatePlan := _, privateRows := _,
        callbackSource := callback, callbackAuthentication := ⟨callbackLexical,callbackAuth⟩,
        certified := certified, requestsSame := requestsSame, answerSame := answerSame,
        tail := tail, next := next, waiting := saved.waiting }⟩

omit evidence in
private theorem original_value_ordinary (closed : ClosedValue value) :
    LexicalUnwind.ordinary value := by
  have isValue := closed.1
  cases value <;> simp_all [LexicalUnwind.ordinary,Code.IsValue]

/-- Current armed authority produces its actual start, successor callback
receipt and SAME original-result runtime carrier in one lawful Nonempty output. -/
theorem original_result_normal_start_event
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    {context : Context hints}
    {callbackDependencies : Dependencies}
    {callbackSignature : SourcePlanSignatures.Signature callbackDependencies}
    {callbackRows : Rows callbackSignature}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root)
    (current : PhaseCurrent program originalEndpoint site)
    (related : CoreValueRelation.ValueRel graph originalEndpoint.owners
      originalEndpoint.state.heap runtimeValue value)
    (origin : ArmedOrigin originalEndpoint data stack)
    (returned : originalEndpoint.state.control = .returned runtimeValue)
    (empty : EmptyFocus originalEndpoint value runtimeScope) :
    Nonempty (OriginalResultNormalStartEvent site current related origin) := by
  obtain ⟨authority⟩ := original_result_authority site related
  obtain ⟨start,predecessor,actual,core,counter⟩ :=
    phase_normal_start_with_origin site current related origin returned empty
  have afterRelated : (started start).point.machine =
      .eval ⟨.app data.action .unit,.none,.push (.running data value related.closed) stack⟩ := rfl
  let run : LexicalUnwind.RunState :=
    ⟨(started start).point.machine,current.run.issued,current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine run.machine [] [] := by
    change LexicalUnwind.Transition current.run.machine (started start).point.machine [] []
    rw [current.machine,current.related,afterRelated]
    exact .evaluate (.startCleanup data value related.closed runtimeScope stack)
      (original_value_ordinary related.closed)
  have fresh : (current.run.issued ++ []).Nodup := by
    simpa only [List.append_nil,LexicalUnwind.RunState.erase] using current.ledger.2
  have event : LexicalUnwind.Event current.run run := by
    simpa only [List.append_nil,List.nil_append] using LexicalUnwind.Event.step transition fresh
  have cleanupBound : ∀ identity, Owner.cleanup identity ∈ run.issued →
      identity < (started start).state.nextCleanup := by
    intro identity member
    rw [counter]
    exact current.cleanupBound identity member
  let after : PhaseCurrent program (started start) authority.next := {
    input := current.input, related := afterRelated,
    coreCount := current.coreCount + 1, core := core,
    run := run, machine := rfl, eventCount := current.eventCount + 1,
    past := .step current.past event,
    ledger := LexicalUnwind.event_preserves_ledger event current.ledger,
    cleanupBound := cleanupBound }
  have positive : CoreUnwindRelation.Positive originalEndpoint.point.machine
      (started start).point.machine [] [] := by
    rw [current.related,afterRelated]
    exact .one (.evaluate (.startCleanup data value related.closed runtimeScope stack)
      (original_value_ordinary related.closed))
  have ownership : CurrentOwnership graph origin.cleanupOwners (started start).state .none
      (.push (.running data value related.closed) stack) := by
    have owned :=
      (normal_start_history origin.installed related origin.outside origin.bounded runtimeScope).2.1
    change CurrentOwnership graph origin.cleanupOwners
      (CoreGeneralRestoration.startedState start.predecessor origin.action origin.environment
        data.identity runtimeValue origin.physical) .none
      (.push (.running data value related.closed) stack)
    rw [predecessor]
    exact owned
  let carrier : OriginalResultCurrent authority start (started start) := {
    predecessor := predecessor, heapSame := rfl, physicalSame := rfl, lexicalSame := rfl }
  exact ⟨⟨authority,start,carrier,after,event,rfl,rfl,rfl,actual,counter,positive,
    Matching.positive positive,ownership⟩⟩


open CoreCallableRichBranchCurrentOrigins (DecisionInput decision_result decision_focus)

/-- Actual beta preserves the same full original-result package and actual
start because its heap and both runtime suffixes are definitionally unchanged. -/
theorem OriginalResultCurrent.beta
    (carrier : OriginalResultCurrent authority start currentEndpoint)
    (input : BetaInput currentEndpoint) :
    OriginalResultCurrent authority start (beta_result input).after := {
  predecessor := carrier.predecessor, heapSame := carrier.heapSame,
  physicalSame := carrier.physicalSame, lexicalSame := carrier.lexicalSame }

/-- Actual Boolean selection preserves the same original-result package and
start using the exported current heap/physical/lexical observations. Generated
is not involved, and no desired successor carrier is supplied. -/
theorem OriginalResultCurrent.decision
    (carrier : OriginalResultCurrent authority start currentEndpoint)
    (input : DecisionInput currentEndpoint) :
    OriginalResultCurrent authority start (decision_result input).after := by
  obtain ⟨_focus,lexical,_history,_owners,heap,physical,_maps⟩ := decision_focus input
  exact {
    predecessor := carrier.predecessor,
    heapSame := heap.trans carrier.heapSame,
    physicalSame := physical.trans carrier.physicalSame,
    lexicalSame := lexical.trans carrier.lexicalSame }

end Ash.OneShot.CoreCallableRichOriginalResultAuthority

#print axioms Ash.OneShot.CoreCallableRichOriginalResultAuthority.original_result_authority
#print axioms Ash.OneShot.CoreCallableRichOriginalResultAuthority.original_result_normal_start_event
#print axioms Ash.OneShot.CoreCallableRichOriginalResultAuthority.OriginalResultCurrent.beta
#print axioms Ash.OneShot.CoreCallableRichOriginalResultAuthority.OriginalResultCurrent.decision
