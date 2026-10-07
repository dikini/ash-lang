import CoreCallableRichOriginalResultAuthority

/-! UNCOMPILED additive current ticket bound and original-result normal finish.
The frozen authority/start carrier is unchanged. No Generated receipt, desired
successor or erased full-contract recovery supplies restoration evidence. -/
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
open RecursiveRequirements (Requirements)
open CoreCallableRichBranchCurrentOrigins (DecisionInput decision_result decision_focus)

variable {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
variable {context : Context hints}

/-- Drop the normal boundary from the SAME current retained proof and its
installation checks. No independently selected retained continuation is input. -/
theorem original_normal_retained_parts
    (retained : SourceAdmission.Pending outward actions budget phases world installations
      (Context.normal context) Context.nil .ordinary .ordinary)
    (checked : InstallationSupport.PendingChecked ambient outward retained) :
    ∃ tail : SourceAdmission.Pending outward actions budget phases world installations
        context Context.nil .ordinary .ordinary,
      InstallationSupport.PendingChecked ambient outward tail := by
  cases retained with
  | normal tail =>
      cases checked with
      | normal tailChecked => exact ⟨tail,tailChecked⟩

variable {graph : Graph} {originalEndpoint currentEndpoint : Endpoint graph}
variable [evidence : DeclarationPolicy]
variable {callbackDependencies : Dependencies}
variable {callbackSignature : SourcePlanSignatures.Signature callbackDependencies}
variable {callbackRows : Rows callbackSignature}
variable {originalSite : PhaseSite globals outward world allowed actions phases budget
  ambient installations value originalScope (.push (.armed data) stack) originalContract final
  (Context.cleanup (needs := requests) latent callbackRows context) originalRoot}
variable {related : CoreValueRelation.ValueRel graph originalEndpoint.owners
  originalEndpoint.state.heap runtimeValue value}
variable {authority : OriginalResultAuthority originalSite related}
variable {start : RunningStartPast graph cleanupOwners action environment data runtimeValue value
  physical stack}

/-- Current ticket observations are additional ownership evidence, separate
from heap/history equality and the cleanup counter bound in PhaseCurrent. This
additive carrier retains the frozen original-result package and SAME start. -/
structure StrongOriginalResultCurrent
    (authority : OriginalResultAuthority originalSite related)
    (start : RunningStartPast graph cleanupOwners action environment data runtimeValue value
      physical stack)
    (currentEndpoint : Endpoint graph) where
  original : OriginalResultCurrent authority start currentEndpoint
  bounded : TicketBound currentEndpoint.state currentEndpoint.lexical

/-- The actual normal-start ownership output produces the stronger carrier.
No fresh bound or desired after carrier is required from the caller. -/
theorem OriginalResultNormalStartEvent.strong_current
    (event : OriginalResultNormalStartEvent originalSite current related origin) :
    StrongOriginalResultCurrent event.authority event.start (started event.start) := {
  original := event.carrier
  bounded := by
    rw [event.carrier.lexicalSame]
    exact event.ownership.tickets }

/-- The existing actual start event and its produced ownership refinement are
returned together; the frozen original event and producers are unchanged. -/
structure StrongOriginalResultNormalStartEvent
    (current : PhaseCurrent program originalEndpoint originalSite)
    (origin : ArmedOrigin originalEndpoint data stack) where
  event : OriginalResultNormalStartEvent originalSite current related origin
  carrier : StrongOriginalResultCurrent event.authority event.start (started event.start)

/-- Current armed premises produce the same actual start and its ticket-bound
carrier lawfully under Nonempty, preserving the original full result and tail. -/
theorem strong_original_result_normal_start_event
    (current : PhaseCurrent program originalEndpoint originalSite)
    (origin : ArmedOrigin originalEndpoint data stack)
    (returned : originalEndpoint.state.control = .returned runtimeValue)
    (empty : EmptyFocus originalEndpoint value originalScope) :
    Nonempty (StrongOriginalResultNormalStartEvent (related := related) current origin) := by
  obtain ⟨event⟩ :=
    original_result_normal_start_event originalSite current related origin returned empty
  exact ⟨⟨event,event.strong_current⟩⟩

/-- Beta preserves the same package/start and current ticket observations by
its actual unchanged state observations and lexical suffix. -/
theorem StrongOriginalResultCurrent.beta
    (carrier : StrongOriginalResultCurrent authority start currentEndpoint)
    (input : BetaInput currentEndpoint) :
    StrongOriginalResultCurrent authority start (beta_result input).after := {
  original := carrier.original.beta input
  bounded := carrier.bounded }

/-- Boolean preserves the same package/start and current bound using its
actual lexical and observation equations; Generated excludes this operation. -/
theorem StrongOriginalResultCurrent.decision
    (carrier : StrongOriginalResultCurrent authority start currentEndpoint)
    (input : DecisionInput currentEndpoint) :
    StrongOriginalResultCurrent authority start (decision_result input).after := by
  obtain ⟨_focus,lexical,_history,_owners,_heap,_physical,_maps⟩ := decision_focus input
  exact {
    original := carrier.original.decision input
    bounded := by
      intro ticket
      change (decision_result input).after.lexical.erase.ticketNames.count ticket ≤
        (CoreTicketHistory.capturedTickets
          (decision_result input).after.state.observations).count ticket
      rw [lexical,phase_decision_observations input]
      exact carrier.bounded ticket }

/-- Current Unit completion supplies its actual Wait/root and lower retained
checks. The original full saved Source/Auth and typed tail come directly from
the original-result package, not from the callback's Unit contract or erasure. -/
theorem restored_original_result_site
    (authority : OriginalResultAuthority originalSite related)
    (callback : PhaseSite globals outward world requests actions phases budget ambient installations
      .unit activeScope currentEndpoint.lexical .unit final (Context.normal context) activeRoot) :
    Nonempty (Site globals outward world allowed actions phases budget ambient installations
      value data.scope stack originalContract final context activeRoot) := by
  have waiting : Accounting.Wait world installations context .ordinary activeRoot :=
    normal_callback_finished_wait callback.current.source
      ⟨trivial,rfl,by intro _ present; cases present⟩ callback.accounting
  obtain ⟨retained,retainedChecked⟩ :=
    original_normal_retained_parts callback.retained callback.retainedChecked
  obtain ⟨lexical,sameEnvironment,authenticated⟩ := authority.original.authentication
  have savedAuth : Authenticated globals.registry outward authority.savedSource lexical
      (actualReceiver world receiving ambient) := by
    rw [authority.savedSame]
    exact authenticated.value_allowed related.closed.1 allowed data.scope
  let restored : Site globals outward world allowed actions phases budget ambient installations
      value data.scope stack originalContract final context activeRoot := {
    sourceDemand := [], requirements := .request [] [], dependencies := _, plan := .pure,
    rows := Rows.pure, bound := actualReceiver world receiving ambient,
    current := ⟨authority.savedSource,
      (by simpa only [sameEnvironment] using savedAuth.current_support),actualReceiver.issued,
      ⟨lexical,sameEnvironment,savedAuth⟩,actualReceiver.issued⟩,
    received := actualReceiver.received, certificate := .pure, certificateChecked := .pure,
    pending := authority.tail, retained := retained, retainedChecked := retainedChecked,
    accounting := .pure waiting,
    annotated := callback.annotated, row := callback.row, annotation := callback.annotation,
    checked := callback.checked, bounded := callback.bounded }
  exact ⟨restored⟩

/-- Finish the exact SAME actual start at current Unit completion. Heap equality
supplies its immutable running receipt and outside history at the current heap;
the additive bound supplies the ownership kernel's current ticket obligation. -/
noncomputable def strong_original_finish_result
    (carrier : StrongOriginalResultCurrent authority start currentEndpoint)
    (returned : currentEndpoint.state.control = .returned .unit)
    (empty : EmptyFocus currentEndpoint .unit activeScope) :
    Result currentEndpoint [] [.cleanup data.identity] := by
  let extension : CoreValueRelation.HeapExtends start.predecessor.heap
      currentEndpoint.state.heap := by
    rw [carrier.original.heapSame]
    intro identity stored known
    exact known
  let receipt := start.running.heap_weaken extension
  let outside := start.originalHistory.heap_weaken extension
  let after : Endpoint graph := {
    state := CoreGeneralRestoration.observedState currentEndpoint.state runtimeValue physical
      (.cleanupFinished data.identity)
    focus := ⟨value,data.scope,.nil⟩, owners := cleanupOwners, maps := []
    physical := physical, lexical := stack, history := outside, frames := rfl }
  have bounded : TicketBound currentEndpoint.state
      (.push (.running data value receipt.value.closed) stack) := by
    rw [← carrier.original.lexicalSame]
    exact carrier.bounded
  have actual := normal_finish_history (base := currentEndpoint.state)
    receipt outside bounded currentEndpoint.owners activeScope
  have frames : currentEndpoint.state.frames = currentEndpoint.physical := by
    simpa only [empty.maps,CoreStrictStack.framesOf,List.map_nil,List.nil_append] using currentEndpoint.frames
  have beforeSame : CoreGeneralRestoration.returnedState currentEndpoint.state .unit
      (.cleanupCompletion data.identity runtimeValue :: physical) = currentEndpoint.state := by
    simp only [CoreGeneralRestoration.returnedState]
    rw [← carrier.original.physicalSame,← frames,← returned]
  refine ⟨after,by simpa only [beforeSame] using actual.1.core,.positive ?_⟩
  simpa only [Endpoint.point,empty.focus,CoreCleanupRunFrames.attach,Stack.append,
    carrier.original.lexicalSame,after] using actual.1.target

/-- Strong current ownership is produced by the actual normal-finish kernel,
using the same immutable installation and current ticket observations. -/
theorem strong_original_finish_ownership
    (carrier : StrongOriginalResultCurrent authority start currentEndpoint)
    (returned : currentEndpoint.state.control = .returned .unit)
    (empty : EmptyFocus currentEndpoint .unit activeScope) :
    CurrentOwnership graph cleanupOwners
      (strong_original_finish_result carrier returned empty).after.state data.scope stack := by
  let extension : CoreValueRelation.HeapExtends start.predecessor.heap
      currentEndpoint.state.heap := by
    rw [carrier.original.heapSame]
    intro identity stored known
    exact known
  let receipt := start.running.heap_weaken extension
  let outside := start.originalHistory.heap_weaken extension
  have bounded : TicketBound currentEndpoint.state
      (.push (.running data value receipt.value.closed) stack) := by
    rw [← carrier.original.lexicalSame]
    exact carrier.bounded
  exact (normal_finish_history (base := currentEndpoint.state)
    receipt outside bounded currentEndpoint.owners activeScope).2.1

/-- Full original-result restoration, actual Core finish, current causal
receipt and exact cleanup discharge are outputs of current Unit completion. -/
structure OriginalResultFinishEvent
    (carrier : StrongOriginalResultCurrent authority start currentEndpoint)
    (callback : PhaseSite globals outward world requests actions phases budget ambient installations
      .unit activeScope currentEndpoint.lexical .unit final (Context.normal context) activeRoot)
    (current : PhaseCurrent program currentEndpoint callback) where
  runtime : Result currentEndpoint [] [.cleanup data.identity]
  restored : Site globals outward world allowed actions phases budget ambient installations
    value data.scope stack originalContract final context activeRoot
  after : PhaseCurrent program runtime.after (PhaseSite.of_site restored)
  savedValue : CoreValueRelation.ValueRel graph runtime.after.owners runtime.after.state.heap
    runtimeValue value
  event : LexicalUnwind.Event current.run after.run
  issued : after.run.issued = current.run.issued
  completed : after.run.completed = .cleanup data.identity :: current.run.completed
  count : after.eventCount = current.eventCount + 1
  actual : CoreMachine.next graph currentEndpoint.state = .stepped runtime.after.state
  returned : runtime.after.state.control = .returned runtimeValue
  scope : runtime.after.focus = ⟨value,data.scope,.nil⟩
  positive : CoreUnwindRelation.Positive currentEndpoint.point.machine
    runtime.after.point.machine [] [.cleanup data.identity]
  ownership : CurrentOwnership graph cleanupOwners runtime.after.state data.scope stack

/-- Finish consumes the current produced-and-preserved strong carrier and
current Unit receipt. No desired future Site, endpoint, Generated, bound or
success witness supplies any restoration field. -/
theorem original_result_finish_event
    (carrier : StrongOriginalResultCurrent authority start currentEndpoint)
    (callback : PhaseSite globals outward world requests actions phases budget ambient installations
      .unit activeScope currentEndpoint.lexical .unit final (Context.normal context) activeRoot)
    (current : PhaseCurrent program currentEndpoint callback)
    (returned : currentEndpoint.state.control = .returned .unit)
    (empty : EmptyFocus currentEndpoint .unit activeScope) :
    Nonempty (OriginalResultFinishEvent carrier callback current) := by
  obtain ⟨restored⟩ := restored_original_result_site authority callback
  let runtime := strong_original_finish_result carrier returned empty
  have afterRelated : runtime.after.point.machine = .eval ⟨value,data.scope,stack⟩ := rfl
  let run : LexicalUnwind.RunState :=
    ⟨runtime.after.point.machine,current.run.issued,.cleanup data.identity :: current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine run.machine
      [] [.cleanup data.identity] := by
    change LexicalUnwind.Transition current.run.machine runtime.after.point.machine
      [] [.cleanup data.identity]
    rw [current.machine,current.related,afterRelated,carrier.original.lexicalSame]
    exact .evaluate (.finishCleanup data value related.closed activeScope stack) (by trivial)
  have fresh : (current.run.issued ++ []).Nodup := by
    simpa only [List.append_nil,LexicalUnwind.RunState.erase] using current.ledger.2
  have event : LexicalUnwind.Event current.run run := by
    simpa only [List.append_nil,List.cons_append,List.nil_append]
      using LexicalUnwind.Event.step transition fresh
  let after : PhaseCurrent program runtime.after (PhaseSite.of_site restored) := {
    input := current.input, related := afterRelated,
    coreCount := current.coreCount + 1, core := .snoc current.core runtime.core,
    run := run, machine := rfl, eventCount := current.eventCount + 1,
    past := .step current.past event,
    ledger := LexicalUnwind.event_preserves_ledger event current.ledger,
    cleanupBound := current.cleanupBound }
  have saved : CoreValueRelation.ValueRel graph cleanupOwners currentEndpoint.state.heap
      runtimeValue value := by
    rw [carrier.original.heapSame]
    exact start.saved.owner_transport cleanupOwners
  have positive : CoreUnwindRelation.Positive currentEndpoint.point.machine
      runtime.after.point.machine [] [.cleanup data.identity] := by
    rw [current.related,afterRelated,carrier.original.lexicalSame]
    exact .one (.evaluate (.finishCleanup data value related.closed activeScope stack) (by trivial))
  exact ⟨⟨runtime,restored,after,saved,event,rfl,rfl,rfl,runtime.core,rfl,rfl,positive,
    strong_original_finish_ownership carrier returned empty⟩⟩

/-- The produced finish receipt retains the whole lifetime ledger, so the SAME
cleanup discharge is unique and no live owner has already completed. -/
theorem OriginalResultFinishEvent.endpoint_accounting
    (event : OriginalResultFinishEvent carrier callback current) :
    Ledger event.after.run.erase ∧ event.after.run.completed.Nodup ∧
      (∀ owner, owner ∈ event.after.run.machine.stack.erase.owners →
        owner ∉ event.after.run.completed) :=
  event.after.past.ownership ⟨List.Perm.refl [],List.nodup_nil⟩

#print axioms OriginalResultNormalStartEvent.strong_current
#print axioms strong_original_result_normal_start_event
#print axioms StrongOriginalResultCurrent.beta
#print axioms StrongOriginalResultCurrent.decision
#print axioms original_normal_retained_parts
#print axioms restored_original_result_site
#print axioms strong_original_finish_result
#print axioms strong_original_finish_ownership
#print axioms original_result_finish_event
#print axioms OriginalResultFinishEvent.endpoint_accounting

end Ash.OneShot.CoreCallableRichOriginalResultAuthority
