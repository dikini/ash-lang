import CoreCallableReachableResume
import CoreGeneralRestoration

/-! Saved caller scope provenance for actual normal cleanup transitions.
The registration producer retains the same entire ActionData and CleanupRel at
its physical outside suffix. Actual callback entry clears only current scope;
Unit completion restores that receipt's own map and ActionData.scope. These
factories work over arbitrary general outside segments. They do not construct
scope provenance from CleanupRel alone, prove callback termination, or transport
saved scope paths across arbitrary captures and projections. -/
namespace Ash.OneShot.CoreCallableCleanupOrigins
open ScopedExpressions ScopedExecution CoreTranslation CoreMachine CoreValueRelation
open CoreStrictStack CoreStrictFrames CoreCleanupFrames CoreCleanupRunFrames
open CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableReachableResume

/-- All entries keep their generated static binder, including retained outer
entries. No dynamic resolution or future source fact is assumed. -/
theorem CurrentScopeOrigin.canonical
    (origin : CurrentScopeOrigin graph owners scope physical) : CanonicalOwnerMap graph owners := by
  cases origin with
  | inactive canonical => exact canonical
  | clause canonical path => exact canonical.clause

/-- The same installed delayed callback and full ActionData retain their caller
map/scope at the exact physical suffix below this obligation. CleanupRel alone
deliberately does not supply this saved scope provenance. -/
structure SavedCleanupOrigin (graph : CoreSyntax.Graph) (owners : OwnerMap) (heap : CoreMachine.Heap)
    (action : CoreSyntax.NodeRef) (environment : CoreMachine.Environment)
    (data : ActionData) (physical : List CoreMachine.Frame) : Prop where
  delayed : CleanupRel graph owners heap (.cleanupBoundary action environment data.identity) data
  origin : CurrentScopeOrigin graph owners data.scope physical

theorem SavedCleanupOrigin.heap_weaken
    (receipt : SavedCleanupOrigin graph owners heap action environment data physical)
    (extension : HeapExtends heap larger) :
    SavedCleanupOrigin graph owners larger action environment data physical :=
  ⟨receipt.delayed.heap_weaken extension, receipt.origin⟩

theorem CurrentScopeOrigin.prepend_cleanup
    (origin : CurrentScopeOrigin graph owners scope physical) :
    CurrentScopeOrigin graph owners scope (.cleanupBoundary action environment identity :: physical) := by
  cases origin with
  | inactive canonical => exact .inactive canonical
  | clause canonical path =>
    exact .clause canonical (.skip _ (by intro _ _ _ _ _ impossible; cases impossible) path)

private theorem lambda_value
    (related : ValueRel graph owners heap value (.lambda parameter body)) :
    ∃ parameter body saved, value = .closure parameter body saved := by
  cases related with
  | closure => exact ⟨_, _, _, rfl⟩

theorem cleanup_enter_owned {graph : CoreSyntax.Graph} { base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .cleanup callback action body)
    (shape : CoreTranslation.checkCleanup graph site callback action = .ok ())
    (translated : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment (.cleanup (.variable callback.id) rawBody)
      (.cleanup data.action bodyCode))
    (callable : data.action = .lambda parameter lambdaBody)
    (identity : data.identity = base.nextCleanup)
    (ownership : CurrentOwnership graph owners {base with frames := framesOf annotations} data.scope target)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations { base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.cleanup data.action bodyCode,data.scope,target⟩ ∧
    CoreMachine.next graph { base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped { base with control := .evaluate body environment, frames := .cleanupBoundary action environment data.identity :: framesOf annotations, nextCleanup := base.nextCleanup + 1, observations := base.observations ++ [.entered site,.cleanupArmed data.identity]} ∧
    RawStep ⟨.cleanup data.action bodyCode,data.scope,target⟩
      ⟨bodyCode,data.scope,.push (.armed data) target⟩ [.cleanup data.identity] [] ∧
    ComponentMapped graph owners ((owners,.cleanupBoundary action environment data.identity) :: annotations)
      { base with control := .evaluate body environment, frames := .cleanupBoundary action environment data.identity :: framesOf annotations, nextCleanup := base.nextCleanup + 1, observations := base.observations ++ [.entered site,.cleanupArmed data.identity]}
      ⟨bodyCode,data.scope,.push (.armed data) target⟩ ∧
    SavedCleanupOrigin graph owners base.heap action environment data (framesOf annotations) ∧
    CurrentOwnership graph owners
      {base with control := .evaluate body environment, frames := .cleanupBoundary action environment data.identity :: framesOf annotations, nextCleanup := base.nextCleanup + 1, observations := base.observations ++ [.entered site,.cleanupArmed data.identity]}
      data.scope (.push (.armed data) target) := by
  obtain ⟨before, next, raw, after⟩ :=
    CoreCleanupEntry.cleanup_enter_mapped known kind shape translated current callable identity older
  obtain ⟨callbackSaved, bodySaved⟩ := cleanup_components current
  obtain ⟨value, lookup, related⟩ := callbackSaved.lookup data.closed
  have closureRelated := related
  rw [callable] at closureRelated
  obtain ⟨parameter, functionBody, captured, closureSame⟩ := lambda_value closureRelated
  cases closureSame
  have delayed := checked_action_translation (owners := owners) shape
  have boundary : CleanupRel graph owners base.heap (.cleanupBoundary action environment data.identity) data :=
    .armed known kind shape delayed (app_unit callbackSaved) lookup related
  have events : CoreTicketHistory.capturedTickets
      (base.observations ++ [.entered site,.cleanupArmed data.identity]) =
      CoreTicketHistory.capturedTickets base.observations ++ issuedTickets [.cleanup data.identity] := by
    simp [CoreTicketHistory.capturedTickets, issuedTickets]
  exact ⟨before, next, raw, after, ⟨boundary, ownership.scopeOrigin⟩,
    ownership.tickets.step raw events, CurrentScopeOrigin.prepend_cleanup ownership.scopeOrigin⟩

/-- Current name counting and the saved caller scope are both recovered after
an actual normal Unit completion; the saved value is interpreted at that same
installation map rather than using the callback's empty capability map. -/
theorem normal_finish_owned {base : CoreMachine.State}
    (receipt : SavedCleanupOrigin graph savedOwners base.heap action environment data physical)
    (saved : ValueRel graph valueOwners base.heap savedValue savedCode)
    (outside : GeneralSegment graph base.heap physical lexical)
    (bounded : TicketBound base (.push (.running data savedCode saved.closed) lexical))
    (activeOwners : OwnerMap) (scope : Execution.Scope) :
    GeneralStepWitness graph
      ⟨returnedState base .unit (.cleanupCompletion data.identity savedValue :: physical),
        .eval ⟨.unit,scope,.push (.running data savedCode saved.closed) lexical⟩,activeOwners,[]⟩
      ⟨observedState base savedValue physical (.cleanupFinished data.identity),
        .eval ⟨savedCode,data.scope,lexical⟩,savedOwners,[]⟩ [] [.cleanup data.identity] ∧
    CurrentOwnership graph savedOwners
      (observedState base savedValue physical (.cleanupFinished data.identity)) data.scope lexical := by
  have savedAtCaller := saved.owner_transport savedOwners
  have step := CoreGeneralRestoration.normal_finish receipt.delayed savedAtCaller outside activeOwners scope
  have raw : RawStep ⟨.unit,scope,.push (.running data savedCode saved.closed) lexical⟩
      ⟨savedCode,data.scope,lexical⟩ [] [.cleanup data.identity] :=
    .finishCleanup data savedCode saved.closed scope lexical
  have events : CoreTicketHistory.capturedTickets
      (observedState base savedValue physical (.cleanupFinished data.identity)).observations =
      CoreTicketHistory.capturedTickets base.observations ++ issuedTickets [] := by
    simp [observedState, CoreTicketHistory.capturedTickets, issuedTickets]
  exact ⟨step, bounded.step raw events, receipt.origin⟩

/-- Actual normal entry authenticates the callback through the same installed
CleanupRel, retains the caller receipt, and derives empty callback scope. -/
theorem normal_start_owned {base : CoreMachine.State}
    (receipt : SavedCleanupOrigin graph cleanupOwners base.heap action environment data physical)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (outside : GeneralSegment graph base.heap physical lexical)
    (bounded : TicketBound base (.push (.armed data) lexical)) (scope : Execution.Scope) :
    GeneralStepWitness graph
      ⟨returnedState base savedValue (.cleanupBoundary action environment data.identity :: physical),
        .eval ⟨savedCode,scope,.push (.armed data) lexical⟩,callerOwners,[]⟩
      ⟨startedState base action environment data.identity savedValue physical,
        .eval ⟨.app data.action .unit,.none,.push (.running data savedCode saved.closed) lexical⟩,cleanupOwners,[]⟩ [] [] ∧
    CurrentOwnership graph cleanupOwners
      (startedState base action environment data.identity savedValue physical) .none
      (.push (.running data savedCode saved.closed) lexical) ∧
    SavedCleanupOrigin graph cleanupOwners
      (startedState base action environment data.identity savedValue physical).heap action environment data physical := by
  have step := CoreGeneralRestoration.normal_start receipt.delayed saved outside scope
  have raw : RawStep ⟨savedCode,scope,.push (.armed data) lexical⟩
      ⟨.app data.action .unit,.none,.push (.running data savedCode saved.closed) lexical⟩ [] [] :=
    .startCleanup data savedCode saved.closed scope lexical
  have events : CoreTicketHistory.capturedTickets
      (startedState base action environment data.identity savedValue physical).observations =
      CoreTicketHistory.capturedTickets base.observations ++ issuedTickets [] := by
    simp [startedState, CoreTicketHistory.capturedTickets, issuedTickets]
  exact ⟨step, ⟨bounded.step raw events, .inactive (CurrentScopeOrigin.canonical receipt.origin)⟩, receipt⟩

#print axioms CurrentScopeOrigin.canonical
#print axioms SavedCleanupOrigin.heap_weaken
#print axioms CurrentScopeOrigin.prepend_cleanup
#print axioms cleanup_enter_owned
#print axioms normal_start_owned
#print axioms normal_finish_owned
end Ash.OneShot.CoreCallableCleanupOrigins
