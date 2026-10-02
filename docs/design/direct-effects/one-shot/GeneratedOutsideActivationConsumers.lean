import GeneratedOutsideActivationOrigins
import CoreCallableGeneratedCleanupCompletion
namespace Ash.OneShot.GeneratedOutsideActivationConsumers
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneratedChronology CoreCallableGeneralHistory
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableSiteLineage CoreCallableCallerBarriers
open CoreCallableCleanupReachableTransport CoreCallableOutsideOrigin CoreCallableGeneratedCleanupCompletion
open CoreCallableRunningOccurrence CoreCallableGeneratedCurrentScopeConsumers GeneratedOutsideActivationOrigins

private theorem marker_check_from_capture {graph : Graph} {owners : OwnerMap} {scope : Execution.Scope}
    {physical : List CoreMachine.Frame}
    (origin : CurrentScopeOrigin graph owners scope physical) (sameScope : data.scope = scope)
    (unique : UniqueHandlerSites graph)
    (past : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data)
    (header : CoreRequestFrames.OwnerHeader graph owners heap handler owner occurrence data) :
    outsideCheck owners scope (GeneralHistory.spent past header .nil) = true := by
  cases origin with
  | inactive canonical => rfl
  | @clause rest callerHandler callerOwner callerOccurrence callerTicket saved originalPhysical front outside canonical path =>
    have different : callerHandler ≠ handler ∨ callerOwner ≠ owner := installed_clause_miss past unique sameScope
    rcases different with different | different
    all_goals simp [outsideCheck,owner_search,OwnerSearch.prepend,different]

/-- Actual K installation forbids its literal identity from being the enclosing
active caller's identity; the cleanup saved scope is computed from K's endpoint. -/
theorem outside_checked_spent {graph : Graph} {before : Endpoint graph}
    (handler : HandlerInput before) (cleanup : CleanupReady (handler_result handler).after)
    (unique : UniqueHandlerSites graph)
    (past : GeneralClausePast graph handler.owners handler.installation.handler owner occurrence dynamicTicket captured handler.data)
    (header : CoreRequestFrames.OwnerHeader graph handler.owners heap handler.installation.handler owner occurrence handler.data) :
    outsideCheck handler.owners cleanup.data.scope (GeneralHistory.spent past header .nil) = true := by
  rw [cleanup_saved_scope handler cleanup]
  exact marker_check_from_capture handler.installation.origin rfl unique past header

/-- A non-clause leading K handler puts every active original first owner
outside that one-frame kept prefix. Inactive scope also has a constructor. -/
theorem scope_outside_handler {graph : Graph}
    (origin : CurrentScopeOrigin graph owners scope (.handlerBoundary site environment activation :: outside)) :
    ScopeOutside origin [.handlerBoundary site environment activation] := by
  cases origin with
  | inactive canonical => exact .inactive canonical
  | clause canonical path =>
    cases path with
    | skip frame miss next => exact .clause canonical (.skip (.handlerBoundary site environment activation) miss next) (by simp)

/-- The original one-frame kept prefix is computed from SAME handler entry.
The current tail remains an explicit physical shape guard, while the saved
scope equality, first-owner position, and inserted-marker check are outputs. -/
noncomputable def finish_without_checked {graph : Graph} {before : Endpoint graph}
    (handler : HandlerInput before) (cleanup : CleanupReady (handler_result handler).after)
    {start : RunningStartPast graph (handler_result handler).after.owners cleanup.action cleanup.environment
      cleanup.data savedValue savedCode (handler_result handler).after.physical (handler_result handler).after.lexical}
    {current : Endpoint graph} (generated : Generated start current count created discharged)
    (unique : UniqueHandlerSites graph)
    (past : GeneralClausePast graph handler.owners handler.installation.handler owner occurrence dynamicTicket captured handler.data)
    (header : CoreRequestFrames.OwnerHeader graph handler.owners current.state.heap handler.installation.handler owner occurrence handler.data)
    (head : RunningHead start current.history)
    (shape : head.tail.physical = .handlerBoundary handler.site handler.environment handler.data.activation ::
      .clauseBoundary handler.installation.handler owner occurrence dynamicTicket none :: before.physical)
    (scope : Execution.Scope) (control : current.state.control = .returned .unit)
    (empty : EmptyFocus current .unit scope) : FinishInput generated := {
  head := head
  activation := by
    rw [shape]
    exact .outside (kept := [.handlerBoundary handler.site handler.environment handler.data.activation])
      (outside := before.physical) rfl
      (scope_outside_handler generated.retained_running_receipt.installed.origin)
      (GeneralHistory.spent past header .nil) (outside_checked_spent handler cleanup unique past header)
  scope := scope,control := control,empty := empty }

theorem finish_without_checked_actual {graph : Graph} {before : Endpoint graph}
    (handler : HandlerInput before) (cleanup : CleanupReady (handler_result handler).after)
    {start : RunningStartPast graph (handler_result handler).after.owners cleanup.action cleanup.environment
      cleanup.data savedValue savedCode (handler_result handler).after.physical (handler_result handler).after.lexical}
    {current : Endpoint graph} (generated : Generated start current count created discharged)
    (unique : UniqueHandlerSites graph)
    (past : GeneralClausePast graph handler.owners handler.installation.handler owner occurrence dynamicTicket captured handler.data)
    (header : CoreRequestFrames.OwnerHeader graph handler.owners current.state.heap handler.installation.handler owner occurrence handler.data)
    (head : RunningHead start current.history)
    (shape : head.tail.physical = .handlerBoundary handler.site handler.environment handler.data.activation ::
      .clauseBoundary handler.installation.handler owner occurrence dynamicTicket none :: before.physical)
    (scope : Execution.Scope) (control : current.state.control = .returned .unit)
    (empty : EmptyFocus current .unit scope) :
    CoreMachine.next graph current.state = .stepped
      (finish_result (finish_without_checked handler cleanup generated unique past header head shape scope control empty)).after.state ∧
    Matching graph current
      (finish_result (finish_without_checked handler cleanup generated unique past header head shape scope control empty)).after [] [.cleanup cleanup.data.identity] := by
  let input := finish_without_checked handler cleanup generated unique past header head shape scope control empty
  exact ⟨(finish_result input).core,(finish_result input).matching⟩

#print axioms outside_checked_spent
#print axioms scope_outside_handler
#print axioms finish_without_checked
#print axioms finish_without_checked_actual
end Ash.OneShot.GeneratedOutsideActivationConsumers
