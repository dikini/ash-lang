import CoreCallableOutsideOrigin
import CoreCallableCallerBarriers
namespace Ash.OneShot.CoreCallableCleanupActivation
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableCleanupReachableTransport
open CoreCallableGeneralHistory CoreCallableOutsideOrigin

/-- A current spent marker actually returns Unit before the running completion
becomes current. The dormant original receipt is reconstructed only for that
completion's CURRENT tail, then consumed by actual normal finish. -/
theorem spent_then_finish_outside {base : CoreMachine.State}
    (past : GeneralClausePast graph markerOwners handler owner occurrence dynamicTicket captured markerData)
    (header : CoreRequestFrames.OwnerHeader graph markerOwners base.heap handler owner occurrence markerData)
    (receipt : RunningReceipt graph cleanupOwners base.heap action environment data savedValue savedCode originalPhysical)
    (same : originalPhysical = kept ++ outside)
    (position : ScopeOutside receipt.installed.origin kept)
    (inserted : GeneralHistory graph base.heap added addedTarget)
    (checked : outsideCheck cleanupOwners data.scope inserted = true)
    (current : GeneralHistory graph base.heap (kept ++ (added ++ outside)) lexical)
    (bounded : TicketBound base
      (.spent dynamicTicket markerData.answer markerData.scope
        (.push (.running data savedCode receipt.value.closed) lexical)))
    (activeOwners : OwnerMap) (runtimeScope : Execution.Scope) :
    let actualTail := kept ++ (added ++ outside)
    let atCompletion := observedState base .unit
      (.cleanupCompletion data.identity savedValue :: actualTail) (.clauseReturned dynamicTicket)
    GeneralStepWitness graph
      ⟨returnedState base .unit
          (.clauseBoundary handler owner occurrence dynamicTicket none ::
            .cleanupCompletion data.identity savedValue :: actualTail),
        .eval ⟨.unit,runtimeScope,.spent dynamicTicket markerData.answer markerData.scope
          (.push (.running data savedCode receipt.value.closed) lexical)⟩,activeOwners,[]⟩
      ⟨atCompletion,.eval ⟨.unit,markerData.scope,
          .push (.running data savedCode receipt.value.closed) lexical⟩,markerOwners,[]⟩ [] [] ∧
    GeneralStepWitness graph
      ⟨atCompletion,.eval ⟨.unit,markerData.scope,
          .push (.running data savedCode receipt.value.closed) lexical⟩,markerOwners,[]⟩
      ⟨observedState atCompletion savedValue actualTail (.cleanupFinished data.identity),
        .eval ⟨savedCode,data.scope,lexical⟩,cleanupOwners,[]⟩ [] [.cleanup data.identity] ∧
    CurrentOwnership graph cleanupOwners
      (observedState atCompletion savedValue actualTail (.cleanupFinished data.identity)) data.scope lexical ∧
    ∃ successor : GeneralHistory graph base.heap actualTail lexical, successor = current ∧
      ∃ activated : RunningReceipt graph cleanupOwners base.heap action environment data savedValue savedCode actualTail,
        activated.installed.delayed = receipt.installed.delayed ∧ activated.value = receipt.value ∧
        (GeneralHistory.spent past header
          (GeneralHistory.append (.running receipt) current)).related =
          GeneralSegment.spent header ((GeneralHistory.append (.running receipt) current).related) := by
  dsimp only
  have activated := CoreCallableOutsideOrigin.RunningReceipt.restore_outside_checked
    receipt same position inserted checked
  have completion : GeneralHistory graph base.heap
      (.cleanupCompletion data.identity savedValue :: (kept ++ (added ++ outside)))
      (.push (.running data savedCode receipt.value.closed) lexical) := by
    simpa only [Stack.append,List.singleton_append] using GeneralHistory.append (.running receipt) current
  have first := leave_clause (base := base) header (ValueRel.unit (owners := activeOwners))
    completion.related dynamicTicket runtimeScope
  let atCompletion := observedState base .unit
    (.cleanupCompletion data.identity savedValue :: (kept ++ (added ++ outside))) (.clauseReturned dynamicTicket)
  have completionBound : TicketBound atCompletion (.push (.running data savedCode receipt.value.closed) lexical) := by
    apply bounded.step (.leaveClause dynamicTicket markerData.answer .unit (ValueRel.unit (graph := graph) (owners := activeOwners) (heap := base.heap)).closed
      runtimeScope markerData.scope (.push (.running data savedCode receipt.value.closed) lexical))
    simp [atCompletion,observedState,CoreTicketHistory.capturedTickets,issuedTickets]
  obtain ⟨second,owned,_⟩ := normal_finish_history (base := atCompletion) activated current
    completionBound markerOwners markerData.scope
  refine ⟨first,?_,owned,current,rfl,activated,?_,?_,?_⟩
  · simpa only [returnedState,atCompletion,observedState] using second
  · rfl
  · rfl
  · rfl

theorem spent_then_finish_inside {base : CoreMachine.State}
    (past : GeneralClausePast graph markerOwners handler owner occurrence dynamicTicket captured markerData)
    (header : CoreRequestFrames.OwnerHeader graph markerOwners base.heap handler owner occurrence markerData)
    (receipt : RunningReceipt graph cleanupOwners base.heap action environment data savedValue savedCode originalPhysical)
    (same : originalPhysical = kept ++ outside)
    (position : ScopeInside receipt.installed.origin kept)
    (nextOutside : List CoreMachine.Frame)
    (current : GeneralHistory graph base.heap (kept ++ nextOutside) lexical)
    (bounded : TicketBound base
      (.spent dynamicTicket markerData.answer markerData.scope
        (.push (.running data savedCode receipt.value.closed) lexical)))
    (activeOwners : OwnerMap) (runtimeScope : Execution.Scope) :
    let actualTail := kept ++ nextOutside
    let atCompletion := observedState base .unit
      (.cleanupCompletion data.identity savedValue :: actualTail) (.clauseReturned dynamicTicket)
    GeneralStepWitness graph
      ⟨returnedState base .unit
          (.clauseBoundary handler owner occurrence dynamicTicket none ::
            .cleanupCompletion data.identity savedValue :: actualTail),
        .eval ⟨.unit,runtimeScope,.spent dynamicTicket markerData.answer markerData.scope
          (.push (.running data savedCode receipt.value.closed) lexical)⟩,activeOwners,[]⟩
      ⟨atCompletion,.eval ⟨.unit,markerData.scope,
          .push (.running data savedCode receipt.value.closed) lexical⟩,markerOwners,[]⟩ [] [] ∧
    GeneralStepWitness graph
      ⟨atCompletion,.eval ⟨.unit,markerData.scope,
          .push (.running data savedCode receipt.value.closed) lexical⟩,markerOwners,[]⟩
      ⟨observedState atCompletion savedValue actualTail (.cleanupFinished data.identity),
        .eval ⟨savedCode,data.scope,lexical⟩,cleanupOwners,[]⟩ [] [.cleanup data.identity] ∧
    CurrentOwnership graph cleanupOwners
      (observedState atCompletion savedValue actualTail (.cleanupFinished data.identity)) data.scope lexical ∧
    ∃ successor : GeneralHistory graph base.heap actualTail lexical, successor = current ∧
      ∃ activated : RunningReceipt graph cleanupOwners base.heap action environment data savedValue savedCode actualTail,
        activated.installed.delayed = receipt.installed.delayed ∧ activated.value = receipt.value ∧
        (GeneralHistory.spent past header
          (GeneralHistory.append (.running receipt) current)).related =
          GeneralSegment.spent header ((GeneralHistory.append (.running receipt) current).related) := by
  dsimp only
  have activated := CoreCallableCleanupReachableTransport.RunningReceipt.restore_inside
    receipt same position nextOutside
  have completion : GeneralHistory graph base.heap
      (.cleanupCompletion data.identity savedValue :: (kept ++ nextOutside))
      (.push (.running data savedCode receipt.value.closed) lexical) := by
    simpa only [Stack.append,List.singleton_append] using GeneralHistory.append (.running receipt) current
  have first := leave_clause (base := base) header (ValueRel.unit (owners := activeOwners))
    completion.related dynamicTicket runtimeScope
  let atCompletion := observedState base .unit
    (.cleanupCompletion data.identity savedValue :: (kept ++ nextOutside)) (.clauseReturned dynamicTicket)
  have completionBound : TicketBound atCompletion (.push (.running data savedCode receipt.value.closed) lexical) := by
    apply bounded.step (.leaveClause dynamicTicket markerData.answer .unit (ValueRel.unit (graph := graph) (owners := activeOwners) (heap := base.heap)).closed
      runtimeScope markerData.scope (.push (.running data savedCode receipt.value.closed) lexical))
    simp [atCompletion,observedState,CoreTicketHistory.capturedTickets,issuedTickets]
  obtain ⟨second,owned,_⟩ := normal_finish_history (base := atCompletion) activated current
    completionBound markerOwners markerData.scope
  refine ⟨first,?_,owned,current,rfl,activated,?_,?_,?_⟩
  · simpa only [returnedState,atCompletion,observedState] using second
  · rfl
  · rfl
  · rfl

#print axioms spent_then_finish_outside
#print axioms spent_then_finish_inside
end Ash.OneShot.CoreCallableCleanupActivation
