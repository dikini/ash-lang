import CoreGeneralUnwind
import CoreEmptyDiscard

/-! Ordinary callback-local discard with an arbitrary caller/outside carrier.
Only the selected capture is required to be ordinary and unprotected. Running
cleanup or CLOSE obligations outside it remain intact. Exact current closeFuel
preflight supplies projection evidence; callback success and future Related
are never premises. This is not arbitrary-GeneralSegment projection. -/
namespace Ash.OneShot.CoreGeneralProjection
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreCleanupProjection
  CoreUnwindRelation CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
  CoreGeneralUnwind
set_option linter.unusedSimpArgs false

/-- Existing ordinary mapped captures contain no running/closing completion,
including recursively saved actual live owners. The discard guard can therefore
be supplied from the current ordinary certificate, independently of outside. -/
theorem ordinary_unprotected (captured : PushedWithMaps graph heap maps target) :
    ProtectionContexts.protectedMode target.erase = false := by
  induction captured with
  | nil => rfl
  | cons frame tail ih | initializer frame tail ih | request frame tail ih | resume frame tail ih =>
      simpa [Stack.erase,ExecFrame.erase,PlainData.erase,ProtectionContexts.protectedMode,ProtectionContexts.frameProtected] using ih
  | cleanup frame tail ih =>
      simpa [Stack.erase,ExecFrame.erase,ActionData.erase,ProtectionContexts.protectedMode,ProtectionContexts.frameProtected] using ih
  | boundary frame tail ih =>
      cases frame <;> simpa [Stack.erase,ExecFrame.erase,HandlerData.erase,ProtectionContexts.protectedMode,ProtectionContexts.frameProtected] using ih
  | live header saved outside ihSaved ihOutside =>
      simp [Stack.erase,ProtectionContexts.protectedMode,ihSaved,ihOutside]
  | spent header outside ih => exact ih

def discardedState (base : CoreMachine.State) (handler owner occurrence ticket : Nat)
    (front outside : List CoreMachine.Frame) (consumed : List CoreMachine.Observation) : CoreMachine.State :=
  {base with control := .returned .unit,frames := front ++ .clauseBoundary handler owner occurrence ticket none :: outside, observations := base.observations ++ [.discarded ticket] ++ consumed}

def projectedState (base : CoreMachine.State) (handler owner occurrence ticket : Nat)
    (closing front outside : List CoreMachine.Frame) (consumed : List CoreMachine.Observation) : CoreMachine.State :=
  {base with control := .returned .unit,frames := closing ++ .closeCompletion base.nextClose :: (front ++ .clauseBoundary handler owner occurrence ticket none :: outside), nextClose := base.nextClose + 1,observations := base.observations ++ [.discarded ticket] ++ consumed ++ [.closeStarted base.nextClose]}

/-- Nonempty current preflight retains the exact selected lexical capture and
ordered physical cleanup/resource projection. Protected outside is untouched. -/
theorem discard_nonempty {base : CoreMachine.State}
    (cut : GeneralOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data input
      (framesOf capturedMaps) capturedTarget outside outsideTarget)
    (captured : PushedWithMaps graph base.heap capturedMaps capturedTarget)
    (carrier : DiscardCarrier graph owners base.heap environment handler owner binder)
    (resolved : scope.resolve binder = some ticket)
    (unprotected : ProtectionContexts.protectedMode capturedTarget.erase = false)
    (projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf capturedMaps) + 1) (framesOf capturedMaps) = .ok (closing,consumed))
    (nonempty : closing.isEmpty = false) (targetClose : Nat) :
    RetainedCursor graph base.heap closing capturedTarget ∧
    consumed = (CoreClosing.consumed capturedTarget.erase).map CoreMachine.Observation.nestedConsumed ∧
    GeneralStepWitness graph
      ⟨{base with control := .discard handler owner,frames := whole},.eval ⟨.discard binder,scope,target⟩,owners,[]⟩
      ⟨projectedState base handler owner occurrence ticket closing front outside consumed,
        .unwind scope (capturedTarget.append (.push (.closing targetClose scope)
          (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))),owners,[]⟩
      [.close targetClose] [.ticket ticket] := by
  obtain ⟨found,shape,header,current,frontSegment,capturedSegment,outsideSegment⟩ := cut.realizes
  obtain ⟨cursor,order⟩ := cursor_of_close captured _ closing consumed projection
  have remaining := frontSegment.append (.spent (ticket := ticket) header outsideSegment)
  refine ⟨cursor,order,?_,?_,?_,?_⟩
  · exact .discardSegment carrier rfl rfl current
  · simp [CoreMachine.next,CoreMachine.discardOwner,found,projection,nonempty,projectedState]
  · apply Positive.one
    rw [shape]
    exact .discard binder ticket targetClose scope data.scope input data.answer frontTarget capturedTarget outsideTarget resolved unprotected
  · exact .unwindSegment (state := projectedState base handler owner occurrence ticket closing front outside consumed) cursor remaining rfl rfl

/-- Empty current preflight performs no physical CLOSE allocation or close
observations. Its target segment accounts for its own transient close label. -/
theorem discard_empty {base : CoreMachine.State}
    (cut : GeneralOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data input
      (framesOf capturedMaps) capturedTarget outside outsideTarget)
    (captured : PushedWithMaps graph base.heap capturedMaps capturedTarget)
    (carrier : DiscardCarrier graph owners base.heap environment handler owner binder)
    (resolved : scope.resolve binder = some ticket)
    (unprotected : ProtectionContexts.protectedMode capturedTarget.erase = false)
    (projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf capturedMaps) + 1) (framesOf capturedMaps) = .ok ([],consumed))
    (targetClose : Nat) :
    consumed = (CoreEmptyDiscard.preorderTickets capturedTarget).map CoreMachine.Observation.nestedConsumed ∧
    (CoreEmptyDiscard.preorderTickets capturedTarget).Perm (CoreEmptyDiscard.completionTickets capturedTarget) ∧
    GeneralStepWitness graph
      ⟨{base with control := .discard handler owner,frames := whole},.eval ⟨.discard binder,scope,target⟩,owners,[]⟩
      ⟨discardedState base handler owner occurrence ticket front outside consumed,
        .eval ⟨.unit,scope,frontTarget.append (.spent ticket data.answer data.scope outsideTarget)⟩,owners,[]⟩
      [.close targetClose]
      ([.close targetClose] ++ (CoreEmptyDiscard.completionTickets capturedTarget).map Owner.ticket ++ [.ticket ticket]) := by
  obtain ⟨found,shape,header,current,frontSegment,capturedSegment,outsideSegment⟩ := cut.realizes
  obtain ⟨order,trace⟩ := CoreEmptyDiscard.empty_projection captured _ consumed scope
    (.push (.closing targetClose scope) (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))) projection
  have completed : Positive
      (.unwind scope (capturedTarget.append (.push (.closing targetClose scope)
        (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))))
      (.eval ⟨.unit,scope,frontTarget.append (.spent ticket data.answer data.scope outsideTarget)⟩)
      [] ([.close targetClose] ++ (CoreEmptyDiscard.completionTickets capturedTarget).map Owner.ticket) := by
    simpa using prepend_positive trace (.one LexicalUnwind.Transition.finishClose)
  have first : LexicalUnwind.Transition (.eval ⟨.discard binder,scope,target⟩)
      (.unwind scope (capturedTarget.append (.push (.closing targetClose scope)
        (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))))) [.close targetClose] [.ticket ticket] := by
    rw [shape]
    exact .discard binder ticket targetClose scope data.scope input data.answer frontTarget capturedTarget outsideTarget resolved unprotected
  refine ⟨order,CoreEmptyDiscard.ticket_orders_perm capturedTarget,?_,?_,?_,?_⟩
  · exact .discardSegment carrier rfl rfl current
  · simp [CoreMachine.next,CoreMachine.discardOwner,found,projection,discardedState]
  · simpa [List.append_assoc] using Positive.next first completed
  · exact returned_related (state := discardedState base handler owner occurrence ticket front outside consumed)
      (frontSegment.append (.spent (ticket := ticket) header outsideSegment)) .unit rfl rfl scope

/-- Local discard connects to actual inner-first release through its SAME
retained projection and arbitrary protected caller/outside carrier. -/
theorem discard_then_resource {base : CoreMachine.State}
    (cut : GeneralOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data input
      (framesOf capturedMaps) capturedTarget outside outsideTarget)
    (captured : PushedWithMaps graph base.heap capturedMaps capturedTarget)
    (carrier : DiscardCarrier graph owners base.heap environment handler owner binder)
    (resolved : scope.resolve binder = some ticket)
    (unprotected : ProtectionContexts.protectedMode capturedTarget.erase = false)
    (projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf capturedMaps) + 1) (framesOf capturedMaps) =
      .ok (.resourceBoundary site key payload :: physical,consumed)) (targetClose : Nat) :
    ∃ remaining discharged,
      RetainedCursor graph base.heap physical remaining ∧
      let prepared := projectedState base handler owner occurrence ticket (.resourceBoundary site key payload :: physical) front outside consumed
      let remainingPhysical := front ++ .clauseBoundary handler owner occurrence ticket none :: outside
      let remainingTarget := frontTarget.append (.spent ticket data.answer data.scope outsideTarget)
      let after := closingPoint (CoreResourceUnwind.releasedBase prepared key) physical remainingPhysical remaining remainingTarget
        base.nextClose targetClose scope scope owners
      GeneralChain graph
        ⟨{base with control := .discard handler owner,frames := whole},.eval ⟨.discard binder,scope,target⟩,owners,[]⟩
        [⟨prepared,.unwind scope (capturedTarget.append (.push (.closing targetClose scope) remainingTarget)),owners,[]⟩,after]
        after [.close targetClose] (discharged ++ [.ticket ticket]) := by
  obtain ⟨cursor,order,first⟩ := discard_nonempty cut captured carrier resolved unprotected projection rfl targetClose
  obtain ⟨found,shape,header,current,frontSegment,capturedSegment,outsideSegment⟩ := cut.realizes
  let prepared := projectedState base handler owner occurrence ticket (.resourceBoundary site key payload :: physical) front outside consumed
  have remaining := frontSegment.append (.spent (ticket := ticket) header outsideSegment)
  obtain ⟨next,discharged,nextCursor,last⟩ := resource_pop (base := prepared) cursor remaining
    base.nextClose targetClose scope scope owners
  have lastExact : GeneralStepWitness graph
      ⟨prepared,.unwind scope (capturedTarget.append (.push (.closing targetClose scope)
        (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))),owners,[]⟩
      (closingPoint (CoreResourceUnwind.releasedBase prepared key) physical
        (front ++ .clauseBoundary handler owner occurrence ticket none :: outside) next
        (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)) base.nextClose targetClose scope scope owners)
      [] discharged := by
    simpa [prepared,closingPoint,closingState,projectedState] using last
  exact ⟨next,discharged,nextCursor,GeneralChain.next (GeneralLink.positive first) (GeneralChain.last (GeneralLink.positive lastExact))⟩

theorem discard_release_observations (base : CoreMachine.State) (handler owner occurrence ticket key : Nat)
    (closing front outside physical : List CoreMachine.Frame) (remaining : Stack) (target : Stack)
    (consumed : List CoreMachine.Observation) (targetClose : Nat) (scope : Scope) (owners : CoreTranslation.OwnerMap) :
    (closingPoint (CoreResourceUnwind.releasedBase (projectedState base handler owner occurrence ticket closing front outside consumed) key)
      physical (front ++ .clauseBoundary handler owner occurrence ticket none :: outside) remaining target base.nextClose targetClose scope scope owners).state.observations =
      base.observations ++ [.discarded ticket] ++ consumed ++ [.closeStarted base.nextClose,.released key] := by
  simp [closingPoint,closingState,projectedState,CoreResourceUnwind.releasedBase,List.append_assoc]

theorem empty_observations (base : CoreMachine.State) (handler owner occurrence ticket : Nat)
    (front outside : List CoreMachine.Frame) (consumed : List CoreMachine.Observation) :
    (discardedState base handler owner occurrence ticket front outside consumed).observations = base.observations ++ [.discarded ticket] ++ consumed ∧
    (discardedState base handler owner occurrence ticket front outside consumed).nextClose = base.nextClose ∧
    (discardedState base handler owner occurrence ticket front outside consumed).frames = front ++ .clauseBoundary handler owner occurrence ticket none :: outside := ⟨rfl,rfl,rfl⟩

theorem nonempty_observations (base : CoreMachine.State) (handler owner occurrence ticket : Nat)
    (closing front outside : List CoreMachine.Frame) (consumed : List CoreMachine.Observation) :
    (projectedState base handler owner occurrence ticket closing front outside consumed).observations = base.observations ++ [.discarded ticket] ++ consumed ++ [.closeStarted base.nextClose] ∧
    (projectedState base handler owner occurrence ticket closing front outside consumed).nextClose = base.nextClose + 1 ∧
    (projectedState base handler owner occurrence ticket closing front outside consumed).frames = closing ++ .closeCompletion base.nextClose :: (front ++ .clauseBoundary handler owner occurrence ticket none :: outside) := ⟨rfl,rfl,rfl⟩

/-- Protected outside remains protected after the selected local capture is
consumed. No protected saved capture is made discardable. -/
theorem outside_protection_empty (obligation : ProtectedCapture outside) (base : CoreMachine.State)
    (handler owner occurrence ticket : Nat) (front : List CoreMachine.Frame) (consumed : List CoreMachine.Observation) :
    ProtectedCapture (discardedState base handler owner occurrence ticket front outside consumed).frames := by
  exact ProtectedCapture.prepend (.tail obligation) front

theorem outside_protection_nonempty (obligation : ProtectedCapture outside) (base : CoreMachine.State)
    (handler owner occurrence ticket : Nat) (closing front : List CoreMachine.Frame) (consumed : List CoreMachine.Observation) :
    ProtectedCapture (projectedState base handler owner occurrence ticket closing front outside consumed).frames := by
  exact ProtectedCapture.prepend (.tail (ProtectedCapture.prepend (.tail obligation) front)) closing

#print axioms ordinary_unprotected
#print axioms discard_nonempty
#print axioms discard_empty
#print axioms discard_then_resource
#print axioms discard_release_observations
#print axioms empty_observations
#print axioms nonempty_observations
#print axioms outside_protection_empty
#print axioms outside_protection_nonempty
end Ash.OneShot.CoreGeneralProjection
