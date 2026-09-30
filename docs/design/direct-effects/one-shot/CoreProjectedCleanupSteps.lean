import CoreNormalCleanupSteps
import CoreResourceUnwind

/-! General cleanup-bearing projected start and current Unit completion.
Finite lexical normalization selects the actual physical head. Callback-body
positive splicing and user-effect dispatch are separate obligations. -/
namespace Ash.OneShot.CoreProjectedCleanupSteps
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreStrictFrames
  CoreEffectFrames CoreCleanupFrames CoreCleanupRunFrames CoreUnwindRelation
  CoreCleanupProjection
open CoreResourceProjection (weight weight_append)

inductive Head (graph : CoreSyntax.Graph) (heap : Heap) : List CoreMachine.Frame → Stack → Prop where
  | nil : Head graph heap [] .nil
  | cell (frame : BoundaryRel graph owners heap (.resourceBoundary site key payload) (.cell key payload savedScope answer))
      (next : RetainedCursor graph heap physical target) :
      Head graph heap (.resourceBoundary site key payload::physical) (.push (.cell key payload savedScope answer) target)
  | armed (delayed : CleanupRel graph owners heap (.cleanupBoundary action environment data.identity) data)
      (next : RetainedCursor graph heap physical target) :
      Head graph heap (.cleanupBoundary action environment data.identity::physical) (.push (.armed data) target)

/-- Every prior skips only named finite administrative unwind cases. -/
theorem normalize (cursor : RetainedCursor graph heap physical lexical) (scope : Scope) (rest : Stack) :
    ∃ normalized discharged,
      RetainedCursor graph heap physical normalized ∧ Head graph heap physical normalized ∧
      Trace (.unwind scope (lexical.append rest)) (.unwind scope (normalized.append rest)) [] discharged := by
  cases cursor with
  | nil => exact ⟨.nil,[],.nil,.nil,.refl _⟩
  | @cell owners site key payload savedScope answer physical target frame next =>
      exact ⟨_,[],.cell frame next,.cell frame next,.refl _⟩
  | armed delayed next => exact ⟨_,[],.armed delayed next,.armed delayed next,.refl _⟩
  | @plain owners core plain physical target frame next =>
      obtain ⟨normalized,discharged,cursor,head,trace⟩ := normalize next scope rest
      exact ⟨normalized,discharged,cursor,head,by
        simpa [Stack.append] using Trace.next (.advance (.plain (frame := plain))) trace⟩
  | @handler owners core data physical target frame next =>
      obtain ⟨normalized,discharged,cursor,head,trace⟩ := normalize next scope rest
      exact ⟨normalized,discharged,cursor,head,by
        simpa [Stack.append] using Trace.next (.advance (.handler (installation := data))) trace⟩
  | @spent owners handler owner occurrence data physical target ticket header next =>
      obtain ⟨normalized,discharged,cursor,head,trace⟩ := normalize next scope rest
      exact ⟨normalized,discharged,cursor,head,by
        simpa [Stack.append] using Trace.next (.advance (.spent (owner := ticket) (answer := data.answer) (scope := data.scope))) trace⟩
  | @retiring owners handler owner occurrence data physical target ticket header next =>
      obtain ⟨normalized,discharged,cursor,head,trace⟩ := normalize next scope rest
      exact ⟨normalized,discharged++[.ticket ticket],cursor,head,by
        simpa [Stack.append] using Trace.next (.advance (.retire (owner := ticket))) trace⟩
  | @live owners handler owner occurrence data savedPhysical savedTarget outsidePhysical outsideTarget ticket result header saved outside =>
      have expanded : RetainedCursor graph heap (savedPhysical++outsidePhysical)
          (savedTarget.append (.push (.retiring ticket) outsideTarget)) := saved.append (.retiring header outside)
      obtain ⟨normalized,discharged,cursor,head,trace⟩ := normalize expanded scope rest
      refine ⟨normalized,discharged,cursor,head,?_⟩
      · have prepared := trace
        rw [stack_append_assoc] at prepared
        simp only [Stack.append] at prepared
        simpa [Stack.append] using
          Trace.next (.advance (LexicalUnwind.Advance.live (owner := ticket) (input := result)
            (answer := data.answer) (scope := data.scope))) prepared
termination_by weight lexical
decreasing_by all_goals simp [weight,weight_append] <;> omega

private theorem prepend_positive (trace : Trace before middle created discharged)
    (last : Positive middle after laterCreated laterDischarged) :
    Positive before after (created++laterCreated) (laterDischarged++discharged) := by
  induction trace with
  | refl => simpa using last
  | next step rest ih => simpa [List.append_assoc] using Positive.next step (ih last)


/-- A cleanup physical head forces the selected lexical armed boundary.
Its saved action evidence comes from normalization of this same cursor. -/
theorem select_cleanup
    (cursor : RetainedCursor graph heap (.cleanupBoundary action environment identity::physical) lexical)
    (scope : Scope) (rest : Stack) :
    ∃ owners data remaining discharged,
      data.identity = identity ∧
      CleanupRel graph owners heap (.cleanupBoundary action environment data.identity) data ∧
      RetainedCursor graph heap physical remaining ∧
      Trace (.unwind scope (lexical.append rest))
        (.unwind scope (.push (.armed data) (remaining.append rest))) [] discharged := by
  obtain ⟨normalized,discharged,current,head,trace⟩ := normalize cursor scope rest
  generalize framesEq : CoreMachine.Frame.cleanupBoundary action environment identity::physical = frames at head current
  cases head with
  | nil => cases framesEq
  | cell frame next => cases framesEq
  | armed delayed next =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj framesEq
    obtain ⟨actionEq,environmentEq,identityEq⟩ := CoreMachine.Frame.cleanupBoundary.inj headEq
    cases actionEq; cases environmentEq; cases tailEq
    exact ⟨_,_,_,discharged,identityEq.symm,delayed,next,trace⟩

def closingState (base : CoreMachine.State) (physical : List CoreMachine.Frame)
    (coreClose : Nat) (maps : List MappedFrame) : CoreMachine.State :=
  {base with control := .returned .unit, frames := physical ++ .closeCompletion coreClose :: framesOf maps}

def closingPoint (base : CoreMachine.State) (physical : List CoreMachine.Frame) (lexical : Stack)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap)
    (maps : List MappedFrame) (target : Stack) : Point :=
  ⟨closingState base physical coreClose maps,
    .unwind scope (lexical.append (.push (.closing targetClose callerScope) target)),owners,maps⟩

def runningState (base : CoreMachine.State) (action : CoreSyntax.NodeRef)
    (environment : CoreMachine.Environment) (identity : Nat)
    (physical : List CoreMachine.Frame) (coreClose : Nat) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .evaluate action environment
    frames := .cleanupCompletion identity .unit :: physical ++ .closeCompletion coreClose :: framesOf maps
    observations := base.observations ++ [.cleanupStarted identity]}

def runningPoint (base : CoreMachine.State) (action : CoreSyntax.NodeRef)
    (environment : CoreMachine.Environment) (data : ActionData)
    (physical : List CoreMachine.Frame) (lexical : Stack) (coreClose targetClose : Nat)
    (callerScope : Scope) (cleanupOwners : CoreTranslation.OwnerMap)
    (maps : List MappedFrame) (target : Stack) : Point :=
  ⟨runningState base action environment data.identity physical coreClose maps,
    .eval ⟨.app data.action .unit,.none,
      .push (.unwinding data) (lexical.append (.push (.closing targetClose callerScope) target))⟩,
    cleanupOwners,[]⟩

/-- Actual start includes the derived finite selection prefix. The callback is
interpreted from its saved CleanupRel; its success is not an input. -/
theorem projected_start {base : CoreMachine.State}
    (cursor : RetainedCursor graph base.heap (.cleanupBoundary action environment identity::physical) lexical)
    (outside : PushedWithMaps graph base.heap maps target)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    ∃ cleanupOwners data remaining discharged,
      data.identity = identity ∧
      CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data ∧
      RetainedCursor graph base.heap physical remaining ∧
      CoreResourceUnwind.StepWitness graph
        (closingPoint base (.cleanupBoundary action environment identity::physical) lexical
          coreClose targetClose scope callerScope owners maps target)
        (runningPoint base action environment data physical remaining coreClose targetClose callerScope cleanupOwners maps target)
        [] discharged := by
  obtain ⟨cleanupOwners,data,remaining,discharged,identityEq,delayed,residual,selection⟩ :=
    select_cleanup cursor scope (.push (.closing targetClose callerScope) target)
  obtain ⟨callback,translated,saved⟩ := CoreNormalCleanupSteps.delayed_action delayed
  have component : ComponentMapped graph cleanupOwners []
      (isolate (runningState base action environment data.identity physical coreClose maps) [])
      ⟨.app data.action .unit,.none,.nil⟩ :=
    ⟨rfl,_,.none,.evaluate translated saved,pushed_mapped .nil⟩
  refine ⟨cleanupOwners,data,remaining,discharged,identityEq,delayed,residual,?_,?_,?_,?_⟩
  · exact .retainedProjected cursor outside rfl rfl
  · simp [closingPoint,closingState,runningPoint,runningState,CoreMachine.next,identityEq]
  · simpa [closingPoint,runningPoint,List.append_nil] using
      prepend_positive selection (Positive.one (LexicalUnwind.Transition.startCleanup))
  · exact .runningCleanup (state := runningState base action environment data.identity physical coreClose maps)
      (.retainedProjected delayed residual outside) component rfl

/-- Construction at actual nonempty discard keeps all delayed actions and
nested captures. Physical and target close labels are not equated. -/
theorem discard_projected {base : CoreMachine.State}
    (cut : CoreResumeEntry.MappedOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data input captured capturedTarget outside outsideTarget)
    (carrier : DiscardCarrier graph owners base.heap environment handler owner binder)
    (resolved : scope.resolve binder = some ticket)
    (unprotected : ProtectionContexts.protectedMode capturedTarget.erase = false)
    (projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf captured)+1)
      (framesOf captured) = .ok (closing,consumed))
    (nonempty : closing.isEmpty = false) (targetClose : Nat) :
    RetainedCursor graph base.heap closing capturedTarget ∧
    consumed = (CoreClosing.consumed capturedTarget.erase).map CoreMachine.Observation.nestedConsumed ∧
    CoreResourceUnwind.StepWitness graph
      ⟨{base with control := .discard handler owner,frames := framesOf whole},
        .eval ⟨.discard binder,scope,target⟩,owners,whole⟩
      (closingPoint (CoreResourceUnwind.preparedBase base ticket consumed) closing capturedTarget
        base.nextClose targetClose scope scope owners
        (front ++ (savedOwners,.clauseBoundary handler owner occurrence ticket none)::outside)
        (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))
      [.close targetClose] [.ticket ticket] := by
  obtain ⟨found,shape,header,current,frontRelated,capturedRelated,outsideRelated⟩ := cut.realizes
  obtain ⟨cursor,order⟩ := cursor_of_close capturedRelated _ closing consumed projection
  have remaining := frontRelated.append (.spent (ticket := ticket) header outsideRelated)
  refine ⟨cursor,order,?_,?_,?_,?_⟩
  · exact .discard carrier rfl rfl current
  · simp only [CoreMachine.next,CoreMachine.discardOwner,found,projection,nonempty]
    simp [closingPoint,closingState,CoreResourceUnwind.preparedBase,framesOf,List.map_append]
  · apply Positive.one
    change LexicalUnwind.Transition (.eval ⟨.discard binder,scope,target⟩)
      (.unwind scope (capturedTarget.append (.push (.closing targetClose scope)
        (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))))) _ _
    rw [shape]
    exact .discard binder ticket targetClose scope data.scope input data.answer
      frontTarget capturedTarget outsideTarget resolved unprotected
  · exact .retainedProjected cursor remaining rfl rfl

def finishState (base : CoreMachine.State) (identity : Nat)
    (physical : List CoreMachine.Frame) (coreClose : Nat) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned .unit
    frames := physical ++ .closeCompletion coreClose :: framesOf maps
    observations := base.observations ++ [.cleanupFinished identity] }

/-- Completion is a current Unit-return redex, not a premise that callback
execution will reach Unit. It restores the same residual and ActionData scope. -/
theorem projected_finish {base : CoreMachine.State}
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (residual : RetainedCursor graph base.heap physical lexical)
    (outside : PushedWithMaps graph base.heap maps target)
    (coreClose targetClose : Nat) (callbackScope callerScope : Scope)
    (activeOwners : CoreTranslation.OwnerMap) :
    CoreResourceUnwind.StepWitness graph
      ⟨{ base with
        control := .returned .unit
        frames := .cleanupCompletion data.identity .unit :: physical ++ .closeCompletion coreClose :: framesOf maps},
        .eval ⟨.unit,callbackScope,.push (.unwinding data)
          (lexical.append (.push (.closing targetClose callerScope) target))⟩,activeOwners,[]⟩
      (closingPoint (finishState base data.identity physical coreClose maps) physical lexical
        coreClose targetClose data.scope callerScope activeOwners maps target)
      [] [.cleanup data.identity] := by
  let current : CoreMachine.State := { base with
    control := .returned .unit
    frames := .cleanupCompletion data.identity .unit :: physical ++ .closeCompletion coreClose :: framesOf maps}
  have component : ComponentMapped graph activeOwners [] (isolate current []) ⟨.unit,callbackScope,.nil⟩ :=
    ⟨rfl,.unit,callbackScope,.returned .unit,pushed_mapped .nil⟩
  refine ⟨?_,?_,Positive.one LexicalUnwind.Transition.finishCleanup,?_⟩
  · exact .runningCleanup (state := current) (.retainedProjected delayed residual outside) component rfl
  · rfl
  · exact .retainedProjected residual outside rfl rfl

/-- A resource head is selected by the same general normalization, even when
later residual work includes further armed cleanup boundaries. -/
theorem resource_pop
    (cursor : RetainedCursor graph base.heap (.resourceBoundary site key payload::physical) lexical)
    (outside : PushedWithMaps graph base.heap maps target)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    ∃ remaining discharged,
      RetainedCursor graph base.heap physical remaining ∧
      CoreResourceUnwind.StepWitness graph
        (closingPoint base (.resourceBoundary site key payload::physical) lexical coreClose targetClose scope callerScope owners maps target)
        (closingPoint (CoreResourceUnwind.releasedBase base key) physical remaining coreClose targetClose scope callerScope owners maps target)
        [] discharged := by
  obtain ⟨normalized,prior,current,head,trace⟩ :=
    normalize cursor scope (.push (.closing targetClose callerScope) target)
  cases head with
  | cell frame next =>
      rename_i savedOwners savedScope answer remaining
      have step : Positive
          (.unwind scope (lexical.append (.push (.closing targetClose callerScope) target)))
          (.unwind scope (remaining.append (.push (.closing targetClose callerScope) target)))
          [] ([.resource key]++prior) := by
        simpa [Stack.append] using prepend_positive trace
          (Positive.one (LexicalUnwind.Transition.advance LexicalUnwind.Advance.cell))
      refine ⟨remaining,[Owner.resource key]++prior,next,?_,?_,?_,?_⟩
      · exact .retainedProjected cursor outside rfl rfl
      · rfl
      · simpa [closingPoint] using step
      · exact .retainedProjected (state := closingState (CoreResourceUnwind.releasedBase base key) physical coreClose maps) next outside rfl rfl

/-- Empty physical work forces all remaining lexical work to be finite skips
or ticket retirement. The actual close pop uses its own physical label. -/
theorem empty_close
    (cursor : RetainedCursor graph base.heap [] lexical)
    (outside : PushedWithMaps graph base.heap maps target)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    ∃ prior,
      CoreResourceUnwind.StepWitness graph
        (closingPoint base [] lexical coreClose targetClose scope callerScope owners maps target)
        (CoreResourceUnwind.finishedPoint base coreClose callerScope owners maps target)
        [] ([.close targetClose]++prior) := by
  obtain ⟨normalized,prior,current,head,trace⟩ :=
    normalize cursor scope (.push (.closing targetClose callerScope) target)
  cases head
  exact ⟨prior,.retainedProjected cursor outside rfl rfl,rfl,
    by simpa [closingPoint,CoreResourceUnwind.finishedPoint] using
      prepend_positive trace (Positive.one LexicalUnwind.Transition.finishClose),
    .eval ⟨rfl,.unit,callerScope,.returned .unit,pushed_mapped outside⟩⟩

/-- The actual discard and selected cleanup start share one accounted chain.
The callback itself is still unevaluated at this endpoint. -/
theorem discard_cleanup_start {base : CoreMachine.State}
    (cut : CoreResumeEntry.MappedOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket handlerData input captured capturedTarget outside outsideTarget)
    (carrier : DiscardCarrier graph owners base.heap environment handler owner binder)
    (resolved : scope.resolve binder = some ticket)
    (unprotected : ProtectionContexts.protectedMode capturedTarget.erase = false)
    (projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf captured)+1)
      (framesOf captured) = .ok (.cleanupBoundary action actionEnvironment identity::physical,consumed))
    (targetClose : Nat) :
    ∃ cleanupOwners data remaining discharged,
      data.identity = identity ∧
      CoreResourceUnwind.AccountedChain graph
        ⟨{base with control := .discard handler owner,frames := framesOf whole},
          .eval ⟨.discard binder,scope,target⟩,owners,whole⟩
        [closingPoint (CoreResourceUnwind.preparedBase base ticket consumed)
          (.cleanupBoundary action actionEnvironment identity::physical) capturedTarget base.nextClose targetClose scope scope owners
          (front ++ (savedOwners,.clauseBoundary handler owner occurrence ticket none)::outside)
          (frontTarget.append (.spent ticket handlerData.answer handlerData.scope outsideTarget)),
         runningPoint (CoreResourceUnwind.preparedBase base ticket consumed) action actionEnvironment data physical remaining
          base.nextClose targetClose scope cleanupOwners
          (front ++ (savedOwners,.clauseBoundary handler owner occurrence ticket none)::outside)
          (frontTarget.append (.spent ticket handlerData.answer handlerData.scope outsideTarget))]
        (runningPoint (CoreResourceUnwind.preparedBase base ticket consumed) action actionEnvironment data physical remaining
          base.nextClose targetClose scope cleanupOwners
          (front ++ (savedOwners,.clauseBoundary handler owner occurrence ticket none)::outside)
          (frontTarget.append (.spent ticket handlerData.answer handlerData.scope outsideTarget)))
        [.close targetClose] (discharged ++ [.ticket ticket]) := by
  obtain ⟨cursor,order,initial⟩ := discard_projected cut carrier resolved unprotected projection (by rfl) targetClose
  obtain ⟨found,shape,header,current,frontRelated,capturedRelated,outsideRelated⟩ := cut.realizes
  have remaining := frontRelated.append (.spent (ticket := ticket) header outsideRelated)
  obtain ⟨cleanupOwners,data,residual,discharged,identityEq,delayed,next,start⟩ :=
    projected_start (base := CoreResourceUnwind.preparedBase base ticket consumed) cursor remaining base.nextClose targetClose scope scope owners
  exact ⟨cleanupOwners,data,residual,discharged,identityEq,by
    simpa using CoreResourceUnwind.AccountedChain.next initial (.last start)⟩

/-- Ownership accounting is for the identical constructed segment, including
its finite normalization and exact exposed discharge list. -/
theorem step_accounting
    (witness : CoreResourceUnwind.StepWitness graph before after created discharged) :
    (before.machine.stack.erase.owners ++ created).Perm (after.machine.stack.erase.owners ++ discharged) :=
  (CoreResourceUnwind.AccountedChain.last witness).accounting

#print axioms normalize
#print axioms select_cleanup
#print axioms projected_start
#print axioms discard_projected
#print axioms projected_finish
#print axioms resource_pop
#print axioms empty_close
#print axioms discard_cleanup_start
#print axioms step_accounting
end Ash.OneShot.CoreProjectedCleanupSteps
