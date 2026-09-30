import CoreUnwindRelation
import CoreEmptyDiscard

/-! Connected resource-only nonempty closing progress. Finite lexical advances
are bundled with actual Core release/close steps. Physical and target close
labels are locally separate; current issued-history freshness and callback
admission are not inferred from the residual cursor. -/
namespace Ash.OneShot.CoreResourceUnwind
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreEffectFrames
  CoreRequestFrames CoreResumeEntry CoreUnwindRelation CoreResourceProjection

private theorem completion_append (target rest : Stack) :
    completionOwners (target.append rest) = completionOwners rest ++ completionOwners target := by
  induction target with
  | nil => simp [Stack.append,completionOwners]
  | push frame target ih => cases frame <;> simp [Stack.append,completionOwners,ih,List.append_assoc]
  | spent ticket answer scope target ih => exact ih
  | live ticket input answer saved scope target ihSaved ihOutside => simp [Stack.append,completionOwners,ihOutside,List.append_assoc]

inductive Head (graph : CoreSyntax.Graph) (heap : Heap) : List CoreMachine.Frame → Stack → Prop where
  | nil : Head graph heap [] .nil
  | cell (frame : BoundaryRel graph owners heap (.resourceBoundary site key payload) (.cell key payload savedScope answer))
      (next : Cursor graph heap physical target) :
      Head graph heap (.resourceBoundary site key payload::physical) (.push (.cell key payload savedScope answer) target)

/-- Every prior skips only named finite administrative unwind cases. -/
theorem normalize (cursor : Cursor graph heap physical lexical) (scope : Scope) (rest : Stack) :
    ∃ normalized discharged,
      Cursor graph heap physical normalized ∧ Head graph heap physical normalized ∧
      Trace (.unwind scope (lexical.append rest)) (.unwind scope (normalized.append rest)) [] discharged ∧
      completionOwners lexical = completionOwners normalized ++ discharged := by
  cases cursor with
  | nil => exact ⟨.nil,[],.nil,.nil,.refl _,rfl⟩
  | @cell owners site key payload savedScope answer physical target frame next =>
      exact ⟨_,[],.cell frame next,.cell frame next,.refl _,by simp⟩
  | @plain owners core plain physical target frame next =>
      obtain ⟨normalized,discharged,cursor,head,trace,account⟩ := normalize next scope rest
      exact ⟨normalized,discharged,cursor,head,by
        simpa [Stack.append] using Trace.next (.advance (.plain (frame := plain))) trace,account⟩
  | @handler owners core data physical target frame next =>
      obtain ⟨normalized,discharged,cursor,head,trace,account⟩ := normalize next scope rest
      exact ⟨normalized,discharged,cursor,head,by
        simpa [Stack.append] using Trace.next (.advance (.handler (installation := data))) trace,account⟩
  | @spent owners handler owner occurrence data physical target ticket header next =>
      obtain ⟨normalized,discharged,cursor,head,trace,account⟩ := normalize next scope rest
      exact ⟨normalized,discharged,cursor,head,by
        simpa [Stack.append] using Trace.next (.advance (.spent (owner := ticket) (answer := data.answer) (scope := data.scope))) trace,account⟩
  | @retiring owners handler owner occurrence data physical target ticket header next =>
      obtain ⟨normalized,discharged,cursor,head,trace,account⟩ := normalize next scope rest
      exact ⟨normalized,discharged++[.ticket ticket],cursor,head,by
        simpa [Stack.append] using Trace.next (.advance (.retire (owner := ticket))) trace,by
        simpa [completionOwners,List.append_assoc] using congrArg (· ++ [.ticket ticket]) account⟩
  | @live owners handler owner occurrence data savedPhysical savedTarget outsidePhysical outsideTarget ticket result header saved outside =>
      have expanded : Cursor graph heap (savedPhysical++outsidePhysical)
          (savedTarget.append (.push (.retiring ticket) outsideTarget)) := saved.append (.retiring header outside)
      obtain ⟨normalized,discharged,cursor,head,trace,account⟩ := normalize expanded scope rest
      refine ⟨normalized,discharged,cursor,head,?_,?_⟩
      · have prepared := trace
        rw [stack_append_assoc] at prepared
        simp only [Stack.append] at prepared
        simpa [Stack.append] using
          Trace.next (.advance (LexicalUnwind.Advance.live (owner := ticket) (input := result)
            (answer := data.answer) (scope := data.scope))) prepared
      · simpa [completion_append,completionOwners,List.append_assoc] using account
termination_by weight lexical
decreasing_by all_goals simp [weight,weight_append] <;> omega

private theorem prepend_positive (trace : Trace before middle created discharged)
    (last : Positive middle after laterCreated laterDischarged) :
    Positive before after (created++laterCreated) (laterDischarged++discharged) := by
  induction trace with
  | refl => simpa using last
  | next step rest ih => simpa [List.append_assoc] using Positive.next step (ih last)

/-- One ledger witness supplies both Link and its companion target trace. -/
structure StepWitness (graph : CoreSyntax.Graph) (before after : Point)
    (created discharged : List Owner) : Prop where
  current : Related graph before
  core : CoreMachine.next graph before.state = .stepped after.state
  target : Positive before.machine after.machine created discharged
  successor : Related graph after

theorem StepWitness.link (witness : StepWitness graph before after created discharged) : Link graph before after :=
  .positive witness.current witness.core witness.target witness.successor

def residualState (base : CoreMachine.State) (physical : List CoreMachine.Frame)
    (coreClose : Nat) (maps : List MappedFrame) : CoreMachine.State :=
  { base with control := .returned .unit, frames := physical ++ .closeCompletion coreClose::framesOf maps }

def residualPoint (base : CoreMachine.State) (physical : List CoreMachine.Frame) (lexical : Stack)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap)
    (maps : List MappedFrame) (target : Stack) : Point :=
  ⟨residualState base physical coreClose maps,
    .unwind scope (lexical.append (.push (.closing targetClose callerScope) target)),owners,maps⟩

def releasedBase (base : CoreMachine.State) (key : Nat) : CoreMachine.State :=
  { base with observations := base.observations ++ [.released key] }

/-- First actual resource pop, preceded only by a finite derived lexical prefix.
The successor cursor and both Related endpoints are constructed, not supplied. -/
theorem resource_step
    (cursor : Cursor graph base.heap (.resourceBoundary site key payload::physical) lexical)
    (outside : PushedWithMaps graph base.heap maps target)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    ∃ nextLexical discharged,
      Cursor graph base.heap physical nextLexical ∧
      StepWitness graph
        (residualPoint base (.resourceBoundary site key payload::physical) lexical coreClose targetClose scope callerScope owners maps target)
        (residualPoint (releasedBase base key) physical nextLexical coreClose targetClose scope callerScope owners maps target)
        [] discharged ∧
      completionOwners lexical = completionOwners nextLexical ++ discharged := by
  obtain ⟨normalized,prior,normalizedCursor,head,trace,account⟩ :=
    normalize cursor scope (.push (.closing targetClose callerScope) target)
  cases head with
  | cell frame next =>
      rename_i savedOwners savedScope answer nextLexical
      have step : Positive
          (.unwind scope (lexical.append (.push (.closing targetClose callerScope) target)))
          (.unwind scope (nextLexical.append (.push (.closing targetClose callerScope) target)))
          [] ([.resource key]++prior) := by
        simpa [Stack.append] using prepend_positive trace
          (Positive.one (LexicalUnwind.Transition.advance LexicalUnwind.Advance.cell))
      refine ⟨nextLexical,[Owner.resource key]++prior,next,⟨?_,?_,by simpa [residualPoint] using step,?_⟩,?_⟩
      · exact .resourceProjected cursor outside rfl rfl
      · rfl
      · exact .resourceProjected (state := residualState (releasedBase base key) physical coreClose maps) next outside rfl rfl
      · simpa [completionOwners,List.append_assoc] using account

def finishedState (base : CoreMachine.State) (coreClose : Nat) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned .unit, frames := framesOf maps,
    observations := base.observations ++ [.closeFinished coreClose] }

def finishedPoint (base : CoreMachine.State) (coreClose : Nat) (callerScope : Scope)
    (owners : CoreTranslation.OwnerMap) (maps : List MappedFrame) (target : Stack) : Point :=
  ⟨finishedState base coreClose maps,.eval ⟨.unit,callerScope,target⟩,owners,maps⟩

/-- Remaining lexical retirements precede the actual close pop. Separate local
Core/target labels are preserved in their respective observation/ledger outputs. -/
theorem finish_step
    (cursor : Cursor graph base.heap [] lexical)
    (outside : PushedWithMaps graph base.heap maps target)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    StepWitness graph (residualPoint base [] lexical coreClose targetClose scope callerScope owners maps target)
      (finishedPoint base coreClose callerScope owners maps target)
      [] ([.close targetClose]++completionOwners lexical) := by
  obtain ⟨normalized,prior,normalizedCursor,head,trace,account⟩ :=
    normalize cursor scope (.push (.closing targetClose callerScope) target)
  cases head
  have ledger : prior = completionOwners lexical := by simpa [completionOwners] using account.symm
  subst prior
  exact ⟨.resourceProjected cursor outside rfl rfl,rfl,
    by simpa [residualPoint,finishedPoint] using prepend_positive trace (Positive.one LexicalUnwind.Transition.finishClose),
    .eval ⟨rfl,.unit,callerScope,.returned .unit,pushed_mapped outside⟩⟩

/-- Ledger companion to the existing Chain. Every link and trace use the
identical StepWitness.target proof, rather than separately chosen transitions. -/
inductive AccountedChain (graph : CoreSyntax.Graph) : Point → List Point → Point → List Owner → List Owner → Prop where
  | last (step : StepWitness graph before after created discharged) :
      AccountedChain graph before [after] after created discharged
  | next (step : StepWitness graph before middle created discharged)
      (rest : AccountedChain graph middle points after laterCreated laterDischarged) :
      AccountedChain graph before (middle::points) after (created++laterCreated) (laterDischarged++discharged)

theorem AccountedChain.chain (accounted : AccountedChain graph before points after created discharged) :
    Chain graph before points after := by
  induction accounted with
  | last step => exact .last step.link
  | next step rest ih => exact .next step.link ih

theorem AccountedChain.trace (accounted : AccountedChain graph before points after created discharged) :
    Trace before.machine after.machine created discharged := by
  induction accounted with
  | last step => exact step.target.trace
  | next step rest ih => exact step.target.trace.append ih

def releaseEvents (physical : List CoreMachine.Frame) : List CoreMachine.Observation :=
  physical.filterMap fun frame => match frame with
    | .resourceBoundary _ key _ => some (.released key)
    | _ => none

def afterReleases (base : CoreMachine.State) (physical : List CoreMachine.Frame) : CoreMachine.State :=
  { base with observations := base.observations ++ releaseEvents physical }

/-- One connected chain releases every exact physical resource in inner-first
order and completes the independently named target close. Nested ticket
retirements occur in their lexical positions along the same target sequence. -/
theorem resource_segment
    (cursor : Cursor graph base.heap physical lexical)
    (outside : PushedWithMaps graph base.heap maps target)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    ∃ points, points.length = physical.length+1 ∧
      AccountedChain graph (residualPoint base physical lexical coreClose targetClose scope callerScope owners maps target)
        points (finishedPoint (afterReleases base physical) coreClose callerScope owners maps target)
        [] ([.close targetClose]++completionOwners lexical) := by
  cases physical with
  | nil =>
      refine ⟨[finishedPoint base coreClose callerScope owners maps target],rfl,?_⟩
      simpa [afterReleases,releaseEvents] using AccountedChain.last (finish_step cursor outside coreClose targetClose scope callerScope owners)
  | cons frame physical =>
      obtain ⟨site,key,payload,rfl⟩ := cursor.resource_only frame (List.mem_cons_self)
      obtain ⟨nextLexical,discharged,nextCursor,step,account⟩ := resource_step cursor outside coreClose targetClose scope callerScope owners
      obtain ⟨points,count,rest⟩ := resource_segment (base := releasedBase base key) nextCursor outside coreClose targetClose scope callerScope owners
      refine ⟨residualPoint (releasedBase base key) physical nextLexical coreClose targetClose scope callerScope owners maps target::points,by simp [count],?_⟩
      have combined := AccountedChain.next step rest
      have ledger : [.close targetClose]++completionOwners nextLexical++discharged =
          [.close targetClose]++completionOwners lexical := by rw [account,List.append_assoc]
      rw [ledger] at combined
      simpa [afterReleases,releasedBase,releaseEvents,List.append_assoc] using combined
termination_by physical.length
decreasing_by simp_all

private theorem trace_accounting (trace : Trace before after created discharged) :
    (before.stack.erase.owners++created).Perm (after.stack.erase.owners++discharged) := by
  induction trace with
  | refl => exact .refl _
  | next step rest ih =>
      have first := LexicalUnwind.transition_accounting step
      apply List.perm_iff_count.mpr
      intro owner
      have firstCount := first.count_eq owner
      have restCount := ih.count_eq owner
      simp only [List.count_append] at firstCount restCount ⊢
      omega

/-- Multiplicity accounting refers to the same accumulated transition witness;
it does not assert freshness or ownership validity. -/
theorem AccountedChain.accounting (accounted : AccountedChain graph before points after created discharged) :
    (before.machine.stack.erase.owners++created).Perm (after.machine.stack.erase.owners++discharged) :=
  trace_accounting accounted.trace

def preparedBase (base : CoreMachine.State) (ticket : Nat) (consumed : List CoreMachine.Observation) : CoreMachine.State :=
  { base with
    nextClose := base.nextClose+1,
    observations := base.observations ++ [.discarded ticket] ++ consumed ++ [.closeStarted base.nextClose] }

/-- Connected actual nonempty discard through all releases and close completion.
The guard selects this proved resource-only batch; cleanup is a later boundary,
not an exclusion from the language. Core and target close labels remain distinct. -/
theorem discard_resource_segment {base : CoreMachine.State}
    (cut : MappedOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data input captured capturedTarget outside outsideTarget)
    (carrier : DiscardCarrier graph owners base.heap environment handler owner binder)
    (resolved : scope.resolve binder = some ticket)
    (unprotected : ProtectionContexts.protectedMode capturedTarget.erase = false)
    (projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf captured)+1)
      (framesOf captured) = .ok (closing,consumed))
    (only : ResourceOnly closing) (nonempty : closing.isEmpty = false)
    (targetClose : Nat) :
    ∃ points, points.length = closing.length+2 ∧
      AccountedChain graph
        ⟨{ base with control := .discard handler owner,frames := framesOf whole },.eval ⟨.discard binder,scope,target⟩,owners,whole⟩
        points
        (finishedPoint (afterReleases (preparedBase base ticket consumed) closing) base.nextClose scope owners
          (front ++ (savedOwners,.clauseBoundary handler owner occurrence ticket none)::outside)
          (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))
        [.close targetClose]
        ([.close targetClose]++completionOwners capturedTarget++[.ticket ticket]) ∧
      consumed = (CoreClosing.consumed capturedTarget.erase).map CoreMachine.Observation.nestedConsumed ∧
      (planOwners (resourceItems closing) ++ (CoreClosing.consumed capturedTarget.erase).map Owner.ticket).Perm capturedTarget.erase.owners := by
  obtain ⟨found,shape,header,current,frontRelated,capturedRelated,outsideRelated⟩ := cut.realizes
  obtain ⟨cursor,order⟩ := cursor_of_close capturedRelated _ closing consumed projection only
  let remainingMaps := front ++ (savedOwners,.clauseBoundary handler owner occurrence ticket none)::outside
  let remainingTarget := frontTarget.append (.spent ticket data.answer data.scope outsideTarget)
  have remaining : PushedWithMaps graph base.heap remainingMaps remainingTarget := frontRelated.append (.spent header outsideRelated)
  have firstTarget : Positive (.eval ⟨.discard binder,scope,target⟩)
      (residualPoint (preparedBase base ticket consumed) closing capturedTarget base.nextClose targetClose scope scope owners remainingMaps remainingTarget).machine
      [.close targetClose] [.ticket ticket] := by
    apply Positive.one
    change LexicalUnwind.Transition (.eval ⟨.discard binder,scope,target⟩)
      (.unwind scope (capturedTarget.append (.push (.closing targetClose scope) remainingTarget))) _ _
    rw [shape]
    exact .discard binder ticket targetClose scope data.scope input data.answer
      frontTarget capturedTarget outsideTarget resolved unprotected
  have first : StepWitness graph
      ⟨{ base with control := .discard handler owner,frames := framesOf whole },.eval ⟨.discard binder,scope,target⟩,owners,whole⟩
      (residualPoint (preparedBase base ticket consumed) closing capturedTarget base.nextClose targetClose scope scope owners remainingMaps remainingTarget)
      [.close targetClose] [.ticket ticket] := by
    refine ⟨.discard carrier rfl rfl current,?_,firstTarget,?_⟩
    · simp only [CoreMachine.next,CoreMachine.discardOwner,found,projection,nonempty]
      simp [residualPoint,residualState,preparedBase,remainingMaps,framesOf,List.map_append]
    · exact .resourceProjected (state := residualState (preparedBase base ticket consumed) closing base.nextClose remainingMaps) cursor remaining rfl rfl
  obtain ⟨points,count,suffix⟩ := resource_segment (base := preparedBase base ticket consumed) cursor remaining base.nextClose targetClose scope scope owners
  have ownership := CoreClosing.ready_accounting (pushed_ready capturedRelated)
  rw [cursor.retained] at ownership
  refine ⟨(residualPoint (preparedBase base ticket consumed) closing capturedTarget base.nextClose targetClose scope scope owners remainingMaps remainingTarget)::points,by simp [count],?_,order,ownership⟩
  simpa [List.append_assoc] using AccountedChain.next first suffix

/-- The reached endpoint records exactly the original release order and the
physical close label; target completion uses its own independently chosen label. -/
theorem completion_observations :
    (finishedPoint (afterReleases base physical) coreClose callerScope owners maps target).state.observations =
      base.observations ++ releaseEvents physical ++ [.closeFinished coreClose] := rfl

theorem completion_counter :
    (finishedPoint (afterReleases base physical) coreClose callerScope owners maps target).state.nextClose = base.nextClose := rfl

#print axioms completion_observations
#print axioms completion_counter
#print axioms AccountedChain.accounting
#print axioms discard_resource_segment
#print axioms AccountedChain.chain
#print axioms AccountedChain.trace
#print axioms resource_segment
#print axioms resource_step
#print axioms finish_step
#print axioms normalize
end Ash.OneShot.CoreResourceUnwind
