import CoreUnwindRelation

/-! Empty closing projections admit a finite lexical unwind, including nested
live-owner retirement. Ghost consumption and completion have distinct orders.
Empty Core discard allocates no close label; its target close label is supplied
independently and completed within the same segment. Freshness/admission remain
separate current-history obligations, with no global historical label map. -/
namespace Ash.OneShot.CoreEmptyDiscard
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreStrictFrames
  CoreEffectFrames CoreCleanupFrames CoreRequestFrames CoreResumeFrames CoreResumeEntry CoreUnwindRelation

/-- Core's eagerly consumed nested-ticket order. -/
def preorderTickets : Stack → List Nat
  | .nil => []
  | .push _ rest => preorderTickets rest
  | .live ticket _ _ saved _ rest => ticket :: preorderTickets saved ++ preorderTickets rest
  | .spent _ _ _ rest => preorderTickets rest

/-- Completed-ledger order: later discharges precede earlier discharges. -/
def completionTickets : Stack → List Nat
  | .nil => []
  | .push _ rest => completionTickets rest
  | .live ticket _ _ saved _ rest => completionTickets rest ++ ticket :: completionTickets saved
  | .spent _ _ _ rest => completionTickets rest

theorem ticket_orders_perm (stack : Stack) : (preorderTickets stack).Perm (completionTickets stack) := by
  induction stack with
  | nil => exact .refl _
  | push frame rest ih | spent ticket answer scope rest ih => exact ih
  | live ticket input answer saved scope rest ihSaved ihRest =>
      simp only [preorderTickets,completionTickets]
      exact ((ihSaved.append ihRest).cons ticket).trans
        (by simpa [List.append_assoc] using
          (List.perm_append_comm (l₁ := ticket :: completionTickets saved) (l₂ := completionTickets rest)))

private theorem plain_drop (frame : PlainFrameRel graph owners heap core plain) :
    CoreMachine.closeFuel (fuel+1) (core::rest) = CoreMachine.closeFuel fuel rest := by
  change FrameRel graph owners heap core plain.context at frame
  generalize contextEq : plain.context = context at frame
  cases frame <;> rfl

private theorem initializer_drop (frame : InitializerRel graph owners heap core plain) :
    CoreMachine.closeFuel (fuel+1) (core::rest) = CoreMachine.closeFuel fuel rest := by
  cases frame; rfl

private theorem request_drop (frame : RequestRel graph owners heap core plain) :
    CoreMachine.closeFuel (fuel+1) (core::rest) = CoreMachine.closeFuel fuel rest := by
  cases frame; rfl

private theorem resume_drop (frame : ResumeRel graph owners heap core plain) :
    CoreMachine.closeFuel (fuel+1) (core::rest) = CoreMachine.closeFuel fuel rest := by
  cases frame; rfl

/-- Arbitrary-fuel successful empty projection constructs a finite trace. The
same nested capture derivations determine both exact ghost orders. -/
theorem empty_projection
    (related : PushedWithMaps graph heap maps target) :
    ∀ fuel consumed scope rest,
      CoreMachine.closeFuel fuel (framesOf maps) = .ok ([],consumed) →
      consumed = (preorderTickets target).map CoreMachine.Observation.nestedConsumed ∧
      Trace (.unwind scope (target.append rest)) (.unwind scope rest) []
        ((completionTickets target).map Owner.ticket) := by
  induction related with
  | nil =>
      intro fuel consumed scope rest projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          have same : consumed = [] := by simpa [framesOf,CoreMachine.closeFuel] using projection.symm
          subst consumed
          exact ⟨rfl,.refl _⟩
  | @cons owners core plain cores target frame tail ih =>
      intro fuel consumed scope rest projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          rw [framesOf_cons,plain_drop frame] at projection
          obtain ⟨order,trace⟩ := ih fuel consumed scope rest projection
          exact ⟨order,by
            simpa only [Stack.append,completionTickets,List.append_nil,List.nil_append] using
              (Trace.next (.advance (.plain (frame := plain))) trace)⟩
  | @initializer owners core plain cores target frame tail ih =>
      intro fuel consumed scope rest projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          rw [framesOf_cons,initializer_drop frame] at projection
          obtain ⟨order,trace⟩ := ih fuel consumed scope rest projection
          exact ⟨order,by
            simpa only [Stack.append,completionTickets,List.append_nil,List.nil_append] using
              (Trace.next (.advance (.plain (frame := plain))) trace)⟩
  | @request owners core plain cores target frame tail ih =>
      intro fuel consumed scope rest projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          rw [framesOf_cons,request_drop frame] at projection
          obtain ⟨order,trace⟩ := ih fuel consumed scope rest projection
          exact ⟨order,by
            simpa only [Stack.append,completionTickets,List.append_nil,List.nil_append] using
              (Trace.next (.advance (.plain (frame := plain))) trace)⟩
  | @resume owners core plain cores target frame tail ih =>
      intro fuel consumed scope rest projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          rw [framesOf_cons,resume_drop frame] at projection
          obtain ⟨order,trace⟩ := ih fuel consumed scope rest projection
          exact ⟨order,by
            simpa only [Stack.append,completionTickets,List.append_nil,List.nil_append] using
              (Trace.next (.advance (.plain (frame := plain))) trace)⟩
  | @boundary owners core effectFrame cores target frame tail ih =>
      intro fuel consumed scope rest projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          cases frame with
          | handler known kind translated header =>
              have tailProjection : CoreMachine.closeFuel fuel _ = .ok ([],consumed) := projection
              obtain ⟨order,trace⟩ := ih fuel consumed scope rest tailProjection
              exact ⟨order,by
                simpa only [Stack.append,completionTickets,List.append_nil,List.nil_append] using
                  (Trace.next (.advance (.handler)) trace)⟩
          | cell known kind =>
              simp only [framesOf_cons,CoreMachine.closeFuel] at projection
              cases next : CoreMachine.closeFuel fuel (framesOf cores) <;>
                simp [next,Bind.bind,Except.bind,Pure.pure,Except.pure] at projection
  | @cleanup owners core data cores target frame tail ih =>
      intro fuel consumed scope rest projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          cases frame
          simp only [framesOf_cons,CoreMachine.closeFuel] at projection
          cases next : CoreMachine.closeFuel fuel (framesOf cores) <;>
            simp [next,Bind.bind,Except.bind,Pure.pure,Except.pure] at projection
  | @spent owners handler owner occurrence data outsideMaps outsideTarget ticket header tail ih =>
      intro fuel consumed scope rest projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          obtain ⟨order,trace⟩ := ih fuel consumed scope rest projection
          exact ⟨order,by
            simpa only [Stack.append,completionTickets,List.append_nil,List.nil_append] using
              (Trace.next (.advance (.spent (owner := ticket) (answer := data.answer) (scope := data.scope))) trace)⟩
  | @live owners handler owner occurrence data capturedMaps capturedTarget outsideMaps outsideTarget ticket result header captured outside ihCaptured ihOutside =>
      intro fuel consumed scope rest projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          simp only [framesOf_cons,CoreMachine.closeFuel] at projection
          cases child : CoreMachine.closeFuel fuel (framesOf capturedMaps) with
          | error error => simp [child,Bind.bind,Except.bind] at projection
          | ok value =>
              rcases value with ⟨closing,childConsumed⟩
              cases after : CoreMachine.closeFuel fuel (framesOf outsideMaps) with
              | error error => simp [child,after,Bind.bind,Except.bind] at projection
              | ok value =>
                  rcases value with ⟨tailClosing,tailConsumed⟩
                  have same : closing ++ tailClosing = [] ∧
                      CoreMachine.Observation.nestedConsumed ticket :: childConsumed ++ tailConsumed = consumed := by
                    simpa [child,after,Bind.bind,Except.bind,Pure.pure,Except.pure] using projection
                  obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp same.1
                  obtain ⟨childOrder,childTrace⟩ := ihCaptured fuel childConsumed scope
                    (.push (.retiring ticket) (outsideTarget.append rest)) child
                  obtain ⟨tailOrder,tailTrace⟩ := ihOutside fuel tailConsumed scope rest after
                  refine ⟨?_,?_⟩
                  · rw [←same.2,childOrder,tailOrder]
                    simp [preorderTickets,List.map_append]
                  · have trace := childTrace.append (.next (.advance .retire) tailTrace)
                    simpa [Stack.append,completionTickets,List.map_append,List.append_assoc] using
                      Trace.next (LexicalUnwind.Transition.advance (LexicalUnwind.Advance.live)) trace

/-- Turn a finite possibly-empty trace followed by a nonempty segment into
one nonempty segment, preserving exact created/completed ledger order. -/
private theorem prepend_positive (trace : Trace before middle created discharged)
    (last : Positive middle after laterCreated laterDischarged) :
    Positive before after (created ++ laterCreated) (laterDischarged ++ discharged) := by
  induction trace with
  | refl => simpa using last
  | next step rest ih => simpa [List.append_assoc] using Positive.next step (ih last)

def discardedAfter (base : CoreMachine.State) (handler owner occurrence ticket : Nat)
    (front outside : List MappedFrame) (consumed : List CoreMachine.Observation) : CoreMachine.State :=
  { base with
    control := .returned .unit,
    frames := framesOf front ++ .clauseBoundary handler owner occurrence ticket none :: framesOf outside,
    observations := base.observations ++ [.discarded ticket] ++ consumed }

/-- Actual empty discard consumes the selected owner and all nested live
captures. Its finite target segment creates/completes an independently supplied
close label while Core.nextClose remains unchanged. No freshness or admission
claim follows without separate current issued-history/static evidence. -/
theorem discard_empty {base : CoreMachine.State}
    (cut : MappedOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data input captured capturedTarget outside outsideTarget)
    (carrier : DiscardCarrier graph owners base.heap environment handler owner binder)
    (resolved : scope.resolve binder = some ticket)
    (unprotected : ProtectionContexts.protectedMode capturedTarget.erase = false)
    (projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf captured)+1)
      (framesOf captured) = .ok ([],consumed))
    (targetClose : Nat) :
    Related graph ⟨{ base with control := .discard handler owner, frames := framesOf whole },
      .eval ⟨.discard binder,scope,target⟩,owners,whole⟩ ∧
    CoreMachine.next graph { base with control := .discard handler owner, frames := framesOf whole } =
      .stepped (discardedAfter base handler owner occurrence ticket front outside consumed) ∧
    (discardedAfter base handler owner occurrence ticket front outside consumed).nextClose = base.nextClose ∧
    consumed = (preorderTickets capturedTarget).map CoreMachine.Observation.nestedConsumed ∧
    (preorderTickets capturedTarget).Perm (completionTickets capturedTarget) ∧
    Positive (.eval ⟨.discard binder,scope,target⟩)
      (.eval ⟨.unit,scope,frontTarget.append (.spent ticket data.answer data.scope outsideTarget)⟩)
      [.close targetClose]
      ([.close targetClose] ++ (completionTickets capturedTarget).map Owner.ticket ++ [.ticket ticket]) ∧
    Related graph ⟨discardedAfter base handler owner occurrence ticket front outside consumed,
      .eval ⟨.unit,scope,frontTarget.append (.spent ticket data.answer data.scope outsideTarget)⟩,
      owners,front ++ (savedOwners,.clauseBoundary handler owner occurrence ticket none)::outside⟩ := by
  obtain ⟨found,shape,header,current,frontRelated,capturedRelated,outsideRelated⟩ := cut.realizes
  obtain ⟨order,trace⟩ := empty_projection capturedRelated _ consumed scope
    (.push (.closing targetClose scope) (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))) projection
  have completed : Positive
      (.unwind scope (capturedTarget.append (.push (.closing targetClose scope)
        (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))))
      (.eval ⟨.unit,scope,frontTarget.append (.spent ticket data.answer data.scope outsideTarget)⟩)
      [] ([.close targetClose] ++ (completionTickets capturedTarget).map Owner.ticket) :=
    by simpa using prepend_positive trace (Positive.one LexicalUnwind.Transition.finishClose)
  have first : LexicalUnwind.Transition (.eval ⟨.discard binder,scope,target⟩)
      (.unwind scope (capturedTarget.append (.push (.closing targetClose scope)
        (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))))
      [.close targetClose] [.ticket ticket] := by
    rw [shape]
    exact .discard binder ticket targetClose scope data.scope input data.answer
      frontTarget capturedTarget outsideTarget resolved unprotected
  refine ⟨.discard carrier rfl rfl current,?_,rfl,order,ticket_orders_perm capturedTarget,
    by simpa [List.append_assoc] using Positive.next first completed,?_⟩
  · simp [CoreMachine.next,CoreMachine.discardOwner,found,projection,discardedAfter]
  · exact .eval ⟨by simp [discardedAfter,framesOf,List.map_append],.unit,scope,.returned .unit,
      pushed_mapped (frontRelated.append (.spent header outsideRelated))⟩

#print axioms discard_empty
#print axioms ticket_orders_perm
#print axioms empty_projection
end Ash.OneShot.CoreEmptyDiscard
