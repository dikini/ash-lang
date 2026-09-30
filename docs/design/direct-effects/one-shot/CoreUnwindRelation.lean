import CoreResumeEntry
import SourceResourceRoutes
import CoreCleanupRunFrames
import CoreResourceProjection

/-! A bounded bridge to the current lexical unwind machine. Core closeFuel
projects captured scopes, while the target retains their lexical order. This
relation records both structures; it does not assume callback safety, target
validity, or unrestricted equality of their effect dispatch. -/
namespace Ash.OneShot.CoreUnwindRelation
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreStrictPotential
  CoreResumeEntry CoreInitialPrefix CoreRequestFrames

structure Point where
  state : CoreMachine.State
  machine : LexicalUnwind.Machine
  owners : CoreTranslation.OwnerMap
  annotations : List MappedFrame

def lift (point : CoreInitialPrefix.Point) : Point :=
  ⟨point.state,.eval point.target,point.owners,point.annotations⟩

/-- The current static site and lexical owner resolution remain available when
Core switches from evaluate to its discard control. -/
inductive DiscardCarrier (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) (environment : CoreMachine.Environment) (handler owner binder : Nat) : Prop where
  | site (known : graph.node site = some node)
      (kind : node.kind = .discard handler owner .consumed)
      (resolved : CoreTranslation.resolveOwner owners site handler owner = .ok binder)
      (closed : EnvCloses graph owners heap environment (.discard binder) (.discard binder)) :
      DiscardCarrier graph owners heap environment handler owner binder

inductive Related (graph : CoreSyntax.Graph) : Point → Prop where
  | eval (component : ComponentMapped graph owners annotations state target) :
      Related graph ⟨state,.eval target,owners,annotations⟩
  | discard (carrier : DiscardCarrier graph owners state.heap environment handler owner binder)
      (control : state.control = .discard handler owner)
      (frames : state.frames = framesOf annotations)
      (stack : PushedWithMaps graph state.heap annotations target) :
      Related graph ⟨state,.eval ⟨.discard binder,scope,target⟩,owners,annotations⟩
  | projected (captured : PushedWithMaps graph state.heap capturedMaps capturedTarget)
      (outside : PushedWithMaps graph state.heap tailMaps tail)
      (projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf capturedMaps) + 1)
        (framesOf capturedMaps) = .ok (closing,consumed))
      (nonempty : closing.isEmpty = false)
      (control : state.control = .returned .unit)
      (frames : state.frames = closing ++ .closeCompletion identity :: framesOf tailMaps)
      (counter : state.nextClose = identity + 1) :
      Related graph ⟨state,.unwind scope (capturedTarget.append (.push (.closing identity scope) tail)),
        owners,tailMaps⟩
  | awaitingClose (control : state.control = .returned .unit)
      (frames : state.frames = .closeCompletion identity :: framesOf annotations)
      (tail : PushedWithMaps graph state.heap annotations target) :
      Related graph ⟨state,.unwind scope (.push (.closing identity callerScope) target),owners,annotations⟩
  /-- Resource-only residual work keeps separate local physical/target close
  labels. No global label map or freshness claim is implied by this carrier. -/
  | resourceProjected (cursor : CoreResourceProjection.Cursor graph state.heap physical lexical)
      (outside : PushedWithMaps graph state.heap annotations target)
      (control : state.control = .returned .unit)
      (frames : state.frames = physical ++ .closeCompletion coreClose :: framesOf annotations) :
      Related graph ⟨state,.unwind scope (lexical.append (.push (.closing targetClose callerScope) target)),
        owners,annotations⟩
  | runningCleanup (carrier : CoreCleanupRunFrames.RunningTail graph state.heap physical lexical)
      (component : ComponentMapped graph owners annotations (CoreCleanupRunFrames.isolate state annotations) target)
      (frames : state.frames = framesOf annotations ++ physical) :
      Related graph ⟨state,.eval (CoreCleanupRunFrames.attach target lexical),owners,annotations⟩

/-- Every lifted ordinary raw step requires the current lexical-machine guard.
In particular this cannot lift the obsolete plan-based discard rule. -/
inductive Positive : LexicalUnwind.Machine → LexicalUnwind.Machine → List Owner → List Owner → Prop where
  | one (step : LexicalUnwind.Transition before after created discharged) : Positive before after created discharged
  | next (step : LexicalUnwind.Transition before middle created discharged)
      (rest : Positive middle after laterCreated laterDischarged) :
      Positive before after (created ++ laterCreated) (laterDischarged ++ discharged)

theorem ordinary_step (step : RawStep before after created discharged)
    (allowed : LexicalUnwind.ordinary before.expression) :
    Positive (.eval before) (.eval after) created discharged :=
  .one (.evaluate step allowed)

inductive Link (graph : CoreSyntax.Graph) : Point → Point → Prop where
  | positive (current : Related graph before)
      (core : CoreMachine.next graph before.state = .stepped after.state)
      (target : Positive before.machine after.machine created discharged)
      (successor : Related graph after) : Link graph before after
  | traversal (witness : SilentMapped graph beforeOwners afterOwners beforeMaps afterMaps before after target) :
      Link graph ⟨before,.eval target,beforeOwners,beforeMaps⟩ ⟨after,.eval target,afterOwners,afterMaps⟩
  | value (witness : CoreAdministrativeTransport.TransportMapped graph beforeOwners afterOwners beforeMaps afterMaps before after target) :
      Link graph ⟨before,.eval target,beforeOwners,beforeMaps⟩ ⟨after,.eval target,afterOwners,afterMaps⟩
  | discardEntry (current : Related graph before) (successor : Related graph after)
      (core : CoreMachine.next graph before.state = .stepped after.state)
      (same : before.machine = after.machine)
      (phase : ∃ site environment handler owner,
        before.state.control = .evaluate site environment ∧ after.state.control = .discard handler owner)
      (decreasing : potential graph after.state < potential graph before.state) : Link graph before after
  | runningAdministration
      (carrier : CoreCleanupRunFrames.RunningTail graph before.heap physical lexical)
      (witness : CoreCleanupRunFrames.Administrative graph beforeOwners afterOwners beforeMaps afterMaps before after target)
      (beforeFrames : before.frames = framesOf beforeMaps ++ physical)
      (afterFrames : after.frames = framesOf afterMaps ++ physical)
      (core : CoreMachine.next graph before = .stepped after) :
      Link graph ⟨before,.eval (CoreCleanupRunFrames.attach target lexical),beforeOwners,beforeMaps⟩
        ⟨after,.eval (CoreCleanupRunFrames.attach target lexical),afterOwners,afterMaps⟩

inductive Chain (graph : CoreSyntax.Graph) : Point → List Point → Point → Prop where
  | last (link : Link graph before after) : Chain graph before [after] after
  | next (link : Link graph before middle) (rest : Chain graph middle points after) :
      Chain graph before (middle :: points) after

theorem positive_lift (execution : CoreInitialPrefix.Positive before after) :
    ∃ created discharged, Positive (.eval before) (.eval after) created discharged := by
  induction execution with
  | one step allowed => exact ⟨_,_,ordinary_step step allowed⟩
  | next step rest allowed ih =>
      obtain ⟨created,discharged,trace⟩ := ih
      exact ⟨_,_,.next (.evaluate step allowed) trace⟩

theorem link_lift (execution : CoreInitialPrefix.Link graph before after) : Link graph (lift before) (lift after) := by
  cases execution with
  | positive current core target successor =>
      obtain ⟨created,discharged,trace⟩ := positive_lift target
      exact .positive (.eval current) core trace (.eval successor)
  | traversal witness => exact .traversal witness
  | value witness => exact .value witness

theorem chain_lift (execution : CoreInitialPrefix.Chain graph before points after) :
    Chain graph (lift before) (points.map lift) (lift after) := by
  induction execution with
  | last link => exact .last (link_lift link)
  | next link rest ih => exact .next (link_lift link) ih

inductive Trace : LexicalUnwind.Machine → LexicalUnwind.Machine → List Owner → List Owner → Prop where
  | refl (machine) : Trace machine machine [] []
  | next (step : LexicalUnwind.Transition before middle created discharged)
      (rest : Trace middle after laterCreated laterDischarged) :
      Trace before after (created ++ laterCreated) (laterDischarged ++ discharged)

private theorem closed_ordinary (closed : ClosedValue code) : LexicalUnwind.ordinary code := by
  cases code <;> simp [LexicalUnwind.ordinary]
  simpa [Code.IsValue] using closed.1

theorem raw_without_close_ordinary (step : RawStep before after created discharged)
    (noClose : ∀ identity, .close identity ∉ created) : LexicalUnwind.ordinary before.expression := by
  cases step <;> simp only [LexicalUnwind.ordinary]
  case focus plain focus tail =>
    generalize same : plain.context = context at focus
    cases focus <;> trivial
  case plug plain value closed scope tail => exact closed_ordinary closed
  case leaveHandler handler value closed scope tail => exact closed_ordinary closed
  case leaveCell identity payload answer savedScope scope value closed tail => exact closed_ordinary closed
  case startCleanup action saved closed scope tail => exact closed_ordinary closed
  case leaveClause ticket answer value closed scope callerScope tail => exact closed_ordinary closed
  case discard binder ticket identity scope caller input answer front captured tail plan resolve build =>
    exact False.elim (noClose identity (by simp))

/-- A no-close ledger constructively supplies the guard at every raw step. -/
theorem raw_trace_lift (trace : RawTrace before after created discharged)
    (noClose : ∀ identity, .close identity ∉ created) : Trace (.eval before) (.eval after) created discharged := by
  induction trace with
  | refl => exact .refl _
  | @next before middle headCreated headDischarged after tailCreated tailDischarged step rest ih =>
      have head : ∀ identity, Owner.close identity ∉ headCreated := fun identity member =>
        noClose identity (List.mem_append_left _ member)
      have tail : ∀ identity, Owner.close identity ∉ tailCreated := fun identity member =>
        noClose identity (List.mem_append_right _ member)
      exact .next (.evaluate step (raw_without_close_ordinary step head)) (ih tail)

theorem Trace.append (first : Trace before middle created discharged)
    (second : Trace middle after laterCreated laterDischarged) :
    Trace before after (created ++ laterCreated) (laterDischarged ++ discharged) := by
  induction first with
  | refl => simpa using second
  | next step rest ih => simpa [List.append_assoc] using Trace.next step (ih second)

theorem Positive.trace (positive : Positive before after created discharged) : Trace before after created discharged := by
  induction positive with
  | one step => simpa using Trace.next step (Trace.refl _)
  | next step rest ih => exact .next step ih

theorem chain_append (first : Chain graph before initial middle) (second : Chain graph middle later after) :
    Chain graph before (initial ++ later) after := by
  induction first with
  | last link => exact .next link second
  | next link rest ih => exact .next link (ih second)

theorem Link.endpoints (link : Link graph before after) : Related graph before ∧ Related graph after := by
  cases link with
  | positive current core target successor | discardEntry current successor core same phase decreasing => exact ⟨current,successor⟩
  | traversal witness => exact ⟨.eval witness.current,.eval witness.successor⟩
  | value witness => exact ⟨.eval witness.current,.eval witness.successor⟩
  | runningAdministration carrier witness beforeFrames afterFrames core =>
      obtain ⟨before,after,heap,_⟩ := witness.components
      exact ⟨.runningCleanup carrier before beforeFrames,
        .runningCleanup (carrier.heap_weaken heap) after afterFrames⟩

theorem Link.core_next (link : Link graph before after) : CoreMachine.next graph before.state = .stepped after.state := by
  cases link with
  | positive _ core _ _ | discardEntry _ _ core _ _ _ => exact core
  | traversal witness => exact witness.core
  | value witness => exact witness.core
  | runningAdministration _ _ _ _ core => exact core

theorem running_administration_decreases
    (witness : CoreCleanupRunFrames.Administrative graph bo ao bm am before after target)
    (beforeFrames : before.frames = framesOf bm ++ physical)
    (afterFrames : after.frames = framesOf am ++ physical) : potential graph after < potential graph before :=
  CoreCleanupRunFrames.potential_splice beforeFrames afterFrames witness.components.2.2.2

theorem Chain.endpoints (chain : Chain graph before points after) : Related graph before ∧ Related graph after := by
  induction chain with
  | last link => exact link.endpoints
  | next link rest ih => exact ⟨link.endpoints.1,ih.2⟩

theorem Chain.core_steps (chain : Chain graph before points after) :
    CoreAllocationHistory.Steps graph points.length before.state after.state := by
  have extend : ∀ {count start}, CoreAllocationHistory.Steps graph count start before.state →
      CoreAllocationHistory.Steps graph (count + points.length) start after.state := by
    induction chain with
    | last link =>
        intro count start earlier
        exact CoreAllocationHistory.Steps.snoc earlier link.core_next
    | next link rest ih =>
        intro count start earlier
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (CoreAllocationHistory.Steps.snoc earlier link.core_next)
  simpa using extend (CoreAllocationHistory.Steps.refl before.state)

/-- One bounded lexical discard constructs the actual projected source state
and retained target state from the same current cut and captured relations. -/
theorem discard_projected {base : CoreMachine.State}
    (cut : MappedOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data input captured capturedTarget outside outsideTarget)
    (carrier : DiscardCarrier graph owners base.heap environment handler owner binder)
    (resolved : scope.resolve binder = some ticket)
    (unprotected : ProtectionContexts.protectedMode capturedTarget.erase = false)
    (projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf captured) + 1)
      (framesOf captured) = .ok (closing,consumed))
    (nonempty : closing.isEmpty = false) :
    ∃ after,
      Related graph ⟨{ base with control := .discard handler owner, frames := framesOf whole },
        .eval ⟨.discard binder,scope,target⟩,owners,whole⟩ ∧
      CoreMachine.next graph { base with control := .discard handler owner, frames := framesOf whole } = .stepped after ∧
      LexicalUnwind.Transition (.eval ⟨.discard binder,scope,target⟩)
        (.unwind scope (capturedTarget.append (.push (.closing base.nextClose scope)
          (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))))
        [.close base.nextClose] [.ticket ticket] ∧
      Related graph ⟨after,.unwind scope (capturedTarget.append (.push (.closing base.nextClose scope)
        (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))),owners,
        front ++ (savedOwners,.clauseBoundary handler owner occurrence ticket none) :: outside⟩ := by
  obtain ⟨found,shape,header,current,frontRelated,capturedRelated,outsideRelated⟩ := cut.realizes
  let after : CoreMachine.State := { base with control := CoreMachine.Control.returned .unit, frames := closing ++ .closeCompletion base.nextClose :: (framesOf front ++ .clauseBoundary handler owner occurrence ticket none :: framesOf outside), nextClose := base.nextClose + 1, observations := base.observations ++ [.discarded ticket] ++ consumed ++ [.closeStarted base.nextClose] }
  refine ⟨after,.discard carrier rfl rfl current,?_,?_,?_⟩
  · simp [CoreMachine.next,CoreMachine.discardOwner,found,projection,nonempty,after]
  · rw [shape]
    exact .discard binder ticket base.nextClose scope data.scope input data.answer frontTarget capturedTarget outsideTarget resolved unprotected
  · exact .projected capturedRelated (frontRelated.append (.spent header outsideRelated)) projection nonempty rfl
      (by simp [after,framesOf,List.map_append]) rfl

#print axioms running_administration_decreases
#print axioms raw_without_close_ordinary
#print axioms raw_trace_lift
#print axioms Trace.append
#print axioms positive_lift
#print axioms link_lift
#print axioms chain_lift
#print axioms ordinary_step
#print axioms Link.endpoints
#print axioms Chain.core_steps
#print axioms discard_projected
end Ash.OneShot.CoreUnwindRelation
