import WorkerChannel
import DrainSafety

/-
A partial model of one-way completion. Conditional concrete finish results
and the draft finite solver are described in the correspondence. Solver
acceptance has not been proved to cover actual execution or grant release.
-/
namespace Ash.OneWayCompletion

open Ash.WorkerChannel

structure Key where
  activation : Nat
  lane : Worker
  side : Side
  deriving DecidableEq, Repr

/-- Exact dynamic operation and static result edge of a sealed End observation. -/
structure EndFact (count : Nat) where
  key : Key
  operation : Nat
  receiveSite : Fin count
  resultEdge : Fin count
  deriving DecidableEq

/-- A reply edge may change while the sealed event's identity remains fixed. -/
def EndFact.SameOrigin {count : Nat} (left right : EndFact count) : Prop :=
  left.key = right.key ∧ left.operation = right.operation ∧ left.receiveSite = right.receiveSite

structure EndEvent (count : Nat) where
  fact : EndFact count
  channel : Channel

def EndEvent.Genuine {count : Nat} (event : EndEvent count) : Prop :=
  event.fact.key.side = .read ∧ event.channel.failed = false ∧
    event.channel.sealed = true ∧ event.channel.queue = []

inductive ForwardKind where
  | alias | construct | project
  deriving DecidableEq, Repr

/-- The normalized caller, handler, owner and selected-evidence context. -/
structure StaticContext (count : Nat) where
  owner : Fin count
  side : Side
  caller : Fin count
  handler : Fin count
  cleanup : Fin count
  target : Fin count
  evidence : Fin count
  successor : Fin count
  deriving DecidableEq, Repr

/-- Nodes in the selected root's bounded capture/cleanup construction. -/
inductive CaptureOp where
  | stutter | cleanupMarker | nestedCapture | retain | callback | unknown
  deriving DecidableEq, Repr

/- Structural fields of a capture are constructed from its graph, not supplied as a safe bit. -/
namespace CapturePlan

def cleanup (ops : List CaptureOp) : RetainedControl.CleanupPhase :=
  if ops.any (fun op ↦ decide (op = .cleanupMarker)) then .armed else .finished

def nested (ops : List CaptureOp) : List RetainedControl.NestedPhase :=
  ops.filterMap fun op ↦ if op = .nestedCapture then some .live else none

def allowedNode : CaptureOp → Bool
  | .stutter | .cleanupMarker => true
  | .nestedCapture | .retain | .callback | .unknown => false

/-- One actual marker, no nested capture and no unverified capture operation. -/
def admitted (ops : List CaptureOp) : Bool :=
  decide (cleanup ops = .armed ∧ nested ops = [] ∧
    (ops.filter (fun op ↦ decide (op = .cleanupMarker))).length = 1) && ops.all allowedNode

/-- Dynamic support and owners remain concrete; graph nodes build the cleanup shape. -/
def build (ops : List CaptureOp) (entry : Entry) (template : RetainedControl.Capture) : RetainedControl.Capture :=
  { template with branch := entry.id, cleanup := cleanup ops, nested := nested ops }

theorem admitted_build_shape (ops : List CaptureOp) (entry : Entry) (template : RetainedControl.Capture)
    (accepted : admitted ops = true) :
    (build ops entry template).branch = entry.id ∧
      (build ops entry template).cleanup = .armed ∧ (build ops entry template).nested = [] := by
  simp only [admitted, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨rfl, accepted.1.1, accepted.1.2.1⟩

end CapturePlan

/-- Constructor identity is distinct from authentication of its origin. -/
inductive ResultCase where
  | endValue | otherValue | unknown
  deriving DecidableEq

/-- The modeled control graph; unsafe operations remain explicit. -/
inductive Node (count ports : Nat) where
  | receive (message empty endSuccess failedReply : Fin count) (payload : Fin ports)
  | call (target continuation : Fin count) (calleeContext : StaticContext count)
      (inputs : List (Fin ports × Fin ports)) (returnSource returnTarget : Fin ports)
  | forward (kind : ForwardKind) (operands : List (Fin ports)) (target : Fin ports) (next : Fin count)
  | branch (operands : List (Fin ports)) (yes no : Fin count)
  | dispatch (next : Fin count) (captureGraph : List CaptureOp)
  | processing (regionEntry next : Fin count)
  | endReply (next : Fin count) (target : Fin ports)
  | endResult (target : Fin ports) (next : Fin count)
  | otherResult (target : Fin ports) (next : Fin count)
  | matchEnd (source : Fin ports) (yes no : Fin count)
  | stop
  | finishReceive
  | returnNode (value : Fin ports)
  | unsupported

structure Frame (count ports : Nat) where
  key : Key
  callSite : Fin count
  target : Fin count
  continuation : Fin count
  callerContext : StaticContext count
  calleeContext : StaticContext count
  inputs : List (Fin ports × Fin ports)
  returnSource : Fin ports
  returnTarget : Fin ports
  callerDependencies : Vector Bool ports

/-- Work not represented by C1 slots remains explicit in the same-Store projection. -/
structure ExternalWork where
  callbacks : Bool
  cleanups : Bool
  captures : Bool
  other : Bool

/-- Dynamic delivery identity and the finite receive site that introduced it. -/
structure Delivery (count : Nat) where
  entry : Entry
  receiveSite : Fin count

inductive ReceiveInfo (count : Nat) where
  | none | message (operation edge : Fin count) | empty (operation edge : Fin count)
  deriving DecidableEq

structure Machine (count ports : Nat) where
  key : Key
  ownerSite : Fin count
  pc : Fin count
  context : StaticContext count
  frames : List (Frame count ports)
  fact : Option (EndFact count)
  pendingEnd : Option (EndFact count)
  receiveInfo : ReceiveInfo count
  network : Network
  currentDelivery : Option (Delivery count)
  external : ExternalWork
  tainted : Bool
  derived : Fin ports → Bool
  endValues : Fin ports → Bool
  resultCases : Fin ports → ResultCase
  driverReturn : Option (Fin count × Fin ports)
  driverSource : Option (Fin ports)
  events : List (EndEvent count)

/-- All listed operands are independent of the current message. -/
def Independent {ports : Nat} (derived : Fin ports → Bool) (operands : List (Fin ports)) : Prop :=
  ∀ port, port ∈ operands → derived port = false

/-- Call inputs read the caller snapshot simultaneously; only mapped formals are initialized. -/
def callInputs {ports : Nat} (inputs : List (Fin ports × Fin ports))
    (caller : Fin ports → Bool) (formal : Fin ports) : Bool :=
  inputs.any fun pair ↦ decide (pair.2 = formal) && caller pair.1

/-- Return assignment replaces the destination's stale origin with the callee result. -/
def returnInputs {ports : Nat} (caller : Vector Bool ports) (result : Bool)
    (target : Fin ports) (port : Fin ports) : Bool :=
  if port = target then result else caller[port]

/-- Only an exact alias transfers a known End-success value to another port. -/
def forwardEndValue {ports : Nat} (kind : ForwardKind) (operands : List (Fin ports))
    (target : Fin ports) (values : Fin ports → Bool) (port : Fin ports) : Bool :=
  if port = target then
    match kind, operands with
    | .alias, [source] => values source
    | _, _ => false
  else values port

/-- Only an exact alias preserves a known constructor. -/
def forwardResultCase {ports : Nat} (kind : ForwardKind) (operands : List (Fin ports))
    (target : Fin ports) (values : Fin ports → ResultCase) (port : Fin ports) : ResultCase :=
  if port = target then
    match kind, operands with
    | .alias, [source] => values source
    | _, _ => .unknown
  else values port

/-- An assignment invalidates permission when it overwrites the matched source. -/
def retainDriverSource {ports : Nat} (target : Fin ports)
    (source : Option (Fin ports)) : Option (Fin ports) :=
  match source with
  | some origin => if target = origin then none else some origin
  | none => none

/-- A constructor marks End-success only while this activation holds the actual End fact. -/
def hasCurrentEnd {count ports : Nat} (s : Machine count ports) : Bool :=
  match s.fact with
  | some fact => decide (fact.key = s.key)
  | none => false

/-- These are modeled control steps; the correspondence to linked Core is open. -/
inductive Step {count ports : Nat} (program : Fin count → Node count ports) :
    Machine count ports → Machine count ports → Prop where
  | receiveEnd (s : Machine count ports) (message empty endSuccess failedReply : Fin count) (payload : Fin ports) (operation : Nat)
      (node : program s.pc = .receive message empty endSuccess failedReply payload) (read : s.key.side = .read)
      (live : s.network.backing = true) (committed : s.network.committed = true)
      (current : s.network.operations operation = some ⟨s.key.lane, .read, s.key.lane.peer⟩)
      (running : s.network.returned s.key.lane.peer = false)
      (healthy : (s.network.channels s.key.lane).failed = false)
      (sealed : (s.network.channels s.key.lane).sealed = true)
      (emptyQueue : (s.network.channels s.key.lane).queue = []) :
      Step program s { s with
        pc := endSuccess
        driverSource := none
        driverReturn := none
        resultCases := fun _ ↦ .unknown
        endValues := fun _ ↦ false
        fact := none
        pendingEnd := some ⟨s.key, operation, s.pc, endSuccess⟩
        receiveInfo := .none
        network := s.network.advance s.key.lane
          { s.network.channels s.key.lane with observedEnd := true } operation
        events := ⟨⟨s.key, operation, s.pc, endSuccess⟩, s.network.channels s.key.lane⟩ :: s.events }
  | receiveMessage (s : Machine count ports) (message empty endSuccess failedReply : Fin count) (payload : Fin ports) (operation : Nat)
      (entry : Entry) (tail : List Entry)
      (node : program s.pc = .receive message empty endSuccess failedReply payload) (read : s.key.side = .read)
      (live : s.network.backing = true) (committed : s.network.committed = true)
      (current : s.network.operations operation = some ⟨s.key.lane, .read, s.key.lane.peer⟩)
      (running : s.network.returned s.key.lane.peer = false)
      (healthy : (s.network.channels s.key.lane).failed = false)
      (head : (s.network.channels s.key.lane).queue = entry :: tail) :
      Step program s { s with
        pc := message
        driverSource := none
        driverReturn := none
        resultCases := fun _ ↦ .unknown
        endValues := fun _ ↦ false
        fact := none
        pendingEnd := none
        receiveInfo := .message s.pc message
        currentDelivery := some ⟨entry, s.pc⟩
        derived := fun port ↦ if port = payload then true else s.derived port
        network := s.network.advance s.key.lane
          { s.network.channels s.key.lane with
            received := (s.network.channels s.key.lane).received ++ [entry]
            queue := tail
            held := (s.network.channels s.key.lane).held ++ [entry] } operation }
  | receiveEmpty (s : Machine count ports) (message empty endSuccess failedReply : Fin count) (payload : Fin ports) (operation : Nat)
      (node : program s.pc = .receive message empty endSuccess failedReply payload) (read : s.key.side = .read)
      (live : s.network.backing = true) (committed : s.network.committed = true)
      (current : s.network.operations operation = some ⟨s.key.lane, .read, s.key.lane.peer⟩)
      (running : s.network.returned s.key.lane.peer = false)
      (healthy : (s.network.channels s.key.lane).failed = false)
      (unsealed : (s.network.channels s.key.lane).sealed = false)
      (emptyQueue : (s.network.channels s.key.lane).queue = []) :
      Step program s { s with
        pc := empty
        driverSource := none
        driverReturn := none
        resultCases := fun _ ↦ .unknown
        endValues := fun _ ↦ false
        fact := none
        pendingEnd := none
        receiveInfo := .empty s.pc empty
        network := s.network.advance s.key.lane (s.network.channels s.key.lane) operation }
  /-- A successfully constructed ReceiveFailed reply forgets success facts.
      Failed reply construction is represented separately by failure transitions. -/
  | receiveFailed (s : Machine count ports) (message empty endSuccess failedReply : Fin count)
      (payload : Fin ports) (operation : Nat)
      (node : program s.pc = .receive message empty endSuccess failedReply payload) (read : s.key.side = .read)
      (noOperation : s.network.operations operation = none) :
      Step program s { s with
        pc := failedReply
        fact := none
        pendingEnd := none
        receiveInfo := .none
        driverSource := none
        driverReturn := none
        endValues := fun _ ↦ false
        resultCases := fun _ ↦ .unknown }
  /-- Refusal of an acquired operation consumes that exact token on an idle channel. -/
  | receiveFailedToken (s : Machine count ports) (message empty endSuccess failedReply : Fin count)
      (payload : Fin ports) (operation : Nat)
      (node : program s.pc = .receive message empty endSuccess failedReply payload) (read : s.key.side = .read)
      (live : s.network.backing = true) (committed : s.network.committed = true)
      (current : s.network.operations operation = some ⟨s.key.lane, .read, s.key.lane.peer⟩)
      (running : s.network.returned s.key.lane.peer = false) :
      Step program s { s with
        pc := failedReply
        fact := none
        pendingEnd := none
        receiveInfo := .none
        driverSource := none
        driverReturn := none
        endValues := fun _ ↦ false
        resultCases := fun _ ↦ .unknown
        network := s.network.advance s.key.lane (s.network.channels s.key.lane) operation }
  | call (s : Machine count ports) (target continuation : Fin count) (calleeContext : StaticContext count)
      (inputs : List (Fin ports × Fin ports)) (returnSource returnTarget : Fin ports)
      (node : program s.pc = .call target continuation calleeContext inputs returnSource returnTarget) :
      Step program s { s with
        pc := target
        driverSource := none
        driverReturn := none
        resultCases := fun _ ↦ .unknown
        context := calleeContext
        fact := none
        receiveInfo := .none
        endValues := fun _ ↦ false
        derived := callInputs inputs s.derived
        frames := ⟨s.key, s.pc, target, continuation, s.context, calleeContext, inputs, returnSource, returnTarget, Vector.ofFn s.derived⟩ :: s.frames }
  | forward (s : Machine count ports) (kind : ForwardKind) (operands : List (Fin ports))
      (target : Fin ports) (next : Fin count) (node : program s.pc = .forward kind operands target next) :
      Step program s { s with
        pc := next
        derived := fun port ↦ if port = target then operands.any s.derived || s.derived port else s.derived port
        endValues := forwardEndValue kind operands target s.endValues
        resultCases := forwardResultCase kind operands target s.resultCases
        driverReturn := none
        driverSource := retainDriverSource target s.driverSource }
  | branchYes (s : Machine count ports) (operands : List (Fin ports)) (yes no : Fin count)
      (node : program s.pc = .branch operands yes no) :
      Step program s { s with pc := yes, driverSource := none, driverReturn := none }
  | branchNo (s : Machine count ports) (operands : List (Fin ports)) (yes no : Fin count)
      (node : program s.pc = .branch operands yes no) :
      Step program s { s with pc := no, driverSource := none, driverReturn := none }
  | endReply (s : Machine count ports) (next : Fin count) (target : Fin ports) (fact : EndFact count)
      (node : program s.pc = .endReply next target) (pending : s.pendingEnd = some fact)
      (same : fact.key = s.key) :
      Step program s { s with
        pc := next
        driverSource := none
        driverReturn := none
        resultCases := fun _ ↦ .unknown
        fact := some { fact with resultEdge := next }
        pendingEnd := none
        receiveInfo := .none
        derived := fun port ↦ if port = target then false else s.derived port
        endValues := fun _ ↦ false }
  | endResult (s : Machine count ports) (target : Fin ports) (next : Fin count)
      (node : program s.pc = .endResult target next) :
      Step program s { s with
        pc := next
        derived := fun port ↦ if port = target then false else s.derived port
        endValues := fun port ↦ if port = target then hasCurrentEnd s else s.endValues port
        resultCases := fun port ↦ if port = target then .endValue else s.resultCases port
        driverReturn := none
        driverSource := none }
  | otherResult (s : Machine count ports) (target : Fin ports) (next : Fin count)
      (node : program s.pc = .otherResult target next) :
      Step program s { s with
        pc := next
        derived := fun port ↦ if port = target then false else s.derived port
        endValues := fun port ↦ if port = target then false else s.endValues port
        resultCases := fun port ↦ if port = target then .otherValue else s.resultCases port
        driverReturn := none
        driverSource := none }
  | matchEndYes (s : Machine count ports) (source : Fin ports) (yes no : Fin count) (fact : EndFact count)
      (node : program s.pc = .matchEnd source yes no) (value : s.endValues source = true)
      (actual : s.resultCases source = .endValue)
      (authentic : s.fact = some fact) (same : fact.key = s.key) (outer : s.frames = [])
      (returned : s.driverReturn = some (s.pc, source)) :
      Step program s { s with pc := yes, driverReturn := none, driverSource := some source }
  | matchEndNo (s : Machine count ports) (source : Fin ports) (yes no : Fin count)
      (node : program s.pc = .matchEnd source yes no)
      (notEnd : s.resultCases source ≠ .endValue) :
      Step program s { s with
        pc := no
        fact := none
        pendingEnd := none
        receiveInfo := .none
        driverReturn := none
        driverSource := none }
  | matchEndUnverified (s : Machine count ports) (source : Fin ports) (yes no : Fin count)
      (node : program s.pc = .matchEnd source yes no)
      (possibleEnd : s.resultCases source ≠ .otherValue)
      (unverified : ¬ (s.resultCases source = .endValue ∧ s.endValues source = true ∧
        (∃ origin, s.fact = some origin ∧ origin.key = s.key) ∧ s.frames = [] ∧
        s.driverReturn = some (s.pc, source))) :
      Step program s { s with
        pc := yes
        fact := none
        receiveInfo := .none
        driverReturn := none
        driverSource := none
        tainted := true }
  | matchedReturn (s : Machine count ports) (frame : Frame count ports) (rest : List (Frame count ports))
      (node : program s.pc = .returnNode frame.returnSource) (stack : s.frames = frame :: rest)
      (same : frame.key = s.key) (context : frame.calleeContext = s.context)
      (fact : EndFact count) (authentic : s.fact = some fact) (owner : fact.key = s.key) :
      Step program s { s with
        pc := frame.continuation
        driverSource := none
        context := frame.callerContext
        frames := rest
        derived := returnInputs frame.callerDependencies (s.derived frame.returnSource) frame.returnTarget
        endValues := fun port ↦ if port = frame.returnTarget then s.endValues frame.returnSource else false
        resultCases := fun port ↦ if port = frame.returnTarget then s.resultCases frame.returnSource else .unknown
        driverReturn := if rest.isEmpty then some (frame.continuation, frame.returnTarget) else none }
  | normalReturn (s : Machine count ports) (frame : Frame count ports) (rest : List (Frame count ports))
      (node : program s.pc = .returnNode frame.returnSource) (stack : s.frames = frame :: rest)
      (same : frame.key = s.key) (context : frame.calleeContext = s.context)
      (noFact : s.fact = none) (noPending : s.pendingEnd = none) :
      Step program s { s with
        pc := frame.continuation
        driverSource := none
        context := frame.callerContext
        frames := rest
        fact := none
        pendingEnd := none
        receiveInfo := .none
        derived := returnInputs frame.callerDependencies (s.derived frame.returnSource) frame.returnTarget
        endValues := fun _ ↦ false
        resultCases := fun port ↦ if port = frame.returnTarget then s.resultCases frame.returnSource else .unknown
        driverReturn := if rest.isEmpty then some (frame.continuation, frame.returnTarget) else none }
  | otherReturn (s : Machine count ports) (frame : Frame count ports) (rest : List (Frame count ports))
      (value : Fin ports) (node : program s.pc = .returnNode value) (stack : s.frames = frame :: rest)
      (unmatched : (∃ fact, s.fact = some fact ∧ fact.key ≠ s.key) ∨ s.pendingEnd ≠ none ∨
        frame.key ≠ s.key ∨ frame.calleeContext ≠ s.context ∨ value ≠ frame.returnSource) :
      Step program s { s with
        pc := frame.continuation
        driverSource := none
        driverReturn := none
        context := frame.callerContext
        frames := rest
        fact := none
        receiveInfo := .none
        tainted := true }
  | failure (s : Machine count ports) (live : s.network.backing = true) :
      Step program s { s with network := s.network.fail, fact := none, pendingEnd := none, receiveInfo := .none, driverSource := none, driverReturn := none, tainted := true }
  | invalidate (s : Machine count ports) (next : Fin count)
      (node : program s.pc = .unsupported) :
      Step program s { s with pc := next, fact := none, pendingEnd := none, receiveInfo := .none, driverSource := none, driverReturn := none, tainted := true }

/-- Each retained fact names an event that was genuine at the moment observed. -/
def Authenticated {count ports : Nat} (s : Machine count ports) : Prop :=
  (∀ event, event ∈ s.events → event.Genuine) ∧
  (∀ fact, s.fact = some fact → ∃ event, event ∈ s.events ∧ event.fact.SameOrigin fact) ∧
  (∀ fact, s.pendingEnd = some fact → ∃ event, event ∈ s.events ∧ event.fact = fact)

theorem receive_end_is_channel_step (c : Channel)
    (healthy : c.failed = false) (sealed : c.sealed = true) (empty : c.queue = []) :
    ChannelStep .read c { c with observedEnd := true } :=
  ChannelStep.observeEnd c healthy sealed empty

theorem step_preserves_authentication {count ports : Nat}
    {program : Fin count → Node count ports} {before after : Machine count ports}
    (valid : Authenticated before) (step : Step program before after) : Authenticated after := by
  rcases valid with ⟨eventsValid, factValid, pendingValid⟩
  cases step with
  | receiveEnd message empty endSuccess failedReply payload operation node read live committed current running healthy sealed emptyQueue =>
      constructor
      · intro event member
        simp only [List.mem_cons] at member
        rcases member with same | old
        · subst event
          exact ⟨read, healthy, sealed, emptyQueue⟩
        · exact eventsValid event old
      constructor
      · intro fact impossible; contradiction
      · intro fact present
        have same : fact = ⟨before.key, operation, before.pc, endSuccess⟩ := by simpa using present.symm
        subst fact
        exact ⟨⟨⟨before.key, operation, before.pc, endSuccess⟩,
          before.network.channels before.key.lane⟩, by simp, rfl⟩
  | receiveMessage =>
      refine ⟨eventsValid, ?_, ?_⟩ <;> intro fact impossible <;> contradiction
  | receiveEmpty | receiveFailed | receiveFailedToken =>
      refine ⟨eventsValid, ?_, ?_⟩ <;> intro fact impossible <;> contradiction
  | call =>
      refine ⟨eventsValid, ?_, pendingValid⟩
      intro fact impossible; contradiction
  | forward => exact ⟨eventsValid, factValid, pendingValid⟩
  | branchYes => exact ⟨eventsValid, factValid, pendingValid⟩
  | branchNo => exact ⟨eventsValid, factValid, pendingValid⟩
  | endReply next target fact node pending same =>
      refine ⟨eventsValid, ?_, ?_⟩
      · intro result present
        have equal : result = { fact with resultEdge := next } := by simpa using present.symm
        subst result
        obtain ⟨event, member, sameEvent⟩ := pendingValid fact pending
        refine ⟨event, member, ?_⟩
        simp [EndFact.SameOrigin, sameEvent]
      · intro result impossible; contradiction
  | endResult | otherResult | matchEndYes | matchedReturn => exact ⟨eventsValid, factValid, pendingValid⟩
  | matchEndNo | normalReturn =>
      refine ⟨eventsValid, ?_, ?_⟩ <;> intro fact impossible <;> contradiction
  | matchEndUnverified =>
      refine ⟨eventsValid, ?_, pendingValid⟩
      intro fact impossible; contradiction
  | otherReturn =>
      refine ⟨eventsValid, ?_, pendingValid⟩
      intro fact impossible; contradiction
  | failure =>
      refine ⟨eventsValid, ?_, ?_⟩ <;> intro fact impossible <;> contradiction
  | invalidate =>
      refine ⟨eventsValid, ?_, ?_⟩ <;> intro fact impossible <;> contradiction

inductive Trace {count ports : Nat} (program : Fin count → Node count ports) :
    Machine count ports → Machine count ports → Prop where
  | initial (s) : Trace program s s
  | next {first middle last} : Trace program first middle → Step program middle last →
      Trace program first last

theorem trace_preserves_authentication {count ports : Nat}
    {program : Fin count → Node count ports} {first last : Machine count ports}
    (valid : Authenticated first) (trace : Trace program first last) : Authenticated last := by
  induction trace with
  | initial => exact valid
  | next _ step ih => exact step_preserves_authentication ih step


/-- Frames come from the actual modeled call node, not a matching function name. -/
def FramesMatch {count ports : Nat} (program : Fin count → Node count ports)
    (s : Machine count ports) : Prop :=
  ∀ frame, frame ∈ s.frames → frame.key = s.key ∧
    program frame.callSite = .call frame.target frame.continuation frame.calleeContext frame.inputs frame.returnSource frame.returnTarget

theorem step_preserves_frames {count ports : Nat} {program : Fin count → Node count ports}
    {before after : Machine count ports} (valid : FramesMatch program before)
    (step : Step program before after) : FramesMatch program after := by
  cases step with
  | receiveEnd => exact valid
  | receiveMessage => exact valid
  | receiveEmpty | receiveFailed | receiveFailedToken => exact valid
  | call target continuation calleeContext inputs returnSource returnTarget node =>
      intro frame member
      simp only [List.mem_cons] at member
      rcases member with same | old
      · subst frame
        exact ⟨rfl, node⟩
      · exact valid frame old
  | forward => exact valid
  | branchYes => exact valid
  | branchNo => exact valid
  | endReply | endResult | otherResult | matchEndYes | matchEndNo | matchEndUnverified => exact valid
  | matchedReturn frame rest node stack same context fact authentic owner =>
      intro current member
      apply valid current
      rw [stack]
      exact List.mem_cons_of_mem frame member
  | normalReturn frame rest node stack same context noFact noPending =>
      intro current member
      apply valid current
      rw [stack]
      exact List.mem_cons_of_mem frame member
  | otherReturn frame rest value node stack unmatched =>
      intro current member
      apply valid current
      rw [stack]
      exact List.mem_cons_of_mem frame member
  | failure => exact valid
  | invalidate => exact valid

theorem trace_preserves_frames {count ports : Nat} {program : Fin count → Node count ports}
    {first last : Machine count ports} (valid : FramesMatch program first)
    (trace : Trace program first last) : FramesMatch program last := by
  induction trace with
  | initial => exact valid
  | next _ step ih => exact step_preserves_frames ih step

theorem empty_seed_frames {count ports : Nat} (program : Fin count → Node count ports)
    (s : Machine count ports) (empty : s.frames = []) : FramesMatch program s := by
  intro frame member
  simp [empty] at member

theorem returned_frame_has_matching_call {count ports : Nat}
    {program : Fin count → Node count ports} {first last : Machine count ports}
    (empty : first.frames = []) (trace : Trace program first last)
    (frame : Frame count ports) (rest : List (Frame count ports)) (stack : last.frames = frame :: rest) :
    frame.key = last.key ∧ program frame.callSite = .call frame.target frame.continuation frame.calleeContext frame.inputs frame.returnSource frame.returnTarget := by
  have valid := trace_preserves_frames (empty_seed_frames program first empty) trace
  apply valid frame
  rw [stack]
  simp

theorem empty_seed_authenticated {count ports : Nat} (s : Machine count ports)
    (noFact : s.fact = none) (noPending : s.pendingEnd = none) (noEvents : s.events = []) : Authenticated s := by
  refine ⟨?_, ?_, ?_⟩
  · intro event member
    simp [noEvents] at member
  · intro fact present
    rw [noFact] at present
    contradiction
  · intro fact present
    rw [noPending] at present
    contradiction

theorem returned_fact_has_genuine_event {count ports : Nat}
    {program : Fin count → Node count ports} {first last : Machine count ports}
    (noFact : first.fact = none) (noPending : first.pendingEnd = none) (noEvents : first.events = [])
    (trace : Trace program first last) (fact : EndFact count) (present : last.fact = some fact)
    (owner : fact.key = last.key) :
    ∃ event, event ∈ last.events ∧ event.fact.SameOrigin fact ∧
      event.fact.key = last.key ∧ event.Genuine := by
  have valid := trace_preserves_authentication (empty_seed_authenticated first noFact noPending noEvents) trace
  obtain ⟨event, member, same⟩ := valid.2.1 fact present
  exact ⟨event, member, same, same.1.trans owner, valid.1 event member⟩

/-
The following summary algebra is independent of any product worklist. A base
is a modeled normal-return edge; wrapping represents a matched call and return.
Actual successor enumeration and revision replay remain correspondence work.
-/
namespace Summary

abbrev Pair (count : Nat) := Fin count × Fin count

def Approx {count : Nat} (base : Pair count → Prop)
    (wrap : Pair count → Pair count → Prop) : Nat → Pair count → Prop
  | 0 => fun _ ↦ False
  | n + 1 => fun pair ↦ Approx base wrap n pair ∨ base pair ∨
      ∃ inner, Approx base wrap n inner ∧ wrap inner pair

theorem approx_mono {count : Nat} {base : Pair count → Prop}
    {wrap : Pair count → Pair count → Prop} {n m : Nat} (order : n ≤ m) :
    ∀ pair, Approx base wrap n pair → Approx base wrap m pair := by
  induction order with
  | refl => intro pair present; exact present
  | @step m order ih =>
      intro pair present
      exact Or.inl (ih pair present)

theorem finite_converges {count : Nat} (base : Pair count → Prop)
    (wrap : Pair count → Pair count → Prop) :
    ∃ n, ∀ pair, Approx base wrap (n + 1) pair → Approx base wrap n pair := by
  let pairs : List (Pair count) := (List.finRange count).flatMap fun entry ↦
    (List.finRange count).map fun result ↦ (entry, result)
  obtain ⟨n, bound⟩ := Ash.RetainedControl.PortCases.Worklist.finite_union_bounded pairs
    (Approx base wrap) (by
      intro n m order pair present
      exact approx_mono order pair present)
  refine ⟨n, ?_⟩
  intro pair present
  apply bound pair
  · rcases pair with ⟨entry, result⟩
    simp [pairs, List.mem_finRange]
  · exact ⟨n + 1, present⟩

theorem no_base_no_returns {count : Nat} {base : Pair count → Prop}
    {wrap : Pair count → Pair count → Prop} (empty : ∀ pair, ¬ base pair) :
    ∀ n pair, ¬ Approx base wrap n pair := by
  intro n
  induction n with
  | zero => intro pair present; exact present
  | succ n ih =>
      intro pair present
      rcases present with prior | initial | ⟨inner, previous, _⟩
      · exact ih pair prior
      · exact empty pair initial
      · exact ih inner previous

/-- Any relation closed under the actual base and matching wraps contains the iteration. -/
theorem least {count : Nat} {base : Pair count → Prop}
    {wrap : Pair count → Pair count → Prop} (closed : Pair count → Prop)
    (hasBase : ∀ pair, base pair → closed pair)
    (hasWrap : ∀ inner outer, closed inner → wrap inner outer → closed outer) :
    ∀ n pair, Approx base wrap n pair → closed pair := by
  intro n
  induction n with
  | zero => intro pair impossible; exact False.elim impossible
  | succ n ih =>
      intro pair present
      rcases present with prior | initial | ⟨inner, previous, matching⟩
      · exact ih pair prior
      · exact hasBase pair initial
      · exact hasWrap inner pair (ih inner previous) matching

end Summary



namespace Analysis

abbrev Context := StaticContext

inductive Fact (count : Nat) where
  | none | invalid | message (operation edge : Fin count) | empty (operation edge : Fin count)
  | endPending (operation edge : Fin count) | endFact (operation edge : Fin count)
  deriving DecidableEq

/-- The symbolic root is an analysis site, not a runtime delivery identity. -/
inductive Phase (count : Nat) where
  | clear | processing (root : Fin count) | pending | unknown
  deriving DecidableEq

/-- Selected actual C1 root, kept separate from the symbolic delivery phase. -/
inductive RootFact (count : Nat) where
  | idle | selected (site : Fin count) | invalid | unknown
  deriving DecidableEq

structure State (count ports : Nat) where
  context : Context count
  ownerSite : Fin count
  side : Side
  control : Fin count
  fact : Fact count
  phase : Phase count
  root : RootFact count
  work : RetainedControl.PortCases.Work
  escape : Bool
  tainted : Bool
  terminal : Bool
  pending : Bool
  compatible : Bool
  dependencies : Vector Bool ports
  endValues : Vector Bool ports
  resultCases : Vector ResultCase ports
  driverReturn : Option (Fin count × Fin ports)
  driverSource : Option (Fin ports)
  frameSites : Vector Bool count
  innerSites : Vector Bool count
  outerReturns : Vector (Vector Bool ports) count
  frameDependencies : Vector (Vector Bool ports) count
  frameLive : Vector Bool ports
  frameReturns : Vector (Vector (Vector Bool ports) ports) count
  framesValid : Bool
  suffixSafe : Bool
  deriving DecidableEq

/-- Only equal full contexts can merge; disagreements lose rather than mint facts. -/
def join {count ports : Nat} (left right : State count ports) : Option (State count ports) :=
  if left.context = right.context ∧ left.control = right.control ∧
      left.ownerSite = right.ownerSite ∧ left.side = right.side then
    some {
      context := left.context
      ownerSite := left.ownerSite
      side := left.side
      control := left.control
      fact := if left.fact = right.fact then left.fact else .none
      phase := if left.phase = right.phase then left.phase else .unknown
      root := if left.root = right.root then left.root else .unknown
      work := if left.work = right.work then left.work else .unknown
      escape := left.escape || right.escape
      tainted := left.tainted || right.tainted
      terminal := left.terminal || right.terminal
      pending := left.pending || right.pending
      compatible := left.compatible && right.compatible
      dependencies := Vector.ofFn fun port ↦ left.dependencies[port] || right.dependencies[port]
      endValues := Vector.ofFn fun port ↦ left.endValues[port] && right.endValues[port]
      resultCases := Vector.ofFn fun port ↦
        if left.resultCases[port] = right.resultCases[port] then left.resultCases[port] else .unknown
      driverReturn := if left.driverReturn = right.driverReturn then left.driverReturn else none
      driverSource := if left.driverSource = right.driverSource then left.driverSource else none
      frameSites := Vector.ofFn fun site ↦ left.frameSites[site] || right.frameSites[site]
      innerSites := Vector.ofFn fun site ↦ left.innerSites[site] || right.innerSites[site]
      outerReturns := Vector.ofFn fun site ↦ Vector.ofFn fun port ↦
        left.outerReturns[site][port] || right.outerReturns[site][port]
      frameDependencies := Vector.ofFn fun site ↦ Vector.ofFn fun port ↦
        left.frameDependencies[site][port] || right.frameDependencies[site][port]
      frameLive := Vector.ofFn fun port ↦ left.frameLive[port] || right.frameLive[port]
      frameReturns := Vector.ofFn fun site ↦ Vector.ofFn fun target ↦ Vector.ofFn fun source ↦
        left.frameReturns[site][target][source] || right.frameReturns[site][target][source]
      framesValid := left.framesValid && right.framesValid
      suffixSafe := left.suffixSafe && right.suffixSafe }
  else none

/-- An End surviving a join came from both matching full predecessors. -/
theorem join_end_from_both {count ports : Nat} (left right result : State count ports)
    (operation edge : Fin count) (joined : join left right = some result)
    (ended : result.fact = .endFact operation edge) :
    left.context = right.context ∧ left.fact = .endFact operation edge ∧
      right.fact = .endFact operation edge := by
  unfold join at joined
  split at joined
  next sameContext =>
    simp only [Option.some.injEq] at joined
    subst result
    split at ended
    next sameFact => exact ⟨sameContext.1, ended, sameFact.symm.trans ended⟩
    next different => contradiction
  next different => contradiction

/-- A context mismatch cannot merge even if its projected work happens to match. -/
theorem join_context_mismatch {count ports : Nat} (left right : State count ports)
    (different : left.context ≠ right.context) : join left right = none := by
  simp [join, different]

/-- Every message-derived site in either predecessor survives the union. -/
theorem join_dependency_from_left {count ports : Nat} (left right result : State count ports)
    (port : Fin ports) (joined : join left right = some result)
    (dependent : left.dependencies[port] = true) : result.dependencies[port] = true := by
  unfold join at joined
  split at joined
  next same =>
    simp only [Option.some.injEq] at joined
    subst result
    change (Vector.ofFn (fun p ↦ left.dependencies[p] || right.dependencies[p]))[port.val]'port.isLt = true
    simp only [Vector.getElem_ofFn, Bool.or_eq_true]
    exact Or.inl dependent
  next different => contradiction

theorem join_dependency_from_right {count ports : Nat} (left right result : State count ports)
    (port : Fin ports) (joined : join left right = some result)
    (dependent : right.dependencies[port] = true) : result.dependencies[port] = true := by
  unfold join at joined
  split at joined
  next same =>
    simp only [Option.some.injEq] at joined
    subst result
    change (Vector.ofFn (fun p ↦ left.dependencies[p] || right.dependencies[p]))[port.val]'port.isLt = true
    simp only [Vector.getElem_ofFn, Bool.or_eq_true]
    exact Or.inr dependent
  next different => contradiction


/-- Join every reachable normal predecessor; no predecessor supplies no fact. -/
def joinFrom {count ports : Nat} (seed : State count ports) :
    List (State count ports) → Option (State count ports)
  | [] => some seed
  | next :: rest => (join seed next).bind fun combined ↦ joinFrom combined rest

def joinAll {count ports : Nat} : List (State count ports) → Option (State count ports)
  | [] => none
  | first :: rest => joinFrom first rest

theorem joinFrom_end_all {count ports : Nat} (seed result : State count ports)
    (predecessors : List (State count ports)) (operation edge : Fin count)
    (joined : joinFrom seed predecessors = some result)
    (ended : result.fact = .endFact operation edge) :
    seed.fact = .endFact operation edge ∧
      ∀ predecessor, predecessor ∈ predecessors → predecessor.fact = .endFact operation edge := by
  induction predecessors generalizing seed with
  | nil =>
      simp [joinFrom] at joined
      subst result
      exact ⟨ended, by simp⟩
  | cons next rest ih =>
      cases merged : join seed next with
      | none => simp [joinFrom, merged] at joined
      | some combined =>
          have remainder : joinFrom combined rest = some result := by simpa [joinFrom, merged] using joined
          obtain ⟨combinedEnd, restEnd⟩ := ih combined remainder
          obtain ⟨_, seedEnd, nextEnd⟩ := join_end_from_both seed next combined operation edge merged combinedEnd
          refine ⟨seedEnd, ?_⟩
          intro predecessor member
          rcases List.mem_cons.mp member with same | member
          · subst predecessor; exact nextEnd
          · exact restEnd predecessor member

theorem joinAll_end_all {count ports : Nat} (predecessors : List (State count ports))
    (result : State count ports) (operation edge : Fin count)
    (joined : joinAll predecessors = some result) (ended : result.fact = .endFact operation edge) :
    ∀ predecessor, predecessor ∈ predecessors → predecessor.fact = .endFact operation edge := by
  cases predecessors with
  | nil => simp [joinAll] at joined
  | cons first rest =>
      have combined := joinFrom_end_all first result rest operation edge (by simpa [joinAll] using joined) ended
      intro predecessor member
      rcases List.mem_cons.mp member with same | member
      · subst predecessor; exact combined.1
      · exact combined.2 predecessor member

end Analysis

namespace Suffix

/-- Unsupported work is explicitly represented and cannot pass the checker. -/
inductive Forbidden where
  | allocate | provider | effect | arbitraryCall | mutableAccess | endpoint | callback | cleanup
  | savedContinuation | unknown
  deriving DecidableEq, Repr

inductive Node (count ports : Nat) where
  | returnNode (value : Fin ports)
  | forward (kind : ForwardKind) (operands : List (Fin ports)) (target : Fin ports) (next : Fin count)
  | branch (operands : List (Fin ports)) (yes no : Fin count)
  | forbidden (kind : Forbidden)

/-- Finite fuel bounds the graph query; failure or a cycle cannot mint a fact. -/
def check {count ports : Nat} (program : Fin count → Node count ports)
    (derived : Fin ports → Bool) : Nat → Fin count → Bool
  | 0, _ => false
  | fuel + 1, pc =>
      match program pc with
      | .returnNode value => !(derived value)
      | .forward _ operands _ next =>
          operands.all (fun port ↦ !(derived port)) && check program derived fuel next
      | .branch operands yes no =>
          operands.all (fun port ↦ !(derived port)) &&
            check program derived fuel yes && check program derived fuel no
      | .forbidden _ => false

/-- A suffix accepted with a conservative dependency superset is safe for a subset. -/
theorem check_dependency_subset {count ports : Nat} (program : Fin count → Node count ports)
    (smaller larger : Fin ports → Bool)
    (subset : ∀ port, smaller port = true → larger port = true) :
    ∀ fuel pc, check program larger fuel pc = true → check program smaller fuel pc = true := by
  intro fuel
  induction fuel with
  | zero => intro pc accepted; simp [check] at accepted
  | succ fuel ih =>
      intro pc accepted
      cases node : program pc with
      | returnNode value =>
          simp only [check, node] at accepted ⊢
          cases h : smaller value with
          | false => rfl
          | true =>
              have largerTrue := subset value h
              simp [largerTrue] at accepted
      | forward kind operands target next =>
          simp only [check, node, Bool.and_eq_true] at accepted ⊢
          refine ⟨?_, ih next accepted.2⟩
          apply List.all_eq_true.mpr
          intro port member
          have largerFalse := (List.all_eq_true.mp accepted.1) port member
          cases h : smaller port with
          | false => simp
          | true =>
              have largerTrue := subset port h
              simp [largerTrue] at largerFalse
      | branch operands yes no =>
          simp only [check, node, Bool.and_eq_true, and_assoc] at accepted ⊢
          refine ⟨?_, ih yes accepted.2.1, ih no accepted.2.2⟩
          apply List.all_eq_true.mpr
          intro port member
          have largerFalse := (List.all_eq_true.mp accepted.1) port member
          cases h : smaller port with
          | false => simp
          | true =>
              have largerTrue := subset port h
              simp [largerTrue] at largerFalse
      | forbidden kind => simp [check, node] at accepted

theorem checked_forward {count ports : Nat} (program : Fin count → Node count ports)
    (derived : Fin ports → Bool) (fuel : Nat) (pc next : Fin count)
    (kind : ForwardKind) (operands : List (Fin ports)) (target : Fin ports)
    (node : program pc = .forward kind operands target next)
    (accepted : check program derived (fuel + 1) pc = true) :
    operands.all (fun port ↦ !(derived port)) = true ∧
      check program derived fuel next = true := by
  simpa [check, node, Bool.and_eq_true] using accepted

theorem checked_branch {count ports : Nat} (program : Fin count → Node count ports)
    (derived : Fin ports → Bool) (fuel : Nat) (pc yes no : Fin count)
    (operands : List (Fin ports)) (node : program pc = .branch operands yes no)
    (accepted : check program derived (fuel + 1) pc = true) :
    operands.all (fun port ↦ !(derived port)) = true ∧
      check program derived fuel yes = true ∧ check program derived fuel no = true := by
  simpa [check, node, Bool.and_eq_true, and_assoc] using accepted

theorem forbidden_rejected {count ports : Nat} (program : Fin count → Node count ports)
    (derived : Fin ports → Bool) (fuel : Nat) (pc : Fin count) (kind : Forbidden)
    (node : program pc = .forbidden kind) : check program derived fuel pc = false := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [check, node]

theorem dependent_forward_rejected {count ports : Nat} (program : Fin count → Node count ports)
    (derived : Fin ports → Bool) (fuel : Nat) (pc next : Fin count) (kind : ForwardKind)
    (operands : List (Fin ports)) (port target : Fin ports)
    (node : program pc = .forward kind operands target next) (member : port ∈ operands)
    (dependent : derived port = true) : check program derived fuel pc = false := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have notAll : operands.all (fun p ↦ !(derived p)) = false := by
        apply List.all_eq_false.mpr
        exact ⟨port, member, by simp [dependent]⟩
      simp [check, node, notAll]

/-- Every older frame is checked under the current message dependencies. -/
def checkFrames {count ports : Nat} (program : Fin count → Node count ports)
    (derived : Fin ports → Bool) (fuel : Nat) (frames : List (Fin count)) : Bool :=
  frames.all (check program derived fuel)

theorem checked_older_frame {count ports : Nat} (program : Fin count → Node count ports)
    (derived : Fin ports → Bool) (fuel : Nat) (frames : List (Fin count)) (pc : Fin count)
    (checked : checkFrames program derived fuel frames = true) (member : pc ∈ frames) :
    check program derived fuel pc = true := by
  exact (List.all_eq_true.mp checked) pc member


/-- The checked suffix list is taken from each actual modeled caller frame. -/
theorem checked_caller_frame {count ports : Nat} (program : Fin count → Node count ports)
    (derived : Fin ports → Bool) (fuel : Nat) (frames : List (Frame count ports))
    (frame : Frame count ports) (member : frame ∈ frames)
    (checked : checkFrames program derived fuel (frames.map Frame.continuation) = true) :
    check program derived fuel frame.continuation = true := by
  apply checked_older_frame program derived fuel (frames.map Frame.continuation)
    frame.continuation checked
  exact List.mem_map_of_mem member


/-- The suffix checker and machine use the same actual modeled Core nodes. -/
def machineProgram {count ports : Nat} (program : Fin count → Node count ports) :
    Fin count → Ash.OneWayCompletion.Node count ports := fun pc ↦
  match program pc with
  | .returnNode value => .returnNode value
  | .forward kind operands target next => .forward kind operands target next
  | .branch operands yes no => .branch operands yes no
  | .forbidden _ => .unsupported

/-- Project actual control nodes to the permitted allocation-free suffix language. -/
def fromCalls {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports) :
    Fin count → Node count ports := fun pc ↦
  match calls pc with
  | .returnNode value => .returnNode value
  | .forward kind operands target next => .forward kind operands target next
  | .branch operands yes no => .branch operands yes no
  | _ => .forbidden .unknown

/-- No suffix node can invent an End fact, even across unsupported successors. -/
theorem step_fact_origin {count ports : Nat} (program : Fin count → Node count ports)
    {before after : Machine count ports} {fact : EndFact count}
    (step : Step (machineProgram program) before after) (present : after.fact = some fact) :
    before.fact = some fact := by
  cases step with
  | receiveEnd => contradiction
  | receiveMessage => contradiction
  | receiveEmpty | receiveFailed | receiveFailedToken => contradiction
  | call target continuation calleeContext inputs returnSource returnTarget node =>
      cases h : program before.pc <;> simp [machineProgram, h] at node
  | forward => exact present
  | branchYes => exact present
  | branchNo => exact present
  | endReply next target fact node pending same =>
      cases h : program before.pc <;> simp [machineProgram, h] at node
  | endResult target next node | otherResult target next node =>
      cases h : program before.pc <;> simp [machineProgram, h] at node
  | matchEndYes source yes no origin node value actual authentic same outer returned =>
      cases h : program before.pc <;> simp [machineProgram, h] at node
  | matchEndNo | matchEndUnverified | normalReturn | otherReturn => contradiction
  | matchedReturn => exact present
  | failure => contradiction
  | invalidate => contradiction

/-- Every finite suffix execution preserves the provenance of a returned End fact. -/
theorem trace_fact_origin {count ports : Nat} (program : Fin count → Node count ports)
    {first last : Machine count ports} {fact : EndFact count}
    (trace : Trace (machineProgram program) first last) (present : last.fact = some fact) :
    first.fact = some fact := by
  induction trace with
  | initial => exact present
  | next _ step ih => exact ih (step_fact_origin program step present)

end Suffix


namespace Region

/-- This fragment has no retain, callback or escaping operation. -/
inductive Forbidden where
  | retain | callback | escape | unknownCall | unknownCapture | unsupported
  deriving DecidableEq, Repr

inductive Stage where
  | processing | cleanupRunning | cleanupReturned
  deriving DecidableEq, Repr

/-- Forward destinations are region-local value or capture sites. Outer cells,
returned values and saved or asynchronous captures use `forbidden .escape`. -/
inductive Node (count ports bindings : Nat) where
  | stutter (next : Fin count)
  | forward (operands : List (Fin ports)) (target : Fin ports) (next : Fin count)
  | native (binding : Fin bindings) (next : Fin count)
  | branch (yes no : Fin count)
  | startCleanup (next : Fin count)
  | returnCleanup (next : Fin count)
  | marker
  | forbidden (kind : Forbidden)

/-- Stutter creates no values or captures and preserves all modeled state.
A checked binding returns synchronously and preserves modeled network, Store and dependencies. -/
def check {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) : Nat → Stage → Fin count → Bool
  | 0, _, _ => false
  | fuel + 1, stage, pc =>
      match stage, program pc with
      | .processing, .stutter next => check program bindingChecked fuel .processing next
      | .processing, .forward _ _ next => check program bindingChecked fuel .processing next
      | .processing, .native binding next =>
          bindingChecked binding && check program bindingChecked fuel .processing next
      | .processing, .branch yes no =>
          check program bindingChecked fuel .processing yes &&
            check program bindingChecked fuel .processing no
      | .processing, .startCleanup next => check program bindingChecked fuel .cleanupRunning next
      | .cleanupRunning, .returnCleanup next => check program bindingChecked fuel .cleanupReturned next
      | .cleanupReturned, .marker => true
      | _, _ => false


/-- Real control successors of this bounded modeled region, before checking reachability. -/
inductive Step {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) : Stage → Fin count → Stage → Fin count → Prop where
  | stutter (pc next) (node : program pc = .stutter next) :
      Step program bindingChecked .processing pc .processing next
  | forward (pc next operands target) (node : program pc = .forward operands target next) :
      Step program bindingChecked .processing pc .processing next
  | native (pc next binding) (node : program pc = .native binding next)
      (premise : bindingChecked binding = true) :
      Step program bindingChecked .processing pc .processing next
  | branchYes (pc yes no) (node : program pc = .branch yes no) :
      Step program bindingChecked .processing pc .processing yes
  | branchNo (pc yes no) (node : program pc = .branch yes no) :
      Step program bindingChecked .processing pc .processing no
  | startCleanup (pc next) (node : program pc = .startCleanup next) :
      Step program bindingChecked .processing pc .cleanupRunning next
  | returnCleanup (pc next) (node : program pc = .returnCleanup next) :
      Step program bindingChecked .cleanupRunning pc .cleanupReturned next

/-- Every modeled normal successor of a checked node is itself checked. -/
theorem check_step {count ports bindings : Nat} {program : Fin count → Node count ports bindings}
    {bindingChecked : Fin bindings → Bool} {stage nextStage : Stage} {pc next : Fin count}
    (fuel : Nat) (accepted : check program bindingChecked (fuel + 1) stage pc = true)
    (step : Step program bindingChecked stage pc nextStage next) :
    check program bindingChecked fuel nextStage next = true := by
  cases step <;> simp_all [check, Bool.and_eq_true]

inductive Walk {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) : Stage → Fin count → Stage → Fin count → Prop where
  | refl (stage pc) : Walk program bindingChecked stage pc stage pc
  | next {startStage start middleStage middle finishStage finish} :
      Walk program bindingChecked startStage start middleStage middle →
      Step program bindingChecked middleStage middle finishStage finish →
      Walk program bindingChecked startStage start finishStage finish

/-- Forwarding unions the actual message-derived operands into the destination. -/
def transfer {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (pc : Fin count) (derived : Vector Bool ports) : Vector Bool ports :=
  match program pc with
  | .forward operands target _ =>
      let dependent := operands.any fun operand ↦ derived[operand]
      Vector.ofFn fun port ↦ if port = target then dependent || derived[port] else derived[port]
  | _ => derived

/-- Every concrete region step carries its evolving value/capture dependencies. -/
inductive DataWalk {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) :
    Stage → Fin count → Vector Bool ports → Stage → Fin count → Vector Bool ports → Prop where
  | refl (stage pc derived) : DataWalk program bindingChecked stage pc derived stage pc derived
  | next {startStage start startDerived middleStage middle middleDerived finishStage finish} :
      DataWalk program bindingChecked startStage start startDerived middleStage middle middleDerived →
      Step program bindingChecked middleStage middle finishStage finish →
      DataWalk program bindingChecked startStage start startDerived finishStage finish
        (transfer program middle middleDerived)

theorem DataWalk.toWalk {count ports bindings : Nat} {program : Fin count → Node count ports bindings}
    {bindingChecked : Fin bindings → Bool} {startStage finishStage : Stage} {start finish : Fin count}
    {initial final : Vector Bool ports} (path : DataWalk program bindingChecked startStage start initial finishStage finish final) :
    Walk program bindingChecked startStage start finishStage finish := by
  induction path with
  | refl => exact Walk.refl _ _
  | next _ edge ih => exact Walk.next ih edge

/-- Enumerate all checked normal processing outputs, including both branch successors. -/
def outputs {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) : Nat → Stage → Fin count → Vector Bool ports → List (Vector Bool ports)
  | 0, _, _, _ => []
  | fuel + 1, stage, pc, derived =>
      match stage, program pc with
      | .processing, .stutter next => outputs program bindingChecked fuel .processing next derived
      | .processing, .forward _ _ next => outputs program bindingChecked fuel .processing next (transfer program pc derived)
      | .processing, .native binding next =>
          if bindingChecked binding then outputs program bindingChecked fuel .processing next derived else []
      | .processing, .branch yes no =>
          outputs program bindingChecked fuel .processing yes derived ++ outputs program bindingChecked fuel .processing no derived
      | .processing, .startCleanup next => outputs program bindingChecked fuel .cleanupRunning next derived
      | .cleanupRunning, .returnCleanup next => outputs program bindingChecked fuel .cleanupReturned next derived
      | .cleanupReturned, .marker => [derived]
      | _, _ => []

/-- Count list cells while charging each cell before traversing it. -/
def countCells {α : Type} : Nat → List α → Option (Nat × Nat)
  | budget, [] => some (0, budget)
  | 0, _ :: _ => none
  | budget + 1, _ :: rest => do
      let (count, remaining) ← countCells budget rest
      pure (count + 1, remaining)

/-- Charge a known finite number of operations before doing them. -/
def debit (budget cost : Nat) : Option Nat :=
  if cost ≤ budget then some (budget - cost) else none

/-- A completed cell traversal charges exactly one unit per visited cell. -/
theorem countCells_exact {α : Type} (budget : Nat) (items : List α) (count remaining : Nat)
    (computed : countCells budget items = some (count, remaining)) :
    count = items.length ∧ remaining + count = budget := by
  induction items generalizing budget count remaining with
  | nil =>
      simp [countCells] at computed
      simp_all
  | cons first rest ih =>
      cases budget with
      | zero => simp [countCells] at computed
      | succ budget =>
          cases prior : countCells budget rest with
          | none => simp [countCells, prior] at computed
          | some pair =>
              rcases pair with ⟨priorCount, priorRemaining⟩
              have exactPrior := ih budget priorCount priorRemaining prior
              simp [countCells, prior] at computed
              simp only [List.length_cons]
              omega

/-- A successful debit consumes its full charge without increasing the budget. -/
theorem debit_exact (budget cost remaining : Nat)
    (computed : debit budget cost = some remaining) : remaining + cost = budget := by
  unfold debit at computed
  split at computed
  next enough =>
    simp at computed
    omega
  next insufficient => simp at computed

/--
Preflight the entire output tree with a shared budget. Each node is charged for
this traversal, later construction and two checker passes; operand cells and
output-copy cells are charged before those traversals. Counts can grow only as charged
marker nodes are encountered. Exhaustion publishes no partial result.
-/
def preflight {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) : Nat → Nat → Stage → Fin count → Option (Nat × Nat)
  | 0, budget, _, _ => some (0, budget)
  | fuel + 1, budget, stage, pc => do
      let available := budget
      let budget ← debit budget 4
      match stage, program pc with
      | .processing, .stutter next => preflight program bindingChecked fuel budget .processing next
      | .processing, .forward operands _ next => do
          let (operandCount, budget) ← countCells budget operands
          let budget ← debit budget operandCount
          let budget ← debit budget ports
          preflight program bindingChecked fuel budget .processing next
      | .processing, .native binding next =>
          if bindingChecked binding then preflight program bindingChecked fuel budget .processing next
          else some (0, budget)
      | .processing, .branch yes no => do
          let (leftCount, budget) ← preflight program bindingChecked fuel budget .processing yes
          let (rightCount, budget) ← preflight program bindingChecked fuel budget .processing no
          let budget ← debit budget leftCount
          if leftCount ≤ available ∧ rightCount ≤ available - leftCount then
            pure (leftCount + rightCount, budget)
          else none
      | .processing, .startCleanup next => preflight program bindingChecked fuel budget .cleanupRunning next
      | .cleanupRunning, .returnCleanup next => preflight program bindingChecked fuel budget .cleanupReturned next
      | .cleanupReturned, .marker => do
          let budget ← debit budget 1
          pure (1, budget)
      | _, _ => some (0, budget)

/-- Mathematical charge and output count for the complete bounded Region tree. -/
def preflightWork {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) : Nat → Stage → Fin count → Nat × Nat
  | 0, _, _ => (0, 0)
  | fuel + 1, stage, pc =>
      match stage, program pc with
      | .processing, .stutter next =>
          let result := preflightWork program bindingChecked fuel .processing next
          (4 + result.1, result.2)
      | .processing, .forward operands _ next =>
          let result := preflightWork program bindingChecked fuel .processing next
          (4 + operands.length + operands.length + ports + result.1, result.2)
      | .processing, .native binding next =>
          if bindingChecked binding then
            let result := preflightWork program bindingChecked fuel .processing next
            (4 + result.1, result.2)
          else (4, 0)
      | .processing, .branch yes no =>
          let left := preflightWork program bindingChecked fuel .processing yes
          let right := preflightWork program bindingChecked fuel .processing no
          (4 + left.1 + right.1 + left.2, left.2 + right.2)
      | .processing, .startCleanup next =>
          let result := preflightWork program bindingChecked fuel .cleanupRunning next
          (4 + result.1, result.2)
      | .cleanupRunning, .returnCleanup next =>
          let result := preflightWork program bindingChecked fuel .cleanupReturned next
          (4 + result.1, result.2)
      | .cleanupReturned, .marker => (5, 1)
      | _, _ => (4, 0)

/-- All recursive output construction occurs only after the complete tree was charged. -/
def outputsBudgeted {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) (fuel budget : Nat) (stage : Stage) (pc : Fin count)
    (derived : Vector Bool ports) : Option (List (Vector Bool ports) × Nat) := do
  let (_, remaining) ← preflight program bindingChecked fuel budget stage pc
  pure (outputs program bindingChecked fuel stage pc derived, remaining)

/-- A successful preflight counts every output before the output list is constructed. -/
theorem preflight_output_count {count ports bindings : Nat}
    (program : Fin count → Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel budget : Nat) (stage : Stage) (pc : Fin count) (derived : Vector Bool ports)
    (size remaining : Nat)
    (computed : preflight program bindingChecked fuel budget stage pc = some (size, remaining)) :
    size = (outputs program bindingChecked fuel stage pc derived).length := by
  induction fuel generalizing budget stage pc derived size remaining with
  | zero =>
      simp [preflight] at computed
      simp [outputs, ← computed.1]
  | succ fuel ih =>
      cases charged : debit budget 4 with
      | none => simp [preflight, charged] at computed
      | some available =>
        cases stage with
        | processing =>
          cases node : program pc with
          | stutter next =>
              have prior : preflight program bindingChecked fuel available .processing next = some (size, remaining) := by
                simpa [preflight, charged, node] using computed
              simpa [outputs, node] using ih available .processing next derived size remaining prior
          | forward operands target next =>
              cases cells : countCells available operands with
              | none => simp [preflight, charged, node, cells] at computed
              | some pair =>
                  rcases pair with ⟨operandCount, afterCells⟩
                  cases first : debit afterCells operandCount with
                  | none => simp [preflight, charged, node, cells, first] at computed
                  | some afterOperands =>
                      cases second : debit afterOperands ports with
                      | none => simp [preflight, charged, node, cells, first, second] at computed
                      | some afterPorts =>
                          have prior : preflight program bindingChecked fuel afterPorts .processing next = some (size, remaining) := by
                            simpa [preflight, charged, node, cells, first, second] using computed
                          simpa [outputs, node] using ih afterPorts .processing next (transfer program pc derived) size remaining prior
          | native binding next =>
              cases valid : bindingChecked binding with
              | false => simp [preflight, charged, node, valid, outputs] at computed ⊢; omega
              | true =>
                  have prior : preflight program bindingChecked fuel available .processing next = some (size, remaining) := by
                    simpa [preflight, charged, node, valid] using computed
                  simpa [outputs, node, valid] using ih available .processing next derived size remaining prior
          | branch yes no =>
              cases left : preflight program bindingChecked fuel available .processing yes with
              | none => simp [preflight, charged, node, left] at computed
              | some leftPair =>
                  rcases leftPair with ⟨leftCount, afterLeft⟩
                  cases right : preflight program bindingChecked fuel afterLeft .processing no with
                  | none => simp [preflight, charged, node, left, right] at computed
                  | some rightPair =>
                      rcases rightPair with ⟨rightCount, afterRight⟩
                      cases copies : debit afterRight leftCount with
                      | none => simp [preflight, charged, node, left, right, copies] at computed
                      | some afterCopies =>
                          by_cases enough : leftCount ≤ budget ∧ rightCount ≤ budget - leftCount
                          · have result : size = leftCount + rightCount := by
                              simp [preflight, charged, node, left, right, copies, enough] at computed
                              omega
                            have leftExact := ih available .processing yes derived leftCount afterLeft left
                            have rightExact := ih afterLeft .processing no derived rightCount afterRight right
                            simp [outputs, node, List.length_append, ← leftExact, ← rightExact, result]
                          · simp [preflight, charged, node, left, right, copies, enough] at computed
          | startCleanup next =>
              have prior : preflight program bindingChecked fuel available .cleanupRunning next = some (size, remaining) := by
                simpa [preflight, charged, node] using computed
              simpa [outputs, node] using ih available .cleanupRunning next derived size remaining prior
          | returnCleanup next => simp [preflight, charged, node, outputs] at computed ⊢; omega
          | marker => simp [preflight, charged, node, outputs] at computed ⊢; omega
          | forbidden kind => simp [preflight, charged, node, outputs] at computed ⊢; omega
        | cleanupRunning =>
          cases node : program pc with
          | returnCleanup next =>
              have prior : preflight program bindingChecked fuel available .cleanupReturned next = some (size, remaining) := by
                simpa [preflight, charged, node] using computed
              simpa [outputs, node] using ih available .cleanupReturned next derived size remaining prior
          | stutter _ | forward _ _ _ | native _ _ | branch _ _ | startCleanup _ | marker | forbidden _ =>
              simp [preflight, charged, node, outputs] at computed ⊢; omega
        | cleanupReturned =>
          cases node : program pc with
          | marker =>
              cases one : debit available 1 with
              | none => simp [preflight, charged, node, one] at computed
              | some left => simp [preflight, charged, node, one, outputs] at computed ⊢; omega
          | stutter _ | forward _ _ _ | native _ _ | branch _ _ | startCleanup _ | returnCleanup _ | forbidden _ =>
              simp [preflight, charged, node, outputs] at computed ⊢; omega

/-- Successful preflight charges the whole traversal, outputs and branch copies exactly. -/
theorem preflight_work_exact {count ports bindings : Nat}
    (program : Fin count → Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel budget : Nat) (stage : Stage) (pc : Fin count) (size remaining : Nat)
    (computed : preflight program bindingChecked fuel budget stage pc = some (size, remaining)) :
    remaining + (preflightWork program bindingChecked fuel stage pc).1 = budget ∧
      size = (preflightWork program bindingChecked fuel stage pc).2 := by
  induction fuel generalizing budget stage pc size remaining with
  | zero =>
      simp [preflight] at computed
      simp [preflightWork, ← computed.1, ← computed.2]
  | succ fuel ih =>
      cases charged : debit budget 4 with
      | none => simp [preflight, charged] at computed
      | some available =>
        have baseCharge := debit_exact budget 4 available charged
        cases stage with
        | processing =>
          cases node : program pc with
          | stutter next =>
              have prior : preflight program bindingChecked fuel available .processing next = some (size, remaining) := by
                simpa [preflight, charged, node] using computed
              have exactPrior := ih available .processing next size remaining prior
              simp only [preflightWork, node]
              omega
          | forward operands target next =>
              cases cells : countCells available operands with
              | none => simp [preflight, charged, node, cells] at computed
              | some pair =>
                  rcases pair with ⟨operandCount, afterCells⟩
                  have cellCharge := countCells_exact available operands operandCount afterCells cells
                  cases first : debit afterCells operandCount with
                  | none => simp [preflight, charged, node, cells, first] at computed
                  | some afterOperands =>
                      have operandCharge := debit_exact afterCells operandCount afterOperands first
                      cases second : debit afterOperands ports with
                      | none => simp [preflight, charged, node, cells, first, second] at computed
                      | some afterPorts =>
                          have portCharge := debit_exact afterOperands ports afterPorts second
                          have prior : preflight program bindingChecked fuel afterPorts .processing next = some (size, remaining) := by
                            simpa [preflight, charged, node, cells, first, second] using computed
                          have exactPrior := ih afterPorts .processing next size remaining prior
                          simp only [preflightWork, node]
                          omega
          | native binding next =>
              cases valid : bindingChecked binding with
              | false =>
                  simp [preflight, charged, node, valid] at computed
                  simp only [preflightWork, node, valid, Bool.false_eq_true, if_false]
                  omega
              | true =>
                  have prior : preflight program bindingChecked fuel available .processing next = some (size, remaining) := by
                    simpa [preflight, charged, node, valid] using computed
                  have exactPrior := ih available .processing next size remaining prior
                  simp only [preflightWork, node, valid, if_true]
                  omega
          | branch yes no =>
              cases left : preflight program bindingChecked fuel available .processing yes with
              | none => simp [preflight, charged, node, left] at computed
              | some leftPair =>
                  rcases leftPair with ⟨leftCount, afterLeft⟩
                  have leftExact := ih available .processing yes leftCount afterLeft left
                  cases right : preflight program bindingChecked fuel afterLeft .processing no with
                  | none => simp [preflight, charged, node, left, right] at computed
                  | some rightPair =>
                      rcases rightPair with ⟨rightCount, afterRight⟩
                      have rightExact := ih afterLeft .processing no rightCount afterRight right
                      cases copies : debit afterRight leftCount with
                      | none => simp [preflight, charged, node, left, right, copies] at computed
                      | some afterCopies =>
                          have copyCharge := debit_exact afterRight leftCount afterCopies copies
                          by_cases enough : leftCount ≤ budget ∧ rightCount ≤ budget - leftCount
                          · simp [preflight, charged, node, left, right, copies, enough] at computed
                            simp only [preflightWork, node]
                            omega
                          · simp [preflight, charged, node, left, right, copies, enough] at computed
          | startCleanup next =>
              have prior : preflight program bindingChecked fuel available .cleanupRunning next = some (size, remaining) := by
                simpa [preflight, charged, node] using computed
              have exactPrior := ih available .cleanupRunning next size remaining prior
              simp only [preflightWork, node]
              omega
          | returnCleanup next => simp [preflight, charged, node] at computed; simp [preflightWork, node]; omega
          | marker => simp [preflight, charged, node] at computed; simp [preflightWork, node]; omega
          | forbidden kind => simp [preflight, charged, node] at computed; simp [preflightWork, node]; omega
        | cleanupRunning =>
          cases node : program pc with
          | returnCleanup next =>
              have prior : preflight program bindingChecked fuel available .cleanupReturned next = some (size, remaining) := by
                simpa [preflight, charged, node] using computed
              have exactPrior := ih available .cleanupReturned next size remaining prior
              simp only [preflightWork, node]
              omega
          | stutter _ | forward _ _ _ | native _ _ | branch _ _ | startCleanup _ | marker | forbidden _ =>
              simp [preflight, charged, node] at computed; simp [preflightWork, node]; omega
        | cleanupReturned =>
          cases node : program pc with
          | marker =>
              cases one : debit available 1 with
              | none => simp [preflight, charged, node, one] at computed
              | some left =>
                  have oneCharge := debit_exact available 1 left one
                  simp [preflight, charged, node, one] at computed
                  simp [preflightWork, node]
                  omega
          | stutter _ | forward _ _ _ | native _ _ | branch _ _ | startCleanup _ | returnCleanup _ | forbidden _ =>
              simp [preflight, charged, node] at computed; simp [preflightWork, node]; omega

/-- A successful bounded enumeration contains exactly the unbounded specification outputs. -/
theorem outputsBudgeted_exact {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) (fuel budget : Nat) (stage : Stage) (pc : Fin count)
    (derived : Vector Bool ports) (result : List (Vector Bool ports)) (remaining : Nat)
    (computed : outputsBudgeted program bindingChecked fuel budget stage pc derived = some (result, remaining)) :
    result = outputs program bindingChecked fuel stage pc derived := by
  unfold outputsBudgeted at computed
  cases pre : preflight program bindingChecked fuel budget stage pc with
  | none => simp [pre] at computed
  | some value =>
      rcases value with ⟨count, left⟩
      simp [pre] at computed
      exact computed.1.symm

/-- Each actual checked edge is included in the enumerated branch outputs. -/
theorem outputs_step {count ports bindings : Nat} {program : Fin count → Node count ports bindings}
    {bindingChecked : Fin bindings → Bool} {stage nextStage : Stage} {pc next : Fin count}
    (fuel : Nat) (derived : Vector Bool ports) (result : Vector Bool ports)
    (edge : Step program bindingChecked stage pc nextStage next)
    (member : result ∈ outputs program bindingChecked fuel nextStage next (transfer program pc derived)) :
    result ∈ outputs program bindingChecked (fuel + 1) stage pc derived := by
  cases edge <;> simp_all [outputs, transfer, List.mem_append]

/-- All actual dependency-carrying prefixes are represented in the output enumeration. -/
theorem outputs_walk {count ports bindings : Nat} {program : Fin count → Node count ports bindings}
    {bindingChecked : Fin bindings → Bool} {startStage finishStage : Stage} {start finish : Fin count}
    {initial final : Vector Bool ports}
    (path : DataWalk program bindingChecked startStage start initial finishStage finish final)
    (fuel : Nat) (accepted : check program bindingChecked fuel startStage start = true) :
    ∃ remaining, check program bindingChecked remaining finishStage finish = true ∧
      ∀ result, result ∈ outputs program bindingChecked remaining finishStage finish final →
        result ∈ outputs program bindingChecked fuel startStage start initial := by
  induction path with
  | refl => exact ⟨fuel, accepted, fun _ member ↦ member⟩
  | next _ edge ih =>
      obtain ⟨remaining, checked, contains⟩ := ih
      cases remaining with
      | zero => simp [check] at checked
      | succ remaining =>
          refine ⟨remaining, check_step remaining checked edge, ?_⟩
          intro result member
          exact contains result (outputs_step remaining _ result edge member)

/-- Every actual checked path to the cleanup marker yields an enumerated dependency output. -/
theorem outputs_marker {count ports bindings : Nat} {program : Fin count → Node count ports bindings}
    {bindingChecked : Fin bindings → Bool} {start marker : Fin count} {initial final : Vector Bool ports}
    (fuel : Nat) (accepted : check program bindingChecked fuel .processing start = true)
    (path : DataWalk program bindingChecked .processing start initial .cleanupReturned marker final)
    (markerNode : program marker = .marker) :
    final ∈ outputs program bindingChecked fuel .processing start initial := by
  obtain ⟨remaining, checked, contains⟩ := outputs_walk path fuel accepted
  cases remaining with
  | zero => simp [check] at checked
  | succ remaining =>
      apply contains final
      simp [outputs, markerNode]

/-- A successful bounded output includes every checked concrete path to the marker. -/
theorem outputsBudgeted_marker {count ports bindings : Nat} {program : Fin count → Node count ports bindings}
    {bindingChecked : Fin bindings → Bool} {start marker : Fin count} {initial final : Vector Bool ports}
    (fuel budget remaining : Nat) (result : List (Vector Bool ports))
    (computed : outputsBudgeted program bindingChecked fuel budget .processing start initial = some (result, remaining))
    (accepted : check program bindingChecked fuel .processing start = true)
    (path : DataWalk program bindingChecked .processing start initial .cleanupReturned marker final)
    (markerNode : program marker = .marker) : final ∈ result := by
  have exactOutputs := outputsBudgeted_exact program bindingChecked fuel budget .processing start initial result remaining computed
  rw [exactOutputs]
  exact outputs_marker fuel accepted path markerNode

/-- Finite actual modeled paths retain a checked suffix at every reached node. -/
theorem checked_walk {count ports bindings : Nat} {program : Fin count → Node count ports bindings}
    {bindingChecked : Fin bindings → Bool} {startStage finishStage : Stage}
    {start finish : Fin count} (path : Walk program bindingChecked startStage start finishStage finish)
    (fuel : Nat) (accepted : check program bindingChecked fuel startStage start = true) :
    ∃ remaining, check program bindingChecked remaining finishStage finish = true := by
  induction path with
  | refl => exact ⟨fuel, accepted⟩
  | next path edge ih =>
      obtain ⟨remaining, checked⟩ := ih
      cases remaining with
      | zero => simp [check] at checked
      | succ remaining => exact ⟨remaining, check_step remaining checked edge⟩

theorem accepted_marker_follows_cleanup {count ports bindings : Nat}
    (program : Fin count → Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel : Nat) (stage : Stage) (pc : Fin count) (node : program pc = .marker)
    (accepted : check program bindingChecked fuel stage pc = true) : stage = .cleanupReturned := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel => cases stage <;> simp_all [check]

theorem branch_checks_both {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) (fuel : Nat) (pc yes no : Fin count)
    (node : program pc = .branch yes no)
    (accepted : check program bindingChecked (fuel + 1) .processing pc = true) :
    check program bindingChecked fuel .processing yes = true ∧
      check program bindingChecked fuel .processing no = true := by
  simpa [check, node, Bool.and_eq_true] using accepted

theorem forbidden_rejected {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) (fuel : Nat) (stage : Stage) (pc : Fin count)
    (kind : Forbidden) (node : program pc = .forbidden kind) :
    check program bindingChecked fuel stage pc = false := by
  cases fuel with
  | zero => rfl
  | succ fuel => cases stage <;> simp [check, node]

theorem native_requires_binding {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) (fuel : Nat) (pc next : Fin count)
    (binding : Fin bindings) (node : program pc = .native binding next)
    (accepted : check program bindingChecked (fuel + 1) .processing pc = true) :
    bindingChecked binding = true ∧ check program bindingChecked fuel .processing next = true := by
  simpa [check, node, Bool.and_eq_true] using accepted

/-- All entry checks must pass before this restricted region is admitted. -/
def admit {count ports bindings : Nat} (program : Fin count → Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) (fuel : Nat) (pc : Fin count)
    (suffix : Fin count → Suffix.Node count ports) (derived : Fin ports → Bool)
    (frames : List (Fin count)) (capture : RetainedControl.Capture)
    (work : RetainedControl.PortCases.Work) (escape : Bool) : Bool :=
  decide (capture.cleanup = .armed ∧ capture.nested = [] ∧ work = .activeOnly ∧ escape = false) &&
    check program bindingChecked fuel .processing pc && Suffix.checkFrames suffix derived fuel frames

theorem admitted_shape {count ports bindings : Nat}
    (program : Fin count → Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel : Nat) (pc : Fin count) (suffix : Fin count → Suffix.Node count ports)
    (derived : Fin ports → Bool) (frames : List (Fin count))
    (capture : RetainedControl.Capture) (work : RetainedControl.PortCases.Work) (escape : Bool)
    (admitted : admit program bindingChecked fuel pc suffix derived frames capture work escape = true) :
    capture.cleanup = .armed ∧ capture.nested = [] ∧ work = .activeOnly ∧ escape = false ∧
      check program bindingChecked fuel .processing pc = true ∧
      Suffix.checkFrames suffix derived fuel frames = true := by
  simpa [admit, Bool.and_eq_true, and_assoc] using admitted

end Region

namespace Processing

open Ash.RetainedControl

def runningCapture (capture : Capture) : Capture := { capture with cleanup := .running }
def finishedCapture (capture : Capture) : Capture := { capture with cleanup := .finished }

def runningStore (store : State) (capture : Capture) (consumer : Consumer) : State :=
  { store with active := some (runningCapture capture, consumer) }

def finishedStore (store : State) (capture : Capture) (consumer : Consumer) : State :=
  { store with active := some (finishedCapture capture, consumer) }

def setStore (network : Network) (worker : Worker) (store : State) : Network :=
  { network with stores := putWorker network.stores worker store }

/-- The selected root goes through the actual C1 cleanup and finish steps. -/
theorem cleanup_then_finish (store : State) (capture : Capture) (consumer : Consumer)
    (active : store.active = some (capture, consumer)) (armed : capture.cleanup = .armed)
    (noNested : capture.nested = []) (healthy : store.failed = false) :
    RetainedControl.Step store [] (runningStore store capture consumer) ∧
    RetainedControl.Step (runningStore store capture consumer) []
      (finishedStore store capture consumer) ∧
    ReadyToFinish (finishedCapture capture) ∧
    RetainedControl.Step (finishedStore store capture consumer) []
      (finishStore (finishedStore store capture consumer) (finishedCapture capture) consumer) := by
  have first : RetainedControl.Step store [] (runningStore store capture consumer) := by
    simpa [runningStore, runningCapture] using
      RetainedControl.Step.startCleanup store capture consumer active armed healthy
  have second : RetainedControl.Step (runningStore store capture consumer) []
      (finishedStore store capture consumer) := by
    simpa [runningStore, finishedStore, runningCapture, finishedCapture] using
      RetainedControl.Step.finishCleanup (runningStore store capture consumer)
        (runningCapture capture) consumer rfl rfl healthy
  have ready : ReadyToFinish (finishedCapture capture) := by
    simp [ReadyToFinish, finishedCapture, noNested]
  have final : RetainedControl.Step (finishedStore store capture consumer) []
      (finishStore (finishedStore store capture consumer) (finishedCapture capture) consumer) := by
    apply actual_c1_finish
    · rfl
    · exact ready
    · exact healthy
  exact ⟨first, second, ready, final⟩

/-- C3 ActiveOnly becomes Empty at the matching actual root finish. -/
theorem finished_active_only_is_quiet (actual : PortCases.ConcreteWork)
    (represented : PortCases.Work.activeOnly.allows actual) :
    PortCases.Work.empty.allows actual.finishRoot := by
  apply PortCases.finish_root_sound represented
  exact represented.1

/--
For an armed root with no nested work, execute both C1 cleanup transitions and
finish exactly the held entry through WorkerChannel. This is one modeled path,
not a general processing cut or a proof of C3/evaluator correspondence.
-/
theorem network_cleanup_then_finish (network : Network) (lane : Worker) (entry : Entry)
    (pre post : List Entry) (capture : Capture) (consumer : Consumer)
    (safe : network.Safe) (live : network.backing = true)
    (committed : network.committed = true) (networkHealthy : network.failed = false)
    (running : network.returned lane.peer = false)
    (found : (network.channels lane).held = pre ++ entry :: post)
    (identity : capture.branch = entry.id) (owned : entry.id ∈ capture.owners)
    (dispatched : network.dispatched lane.peer entry.id = true)
    (active : (network.stores lane.peer).active = some (capture, consumer))
    (armed : capture.cleanup = .armed) (noNested : capture.nested = [])
    (healthy : (network.stores lane.peer).failed = false) :
    ∃ first second final,
      NetworkStep network first ∧ NetworkStep first second ∧ NetworkStep second final ∧
      entry.id ∉ (final.channels lane).held.map Entry.id ∧
      (final.channels lane).held = pre ++ post := by
  let initialStore := network.stores lane.peer
  let firstStore := runningStore initialStore capture consumer
  let secondStore := finishedStore initialStore capture consumer
  let first := setStore network lane.peer firstStore
  let second := setStore first lane.peer secondStore
  let final := second.processingFinished lane entry pre post
    (finishStore (second.stores lane.peer) (finishedCapture capture) consumer)
  have c1 := cleanup_then_finish initialStore capture consumer active armed noNested healthy
  have firstStep : NetworkStep network first := by
    apply NetworkStep.localStep network lane.peer lane.peer [] firstStore live committed
      networkHealthy rfl running c1.1
    intro c d _ _ impossible
    simp [firstStore, runningStore] at impossible
  have secondStep : NetworkStep first second := by
    apply NetworkStep.localStep first lane.peer lane.peer [] secondStore
    · simpa [first, setStore] using live
    · simpa [first, setStore] using committed
    · simpa [first, setStore] using networkHealthy
    · rfl
    · simpa [first, setStore] using running
    · simpa [first, setStore, putWorker, firstStore] using c1.2.1
    · intro c d _ _ impossible
      simp [secondStore, finishedStore] at impossible
  have finishStep : NetworkStep second final := by
    apply NetworkStep.finishProcessing second lane entry pre post (finishedCapture capture) consumer
    · simpa [second, first, setStore] using live
    · simpa [second, first, setStore] using committed
    · simpa [second, first, setStore] using running
    · simpa [second, first, setStore] using found
    · simpa [finishedCapture] using identity
    · simpa [finishedCapture] using owned
    · simpa [second, first, setStore] using dispatched
    · simp [second, setStore, putWorker, secondStore, finishedStore]
    · exact c1.2.2.1
    · simpa [second, setStore, putWorker, secondStore, finishedStore] using healthy
  have safeSecond := network_step_safe (network_step_safe safe firstStep) secondStep
  have noRepeat := finished_entry_cannot_repeat (second.channels lane) entry pre post
    (safeSecond.1.1 lane) (by simpa [second, first, setStore] using found)
  refine ⟨first, second, final, firstStep, secondStep, finishStep, ?_, ?_⟩
  · simpa [final, Network.processingFinished, putWorker] using noRepeat
  · simp [final, Network.processingFinished, finishChannel, putWorker]


/--
A single positive modeled Message path: commit the queue head to held work,
dispatch the same entry to its selected root, execute cleanup, and finish it.
The hypotheses are concrete operation, admission and control premises. They
still need derivation from the finite checker and the actual linked program.
-/
theorem receive_dispatch_cleanup_finish (network : Network) (lane : Worker)
    (operationId : Nat) (entry : Entry) (tail : List Entry)
    (capture : Capture) (consumer : Consumer)
    (safe : network.Safe) (live : network.backing = true)
    (committed : network.committed = true) (networkHealthy : network.failed = false)
    (operation : network.operations operationId = some ⟨lane, .read, lane.peer⟩)
    (running : network.returned lane.peer = false)
    (head : (network.channels lane).queue = entry :: tail)
    (channelHealthy : (network.channels lane).failed = false)
    (notDispatched : network.dispatched lane.peer entry.id = false)
    (identity : capture.branch = entry.id) (owned : entry.id ∈ capture.owners)
    (noClause : (network.stores lane.peer).clause = none)
    (driver : (network.stores lane.peer).active = none)
    (admission : Admit (network.stores lane.peer) capture)
    (fresh : RootFresh (network.stores lane.peer) capture)
    (unique : CaptureUnique capture)
    (interpretation : consumer.interpretation = (network.stores lane.peer).interpretation)
    (kind : consumer.kind = .root) (openStore : (network.stores lane.peer).closed = false)
    (healthy : (network.stores lane.peer).failed = false)
    (armed : capture.cleanup = .armed) (noNested : capture.nested = []) :
    ∃ received started first second final,
      NetworkStep network received ∧ NetworkStep received started ∧
      NetworkStep started first ∧ NetworkStep first second ∧ NetworkStep second final ∧
      entry.id ∉ (final.channels lane).held.map Entry.id ∧
      (final.channels lane).held = (network.channels lane).held := by
  let channel := network.channels lane
  let changed : Channel := { channel with
    received := channel.received ++ [entry]
    queue := tail
    held := channel.held ++ [entry] }
  let received := network.advance lane changed operationId
  let started := received.dispatch lane entry capture consumer
  have receiveStep : NetworkStep network received := by
    apply NetworkStep.channel network operationId ⟨lane, .read, lane.peer⟩ changed
      live committed operation rfl running
    exact ChannelStep.receive channel entry tail head channelHealthy
  have held : entry ∈ (received.channels lane).held := by
    simp [received, Network.advance, putWorker, changed]
  have dispatchStep : NetworkStep received started := by
    apply NetworkStep.dispatch received lane lane.peer entry capture consumer
    · simpa [received, Network.advance] using live
    · simpa [received, Network.advance] using committed
    · simpa [received, Network.advance] using networkHealthy
    · rfl
    · simpa [received, Network.advance] using running
    · exact held
    · simpa [received, Network.advance] using notDispatched
    · exact identity
    · exact owned
    · simpa [received, Network.advance] using noClause
    · simpa [received, Network.advance] using driver
    · simpa [received, Network.advance] using admission
    · simpa [received, Network.advance] using fresh
    · exact unique
    · simpa [received, Network.advance] using interpretation
    · exact kind
    · simpa [received, Network.advance] using openStore
    · simpa [received, Network.advance] using healthy
  have startedSafe := network_step_safe (network_step_safe safe receiveStep) dispatchStep
  obtain ⟨first, second, final, firstStep, secondStep, finalStep, removed, preserved⟩ :=
    network_cleanup_then_finish started lane entry channel.held [] capture consumer
      startedSafe (by simpa [started, received, Network.dispatch, Network.advance] using live)
      (by simpa [started, received, Network.dispatch, Network.advance] using committed)
      (by simpa [started, received, Network.dispatch, Network.advance] using networkHealthy)
      (by simpa [started, received, Network.dispatch, Network.advance] using running)
      (by simp [started, received, Network.dispatch, Network.advance, putWorker, changed])
      identity owned
      (by simp [started, Network.dispatch, putWorker, put])
      (by simp [started, received, Network.dispatch, Network.advance, putWorker])
      armed noNested
      (by simpa [started, received, Network.dispatch, Network.advance, putWorker] using healthy)
  exact ⟨received, started, first, second, final, receiveStep, dispatchStep,
    firstStep, secondStep, finalStep, removed, by simpa [channel] using preserved⟩


/--
The region entry check supplies the capture shape needed by the modeled C1
cleanup path. The work projection is conditional on its own representation;
this theorem does not establish same-Store correspondence or graph execution.
-/
theorem admitted_region_cleanup {count ports bindings : Nat}
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel : Nat) (pc : Fin count) (suffix : Fin count → Suffix.Node count ports)
    (derived : Fin ports → Bool) (frames : List (Fin count))
    (network : Network) (lane : Worker) (entry : Entry) (pre post : List Entry)
    (capture : Capture) (consumer : Consumer) (work : PortCases.Work) (escape : Bool)
    (actualWork : PortCases.ConcreteWork) (represented : work.allows actualWork)
    (admitted : Region.admit program bindingChecked fuel pc suffix derived frames capture work escape = true)
    (safe : network.Safe) (live : network.backing = true)
    (committed : network.committed = true) (networkHealthy : network.failed = false)
    (running : network.returned lane.peer = false)
    (found : (network.channels lane).held = pre ++ entry :: post)
    (identity : capture.branch = entry.id) (owned : entry.id ∈ capture.owners)
    (dispatched : network.dispatched lane.peer entry.id = true)
    (active : (network.stores lane.peer).active = some (capture, consumer))
    (healthy : (network.stores lane.peer).failed = false) :
    (∃ first second final,
      NetworkStep network first ∧ NetworkStep first second ∧ NetworkStep second final ∧
      entry.id ∉ (final.channels lane).held.map Entry.id ∧
      (final.channels lane).held = pre ++ post) ∧
    PortCases.Work.empty.allows actualWork.finishRoot := by
  have shape := Region.admitted_shape program bindingChecked fuel pc suffix derived frames
    capture work escape admitted
  have activeWork : PortCases.Work.activeOnly.allows actualWork := by
    simpa [shape.2.2.1] using represented
  exact ⟨network_cleanup_then_finish network lane entry pre post capture consumer safe live
    committed networkHealthy running found identity owned dispatched active shape.1 shape.2.1 healthy,
    finished_active_only_is_quiet actualWork activeWork⟩



/-- C1's active capture and live clause/slots projected into C3's concrete work view. -/
def slotLive (slot : Slot) : Bool :=
  match slot.phase with
  | .live _ => true
  | .vacant | .spent => false

def storeWork (external : ExternalWork) (store : State) : PortCases.ConcreteWork :=
  ⟨store.active.isSome, store.clause.isSome || store.slots.any slotLive ||
    external.callbacks || external.cleanups || external.captures || external.other⟩

/-- Finishing a root changes the projection of this same Store only at its active component. -/
theorem finish_store_work (external : ExternalWork) (store : State)
    (capture : Capture) (consumer : Consumer) :
    storeWork external (finishStore store capture consumer) = (storeWork external store).finishRoot := by
  rfl


namespace Projection

/-- Exact concrete C3 work projected to its finite four-case analysis domain. -/
def classifyWork (actual : PortCases.ConcreteWork) : PortCases.Work :=
  if actual.other then .pending else if actual.active then .activeOnly else .empty

theorem classify_work_sound (actual : PortCases.ConcreteWork) :
    (classifyWork actual).allows actual := by
  cases actual with
  | mk active other => cases active <;> cases other <;> simp [classifyWork, PortCases.Work.allows]

/-- A frame's identity check is independent of message-derived operands. -/
def frameShape {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (key : Key) (owner : Fin count) (frame : Frame count ports) : Bool :=
  match calls frame.callSite with
  | .call target continuation context inputs returnSource returnTarget =>
      decide (target = frame.target ∧ continuation = frame.continuation ∧
        context = frame.calleeContext ∧ inputs = frame.inputs ∧ returnSource = frame.returnSource ∧
        returnTarget = frame.returnTarget ∧ frame.key = key ∧ context.owner = owner ∧
        context.side = key.side)
  | _ => false

/-- The oldest caller may match its exact return port and finish only on End. -/
def driverCheck {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (derived : Fin ports → Bool) (site : Fin count) (target : Fin ports) : Bool :=
  match calls site with
  | .matchEnd source yes no =>
      decide (source = target) && !derived source &&
        (match calls yes, calls no with | .finishReceive, .stop => true | _, _ => false)
  | _ => false

/-- A saved frame names its exact resolved call and a checked forwarding suffix. -/
def frameSafe {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (key : Key) (owner : Fin count) (fuel : Nat) (derived : Fin ports → Bool)
    (frame : Frame count ports) : Bool :=
  frameShape calls key owner frame &&
    Suffix.check (Suffix.fromCalls calls)
      (returnInputs frame.callerDependencies (derived frame.returnSource) frame.returnTarget)
      fuel frame.continuation

/-- Per-frame checks do not equate repeated dynamic activations or delivery IDs. -/
def framesSafe {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (s : Machine count ports) (fuel : Nat) : Bool :=
  s.frames.dropLast.all (frameSafe calls s.key s.ownerSite fuel s.derived) &&
    match s.frames.getLast? with
    | none => true
    | some frame =>
        frameSafe calls s.key s.ownerSite fuel s.derived frame ||
          (frameShape calls s.key s.ownerSite frame &&
            driverCheck calls
              (returnInputs frame.callerDependencies (s.derived frame.returnSource) frame.returnTarget)
              frame.continuation frame.returnTarget)

/-- The phase is conservative when any older held delivery remains. -/
def phase {count ports : Nat} (s : Machine count ports) : Analysis.Phase count :=
  match s.currentDelivery with
  | none => if (s.network.channels s.key.lane).held.isEmpty then .clear else .pending
  | some delivery =>
      if (s.network.channels s.key.lane).held = [delivery.entry] then
        .processing delivery.receiveSite
      else .pending

/-- Only successful reply facts project to authenticated End. -/
def fact {count ports : Nat} (s : Machine count ports) : Analysis.Fact count :=
  match s.fact with
  | some origin =>
      if origin.key = s.key then .endFact origin.receiveSite origin.resultEdge else .invalid
  | none =>
      match s.pendingEnd with
      | some origin =>
          if origin.key = s.key then .endPending origin.receiveSite origin.resultEdge else .invalid
      | none =>
          match s.receiveInfo with
          | .none => .none
          | .message operation edge => .message operation edge
          | .empty operation edge => .empty operation edge

/-- Classify the actual active root against the same dynamic held delivery. -/
def root {count ports : Nat} (s : Machine count ports) : Analysis.RootFact count :=
  match s.currentDelivery, (s.network.stores s.key.lane.peer).active with
  | _, none => .idle
  | none, some _ => .invalid
  | some delivery, some (capture, consumer) =>
      if capture.branch = delivery.entry.id ∧ delivery.entry.id ∈ capture.owners ∧
          capture.cleanup = .armed ∧ capture.nested = [] ∧ consumer.kind = .root then
        .selected delivery.receiveSite
      else .invalid

/-- The finite projection drops dynamic IDs but retains all checked static context. -/
def state {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (fuel : Nat) (s : Machine count ports) : Analysis.State count ports :=
  { context := s.context
    ownerSite := s.ownerSite
    side := s.key.side
    control := s.pc
    fact := fact s
    phase := phase s
    root := root s
    work := classifyWork (storeWork s.external (s.network.stores s.key.lane.peer))
    escape := s.tainted || s.network.failed ||
      decide (s.context.owner ≠ s.ownerSite ∨ s.context.side ≠ s.key.side) || s.pendingEnd.isSome
    tainted := s.tainted
    terminal := s.network.failed
    pending := s.pendingEnd.isSome
    compatible := decide (s.context.owner = s.ownerSite ∧ s.context.side = s.key.side)
    dependencies := Vector.ofFn s.derived
    endValues := Vector.ofFn s.endValues
    resultCases := Vector.ofFn s.resultCases
    driverReturn := s.driverReturn
    driverSource := s.driverSource
    frameSites := Vector.ofFn fun site ↦ s.frames.any (fun frame ↦ decide (frame.continuation = site))
    innerSites := Vector.ofFn fun site ↦ s.frames.dropLast.any (fun frame ↦ decide (frame.continuation = site))
    outerReturns := Vector.ofFn fun site ↦ Vector.ofFn fun port ↦
      match s.frames.getLast? with
      | none => false
      | some frame => decide (frame.continuation = site ∧ frame.returnTarget = port)
    frameDependencies := Vector.ofFn fun site ↦ Vector.ofFn fun port ↦
      s.frames.any (fun frame ↦ decide (frame.continuation = site ∧ frame.returnTarget ≠ port) &&
        frame.callerDependencies[port])
    frameLive := Vector.ofFn fun port ↦ s.frames.any (fun frame ↦ frame.callerDependencies[port])
    frameReturns := Vector.ofFn fun site ↦ Vector.ofFn fun target ↦ Vector.ofFn fun source ↦
      s.frames.any (fun frame ↦ decide (frame.continuation = site ∧ frame.returnTarget = target ∧
        frame.returnSource = source))
    framesValid := s.frames.all (frameShape calls s.key s.ownerSite)
    suffixSafe := framesSafe calls s fuel }

/-- Finish is checked on its actual predecessor, never on a projected queue alone. -/
def finishAccepted {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (a : Analysis.State count ports) : Bool :=
  match calls a.control, a.fact, a.phase, a.work with
  | .finishReceive, .endFact _ _, .clear, .empty => !a.escape && a.suffixSafe && a.driverSource.isSome
  | _, _, _, _ => false

end Projection

namespace Analysis

abbrev State := Ash.OneWayCompletion.Analysis.State

/-- Recompute the rejection bit after changing its individual finite components. -/
def refresh {count ports : Nat} (s : State count ports) : State count ports :=
  { s with escape := s.tainted || s.terminal || !s.compatible || s.pending }

/-- The explicit terminal failure edge cannot return a successful End. -/
def failed {count ports : Nat} (s : State count ports) : State count ports :=
  refresh { s with fact := .none, driverSource := none, driverReturn := none, tainted := true, terminal := true, pending := false }

/--
Finite intraprocedural successor candidates. Calls and returns are deliberately
not admitted until their actual matching summary edges have been installed.
The list is not yet proved to cover concrete execution.
-/
def localSuccessors {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (fuel : Nat) (s : State count ports) : List (State count ports) :=
  let failure := if s.terminal then [] else [failed s]
  let normal := match calls s.control with
    | .receive message empty endEdge failedReply payload =>
        let messageState := refresh { s with
          control := message
          driverSource := none
          driverReturn := none
          resultCases := Vector.ofFn fun _ ↦ .unknown
          endValues := Vector.ofFn fun _ ↦ false
          fact := .message s.control message
          pending := false
          phase := if s.phase = .clear then .processing s.control else .pending
          dependencies := Vector.ofFn fun port ↦ if port = payload then true else s.dependencies[port] }
        let emptyState := refresh { s with
          control := empty
          fact := .empty s.control empty
          pending := false
          driverSource := none
          driverReturn := none
          resultCases := Vector.ofFn fun _ ↦ .unknown
          endValues := Vector.ofFn fun _ ↦ false }
        let endState := refresh { s with
          control := endEdge
          fact := .endPending s.control endEdge
          pending := true
          driverSource := none
          driverReturn := none
          resultCases := Vector.ofFn fun _ ↦ .unknown
          endValues := Vector.ofFn fun _ ↦ false }
        let failedState := refresh { s with
          control := failedReply
          fact := .none
          pending := false
          driverSource := none
          driverReturn := none
          resultCases := Vector.ofFn fun _ ↦ .unknown
          endValues := Vector.ofFn fun _ ↦ false }
        [messageState, emptyState, endState, failedState]
    | .endReply next target =>
        match s.fact with
        | .endPending site _ => [refresh { s with
            control := next
            driverSource := none
            driverReturn := none
            resultCases := Vector.ofFn fun _ ↦ .unknown
            fact := .endFact site next
            pending := false
            endValues := Vector.ofFn fun _ ↦ false
            dependencies := Vector.ofFn (fun port ↦ if port = target then false else s.dependencies[port]) }]
        | _ => []
    | .endResult target next =>
        let authenticated := match s.fact with | .endFact _ _ => true | _ => false
        [refresh { s with
          control := next
          driverSource := none
          driverReturn := none
          dependencies := Vector.ofFn fun port ↦ if port = target then false else s.dependencies[port]
          resultCases := Vector.ofFn fun port ↦ if port = target then .endValue else s.resultCases[port]
          endValues := Vector.ofFn fun port ↦ if port = target then authenticated else s.endValues[port] }]
    | .otherResult target next =>
        [refresh { s with
          control := next
          driverSource := none
          driverReturn := none
          dependencies := Vector.ofFn fun port ↦ if port = target then false else s.dependencies[port]
          resultCases := Vector.ofFn fun port ↦ if port = target then .otherValue else s.resultCases[port]
          endValues := Vector.ofFn fun port ↦ if port = target then false else s.endValues[port] }]
    | .matchEnd source yes no =>
        let authenticated := match s.fact with | .endFact _ _ => true | _ => false
        let authorized := decide (s.resultCases[source] = .endValue) && s.endValues[source] && authenticated &&
          (List.finRange count).all (fun site ↦ !s.frameSites[site]) &&
          decide (s.driverReturn = some (s.control, source))
        let endBranch := if authorized then
          [refresh { s with control := yes, driverReturn := none, driverSource := some source }]
          else [refresh { s with
            control := yes
            fact := .none
            driverReturn := none
            driverSource := none
            tainted := true }]
        let otherBranch := [refresh { s with
          control := no
          fact := .none
          pending := false
          driverReturn := none
          driverSource := none }]
        match s.resultCases[source] with
        | .endValue => endBranch
        | .otherValue => otherBranch
        | .unknown => endBranch ++ otherBranch
    | .forward kind operands target next =>
        let dependent := operands.any fun port ↦ s.dependencies[port]
        [refresh { s with
          control := next
          driverSource := retainDriverSource target s.driverSource
          driverReturn := none
          resultCases := Vector.ofFn (forwardResultCase kind operands target (fun port ↦ s.resultCases[port]))
          endValues := Vector.ofFn (forwardEndValue kind operands target (fun port ↦ s.endValues[port]))
          dependencies := Vector.ofFn fun port ↦
            if port = target then dependent || s.dependencies[port] else s.dependencies[port] }]
    | .branch _ yes no => [refresh { s with control := yes, driverSource := none, driverReturn := none },
        refresh { s with control := no, driverSource := none, driverReturn := none }]
    | .dispatch next graph =>
        let receiveFact := match s.fact with
          | .message site edge => .message site edge
          | _ => .none
        let selected := match s.phase with
          | .processing site => if CapturePlan.admitted graph then .selected site else .invalid
          | _ => .invalid
        [refresh { s with
          control := next
          driverSource := none
          driverReturn := none
          endValues := Vector.ofFn fun _ ↦ false
          resultCases := Vector.ofFn fun _ ↦ .unknown
          fact := receiveFact
          pending := false
          root := selected
          work := s.work.enterRoot }]
    | .processing entry next =>
        if Region.check regions checked fuel .processing entry &&
            decide (s.work = .activeOnly) then
          (Region.outputs regions checked fuel .processing entry s.dependencies).map fun derived ↦
            refresh { s with
              control := next
              driverSource := none
              driverReturn := none
              endValues := Vector.ofFn fun _ ↦ false
              resultCases := Vector.ofFn fun _ ↦ .unknown
              fact := .none
              pending := false
              phase := .clear
              root := .idle
              work := .empty
              dependencies := derived }
        else []
    | .unsupported =>
        if s.terminal then (List.finRange count).map fun next ↦ refresh { s with
          control := next
          fact := .none
          pending := false
          driverReturn := none
          driverSource := none
          tainted := true }
        else []
    | .call .. | .returnNode .. | .stop | .finishReceive => []
  failure ++ normal

/-- Unsupported calls and returns cannot be silently accepted as dead ends. -/
def localAdmitted {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (fuel : Nat) (s : State count ports) : Bool :=
  if s.terminal then true else
  match calls s.control with
  | .call .. | .returnNode .. | .unsupported => false
  | .finishReceive => Projection.finishAccepted calls s
  | .processing entry _ =>
      Region.check regions checked fuel .processing entry &&
        decide (s.work = .activeOnly) &&
        match s.phase, s.root with | .processing site, .selected root => decide (site = root) | _, _ => false
  | .dispatch _ graph =>
      CapturePlan.admitted graph && decide (s.work = .empty ∧ s.root = .idle) &&
        (match s.phase with | .processing _ => true | _ => false) &&
        match s.fact with | .message _ _ => true | _ => false
  | .receive .. => decide (s.phase = .clear ∧ s.work = .empty)
  | _ => true

/--
A bounded queue charges two edge traversals before expansion: one for
construction and one for final closure validation. Exhaustion returns no
candidate and cannot publish partial facts.
-/
def visit {count ports : Nat} (next : State count ports → List (State count ports))
    (estimate : State count ports → Nat) : Nat → Nat → List (State count ports) →
      List (State count ports) → Option (List (State count ports))
  | 0, _, _, _ => none
  | _ + 1, _, seen, [] => some seen
  | fuel + 1, budget, seen, state :: queue =>
      if state ∈ seen then visit next estimate fuel budget seen queue
      else if 2 * estimate state + 1 > budget then none
      else
        let edges := next state
        if edges.length > estimate state then none
        else visit next estimate fuel (budget - (2 * estimate state + 1)) (state :: seen) (edges ++ queue)

/-- Final closure is rechecked; failed validation returns no partial result. -/
def certify {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel fuel budget edgeBound : Nat) (seed : State count ports) : Option (List (State count ports)) :=
  let next := localSuccessors calls regions checked regionFuel
  match visit next (fun _ ↦ edgeBound) fuel budget [] [seed] with
  | none => none
  | some seen =>
      if decide (seed ∈ seen) && seen.all (fun state ↦
          localAdmitted calls regions checked regionFuel state &&
          (next state).all (fun successor ↦ decide (successor ∈ seen))) then some seen else none

/-- A published candidate includes the seed, all enumerated edges and accepted nodes. -/
theorem certified_closed {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel fuel budget edgeBound : Nat) (seed : State count ports) (seen : List (State count ports))
    (result : certify calls regions checked regionFuel fuel budget edgeBound seed = some seen) :
    seed ∈ seen ∧ ∀ state, state ∈ seen →
      localAdmitted calls regions checked regionFuel state = true ∧
      ∀ successor, successor ∈ localSuccessors calls regions checked regionFuel state → successor ∈ seen := by
  unfold certify at result
  cases run : visit (localSuccessors calls regions checked regionFuel) (fun _ ↦ edgeBound)
      fuel budget [] [seed] with
  | none => simp [run] at result
  | some visited =>
      simp only [run] at result
      split at result
      next accepted =>
        simp only [Option.some.injEq] at result
        subst seen
        simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
        refine ⟨accepted.1, ?_⟩
        intro state member
        have all := (List.all_eq_true.mp accepted.2) state member
        simp only [Bool.and_eq_true] at all
        refine ⟨all.1, ?_⟩
        intro successor edge
        have present := (List.all_eq_true.mp all.2) successor edge
        simpa using present
      next rejected => contradiction

/-- Full entry and current state prevent caller and evidence contexts from merging. -/
structure Configuration (count ports : Nat) where
  entry : State count ports
  current : State count ports
  deriving DecidableEq

/-- A return is learned only from an actual reached return configuration. -/
structure ReturnPair (count ports : Nat) where
  entry : State count ports
  result : State count ports
  deriving DecidableEq

/-- One finite return-port propagation pass over all saved frames. -/
def dependencyStep {count ports : Nat}
    (edges : Vector (Vector (Vector Bool ports) ports) count) (prior : Vector Bool ports) : Vector Bool ports :=
  Vector.ofFn fun target ↦ prior[target] || (List.finRange count).any (fun site ↦
    (List.finRange ports).any (fun source ↦ edges[site][target][source] && prior[source]))

/-- Close finite return-port flow over all saved frames; recursion depth is unbounded. -/
def dependencyClosure {count ports : Nat} (s : State count ports) : Vector Bool ports :=
  let initial := Vector.ofFn fun port ↦ s.dependencies[port] || s.frameLive[port]
  Nat.repeat (dependencyStep s.frameReturns) ports initial

/-- Closure never loses a dependency in the current activation. -/
theorem dependencyClosure_contains_current {count ports : Nat} (s : State count ports)
    (port : Fin ports) (present : s.dependencies[port] = true) :
    (dependencyClosure s)[port] = true := by
  let step : Vector Bool ports → Vector Bool ports := fun prior ↦ Vector.ofFn fun target ↦
    prior[target] || (List.finRange count).any (fun site ↦
      (List.finRange ports).any (fun source ↦ s.frameReturns[site][target][source] && prior[source]))
  have preserved : ∀ n (initial : Vector Bool ports), initial[port] = true →
      (Nat.repeat step n initial)[port] = true := by
    intro n
    induction n with
    | zero => intro initial initialPresent; exact initialPresent
    | succ n ih =>
        intro initial initialPresent
        have prior := ih initial initialPresent
        simp only [Nat.repeat]
        change ((Vector.ofFn (fun (target : Fin ports) ↦ (Nat.repeat step n initial)[target] ||
          (List.finRange count).any (fun site ↦ (List.finRange ports).any (fun source ↦
            s.frameReturns[site][target][source] && (Nat.repeat step n initial)[source])))) : Vector Bool ports)[port.val]'port.isLt = true
        simp only [Vector.getElem_ofFn, Bool.or_eq_true]
        left
        change (Nat.repeat step n initial)[port.val]'port.isLt = true at prior
        exact prior
  unfold dependencyClosure dependencyStep
  apply preserved
  change (Vector.ofFn (fun p : Fin ports ↦ s.dependencies[p] || s.frameLive[p]))[port.val]'port.isLt = true
  change s.dependencies[port.val]'port.isLt = true at present
  simp only [Vector.getElem_ofFn, Bool.or_eq_true]
  exact Or.inl present

/-- Recheck all finite saved-continuation obligations against current dependencies. -/
def normalize {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat)
    (s : State count ports) : State count ports :=
  let closed := dependencyClosure s
  refresh { s with suffixSafe := s.framesValid && decide (dependencyStep s.frameReturns closed = closed) &&
    (List.finRange count).all (fun site ↦
      let derived := fun port ↦ s.frameDependencies[site][port] ||
        (List.finRange ports).any (fun source ↦ s.frameReturns[site][port][source] && closed[source])
      let strict := Suffix.check (Suffix.fromCalls calls) derived fuel site
      (!s.innerSites[site] || strict) &&
        (List.finRange ports).all (fun target ↦
          !s.outerReturns[site][target] || strict || Projection.driverCheck calls derived site target)) }

/-- A published suffix check has replayed every return-port transfer to a fixed point. -/
theorem normalized_dependency_closed {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat) (s : State count ports)
    (accepted : (normalize calls fuel s).suffixSafe = true) :
    dependencyStep s.frameReturns (dependencyClosure s) = dependencyClosure s := by
  simp only [normalize, refresh, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
  exact accepted.2.1

/-- Every saved return-port edge is closed under an accepted finite replay. -/
theorem normalized_dependency_edge {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat) (s : State count ports)
    (accepted : (normalize calls fuel s).suffixSafe = true)
    (site : Fin count) (target source : Fin ports)
    (edge : s.frameReturns[site][target][source] = true)
    (dependent : (dependencyClosure s)[source] = true) :
    (dependencyClosure s)[target] = true := by
  have allEdges : (List.finRange count).any (fun current ↦
      (List.finRange ports).any (fun input ↦ s.frameReturns[current][target][input] &&
        (dependencyClosure s)[input])) = true := by
    apply List.any_eq_true.mpr
    refine ⟨site, List.mem_finRange _, ?_⟩
    apply List.any_eq_true.mpr
    refine ⟨source, List.mem_finRange _, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨edge, dependent⟩
  have stepped : (dependencyStep s.frameReturns (dependencyClosure s))[target] = true := by
    let entries : Fin ports → Bool := fun current ↦ (dependencyClosure s)[current] ||
      (List.finRange count).any (fun site ↦ (List.finRange ports).any (fun source ↦
        s.frameReturns[site][current][source] && (dependencyClosure s)[source]))
    change (Vector.ofFn entries)[target.val]'target.isLt = true
    simp only [Vector.getElem_ofFn, entries, Bool.or_eq_true]
    right
    exact allEdges
  have fixed := normalized_dependency_closed calls fuel s accepted
  rw [fixed] at stepped
  exact stepped

/-- Refuse before multiplying when the result would exceed the remaining budget. -/
def debitProduct (budget left right : Nat) : Option Nat :=
  if left = 0 then some budget
  else if right ≤ budget / left then Region.debit budget (left * right) else none

/-- Charge all suffix branches and operand scans before a suffix check runs. -/
def suffixPreflight {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports) :
    Nat → Nat → Fin count → Option Nat
  | 0, budget, _ => some budget
  | fuel + 1, budget, pc => do
      let budget ← Region.debit budget 2
      match calls pc with
      | .forward _ operands _ next => do
          let (length, budget) ← Region.countCells budget operands
          let budget ← Region.debit budget length
          let budget ← debitProduct budget length ports
          let budget ← debitProduct budget length ports
          suffixPreflight calls fuel budget next
      | .branch operands yes no => do
          let (length, budget) ← Region.countCells budget operands
          let budget ← Region.debit budget length
          let budget ← debitProduct budget length ports
          let budget ← debitProduct budget length ports
          let budget ← suffixPreflight calls fuel budget yes
          suffixPreflight calls fuel budget no
      | .returnNode _ => do
          let budget ← Region.debit budget ports
          Region.debit budget ports
      | _ => some budget

/-- One shared budget is carried through every active saved-frame suffix. -/
def framePreflight {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (fuel : Nat) (state : State count ports) (budget : Nat) : Option Nat := do
  let budget ← Region.debit budget count
  let budget ← Region.debit budget count
  let budget ← debitProduct budget count ports
  let budget ← debitProduct budget count ports
  let budget ← debitProduct budget count ports
  let matrixSize := count * ports
  let budget ← debitProduct budget matrixSize ports
  let returnSize := matrixSize * ports
  let budget ← debitProduct budget returnSize ports
  let budget ← debitProduct budget returnSize ports
  let budget ← debitProduct budget returnSize 2
  let budget ← Region.debit budget ports
  let rec walk : List (Fin count) → Nat → Option Nat
    | [], budget => some budget
    | site :: rest, budget => do
        let budget ← if state.frameSites[site] then suffixPreflight calls fuel budget site else some budget
        walk rest budget
  walk (List.finRange count) budget

/-- The callee entry includes its resolved target, selected evidence and saved suffix. -/
def callEntry {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (fuel : Nat) (s : State count ports) : Option (State count ports) :=
  match calls s.control with
  | .call target continuation context inputs returnSource returnTarget =>
      if s.pending then none else
      let hasFrames := (List.finRange count).any (fun site ↦ s.frameSites[site])
      some (normalize calls fuel { s with
        control := target
        driverSource := none
        driverReturn := none
        resultCases := Vector.ofFn fun _ ↦ .unknown
        context := context
        fact := .none
        endValues := Vector.ofFn fun _ ↦ false
        dependencies := Vector.ofFn (callInputs inputs (fun port ↦ s.dependencies[port]))
        frameDependencies := Vector.ofFn fun site ↦ Vector.ofFn fun port ↦
          (decide (continuation = site ∧ returnTarget ≠ port) && s.dependencies[port]) ||
            s.frameDependencies[site][port]
        frameLive := Vector.ofFn fun port ↦ s.dependencies[port] || s.frameLive[port]
        frameReturns := Vector.ofFn fun site ↦ Vector.ofFn fun target ↦ Vector.ofFn fun source ↦
          decide (continuation = site ∧ returnTarget = target ∧ returnSource = source) ||
            s.frameReturns[site][target][source]
        compatible := decide (context.owner = s.ownerSite ∧ context.side = s.side)
        framesValid := decide (context.owner = s.ownerSite ∧ context.side = s.side) && s.framesValid
        frameSites := Vector.ofFn fun site ↦ decide (continuation = site) || s.frameSites[site]
        innerSites := Vector.ofFn fun site ↦ (hasFrames && decide (continuation = site)) || s.innerSites[site]
        outerReturns := Vector.ofFn fun site ↦ Vector.ofFn fun port ↦
          (!hasFrames && decide (continuation = site ∧ returnTarget = port)) || s.outerReturns[site][port] })
  | _ => none

/-- A return pair restores the exact caller's context and previous frame obligations. -/
def resumeCall {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (fuel : Nat) (caller : State count ports) (pair : ReturnPair count ports) : Option (State count ports) :=
  match calls caller.control, callEntry calls fuel caller with
  | .call _ continuation context inputs returnSource returnTarget, some entry =>
      if decide (pair.entry = entry ∧ pair.result.context = context) &&
          (match pair.result.fact with | .endPending _ _ | .invalid => false | _ => true) then
        let matchingReturn := match calls pair.result.control with
          | .returnNode value => decide (value = returnSource)
          | _ => false
        some (normalize calls fuel { pair.result with
          control := continuation
          driverSource := none
          driverReturn := if matchingReturn && (List.finRange count).all (fun site ↦ !caller.frameSites[site])
            then some (continuation, returnTarget) else none
          resultCases := if matchingReturn then
            Vector.ofFn fun port ↦ if port = returnTarget then pair.result.resultCases[returnSource] else .unknown
            else Vector.ofFn fun _ ↦ .unknown
          context := caller.context
          fact := if matchingReturn then
            (match pair.result.fact with | .endFact site edge => .endFact site edge | _ => .none)
            else .none
          tainted := pair.result.tainted || !matchingReturn
          compatible := caller.compatible
          endValues := if matchingReturn then
            (match pair.result.fact with
             | .endFact _ _ => Vector.ofFn fun port ↦ if port = returnTarget then pair.result.endValues[returnSource] else false
             | _ => Vector.ofFn fun _ ↦ false)
            else Vector.ofFn fun _ ↦ false
          dependencies := if matchingReturn then
            Vector.ofFn (returnInputs caller.dependencies pair.result.dependencies[returnSource] returnTarget)
            else pair.result.dependencies
          frameSites := caller.frameSites
          innerSites := caller.innerSites
          outerReturns := caller.outerReturns
          frameDependencies := caller.frameDependencies
          frameLive := caller.frameLive
          frameReturns := caller.frameReturns
          framesValid := caller.framesValid })
      else none
  | _, _ => none

/-- No return is seeded: a bare recursive cycle cannot create one. -/
def observedReturn {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (configuration : Configuration count ports) : Option (ReturnPair count ports) :=
  match calls configuration.current.control, configuration.current.fact with
  | .returnNode _, .endPending _ _ | .returnNode _, .invalid => none
  | .returnNode _, _ => some ⟨configuration.entry, configuration.current⟩
  | _, _ => none

/-- All prior call configurations are replayed against every new return revision. -/
def configurationSuccessors {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (fuel : Nat) (returns : List (ReturnPair count ports))
    (configuration : Configuration count ports) : List (Configuration count ports) :=
  let s := configuration.current
  match calls s.control with
  | .call .. =>
      let failure := if s.terminal then [] else [⟨configuration.entry, failed s⟩]
      match callEntry calls fuel s with
      | none => failure
      | some entry => failure ++ [⟨entry, entry⟩] ++
          returns.filterMap (fun pair ↦ (resumeCall calls fuel s pair).map (fun result ↦ ⟨configuration.entry, result⟩))
  | .returnNode .. => if s.terminal then [] else [⟨configuration.entry, failed s⟩]
  | _ => (localSuccessors calls regions checked fuel s).map fun next ↦
      ⟨configuration.entry, normalize calls fuel next⟩

/-- Charge repeated suffix checks without constructing their results. -/
def repeatFramePreflight {count ports : Nat} (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (fuel : Nat) (state : State count ports) : Nat → Nat → Option Nat
  | 0, budget => some budget
  | repetitions + 1, budget => do
      let budget ← Region.debit budget 1
      let budget ← framePreflight calls fuel state budget
      repeatFramePreflight calls fuel state repetitions budget

/--
Precharge one configuration's successor generation, operand scans, branch
outputs, selected capture graph, return lookups and all suffix normalizations.
The returned number bounds the number of generated configurations.
-/
def configurationPreflight {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (fuel : Nat) (returns : List (ReturnPair count ports))
    (configuration : Configuration count ports) (budget : Nat) : Option (Nat × Nat) := do
  let available := budget
  let budget ← Region.debit budget 1
  let (returnCount, budget) ← Region.countCells budget returns
  let budget ← Region.debit budget returnCount
  let state := configuration.current
  match calls state.control with
  | .processing entry _ => do
      let (outputCount, budget) ← Region.preflight regions checked fuel budget .processing entry
      let budget ← Region.debit budget 1
      if outputCount < available then
        let budget ← repeatFramePreflight calls fuel state (outputCount + 1) budget
        pure (outputCount + 1, budget)
      else none
  | .dispatch _ graph => do
      let (graphCount, budget) ← Region.countCells budget graph
      let budget ← debitProduct budget graphCount 12
      let budget ← Region.debit budget 2
      let budget ← repeatFramePreflight calls fuel state 2 budget
      pure (2, budget)
  | .forward _ operands _ _ => do
      let (operandCount, budget) ← Region.countCells budget operands
      let budget ← Region.debit budget operandCount
      let budget ← Region.debit budget ports
      let budget ← Region.debit budget 2
      let budget ← repeatFramePreflight calls fuel state 2 budget
      pure (2, budget)
  | .call _ continuation _ inputs returnSource returnTarget => do
      let (inputCount, budget) ← Region.countCells budget inputs
      if 2 ≤ available ∧ returnCount ≤ available - 2 then
        let repetitions := returnCount + 2
        let budget ← debitProduct budget inputCount ports
        let inputWork := inputCount * ports
        let budget ← debitProduct budget inputWork repetitions
        let budget ← debitProduct budget count ports
        let matrixSize := count * ports
        let budget ← debitProduct budget matrixSize ports
        let returnSize := matrixSize * ports
        let budget ← debitProduct budget matrixSize repetitions
        let budget ← debitProduct budget returnSize repetitions
        let budget ← debitProduct budget count repetitions
        let budget ← debitProduct budget ports repetitions
        let hasFrames := (List.finRange count).any (fun site ↦ state.frameSites[site])
        let callee := { state with
          frameSites := Vector.ofFn (fun site ↦ decide (continuation = site) || state.frameSites[site])
          innerSites := Vector.ofFn (fun site ↦ (hasFrames && decide (continuation = site)) || state.innerSites[site])
          outerReturns := Vector.ofFn (fun site ↦ Vector.ofFn (fun port ↦
            (!hasFrames && decide (continuation = site ∧ returnTarget = port)) || state.outerReturns[site][port]))
          frameDependencies := Vector.ofFn (fun site ↦ Vector.ofFn (fun port ↦
            (decide (continuation = site ∧ returnTarget ≠ port) && state.dependencies[port]) ||
              state.frameDependencies[site][port]))
          frameLive := Vector.ofFn (fun port ↦ state.dependencies[port] || state.frameLive[port])
          frameReturns := Vector.ofFn (fun site ↦ Vector.ofFn (fun target ↦ Vector.ofFn (fun source ↦
            decide (continuation = site ∧ returnTarget = target ∧ returnSource = source) ||
              state.frameReturns[site][target][source]))) }
        let budget ← Region.debit budget returnCount
        let budget ← debitProduct budget returnCount ports
        let budget ← Region.debit budget 2
        let budget ← repeatFramePreflight calls fuel callee repetitions budget
        let budget ← repeatFramePreflight calls fuel state returnCount budget
        pure (repetitions, budget)
      else none
  | .receive .. => do
      let budget ← Region.debit budget ports
      let budget ← Region.debit budget 5
      let budget ← repeatFramePreflight calls fuel state 5 budget
      pure (5, budget)
  | .branch .. => do
      let budget ← Region.debit budget 3
      let budget ← repeatFramePreflight calls fuel state 3 budget
      pure (3, budget)
  | .endReply .. | .endResult .. | .otherResult .. => do
      let budget ← Region.debit budget ports
      let budget ← Region.debit budget 2
      let budget ← repeatFramePreflight calls fuel state 2 budget
      pure (2, budget)
  | .matchEnd .. => do
      let budget ← Region.debit budget count
      let budget ← Region.debit budget 3
      let budget ← repeatFramePreflight calls fuel state 3 budget
      pure (3, budget)
  | .unsupported => do
      let budget ← Region.debit budget count
      let budget ← repeatFramePreflight calls fuel state count budget
      pure (count + 1, budget)
  | .returnNode .. | .stop | .finishReceive => do
      let budget ← Region.debit budget 1
      pure (1, budget)

/-- Charge all configurations and bound counts before adding them. -/
def configurationsPreflight {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (fuel : Nat) (returns : List (ReturnPair count ports)) (limit : Nat) :
    List (Configuration count ports) → Nat → Nat → Option (Nat × Nat)
  | [], total, budget => some (total, budget)
  | configuration :: rest, total, budget => do
      let (size, budget) ← configurationPreflight calls regions checked fuel returns configuration budget
      if total ≤ limit ∧ size ≤ limit - total then
        configurationsPreflight calls regions checked fuel returns limit rest (total + size) budget
      else none

/-- Precharge quadratic full-context comparisons before deduplication or closure validation. -/
def revisionPreflight {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (fuel budget : Nat) (configurations : List (Configuration count ports)) (returns : List (ReturnPair count ports)) : Option Nat := do
  let (configCount, remaining) ← Region.countCells budget configurations
  let (returnCount, remaining) ← Region.countCells remaining returns
  let (generated, remaining) ← configurationsPreflight calls regions checked fuel returns budget configurations 0 remaining
  if generated ≤ budget - configCount ∧ returnCount ≤ budget - configCount then
    let configBound := configCount + generated
    let returnBound := configCount + returnCount
    let remaining ← debitProduct remaining count ports
    let matrixSize := count * ports
    let remaining ← debitProduct remaining matrixSize ports
    let returnSize := matrixSize * ports
    if count ≤ remaining ∧ ports ≤ remaining - count ∧
        matrixSize ≤ remaining - count - ports ∧
        returnSize ≤ remaining - count - ports - matrixSize ∧
        24 ≤ remaining - count - ports - matrixSize - returnSize then
      let halfWidth := count + ports + matrixSize + returnSize + 24
      if halfWidth ≤ remaining / 2 then
        let width := halfWidth * 2
        let remaining ← Region.debit remaining width
        let remaining ← debitProduct remaining configBound configBound
        let remaining ← debitProduct remaining (configBound * configBound) width
        let remaining ← debitProduct remaining returnBound returnBound
        debitProduct remaining (returnBound * returnBound) width
      else none
    else none
  else none

/-- New pairs are observed from already reached returns; successor growth uses the prior revision. -/
def revise {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool) (regionFuel : Nat)
    (configurations : List (Configuration count ports)) (returns : List (ReturnPair count ports)) :
    List (Configuration count ports) × List (ReturnPair count ports) :=
  let learned := configurations.filterMap (observedReturn calls)
  let successors := configurations.flatMap (configurationSuccessors calls regions checked regionFuel returns)
  ((configurations ++ successors).eraseDups, (returns ++ learned).eraseDups)

/-- Every reachable normal configuration must be admitted; failure remains terminal. -/
def configurationAdmitted {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (fuel : Nat) (configuration : Configuration count ports) : Bool :=
  let s := configuration.current
  if s.terminal then true else if s.tainted || !s.compatible || decide (s.fact = .invalid) then false else
  match calls s.control with
  | .call .. =>
      match callEntry calls fuel s with
      | some entry => !s.escape && entry.suffixSafe && entry.compatible
      | none => false
  | .returnNode value =>
      match s.fact with
      | .endPending _ _ | .invalid => false
      | .endFact _ _ => !s.escape && s.suffixSafe && !s.dependencies[value]
      | _ => !s.escape && s.suffixSafe
  | _ => localAdmitted calls regions checked fuel s

/-- Budget is charged before each complete replay; exhaustion yields no summary. -/
def solve {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool) (regionFuel : Nat) :
    Nat → Nat → List (Configuration count ports) → List (ReturnPair count ports) →
      Option (List (Configuration count ports) × List (ReturnPair count ports))
  | 0, _, _, _ => none
  | fuel + 1, budget, configurations, returns =>
      match revisionPreflight calls regions checked regionFuel budget configurations returns with
      | none => none
      | some remaining =>
          let revised := revise calls regions checked regionFuel configurations returns
          if revised.1 = configurations ∧ revised.2 = returns then
            if configurations.all (configurationAdmitted calls regions checked regionFuel) then some revised else none
          else solve calls regions checked regionFuel fuel remaining revised.1 revised.2

/-- A published solution is a final replay closure and admits all reached nodes. -/
theorem solve_closed {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel fuel budget : Nat) (configurations : List (Configuration count ports))
    (returns : List (ReturnPair count ports))
    (answer : List (Configuration count ports) × List (ReturnPair count ports))
    (result : solve calls regions checked regionFuel fuel budget configurations returns = some answer) :
    revise calls regions checked regionFuel answer.1 answer.2 = answer ∧
      answer.1.all (configurationAdmitted calls regions checked regionFuel) = true := by
  induction fuel generalizing budget configurations returns with
  | zero => simp [solve] at result
  | succ fuel ih =>
      simp only [solve] at result
      cases preflight : revisionPreflight calls regions checked regionFuel budget configurations returns with
      | none => simp [preflight] at result
      | some remaining =>
        simp only [preflight] at result
        split at result
        next fixed =>
          split at result
          next admitted =>
            have stable : revise calls regions checked regionFuel configurations returns =
                (configurations, returns) := Prod.ext fixed.1 fixed.2
            rw [stable] at result
            simp only [Option.some.injEq] at result
            subst answer
            exact ⟨stable, admitted⟩
          next rejected => contradiction
        next changed => exact ih _ _ _ result

/-- Revision never discards a reached full-context configuration. -/
theorem revise_preserves_configuration {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel : Nat) (configurations : List (Configuration count ports))
    (returns : List (ReturnPair count ports)) (current : Configuration count ports)
    (present : current ∈ configurations) :
    current ∈ (revise calls regions checked regionFuel configurations returns).1 := by
  simp [revise, present]

/-- A published solution retains every configuration supplied to the solver. -/
theorem solve_preserves_configuration {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel fuel budget : Nat) (configurations : List (Configuration count ports))
    (returns : List (ReturnPair count ports))
    (answer : List (Configuration count ports) × List (ReturnPair count ports))
    (result : solve calls regions checked regionFuel fuel budget configurations returns = some answer)
    (current : Configuration count ports) (present : current ∈ configurations) : current ∈ answer.1 := by
  induction fuel generalizing budget configurations returns with
  | zero => simp [solve] at result
  | succ fuel ih =>
      simp only [solve] at result
      cases preflight : revisionPreflight calls regions checked regionFuel budget configurations returns with
      | none => simp [preflight] at result
      | some remaining =>
        simp only [preflight] at result
        split at result
        next fixed =>
          split at result
          next admitted =>
            have stable : revise calls regions checked regionFuel configurations returns =
                (configurations, returns) := Prod.ext fixed.1 fixed.2
            rw [stable] at result
            simp only [Option.some.injEq] at result
            subst answer
            exact present
          next rejected => contradiction
        next changed =>
          exact ih _ _ _ result (revise_preserves_configuration calls regions checked regionFuel
            configurations returns current present)

/-- Final closure includes every enumerated successor and every observed return. -/
theorem solved_replays {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel fuel budget : Nat) (configurations : List (Configuration count ports))
    (returns : List (ReturnPair count ports))
    (answer : List (Configuration count ports) × List (ReturnPair count ports))
    (result : solve calls regions checked regionFuel fuel budget configurations returns = some answer) :
    (∀ current, current ∈ answer.1 → ∀ next,
      next ∈ configurationSuccessors calls regions checked regionFuel answer.2 current → next ∈ answer.1) ∧
    (∀ current, current ∈ answer.1 → ∀ pair,
      observedReturn calls current = some pair → pair ∈ answer.2) := by
  obtain ⟨closed, _⟩ := solve_closed calls regions checked regionFuel fuel budget configurations returns answer result
  constructor
  · intro current present next edge
    have member : next ∈ (revise calls regions checked regionFuel answer.1 answer.2).1 := by
      simp only [revise, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨current, present, edge⟩
    simpa [closed] using member
  · intro current present pair observed
    have member : pair ∈ (revise calls regions checked regionFuel answer.1 answer.2).2 := by
      simp only [revise, List.mem_eraseDups, List.mem_append, List.mem_filterMap]
      exact Or.inr ⟨current, present, observed⟩
    simpa [closed] using member

/-- Every closed relation containing the seed also contains every learned fact. -/
theorem solve_least {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel fuel budget : Nat) (configurations : List (Configuration count ports))
    (returns : List (ReturnPair count ports))
    (answer : List (Configuration count ports) × List (ReturnPair count ports))
    (result : solve calls regions checked regionFuel fuel budget configurations returns = some answer)
    (configClosed : Configuration count ports → Prop) (returnClosed : ReturnPair count ports → Prop)
    (initialConfigs : ∀ current, current ∈ configurations → configClosed current)
    (initialReturns : ∀ pair, pair ∈ returns → returnClosed pair)
    (successorsClosed : ∀ current, configClosed current → ∀ known,
      (∀ pair, pair ∈ known → returnClosed pair) → ∀ next,
      next ∈ configurationSuccessors calls regions checked regionFuel known current → configClosed next)
    (returnsClosed : ∀ current, configClosed current → ∀ pair,
      observedReturn calls current = some pair → returnClosed pair) :
    (∀ current, current ∈ answer.1 → configClosed current) ∧
      (∀ pair, pair ∈ answer.2 → returnClosed pair) := by
  induction fuel generalizing budget configurations returns with
  | zero => simp [solve] at result
  | succ fuel ih =>
      simp only [solve] at result
      cases preflight : revisionPreflight calls regions checked regionFuel budget configurations returns with
      | none => simp [preflight] at result
      | some remaining =>
        simp only [preflight] at result
        split at result
        next fixed =>
          split at result
          next admitted =>
            have stable : revise calls regions checked regionFuel configurations returns =
                (configurations, returns) := Prod.ext fixed.1 fixed.2
            rw [stable] at result
            simp only [Option.some.injEq] at result
            subst answer
            exact ⟨initialConfigs, initialReturns⟩
          next rejected => contradiction
        next changed =>
          have configNext : ∀ current, current ∈ (revise calls regions checked regionFuel configurations returns).1 →
              configClosed current := by
            intro current member
            simp only [revise, List.mem_eraseDups, List.mem_append, List.mem_flatMap] at member
            rcases member with old | ⟨previous, present, edge⟩
            · exact initialConfigs current old
            · exact successorsClosed previous (initialConfigs previous present) returns initialReturns current edge
          have returnNext : ∀ pair, pair ∈ (revise calls regions checked regionFuel configurations returns).2 →
              returnClosed pair := by
            intro pair member
            simp only [revise, List.mem_eraseDups, List.mem_append, List.mem_filterMap] at member
            rcases member with old | ⟨current, present, observed⟩
            · exact initialReturns pair old
            · exact returnsClosed current (initialConfigs current present) pair observed
          exact ih _ _ _ result configNext returnNext

/-- The only public seed has no pre-existing return pair. -/
def solveFrom {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel fuel budget : Nat) (seed : State count ports) :
    Option (List (Configuration count ports) × List (ReturnPair count ports)) :=
  if seed.fact = .none ∧ !seed.pending ∧ !seed.terminal ∧ !seed.tainted then
    solve calls regions checked regionFuel fuel budget [⟨seed, seed⟩] []
  else none

/-- An accepted solve contains its real seed and is closed under every replayed edge. -/
theorem solveFrom_certified {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel fuel budget : Nat) (seed : State count ports)
    (answer : List (Configuration count ports) × List (ReturnPair count ports))
    (result : solveFrom calls regions checked regionFuel fuel budget seed = some answer) :
    (⟨seed, seed⟩ : Configuration count ports) ∈ answer.1 ∧
      (∀ current, current ∈ answer.1 → configurationAdmitted calls regions checked regionFuel current = true) ∧
      (∀ current, current ∈ answer.1 → ∀ next,
        next ∈ configurationSuccessors calls regions checked regionFuel answer.2 current → next ∈ answer.1) ∧
      (∀ current, current ∈ answer.1 → ∀ pair,
        observedReturn calls current = some pair → pair ∈ answer.2) := by
  unfold solveFrom at result
  split at result
  next valid =>
    have initial : (⟨seed, seed⟩ : Configuration count ports) ∈ [⟨seed, seed⟩] := by simp
    have present := solve_preserves_configuration calls regions checked regionFuel fuel budget
      [⟨seed, seed⟩] [] answer result ⟨seed, seed⟩ initial
    have closed := solve_closed calls regions checked regionFuel fuel budget [⟨seed, seed⟩] [] answer result
    have replay := solved_replays calls regions checked regionFuel fuel budget [⟨seed, seed⟩] [] answer result
    exact ⟨present, fun current member ↦ (List.all_eq_true.mp closed.2) current member, replay.1, replay.2⟩
  next invalid => contradiction

/-- If the reachable fragment has no base return, recursion alone learns none. -/
theorem solveFrom_no_base_returns {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel fuel budget : Nat) (seed : State count ports)
    (answer : List (Configuration count ports) × List (ReturnPair count ports))
    (result : solveFrom calls regions checked regionFuel fuel budget seed = some answer)
    (reachable : Configuration count ports → Prop) (seedReachable : reachable ⟨seed, seed⟩)
    (noBase : ∀ current, reachable current → ∀ pair, observedReturn calls current ≠ some pair)
    (closed : ∀ current, reachable current → ∀ next,
      next ∈ configurationSuccessors calls regions checked regionFuel [] current → reachable next) :
    answer.2 = [] := by
  unfold solveFrom at result
  split at result
  next valid =>
    have least := solve_least calls regions checked regionFuel fuel budget [⟨seed, seed⟩] [] answer result
      reachable (fun _ ↦ False)
      (by intro current member; simp only [List.mem_singleton] at member; subst current; exact seedReachable)
      (by intro pair member; simp at member)
      (by
        intro current currentReachable known absent next edge
        have empty : known = [] := by
          cases known with
          | nil => rfl
          | cons first rest => exact False.elim (absent first (by simp))
        subst known
        exact closed current currentReachable next edge)
      (by intro current currentReachable pair observed; exact (noBase current currentReachable pair) observed)
    cases h : answer.2 with
    | nil => rfl
    | cons first rest =>
        have impossible := least.2 first (by rw [h]; simp)
        exact False.elim impossible
  next invalid => contradiction

end Analysis

/-- The selected network Store at each point in the checked region. -/
def stageNetwork (network : Network) (lane : Worker) (capture : Capture) (consumer : Consumer) :
    Region.Stage → Network
  | .processing => network
  | .cleanupRunning =>
      setStore network lane.peer (runningStore (network.stores lane.peer) capture consumer)
  | .cleanupReturned =>
      let first := setStore network lane.peer
        (runningStore (network.stores lane.peer) capture consumer)
      setStore first lane.peer (finishedStore (network.stores lane.peer) capture consumer)


/-- The exact Network successor after the checked marker finishes this entry. -/
def regionFinal (network : Network) (lane : Worker) (entry : Entry) (pre post : List Entry)
    (capture : Capture) (consumer : Consumer) : Network :=
  let second := stageNetwork network lane capture consumer .cleanupReturned
  second.processingFinished lane entry pre post
    (finishStore (second.stores lane.peer) (finishedCapture capture) consumer)

theorem network_trace_trans {first middle last : Network}
    (one : NetworkTrace first middle) (two : NetworkTrace middle last) :
    NetworkTrace first last := by
  induction two with
  | refl => exact one
  | next _ edge ih => exact NetworkTrace.next ih edge

/-- A region successor either stutters or performs the corresponding actual C1 cleanup step. -/
theorem region_step_network {count ports bindings : Nat} {program : Fin count → Region.Node count ports bindings}
    {bindingChecked : Fin bindings → Bool} {stage nextStage : Region.Stage} {pc next : Fin count}
    (network : Network) (lane : Worker) (capture : Capture) (consumer : Consumer)
    (live : network.backing = true) (committed : network.committed = true)
    (networkHealthy : network.failed = false) (running : network.returned lane.peer = false)
    (active : (network.stores lane.peer).active = some (capture, consumer))
    (armed : capture.cleanup = .armed) (noNested : capture.nested = [])
    (healthy : (network.stores lane.peer).failed = false)
    (step : Region.Step program bindingChecked stage pc nextStage next) :
    NetworkTrace (stageNetwork network lane capture consumer stage)
      (stageNetwork network lane capture consumer nextStage) := by
  have c1 := cleanup_then_finish (network.stores lane.peer) capture consumer active armed noNested healthy
  cases step with
  | stutter => exact NetworkTrace.refl _
  | forward => exact NetworkTrace.refl _
  | native => exact NetworkTrace.refl _
  | branchYes => exact NetworkTrace.refl _
  | branchNo => exact NetworkTrace.refl _
  | startCleanup =>
      apply NetworkTrace.next (NetworkTrace.refl network)
      apply NetworkStep.localStep network lane.peer lane.peer []
        (runningStore (network.stores lane.peer) capture consumer)
        live committed networkHealthy rfl running c1.1
      intro c d _ _ impossible
      simp [runningStore] at impossible
  | returnCleanup =>
      let first := setStore network lane.peer
        (runningStore (network.stores lane.peer) capture consumer)
      apply NetworkTrace.next (NetworkTrace.refl first)
      apply NetworkStep.localStep first lane.peer lane.peer []
        (finishedStore (network.stores lane.peer) capture consumer)
      · simpa [first, setStore] using live
      · simpa [first, setStore] using committed
      · simpa [first, setStore] using networkHealthy
      · rfl
      · simpa [first, setStore] using running
      · simpa [first, setStore, putWorker] using c1.2.1
      · intro c d _ _ impossible
        simp [finishedStore] at impossible

/-- Every finite actual modeled region path maps to its corresponding network trace. -/
theorem region_walk_network {count ports bindings : Nat} {program : Fin count → Region.Node count ports bindings}
    {bindingChecked : Fin bindings → Bool} {startStage finishStage : Region.Stage}
    {start finish : Fin count} (network : Network) (lane : Worker) (capture : Capture)
    (consumer : Consumer) (live : network.backing = true) (committed : network.committed = true)
    (networkHealthy : network.failed = false) (running : network.returned lane.peer = false)
    (active : (network.stores lane.peer).active = some (capture, consumer))
    (armed : capture.cleanup = .armed) (noNested : capture.nested = [])
    (healthy : (network.stores lane.peer).failed = false)
    (path : Region.Walk program bindingChecked startStage start finishStage finish) :
    NetworkTrace (stageNetwork network lane capture consumer startStage)
      (stageNetwork network lane capture consumer finishStage) := by
  induction path with
  | refl => exact NetworkTrace.refl _
  | next _ edge ih =>
      exact network_trace_trans ih (region_step_network network lane capture consumer live committed
        networkHealthy running active armed noNested healthy edge)


/-- An unverified processing operation is observable even if no checked walk can finish. -/
def Region.permittedAt {count ports bindings : Nat} (program : Fin count → Region.Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) (stage : Region.Stage) (pc : Fin count) : Bool :=
  match stage, program pc with
  | .processing, .stutter _ => true
  | .processing, .forward _ _ _ => true
  | .processing, .native binding _ => bindingChecked binding
  | .processing, .branch _ _ => true
  | .processing, .startCleanup _ => true
  | .cleanupRunning, .returnCleanup _ => true
  | .cleanupReturned, .marker => true
  | _, _ => false

/-- A checked prefix reaching an unsupported operation invalidates completion evidence. -/
def Region.ReachesUnverified {count ports bindings : Nat} (program : Fin count → Region.Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) (entry : Fin count) : Prop :=
  ∃ stage pc, Region.Walk program bindingChecked .processing entry stage pc ∧
    Region.permittedAt program bindingChecked stage pc = false

/-- A checked region cannot reach an unverified operation on any modeled prefix. -/
theorem Region.checked_excludes_unverified {count ports bindings : Nat}
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel : Nat) (entry : Fin count)
    (accepted : Region.check program bindingChecked fuel .processing entry = true) :
    ¬ Region.ReachesUnverified program bindingChecked entry := by
  intro reached
  obtain ⟨stage, pc, path, unverifiedAt⟩ := reached
  obtain ⟨remaining, checked⟩ := Region.checked_walk path fuel accepted
  cases remaining with
  | zero => simp [Region.check] at checked
  | succ remaining =>
      cases stage <;> cases node : program pc <;>
        simp_all [Region.check, Region.permittedAt]

/-- Control, Network, delivery and external work advance in one concrete state. -/
inductive ExecutionStep {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool) :
    Machine count ports → Machine count ports → Prop where
  | control {before after} (step : Step calls before after) :
      ExecutionStep calls program bindingChecked before after
  | dispatch (s : Machine count ports) (next : Fin count) (graph : List CaptureOp) (entry : Entry) (site : Fin count)
      (template capture : Capture) (consumer : Consumer)
      (node : calls s.pc = .dispatch next graph) (constructed : capture = CapturePlan.build graph entry template)
      (currentDelivery : s.currentDelivery = some ⟨entry, site⟩)
      (live : s.network.backing = true) (committed : s.network.committed = true)
      (networkHealthy : s.network.failed = false) (running : s.network.returned s.key.lane.peer = false)
      (held : entry ∈ (s.network.channels s.key.lane).held)
      (notDispatched : s.network.dispatched s.key.lane.peer entry.id = false)
      (identity : capture.branch = entry.id) (owned : entry.id ∈ capture.owners)
      (noClause : (s.network.stores s.key.lane.peer).clause = none)
      (driver : (s.network.stores s.key.lane.peer).active = none)
      (admission : Admit (s.network.stores s.key.lane.peer) capture)
      (fresh : RootFresh (s.network.stores s.key.lane.peer) capture)
      (unique : CaptureUnique capture)
      (interpretation : consumer.interpretation = (s.network.stores s.key.lane.peer).interpretation)
      (kind : consumer.kind = .root) (openStore : (s.network.stores s.key.lane.peer).closed = false)
      (healthy : (s.network.stores s.key.lane.peer).failed = false) :
      ExecutionStep calls program bindingChecked s { s with
        pc := next
        driverSource := none
        driverReturn := none
        endValues := fun _ ↦ false
        resultCases := fun _ ↦ .unknown
        fact := none
        pendingEnd := none
        network := s.network.dispatch s.key.lane entry capture consumer }
  | processing (s : Machine count ports) (regionEntry next marker : Fin count)
      (entry : Entry) (site : Fin count) (pre post : List Entry) (capture : Capture) (consumer : Consumer)
      (finalDerived : Vector Bool ports)
      (node : calls s.pc = .processing regionEntry next)
      (currentDelivery : s.currentDelivery = some ⟨entry, site⟩)
      (path : Region.DataWalk program bindingChecked .processing regionEntry (Vector.ofFn s.derived)
        .cleanupReturned marker finalDerived)
      (markerNode : program marker = .marker)
      (live : s.network.backing = true) (committed : s.network.committed = true)
      (networkHealthy : s.network.failed = false) (running : s.network.returned s.key.lane.peer = false)
      (found : (s.network.channels s.key.lane).held = pre ++ entry :: post)
      (identity : capture.branch = entry.id) (owned : entry.id ∈ capture.owners)
      (dispatched : s.network.dispatched s.key.lane.peer entry.id = true)
      (active : (s.network.stores s.key.lane.peer).active = some (capture, consumer))
      (armed : capture.cleanup = .armed) (noNested : capture.nested = [])
      (healthy : (s.network.stores s.key.lane.peer).failed = false) :
      ExecutionStep calls program bindingChecked s { s with
        pc := next
        driverSource := none
        driverReturn := none
        endValues := fun _ ↦ false
        resultCases := fun _ ↦ .unknown
        fact := none
        pendingEnd := none
        receiveInfo := .none
        currentDelivery := none
        derived := fun port ↦ finalDerived[port]
        network := regionFinal s.network s.key.lane entry pre post capture consumer }
  | processingUnverified (s : Machine count ports) (regionEntry next : Fin count)
      (network : Network) (external : ExternalWork) (derived : Fin ports → Bool)
      (node : calls s.pc = .processing regionEntry next) (running : s.network.failed = false)
      (unverified : Region.ReachesUnverified program bindingChecked regionEntry)
      (steps : NetworkTrace s.network network) :
      ExecutionStep calls program bindingChecked s { s with
        pc := next
        driverSource := none
        driverReturn := none
        endValues := fun _ ↦ false
        resultCases := fun _ ↦ .unknown
        fact := none
        pendingEnd := none
        receiveInfo := .none
        tainted := true
        network := network
        external := external
        derived := derived }
  | unverifiedDispatch (s : Machine count ports) (next : Fin count) (graph : List CaptureOp)
      (network : Network) (external : ExternalWork) (derived : Fin ports → Bool)
      (node : calls s.pc = .dispatch next graph) (running : s.network.failed = false)
      (rejected : CapturePlan.admitted graph = false) (steps : NetworkTrace s.network network) :
      ExecutionStep calls program bindingChecked s { s with
        pc := next
        driverSource := none
        driverReturn := none
        endValues := fun _ ↦ false
        resultCases := fun _ ↦ .unknown
        fact := none
        pendingEnd := none
        receiveInfo := .none
        tainted := true
        network := network
        external := external
        derived := derived }
  | unverifiedCapture (s : Machine count ports) (regionEntry next : Fin count)
      (entry : Entry) (site : Fin count) (capture : Capture) (consumer : Consumer)
      (network : Network) (external : ExternalWork) (derived : Fin ports → Bool)
      (node : calls s.pc = .processing regionEntry next) (running : s.network.failed = false)
      (delivery : s.currentDelivery = some ⟨entry, site⟩)
      (active : (s.network.stores s.key.lane.peer).active = some (capture, consumer))
      (mismatch : capture.branch ≠ entry.id ∨ entry.id ∉ capture.owners ∨
        capture.cleanup ≠ .armed ∨ capture.nested ≠ [] ∨ consumer.kind ≠ .root)
      (steps : NetworkTrace s.network network) :
      ExecutionStep calls program bindingChecked s { s with
        pc := next
        driverSource := none
        driverReturn := none
        endValues := fun _ ↦ false
        resultCases := fun _ ↦ .unknown
        fact := none
        pendingEnd := none
        receiveInfo := .none
        tainted := true
        network := network
        external := external
        derived := derived }
  | unverified (s : Machine count ports) (network : Network) (external : ExternalWork) (next : Fin count)
      (node : calls s.pc = .unsupported) (running : s.network.failed = false)
      (steps : NetworkTrace s.network network) :
      ExecutionStep calls program bindingChecked s { s with
        pc := next
        driverSource := none
        driverReturn := none
        endValues := fun _ ↦ false
        resultCases := fun _ ↦ .unknown
        fact := none
        pendingEnd := none
        receiveInfo := .none
        tainted := true
        network := network
        external := external }

/-- A structurally admitted dispatch selects the actual C1 root for this held delivery. -/
theorem checked_dispatch_selects_root {count ports : Nat}
    (s : Machine count ports) (graph : List CaptureOp) (entry : Entry) (site : Fin count)
    (template capture : Capture) (consumer : Consumer)
    (delivery : s.currentDelivery = some ⟨entry, site⟩)
    (constructed : capture = CapturePlan.build graph entry template)
    (accepted : CapturePlan.admitted graph = true)
    (admission : Admit (s.network.stores s.key.lane.peer) capture)
    (kind : consumer.kind = .root) :
    Projection.root { s with network := s.network.dispatch s.key.lane entry capture consumer } = .selected site := by
  have shape := CapturePlan.admitted_build_shape graph entry template accepted
  have branch : capture.branch = entry.id := by simpa [constructed] using shape.1
  have armed : capture.cleanup = .armed := by simpa [constructed] using shape.2.1
  have noNested : capture.nested = [] := by simpa [constructed] using shape.2.2
  have owned : entry.id ∈ capture.owners := by simpa [branch] using admission.1
  simp [Projection.root, delivery, Network.dispatch, putWorker, branch, owned, armed, noNested, kind]

/-- An admitted concrete dispatch is an enumerated finite successor. -/
theorem dispatch_successor_is_enumerated {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel : Nat) (s : Machine count ports) (next : Fin count) (graph : List CaptureOp)
    (entry : Entry) (site operation edge : Fin count) (template capture : Capture) (consumer : Consumer)
    (node : calls s.pc = .dispatch next graph) (healthy : s.network.failed = false)
    (delivery : s.currentDelivery = some ⟨entry, site⟩)
    (constructed : capture = CapturePlan.build graph entry template)
    (accepted : CapturePlan.admitted graph = true)
    (admission : Admit (s.network.stores s.key.lane.peer) capture) (kind : consumer.kind = .root)
    (phase : Projection.phase s = .processing site)
    (fact : Projection.fact s = .message operation edge)
    (work : Projection.classifyWork (storeWork s.external (s.network.stores s.key.lane.peer)) = .empty) :
    let before := Analysis.normalize calls fuel (Projection.state calls fuel s)
    let after := { s with
      pc := next
      driverSource := none
      driverReturn := none
      endValues := fun _ ↦ false
      resultCases := fun _ ↦ .unknown
      fact := none
      pendingEnd := none
      network := s.network.dispatch s.key.lane entry capture consumer }
    Analysis.normalize calls fuel (Projection.state calls fuel after) ∈
      (Analysis.localSuccessors calls program bindingChecked fuel before).map (Analysis.normalize calls fuel) := by
  have selected := checked_dispatch_selects_root s graph entry site template capture consumer
    delivery constructed accepted admission kind
  have noOther : (storeWork s.external (s.network.stores s.key.lane.peer)).other = false := by
    have quiet := Projection.classify_work_sound (storeWork s.external (s.network.stores s.key.lane.peer))
    rw [work] at quiet
    exact quiet.2
  have afterWork : Projection.classifyWork
      (storeWork s.external ((s.network.dispatch s.key.lane entry capture consumer).stores s.key.lane.peer)) =
        .activeOnly := by
    simpa [Projection.classifyWork, storeWork, Network.dispatch, putWorker] using noOther
  have afterFact : Projection.fact { s with fact := none, pendingEnd := none } = .message operation edge := by
    cases actual : s.fact with
    | some origin =>
        by_cases same : origin.key = s.key <;> simp [Projection.fact, actual, same] at fact
    | none =>
        cases pending : s.pendingEnd with
        | some origin =>
            by_cases same : origin.key = s.key <;> simp [Projection.fact, actual, pending, same] at fact
        | none => simpa [Projection.fact, actual, pending] using fact
  let after := { s with
    pc := next
    driverSource := none
    driverReturn := none
    endValues := fun _ ↦ false
    resultCases := fun _ ↦ .unknown
    fact := none
    pendingEnd := none
    network := s.network.dispatch s.key.lane entry capture consumer }
  have actualFact : Projection.fact after = .message operation edge := afterFact
  have actualPhase : Projection.phase after = Projection.phase s := rfl
  have actualRoot : Projection.root after = .selected site := selected
  have actualWork : Projection.classifyWork (storeWork after.external (after.network.stores after.key.lane.peer)) =
      .activeOnly := afterWork
  let before := Analysis.normalize calls fuel (Projection.state calls fuel s)
  let candidate := Analysis.refresh { before with
    control := next
    driverSource := none
    driverReturn := none
    endValues := Vector.ofFn fun _ ↦ false
    resultCases := Vector.ofFn fun _ ↦ .unknown
    fact := .message operation edge
    pending := false
    root := .selected site
    work := .activeOnly }
  refine List.mem_map.mpr ⟨candidate, ?_, ?_⟩
  · simp [candidate, before, Analysis.localSuccessors, Analysis.normalize, Analysis.refresh,
      Projection.state, node, healthy, phase, fact, accepted, work, PortCases.Work.enterRoot]
  · simp [candidate, before, Analysis.normalize, Analysis.refresh, Projection.state]
    refine ⟨actualFact.symm, actualPhase.symm, actualRoot.symm, actualWork.symm, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl

/-- Selected root facts name the same actual delivery, branch and consumer. -/
theorem selected_root_matches {count ports : Nat}
    (s : Machine count ports) (entry : Entry) (site : Fin count) (capture : Capture) (consumer : Consumer)
    (delivery : s.currentDelivery = some ⟨entry, site⟩)
    (active : (s.network.stores s.key.lane.peer).active = some (capture, consumer))
    (selected : Projection.root s = .selected site) :
    capture.branch = entry.id ∧ entry.id ∈ capture.owners ∧ capture.cleanup = .armed ∧
      capture.nested = [] ∧ consumer.kind = .root := by
  simp only [Projection.root, delivery, active] at selected
  split at selected
  next matched => exact matched
  next mismatch => contradiction

/-- The actual call push is the solver's exact callee entry, including value snapshots. -/
theorem call_successor_is_enumerated {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat)
    (s : Machine count ports) (target continuation : Fin count) (context : StaticContext count)
    (inputs : List (Fin ports × Fin ports)) (returnSource returnTarget : Fin ports)
    (node : calls s.pc = .call target continuation context inputs returnSource returnTarget)
    (pending : s.pendingEnd = none) (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls fuel (Projection.state calls fuel s)
    let after := { s with
      pc := target
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      context := context
      fact := none
      receiveInfo := .none
      endValues := fun _ ↦ false
      derived := callInputs inputs s.derived
      frames := ⟨s.key, s.pc, target, continuation, s.context, context,
        inputs, returnSource, returnTarget, Vector.ofFn s.derived⟩ :: s.frames }
    Analysis.callEntry calls fuel before = some (Analysis.normalize calls fuel (Projection.state calls fuel after)) := by
  cases frames : s.frames with
  | nil =>
      have emptyAny : (List.finRange count).any (fun _ ↦ false) = false := by
        simp only [List.any_eq_false]
        intro site member
        simp
      simp [Analysis.callEntry, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
        Projection.phase, Projection.root, Projection.frameShape, Analysis.dependencyClosure,
        Analysis.dependencyStep, callInputs, node, pending, healthy, frames, emptyAny]
  | cons head tail =>
      have nonempty : (List.finRange count).any (fun site ↦
          (head :: tail).any (fun frame ↦ decide (frame.continuation = site))) = true := by
        apply List.any_eq_true.mpr
        exact ⟨head.continuation, List.mem_finRange _, by simp⟩
      simp only [List.any_cons] at nonempty
      simp [Analysis.callEntry, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
        Projection.phase, Projection.root, Projection.frameShape, Analysis.dependencyClosure,
        Analysis.dependencyStep, callInputs, node, pending, healthy, frames, nonempty]

/-- A reached concrete call enters its corresponding accepted solver configuration. -/
theorem certified_call_enters {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls regions checked regionFuel solverFuel budget seed = some answer)
    (caller : Machine count ports) (target continuation : Fin count) (context : StaticContext count)
    (inputs : List (Fin ports × Fin ports)) (returnSource returnTarget : Fin ports)
    (node : calls caller.pc = .call target continuation context inputs returnSource returnTarget)
    (pending : caller.pendingEnd = none) (healthy : caller.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
    let callee := { caller with
      pc := target
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      context := context
      fact := none
      receiveInfo := .none
      endValues := fun _ ↦ false
      derived := callInputs inputs caller.derived
      frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
        inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
    let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨entry, entry⟩ : Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro callerSeen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
  let callee := { caller with
    pc := target
    driverSource := none
    driverReturn := none
    resultCases := fun _ ↦ .unknown
    context := context
    fact := none
    receiveInfo := .none
    endValues := fun _ ↦ false
    derived := callInputs inputs caller.derived
    frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
  let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
  have push : Analysis.callEntry calls regionFuel before = some entry :=
    call_successor_is_enumerated calls regionFuel caller target continuation context inputs
      returnSource returnTarget node pending healthy
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have callHere : calls before.control = .call target continuation context inputs returnSource returnTarget := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have edge : (⟨entry, entry⟩ : Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls regions checked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp [Analysis.configurationSuccessors, notTerminal, callHere, push]
  have certified := Analysis.solveFrom_certified calls regions checked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ callerSeen _ edge

/-- A matched dynamic return replays the saved caller with its actual returned value. -/
theorem matched_return_is_enumerated {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat)
    (caller current : Machine count ports) (target continuation : Fin count)
    (context : StaticContext count) (inputs : List (Fin ports × Fin ports))
    (returnSource returnTarget : Fin ports) (fact : EndFact count)
    (callNode : calls caller.pc = .call target continuation context inputs returnSource returnTarget)
    (returnNode : calls current.pc = .returnNode returnSource)
    (callerPending : caller.pendingEnd = none) (callerHealthy : caller.network.failed = false)
    (currentPending : current.pendingEnd = none) (currentHealthy : current.network.failed = false)
    (sameKey : current.key = caller.key) (sameOwner : current.ownerSite = caller.ownerSite)
    (sameContext : current.context = context) (authentic : current.fact = some fact)
    (owner : fact.key = current.key)
    (stack : current.frames = ⟨caller.key, caller.pc, target, continuation, caller.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames) :
    let before := Analysis.normalize calls fuel (Projection.state calls fuel caller)
    let callee := { caller with
      pc := target
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      context := context
      fact := none
      receiveInfo := .none
      endValues := fun _ ↦ false
      derived := callInputs inputs caller.derived
      frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
        inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
    let entry := Analysis.normalize calls fuel (Projection.state calls fuel callee)
    let result := Analysis.normalize calls fuel (Projection.state calls fuel current)
    let pair : Analysis.ReturnPair count ports := ⟨entry, result⟩
    let after := { current with
      pc := continuation
      context := caller.context
      frames := caller.frames
      derived := returnInputs (Vector.ofFn caller.derived) (current.derived returnSource) returnTarget
      endValues := fun port ↦ if port = returnTarget then current.endValues returnSource else false
      resultCases := fun port ↦ if port = returnTarget then current.resultCases returnSource else .unknown
      driverReturn := if caller.frames.isEmpty then some (continuation, returnTarget) else none
      driverSource := none }
    Analysis.resumeCall calls fuel before pair = some (Analysis.normalize calls fuel (Projection.state calls fuel after)) := by
  have push := call_successor_is_enumerated calls fuel caller target continuation context inputs
    returnSource returnTarget callNode callerPending callerHealthy
  have callerControl : calls (Analysis.normalize calls fuel (Projection.state calls fuel caller)).control =
      .call target continuation context inputs returnSource returnTarget := by
    simpa [Analysis.normalize, Analysis.refresh, Projection.state] using callNode
  dsimp only
  unfold Analysis.resumeCall
  rw [callerControl, push]
  simp [Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
    Projection.phase, Projection.root, Analysis.dependencyClosure, Analysis.dependencyStep,
    returnInputs, returnNode, currentPending, currentHealthy, sameKey, sameOwner, sameContext,
    authentic, owner, stack]
  simp only [← List.eq_nil_iff_forall_not_mem]

/-- A normal non-End return also replays its exact caller and result port. -/
theorem normal_return_is_enumerated {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat)
    (caller current : Machine count ports) (target continuation : Fin count)
    (context : StaticContext count) (inputs : List (Fin ports × Fin ports))
    (returnSource returnTarget : Fin ports)
    (callNode : calls caller.pc = .call target continuation context inputs returnSource returnTarget)
    (returnNode : calls current.pc = .returnNode returnSource)
    (callerPending : caller.pendingEnd = none) (callerHealthy : caller.network.failed = false)
    (currentPending : current.pendingEnd = none) (currentHealthy : current.network.failed = false)
    (sameKey : current.key = caller.key) (sameOwner : current.ownerSite = caller.ownerSite)
    (sameContext : current.context = context) (noFact : current.fact = none)
    (stack : current.frames = ⟨caller.key, caller.pc, target, continuation, caller.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames) :
    let before := Analysis.normalize calls fuel (Projection.state calls fuel caller)
    let callee := { caller with
      pc := target
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      context := context
      fact := none
      receiveInfo := .none
      endValues := fun _ ↦ false
      derived := callInputs inputs caller.derived
      frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
        inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
    let entry := Analysis.normalize calls fuel (Projection.state calls fuel callee)
    let result := Analysis.normalize calls fuel (Projection.state calls fuel current)
    let pair : Analysis.ReturnPair count ports := ⟨entry, result⟩
    let after := { current with
      pc := continuation
      context := caller.context
      frames := caller.frames
      fact := none
      pendingEnd := none
      receiveInfo := .none
      derived := returnInputs (Vector.ofFn caller.derived) (current.derived returnSource) returnTarget
      endValues := fun _ ↦ false
      resultCases := fun port ↦ if port = returnTarget then current.resultCases returnSource else .unknown
      driverReturn := if caller.frames.isEmpty then some (continuation, returnTarget) else none
      driverSource := none }
    Analysis.resumeCall calls fuel before pair = some (Analysis.normalize calls fuel (Projection.state calls fuel after)) := by
  have push := call_successor_is_enumerated calls fuel caller target continuation context inputs
    returnSource returnTarget callNode callerPending callerHealthy
  have callerControl : calls (Analysis.normalize calls fuel (Projection.state calls fuel caller)).control =
      .call target continuation context inputs returnSource returnTarget := by
    simpa [Analysis.normalize, Analysis.refresh, Projection.state] using callNode
  dsimp only
  unfold Analysis.resumeCall
  rw [callerControl, push]
  cases info : current.receiveInfo <;>
    simp [Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
      Projection.phase, Projection.root, Analysis.dependencyClosure, Analysis.dependencyStep,
      returnInputs, returnNode, currentPending, currentHealthy, sameKey, sameOwner, sameContext,
      noFact, info, stack, ← List.eq_nil_iff_forall_not_mem]

/-- Final replay includes the exact matched return learned from a reached callee. -/
theorem certified_matched_return_replayed {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls regions checked regionFuel solverFuel budget seed = some answer)
    (caller current : Machine count ports) (target continuation : Fin count)
    (context : StaticContext count) (inputs : List (Fin ports × Fin ports))
    (returnSource returnTarget : Fin ports) (fact : EndFact count)
    (callNode : calls caller.pc = .call target continuation context inputs returnSource returnTarget)
    (returnNode : calls current.pc = .returnNode returnSource)
    (callerPending : caller.pendingEnd = none) (callerHealthy : caller.network.failed = false)
    (currentPending : current.pendingEnd = none) (currentHealthy : current.network.failed = false)
    (sameKey : current.key = caller.key) (sameOwner : current.ownerSite = caller.ownerSite)
    (sameContext : current.context = context) (authentic : current.fact = some fact)
    (owner : fact.key = current.key)
    (stack : current.frames = ⟨caller.key, caller.pc, target, continuation, caller.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
    let callee := { caller with
      pc := target
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      context := context
      fact := none
      receiveInfo := .none
      endValues := fun _ ↦ false
      derived := callInputs inputs caller.derived
      frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
        inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
    let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
    let result := Analysis.normalize calls regionFuel (Projection.state calls regionFuel current)
    let after := { current with
      pc := continuation
      context := caller.context
      frames := caller.frames
      derived := returnInputs (Vector.ofFn caller.derived) (current.derived returnSource) returnTarget
      endValues := fun port ↦ if port = returnTarget then current.endValues returnSource else false
      resultCases := fun port ↦ if port = returnTarget then current.resultCases returnSource else .unknown
      driverReturn := if caller.frames.isEmpty then some (continuation, returnTarget) else none
      driverSource := none }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
    (⟨entry, result⟩ : Analysis.Configuration count ports) ∈ answer.1 →
    (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro callerSeen returnSeen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
  let callee := { caller with
    pc := target
    driverSource := none
    driverReturn := none
    resultCases := fun _ ↦ .unknown
    context := context
    fact := none
    receiveInfo := .none
    endValues := fun _ ↦ false
    derived := callInputs inputs caller.derived
    frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
  let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
  let result := Analysis.normalize calls regionFuel (Projection.state calls regionFuel current)
  let pair : Analysis.ReturnPair count ports := ⟨entry, result⟩
  let after := { current with
    pc := continuation
    context := caller.context
    frames := caller.frames
    derived := returnInputs (Vector.ofFn caller.derived) (current.derived returnSource) returnTarget
    endValues := fun port ↦ if port = returnTarget then current.endValues returnSource else false
    resultCases := fun port ↦ if port = returnTarget then current.resultCases returnSource else .unknown
    driverReturn := if caller.frames.isEmpty then some (continuation, returnTarget) else none
    driverSource := none }
  have push : Analysis.callEntry calls regionFuel before = some entry :=
    call_successor_is_enumerated calls regionFuel caller target continuation context inputs
      returnSource returnTarget callNode callerPending callerHealthy
  have resumed : Analysis.resumeCall calls regionFuel before pair =
      some (Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)) :=
    matched_return_is_enumerated calls regionFuel caller current target continuation context inputs
      returnSource returnTarget fact callNode returnNode callerPending callerHealthy currentPending currentHealthy
      sameKey sameOwner sameContext authentic owner stack
  have observed : Analysis.observedReturn calls ⟨entry, result⟩ = some pair := by
    simp [Analysis.observedReturn, result, Analysis.normalize, Analysis.refresh, Projection.state,
      Projection.fact, returnNode, currentHealthy, authentic, owner, pair]
  have certified := Analysis.solveFrom_certified calls regions checked regionFuel solverFuel budget seed answer accepted
  have learned : pair ∈ answer.2 := certified.2.2.2 ⟨entry, result⟩ returnSeen pair observed
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls regions checked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    have notTerminal : before.terminal = false := by
      simp [before, Analysis.normalize, Analysis.refresh, Projection.state, callerHealthy]
    have callHere : calls before.control = .call target continuation context inputs returnSource returnTarget := by
      simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using callNode
    simp only [Analysis.configurationSuccessors, notTerminal, Bool.false_eq_true, if_false, callHere, push]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    right
    apply List.mem_filterMap.mpr
    exact ⟨pair, learned, by simp [resumed]⟩
  exact certified.2.2.1 ⟨parentEntry, before⟩ callerSeen _ edge

/-- A reached normal non-End return is replayed to its actual caller. -/
theorem certified_normal_return_replayed {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (regions : Fin count → Region.Node count ports bindings) (checked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls regions checked regionFuel solverFuel budget seed = some answer)
    (caller current : Machine count ports) (target continuation : Fin count)
    (context : StaticContext count) (inputs : List (Fin ports × Fin ports))
    (returnSource returnTarget : Fin ports)
    (callNode : calls caller.pc = .call target continuation context inputs returnSource returnTarget)
    (returnNode : calls current.pc = .returnNode returnSource)
    (callerPending : caller.pendingEnd = none) (callerHealthy : caller.network.failed = false)
    (currentPending : current.pendingEnd = none) (currentHealthy : current.network.failed = false)
    (sameKey : current.key = caller.key) (sameOwner : current.ownerSite = caller.ownerSite)
    (sameContext : current.context = context) (noFact : current.fact = none)
    (stack : current.frames = ⟨caller.key, caller.pc, target, continuation, caller.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
    let callee := { caller with
      pc := target
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      context := context
      fact := none
      receiveInfo := .none
      endValues := fun _ ↦ false
      derived := callInputs inputs caller.derived
      frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
        inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
    let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
    let result := Analysis.normalize calls regionFuel (Projection.state calls regionFuel current)
    let after := { current with
      pc := continuation
      context := caller.context
      frames := caller.frames
      fact := none
      pendingEnd := none
      receiveInfo := .none
      derived := returnInputs (Vector.ofFn caller.derived) (current.derived returnSource) returnTarget
      endValues := fun _ ↦ false
      resultCases := fun port ↦ if port = returnTarget then current.resultCases returnSource else .unknown
      driverReturn := if caller.frames.isEmpty then some (continuation, returnTarget) else none
      driverSource := none }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
    (⟨entry, result⟩ : Analysis.Configuration count ports) ∈ answer.1 →
    (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro callerSeen returnSeen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
  let callee := { caller with
    pc := target
    driverSource := none
    driverReturn := none
    resultCases := fun _ ↦ .unknown
    context := context
    fact := none
    receiveInfo := .none
    endValues := fun _ ↦ false
    derived := callInputs inputs caller.derived
    frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
  let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
  let result := Analysis.normalize calls regionFuel (Projection.state calls regionFuel current)
  let pair : Analysis.ReturnPair count ports := ⟨entry, result⟩
  let after := { current with
    pc := continuation
    context := caller.context
    frames := caller.frames
    fact := none
    pendingEnd := none
    receiveInfo := .none
    derived := returnInputs (Vector.ofFn caller.derived) (current.derived returnSource) returnTarget
    endValues := fun _ ↦ false
    resultCases := fun port ↦ if port = returnTarget then current.resultCases returnSource else .unknown
    driverReturn := if caller.frames.isEmpty then some (continuation, returnTarget) else none
    driverSource := none }
  have push : Analysis.callEntry calls regionFuel before = some entry :=
    call_successor_is_enumerated calls regionFuel caller target continuation context inputs
      returnSource returnTarget callNode callerPending callerHealthy
  have resumed : Analysis.resumeCall calls regionFuel before pair =
      some (Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)) :=
    normal_return_is_enumerated calls regionFuel caller current target continuation context inputs
      returnSource returnTarget callNode returnNode callerPending callerHealthy currentPending currentHealthy
      sameKey sameOwner sameContext noFact stack
  have observed : Analysis.observedReturn calls ⟨entry, result⟩ = some pair := by
    cases info : current.receiveInfo <;>
      simp [Analysis.observedReturn, result, Analysis.normalize, Analysis.refresh, Projection.state,
        Projection.fact, returnNode, currentHealthy, noFact, currentPending, info, pair]
  have certified := Analysis.solveFrom_certified calls regions checked regionFuel solverFuel budget seed answer accepted
  have learned : pair ∈ answer.2 := certified.2.2.2 ⟨entry, result⟩ returnSeen pair observed
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls regions checked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    have notTerminal : before.terminal = false := by
      simp [before, Analysis.normalize, Analysis.refresh, Projection.state, callerHealthy]
    have callHere : calls before.control = .call target continuation context inputs returnSource returnTarget := by
      simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using callNode
    simp only [Analysis.configurationSuccessors, notTerminal, Bool.false_eq_true, if_false, callHere, push]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    right
    apply List.mem_filterMap.mpr
    exact ⟨pair, learned, by simp [resumed]⟩
  exact certified.2.2.1 ⟨parentEntry, before⟩ callerSeen _ edge

/-- A reached callee cannot return a different value port to its reached caller. -/
theorem certified_return_matches {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (caller current : Machine count ports) (target continuation : Fin count)
    (context : StaticContext count) (inputs : List (Fin ports × Fin ports))
    (returnSource returnTarget value : Fin ports) (fact : EndFact count)
    (callNode : calls caller.pc = .call target continuation context inputs returnSource returnTarget)
    (returnNode : calls current.pc = .returnNode value)
    (callerPending : caller.pendingEnd = none) (callerHealthy : caller.network.failed = false)
    (currentHealthy : current.network.failed = false) (sameContext : current.context = context)
    (authentic : current.fact = some fact) (owner : fact.key = current.key) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
    let callee := { caller with
      pc := target
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      context := context
      fact := none
      receiveInfo := .none
      endValues := fun _ ↦ false
      derived := callInputs inputs caller.derived
      frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
        inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
    let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
    let result := Analysis.normalize calls regionFuel (Projection.state calls regionFuel current)
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
    (⟨entry, result⟩ : Analysis.Configuration count ports) ∈ answer.1 → value = returnSource := by
  dsimp only
  intro callerSeen returnSeen
  apply Classical.byContradiction
  intro mismatch
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
  let callee := { caller with
    pc := target
    driverSource := none
    driverReturn := none
    resultCases := fun _ ↦ .unknown
    context := context
    fact := none
    receiveInfo := .none
    endValues := fun _ ↦ false
    derived := callInputs inputs caller.derived
    frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
  let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
  let result := Analysis.normalize calls regionFuel (Projection.state calls regionFuel current)
  let pair : Analysis.ReturnPair count ports := ⟨entry, result⟩
  let bad := Analysis.normalize calls regionFuel { result with
    control := continuation
    context := before.context
    fact := .none
    tainted := true
    driverSource := none
    driverReturn := none
    endValues := Vector.ofFn fun _ ↦ false
    resultCases := Vector.ofFn fun _ ↦ .unknown
    compatible := before.compatible
    dependencies := result.dependencies
    frameSites := before.frameSites
    innerSites := before.innerSites
    outerReturns := before.outerReturns
    frameDependencies := before.frameDependencies
    frameLive := before.frameLive
    frameReturns := before.frameReturns
    framesValid := before.framesValid }
  have push : Analysis.callEntry calls regionFuel before = some entry :=
    call_successor_is_enumerated calls regionFuel caller target continuation context inputs
      returnSource returnTarget callNode callerPending callerHealthy
  have callHere : calls before.control = .call target continuation context inputs returnSource returnTarget := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using callNode
  have observed : Analysis.observedReturn calls ⟨entry, result⟩ = some pair := by
    simp [Analysis.observedReturn, result, Analysis.normalize, Analysis.refresh, Projection.state,
      Projection.fact, returnNode, currentHealthy, authentic, owner, pair]
  have resumed : Analysis.resumeCall calls regionFuel before pair = some bad := by
    simp [Analysis.resumeCall, callHere, push, pair, entry, result, bad, Analysis.normalize,
      Analysis.refresh, Projection.state, Projection.fact, currentHealthy, sameContext, authentic,
      owner, returnNode, mismatch]
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have learned : pair ∈ answer.2 := certified.2.2.2 ⟨entry, result⟩ returnSeen pair observed
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, callerHealthy]
  have edge : (⟨parentEntry, bad⟩ : Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, notTerminal, Bool.false_eq_true, if_false, callHere, push]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    right
    apply List.mem_filterMap.mpr
    exact ⟨pair, learned, by simp [resumed]⟩
  have badSeen := certified.2.2.1 ⟨parentEntry, before⟩ callerSeen _ edge
  have badAdmitted := certified.2.1 ⟨parentEntry, bad⟩ badSeen
  simp [Analysis.configurationAdmitted, bad, result, Analysis.normalize, Analysis.refresh,
    Projection.state, currentHealthy] at badAdmitted

/-- A reached non-End callee cannot return a different port either. -/
theorem certified_normal_return_matches {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (caller current : Machine count ports) (target continuation : Fin count)
    (context : StaticContext count) (inputs : List (Fin ports × Fin ports))
    (returnSource returnTarget value : Fin ports)
    (callNode : calls caller.pc = .call target continuation context inputs returnSource returnTarget)
    (returnNode : calls current.pc = .returnNode value)
    (callerPending : caller.pendingEnd = none) (callerHealthy : caller.network.failed = false)
    (currentHealthy : current.network.failed = false) (currentPending : current.pendingEnd = none)
    (sameContext : current.context = context) (noFact : current.fact = none) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
    let callee := { caller with
      pc := target
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      context := context
      fact := none
      receiveInfo := .none
      endValues := fun _ ↦ false
      derived := callInputs inputs caller.derived
      frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
        inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
    let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
    let result := Analysis.normalize calls regionFuel (Projection.state calls regionFuel current)
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
    (⟨entry, result⟩ : Analysis.Configuration count ports) ∈ answer.1 → value = returnSource := by
  dsimp only
  intro callerSeen returnSeen
  apply Classical.byContradiction
  intro mismatch
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel caller)
  let callee := { caller with
    pc := target
    driverSource := none
    driverReturn := none
    resultCases := fun _ ↦ .unknown
    context := context
    fact := none
    receiveInfo := .none
    endValues := fun _ ↦ false
    derived := callInputs inputs caller.derived
    frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }
  let entry := Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee)
  let result := Analysis.normalize calls regionFuel (Projection.state calls regionFuel current)
  let pair : Analysis.ReturnPair count ports := ⟨entry, result⟩
  let bad := Analysis.normalize calls regionFuel { result with
    control := continuation
    context := before.context
    fact := .none
    tainted := true
    driverSource := none
    driverReturn := none
    endValues := Vector.ofFn fun _ ↦ false
    resultCases := Vector.ofFn fun _ ↦ .unknown
    compatible := before.compatible
    dependencies := result.dependencies
    frameSites := before.frameSites
    innerSites := before.innerSites
    outerReturns := before.outerReturns
    frameDependencies := before.frameDependencies
    frameLive := before.frameLive
    frameReturns := before.frameReturns
    framesValid := before.framesValid }
  have push : Analysis.callEntry calls regionFuel before = some entry :=
    call_successor_is_enumerated calls regionFuel caller target continuation context inputs
      returnSource returnTarget callNode callerPending callerHealthy
  have callHere : calls before.control = .call target continuation context inputs returnSource returnTarget := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using callNode
  have observed : Analysis.observedReturn calls ⟨entry, result⟩ = some pair := by
    cases info : current.receiveInfo <;>
      simp [Analysis.observedReturn, result, Analysis.normalize, Analysis.refresh, Projection.state,
        Projection.fact, returnNode, currentHealthy, currentPending, noFact, info, pair]
  have resumed : Analysis.resumeCall calls regionFuel before pair = some bad := by
    cases info : current.receiveInfo <;>
      simp [Analysis.resumeCall, callHere, push, pair, entry, result, bad, Analysis.normalize,
        Analysis.refresh, Projection.state, Projection.fact, currentHealthy, currentPending, sameContext,
        noFact, info, returnNode, mismatch]
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have learned : pair ∈ answer.2 := certified.2.2.2 ⟨entry, result⟩ returnSeen pair observed
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, callerHealthy]
  have edge : (⟨parentEntry, bad⟩ : Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, notTerminal, Bool.false_eq_true, if_false, callHere, push]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    right
    apply List.mem_filterMap.mpr
    exact ⟨pair, learned, by simp [resumed]⟩
  have badSeen := certified.2.2.1 ⟨parentEntry, before⟩ callerSeen _ edge
  have badAdmitted := certified.2.1 ⟨parentEntry, bad⟩ badSeen
  simp [Analysis.configurationAdmitted, bad, result, Analysis.normalize, Analysis.refresh,
    Projection.state, currentHealthy] at badAdmitted

/-- Processing removes the selected held entry and empties this same Store. -/
theorem checked_processing_projection {count ports : Nat}
    (s : Machine count ports) (entry : Entry) (site : Fin count) (pre post : List Entry)
    (capture : Capture) (consumer : Consumer) (finalDerived : Vector Bool ports)
    (delivery : s.currentDelivery = some ⟨entry, site⟩)
    (processing : Projection.phase s = .processing site)
    (selected : Projection.root s = .selected site)
    (found : (s.network.channels s.key.lane).held = pre ++ entry :: post)
    (active : (s.network.stores s.key.lane.peer).active = some (capture, consumer))
    (work : Projection.classifyWork (storeWork s.external (s.network.stores s.key.lane.peer)) = .activeOnly) :
    let after : Machine count ports := { s with
      currentDelivery := none
      derived := fun port ↦ finalDerived[port]
      network := regionFinal s.network s.key.lane entry pre post capture consumer }
    Projection.phase after = .clear ∧ Projection.root after = .idle ∧
      Projection.classifyWork (storeWork after.external (after.network.stores after.key.lane.peer)) = .empty ∧
      capture.branch = entry.id ∧ entry.id ∈ capture.owners ∧ capture.cleanup = .armed ∧
      capture.nested = [] ∧ consumer.kind = .root := by
  have identity := selected_root_matches s entry site capture consumer delivery active selected
  have singleton : (s.network.channels s.key.lane).held = [entry] := by
    simp only [Projection.phase, delivery] at processing
    split at processing
    next held => exact held
    next different => contradiction
  have lengths := congrArg List.length (found.symm.trans singleton)
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  have preEmpty : pre = [] := by
    apply List.eq_nil_of_length_eq_zero
    omega
  have postEmpty : post = [] := by
    apply List.eq_nil_of_length_eq_zero
    omega
  have activeWork := Projection.classify_work_sound (storeWork s.external (s.network.stores s.key.lane.peer))
  rw [work] at activeWork
  have quiet := finished_active_only_is_quiet (storeWork s.external (s.network.stores s.key.lane.peer)) activeWork
  have finalQuiet : PortCases.Work.empty.allows
      (storeWork s.external ((regionFinal s.network s.key.lane entry pre post capture consumer).stores s.key.lane.peer)) := by
    simpa [regionFinal, Network.processingFinished, putWorker, stageNetwork, setStore,
      finishStore, storeWork, finishedStore, PortCases.ConcreteWork.finishRoot] using quiet
  have finalClass : Projection.classifyWork
      (storeWork s.external ((regionFinal s.network s.key.lane entry pre post capture consumer).stores s.key.lane.peer)) = .empty := by
    cases result : storeWork s.external ((regionFinal s.network s.key.lane entry pre post capture consumer).stores s.key.lane.peer) with
    | mk active other => cases active <;> cases other <;> simp_all [PortCases.Work.allows, Projection.classifyWork]
  refine ⟨?_, ?_, finalClass, identity⟩
  · simp [Projection.phase, regionFinal, Network.processingFinished, finishChannel, putWorker,
      stageNetwork, setStore, preEmpty, postEmpty]
  · simp [Projection.root, regionFinal, Network.processingFinished, putWorker, finishStore]

/-- The actual checked processing successor is among the solver's region outputs. -/
theorem processing_successor_is_enumerated {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel : Nat) (s : Machine count ports) (regionEntry next marker : Fin count)
    (entry : Entry) (site : Fin count) (pre post : List Entry) (capture : Capture) (consumer : Consumer)
    (finalDerived : Vector Bool ports)
    (node : calls s.pc = .processing regionEntry next) (healthy : s.network.failed = false)
    (checked : Region.check program bindingChecked fuel .processing regionEntry = true)
    (delivery : s.currentDelivery = some ⟨entry, site⟩)
    (processing : Projection.phase s = .processing site)
    (selected : Projection.root s = .selected site)
    (found : (s.network.channels s.key.lane).held = pre ++ entry :: post)
    (active : (s.network.stores s.key.lane.peer).active = some (capture, consumer))
    (work : Projection.classifyWork (storeWork s.external (s.network.stores s.key.lane.peer)) = .activeOnly)
    (path : Region.DataWalk program bindingChecked .processing regionEntry (Vector.ofFn s.derived)
      .cleanupReturned marker finalDerived) (markerNode : program marker = .marker) :
    let before := Analysis.normalize calls fuel (Projection.state calls fuel s)
    let after := { s with
      pc := next
      driverSource := none
      driverReturn := none
      endValues := fun _ ↦ false
      resultCases := fun _ ↦ .unknown
      fact := none
      pendingEnd := none
      receiveInfo := .none
      currentDelivery := none
      derived := fun port ↦ finalDerived[port]
      network := regionFinal s.network s.key.lane entry pre post capture consumer }
    Analysis.normalize calls fuel (Projection.state calls fuel after) ∈
      (Analysis.localSuccessors calls program bindingChecked fuel before).map (Analysis.normalize calls fuel) := by
  have shape := checked_processing_projection s entry site pre post capture consumer finalDerived
    delivery processing selected found active work
  have output := Region.outputs_marker fuel checked path markerNode
  let before := Analysis.normalize calls fuel (Projection.state calls fuel s)
  let candidate := Analysis.refresh { before with
    control := next
    driverSource := none
    driverReturn := none
    endValues := Vector.ofFn fun _ ↦ false
    resultCases := Vector.ofFn fun _ ↦ .unknown
    fact := .none
    pending := false
    phase := .clear
    root := .idle
    work := .empty
    dependencies := finalDerived }
  refine List.mem_map.mpr ⟨candidate, ?_, ?_⟩
  · simp [candidate, before, Analysis.localSuccessors, Analysis.normalize, Analysis.refresh,
      Projection.state, node, healthy, checked, work, output]
  · simp [candidate, before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
      Vector.ofFn_getElem]
    refine ⟨shape.1.symm, shape.2.1.symm, shape.2.2.1.symm, ?_, ?_⟩
    · simp [regionFinal, Network.processingFinished, stageNetwork, setStore]
    · simp [Analysis.dependencyClosure, Analysis.dependencyStep, regionFinal, Network.processingFinished, stageNetwork, setStore]

/-- An admitted actual dispatch reaches its exact finite solver successor. -/
theorem certified_dispatch_successor {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (next : Fin count) (graph : List CaptureOp)
    (entry : Entry) (site : Fin count) (template capture : Capture) (consumer : Consumer)
    (node : calls s.pc = .dispatch next graph) (healthy : s.network.failed = false)
    (delivery : s.currentDelivery = some ⟨entry, site⟩)
    (constructed : capture = CapturePlan.build graph entry template)
    (admission : Admit (s.network.stores s.key.lane.peer) capture) (kind : consumer.kind = .root) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := next
      driverSource := none
      driverReturn := none
      endValues := fun _ ↦ false
      resultCases := fun _ ↦ .unknown
      fact := none
      pendingEnd := none
      network := s.network.dispatch s.key.lane entry capture consumer }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := next
    driverSource := none
    driverReturn := none
    endValues := fun _ ↦ false
    resultCases := fun _ ↦ .unknown
    fact := none
    pendingEnd := none
    network := s.network.dispatch s.key.lane entry capture consumer }
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have admitted := certified.2.1 ⟨parentEntry, before⟩ seen
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .dispatch next graph := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have localAccepted : Analysis.localAdmitted calls program bindingChecked regionFuel before = true := by
    unfold Analysis.configurationAdmitted at admitted
    simp only [notTerminal, Bool.false_eq_true, if_false] at admitted
    split at admitted
    next rejected => contradiction
    next allowed =>
      rw [nodeHere] at admitted
      exact admitted
  have beforeShape : CapturePlan.admitted graph = true ∧
      (before.work = .empty ∧ before.root = .idle) ∧
      (match before.phase with | .processing _ => true | _ => false) = true ∧
      (match before.fact with | .message _ _ => true | _ => false) = true := by
    simpa only [Analysis.localAdmitted, notTerminal, Bool.false_eq_true, if_false, nodeHere,
      Bool.and_eq_true, decide_eq_true_eq, and_assoc] using localAccepted
  have shape : CapturePlan.admitted graph = true ∧
      (Projection.classifyWork (storeWork s.external (s.network.stores s.key.lane.peer)) = .empty ∧
        Projection.root s = .idle) ∧
      (match Projection.phase s with | .processing _ => true | _ => false) = true ∧
      (match Projection.fact s with | .message _ _ => true | _ => false) = true := by
    simpa only [before, Analysis.normalize, Analysis.refresh, Projection.state] using beforeShape
  have singleton : (s.network.channels s.key.lane).held = [entry] := by
    by_cases same : (s.network.channels s.key.lane).held = [entry]
    · exact same
    · have phase : Projection.phase s = .pending := by simp [Projection.phase, delivery, same]
      simp [phase] at shape
  have phase : Projection.phase s = .processing site := by
    simp [Projection.phase, delivery, singleton]
  have message : ∃ operation edge, Projection.fact s = .message operation edge := by
    have matching := shape.2.2.2
    cases result : Projection.fact s with
    | none => simp [result] at matching
    | invalid => simp [result] at matching
    | empty operation edge => simp [result] at matching
    | endPending operation edge => simp [result] at matching
    | endFact operation edge => simp [result] at matching
    | message operation edge => exact ⟨operation, edge, rfl⟩
  obtain ⟨operation, edge, fact⟩ := message
  have localEdge := dispatch_successor_is_enumerated calls program bindingChecked regionFuel s
    next graph entry site operation edge template capture consumer node healthy delivery constructed
    shape.1 admission kind phase fact shape.2.1.1
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    obtain ⟨candidate, member, equal⟩ := List.mem_map.mp localEdge
    apply List.mem_map.mpr
    exact ⟨candidate, member, congrArg (fun state ↦ (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) equal⟩
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- An accepted concrete processing path reaches its actual solver successor. -/
theorem certified_processing_successor {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (regionEntry next marker : Fin count)
    (entry : Entry) (site : Fin count) (pre post : List Entry) (capture : Capture) (consumer : Consumer)
    (finalDerived : Vector Bool ports)
    (node : calls s.pc = .processing regionEntry next) (healthy : s.network.failed = false)
    (delivery : s.currentDelivery = some ⟨entry, site⟩)
    (found : (s.network.channels s.key.lane).held = pre ++ entry :: post)
    (active : (s.network.stores s.key.lane.peer).active = some (capture, consumer))
    (path : Region.DataWalk program bindingChecked .processing regionEntry (Vector.ofFn s.derived)
      .cleanupReturned marker finalDerived) (markerNode : program marker = .marker) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := next
      driverSource := none
      driverReturn := none
      endValues := fun _ ↦ false
      resultCases := fun _ ↦ .unknown
      fact := none
      pendingEnd := none
      receiveInfo := .none
      currentDelivery := none
      derived := fun port ↦ finalDerived[port]
      network := regionFinal s.network s.key.lane entry pre post capture consumer }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := next
    driverSource := none
    driverReturn := none
    endValues := fun _ ↦ false
    resultCases := fun _ ↦ .unknown
    fact := none
    pendingEnd := none
    receiveInfo := .none
    currentDelivery := none
    derived := fun port ↦ finalDerived[port]
    network := regionFinal s.network s.key.lane entry pre post capture consumer }
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have admitted := certified.2.1 ⟨parentEntry, before⟩ seen
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .processing regionEntry next := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have localAccepted : Analysis.localAdmitted calls program bindingChecked regionFuel before = true := by
    unfold Analysis.configurationAdmitted at admitted
    simp only [notTerminal, Bool.false_eq_true, if_false] at admitted
    split at admitted
    next rejected => contradiction
    next allowed =>
      rw [nodeHere] at admitted
      exact admitted
  have beforeShape : Region.check program bindingChecked regionFuel .processing regionEntry = true ∧
      before.work = .activeOnly ∧
      (match before.phase, before.root with
       | .processing first, .selected second => decide (first = second)
       | _, _ => false) = true := by
    simpa only [Analysis.localAdmitted, notTerminal, Bool.false_eq_true, if_false, nodeHere,
      Bool.and_eq_true, decide_eq_true_eq, and_assoc] using localAccepted
  have shape : Region.check program bindingChecked regionFuel .processing regionEntry = true ∧
      Projection.classifyWork (storeWork s.external (s.network.stores s.key.lane.peer)) = .activeOnly ∧
      (match Projection.phase s, Projection.root s with
       | .processing first, .selected second => decide (first = second)
       | _, _ => false) = true := by
    simpa only [before, Analysis.normalize, Analysis.refresh, Projection.state] using beforeShape
  have singleton : (s.network.channels s.key.lane).held = [entry] := by
    by_cases same : (s.network.channels s.key.lane).held = [entry]
    · exact same
    · have phase : Projection.phase s = .pending := by simp [Projection.phase, delivery, same]
      simp [phase] at shape
  have phase : Projection.phase s = .processing site := by
    simp [Projection.phase, delivery, singleton]
  have selected : Projection.root s = .selected site := by
    have matching := shape.2.2
    cases rootCase : Projection.root s with
    | idle => simp [phase, rootCase] at matching
    | invalid => simp [phase, rootCase] at matching
    | unknown => simp [phase, rootCase] at matching
    | selected other =>
        have same : site = other := by simpa [phase, rootCase] using matching
        cases same
        rfl
  have localEdge := processing_successor_is_enumerated calls program bindingChecked regionFuel s
    regionEntry next marker entry site pre post capture consumer finalDerived node healthy shape.1 delivery
    phase selected found active shape.2.1 path markerNode
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    obtain ⟨candidate, member, equal⟩ := List.mem_map.mp localEdge
    apply List.mem_map.mpr
    exact ⟨candidate, member, congrArg (fun state ↦ (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) equal⟩
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- Receive control steps use the same network transition as their state update. -/
theorem control_step_network {count ports : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports} {before after : Machine count ports}
    (step : Step calls before after) : NetworkTrace before.network after.network := by
  cases step with
  | receiveEnd message empty endSuccess failedReply payload operation node read live committed current running healthy sealed emptyQueue =>
      apply NetworkTrace.next (NetworkTrace.refl before.network)
      apply NetworkStep.channel before.network operation ⟨before.key.lane, .read, before.key.lane.peer⟩
        { before.network.channels before.key.lane with observedEnd := true } live committed current rfl running
      exact ChannelStep.observeEnd (before.network.channels before.key.lane) healthy sealed emptyQueue
  | receiveMessage message empty endSuccess failedReply payload operation entry tail node read live committed current running healthy head =>
      apply NetworkTrace.next (NetworkTrace.refl before.network)
      apply NetworkStep.channel before.network operation ⟨before.key.lane, .read, before.key.lane.peer⟩
        { before.network.channels before.key.lane with
          received := (before.network.channels before.key.lane).received ++ [entry]
          queue := tail
          held := (before.network.channels before.key.lane).held ++ [entry] }
        live committed current rfl running
      exact ChannelStep.receive (before.network.channels before.key.lane) entry tail head healthy
  | receiveEmpty message empty endSuccess failedReply payload operation node read live committed current running healthy unsealed emptyQueue =>
      apply NetworkTrace.next (NetworkTrace.refl before.network)
      apply NetworkStep.channel before.network operation ⟨before.key.lane, .read, before.key.lane.peer⟩
        (before.network.channels before.key.lane) live committed current rfl running
      exact ChannelStep.idle (before.network.channels before.key.lane) .read
  | receiveFailed => exact NetworkTrace.refl _
  | receiveFailedToken message empty endSuccess failedReply payload operation node read live committed current running =>
      apply NetworkTrace.next (NetworkTrace.refl before.network)
      apply NetworkStep.channel before.network operation ⟨before.key.lane, .read, before.key.lane.peer⟩
        (before.network.channels before.key.lane) live committed current rfl running
      exact ChannelStep.idle (before.network.channels before.key.lane) .read
  | call => exact NetworkTrace.refl _
  | forward => exact NetworkTrace.refl _
  | branchYes => exact NetworkTrace.refl _
  | branchNo => exact NetworkTrace.refl _
  | endReply | endResult | otherResult | matchEndYes | matchEndNo | matchEndUnverified => exact NetworkTrace.refl _
  | normalReturn | matchedReturn => exact NetworkTrace.refl _
  | otherReturn => exact NetworkTrace.refl _
  | failure live =>
      apply NetworkTrace.next (NetworkTrace.refl before.network)
      exact NetworkStep.failure before.network live
  | invalidate => exact NetworkTrace.refl _

/-- Every actual modeled execution step maps to concrete Network transitions. -/
theorem execution_step_network {count ports bindings : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports}
    {program : Fin count → Region.Node count ports bindings} {bindingChecked : Fin bindings → Bool}
    {before after : Machine count ports} (step : ExecutionStep calls program bindingChecked before after) :
    NetworkTrace before.network after.network := by
  cases step with
  | control step => exact control_step_network step
  | unverified network external next node running steps => exact steps
  | processingUnverified regionEntry next network external derived node running unverified steps => exact steps
  | unverifiedDispatch next graph network external derived node running rejected steps => exact steps
  | unverifiedCapture regionEntry next entry site capture consumer network external derived node running delivery active mismatch steps => exact steps
  | dispatch next graph entry site template capture consumer node constructed currentDelivery live committed networkHealthy running held
      notDispatched identity owned noClause driver admission fresh unique interpretation kind openStore healthy =>
      apply NetworkTrace.next (NetworkTrace.refl before.network)
      exact NetworkStep.dispatch before.network before.key.lane before.key.lane.peer entry capture consumer
        live committed networkHealthy rfl running held notDispatched identity owned noClause driver admission
        fresh unique interpretation kind openStore healthy
  | processing regionEntry next marker entry site pre post capture consumer finalDerived node currentDelivery path markerNode
      live committed networkHealthy running found identity owned dispatched active armed noNested healthy =>
      let second := stageNetwork before.network before.key.lane capture consumer .cleanupReturned
      have prior : NetworkTrace before.network second :=
        region_walk_network before.network before.key.lane capture consumer live committed networkHealthy
          running active armed noNested healthy path.toWalk
      have ready := (cleanup_then_finish (before.network.stores before.key.lane.peer) capture consumer
        active armed noNested healthy).2.2.1
      have finishStep : NetworkStep second (regionFinal before.network before.key.lane entry pre post capture consumer) := by
        apply NetworkStep.finishProcessing second before.key.lane entry pre post (finishedCapture capture) consumer
        · simpa [second, stageNetwork, setStore] using live
        · simpa [second, stageNetwork, setStore] using committed
        · simpa [second, stageNetwork, setStore] using running
        · simpa [second, stageNetwork, setStore] using found
        · simpa [finishedCapture] using identity
        · simpa [finishedCapture] using owned
        · simpa [second, stageNetwork, setStore] using dispatched
        · simp [second, stageNetwork, setStore, putWorker, finishedStore]
        · exact ready
        · simpa [second, stageNetwork, setStore, putWorker, finishedStore] using healthy
      exact NetworkTrace.next prior finishStep

inductive Execution {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool) :
    Machine count ports → Machine count ports → Prop where
  | refl (s) : Execution calls program bindingChecked s s
  | next {first middle last} : Execution calls program bindingChecked first middle →
      ExecutionStep calls program bindingChecked middle last →
      Execution calls program bindingChecked first last

/-- Execution never changes the selected activation, lane, side or owner site. -/
theorem execution_preserves_identity {count ports bindings : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports}
    {program : Fin count → Region.Node count ports bindings} {bindingChecked : Fin bindings → Bool}
    {first last : Machine count ports} (execution : Execution calls program bindingChecked first last) :
    last.key = first.key ∧ last.ownerSite = first.ownerSite := by
  induction execution with
  | refl => exact ⟨rfl, rfl⟩
  | next _ edge ih =>
      cases edge with
      | control control => cases control <;> exact ih
      | dispatch | processing | processingUnverified | unverifiedDispatch | unverifiedCapture | unverified =>
          exact ih

/-- Pending End and a returned End fact cannot coexist in a reachable activation. -/
def ReplyConsistent {count ports : Nat} (s : Machine count ports) : Prop :=
  s.fact = none ∨ s.pendingEnd = none

theorem execution_preserves_reply_consistency {count ports bindings : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports}
    {program : Fin count → Region.Node count ports bindings} {bindingChecked : Fin bindings → Bool}
    {first last : Machine count ports} (initial : ReplyConsistent first)
    (execution : Execution calls program bindingChecked first last) : ReplyConsistent last := by
  induction execution with
  | refl => exact initial
  | next _ edge ih =>
      cases edge with
      | control control => cases control <;> simp_all [ReplyConsistent]
      | dispatch | processing | processingUnverified | unverifiedDispatch | unverifiedCapture | unverified =>
          simp [ReplyConsistent]

/-- The concrete top frame and each older frame retain their exact caller contexts. -/
def FrameChain {count ports : Nat} (key : Key) : StaticContext count → List (Frame count ports) → Prop
  | _, [] => True
  | context, frame :: rest => frame.key = key ∧ frame.calleeContext = context ∧
      FrameChain key frame.callerContext rest

theorem step_preserves_frame_chain {count ports : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports} {before after : Machine count ports}
    (valid : FrameChain before.key before.context before.frames) (edge : Step calls before after) :
    FrameChain after.key after.context after.frames := by
  cases edge with
  | call target continuation calleeContext inputs returnSource returnTarget node => exact ⟨rfl, rfl, valid⟩
  | matchedReturn frame rest node stack same context fact authentic owner =>
      have chain : frame.key = before.key ∧ frame.calleeContext = before.context ∧
          FrameChain before.key frame.callerContext rest := by simpa [FrameChain, stack] using valid
      exact chain.2.2
  | normalReturn frame rest node stack same context noFact noPending =>
      have chain : frame.key = before.key ∧ frame.calleeContext = before.context ∧
          FrameChain before.key frame.callerContext rest := by simpa [FrameChain, stack] using valid
      exact chain.2.2
  | otherReturn frame rest value node stack unmatched =>
      have chain : frame.key = before.key ∧ frame.calleeContext = before.context ∧
          FrameChain before.key frame.callerContext rest := by simpa [FrameChain, stack] using valid
      exact chain.2.2
  | receiveEnd | receiveMessage | receiveEmpty | receiveFailed | receiveFailedToken |
      forward | branchYes | branchNo | endReply | endResult | otherResult | matchEndYes |
      matchEndNo | matchEndUnverified | failure | invalidate => exact valid

/-- An admitted actual call cannot carry an unfinished End reply into its callee. -/
theorem certified_call_pending_clear {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (target continuation : Fin count) (context : StaticContext count)
    (inputs : List (Fin ports × Fin ports)) (returnSource returnTarget : Fin ports)
    (node : calls s.pc = .call target continuation context inputs returnSource returnTarget)
    (healthy : s.network.failed = false)
    (seen : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) : s.pendingEnd = none := by
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have admitted := certified.2.1 _ seen
  cases pending : s.pendingEnd with
  | none => rfl
  | some fact =>
      simp [Analysis.configurationAdmitted, Analysis.callEntry, Analysis.normalize, Analysis.refresh,
        Projection.state, healthy, node, pending] at admitted

/-- An admitted return has no pending reply and no fact from a different activation. -/
theorem certified_return_ready {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (value : Fin ports) (node : calls s.pc = .returnNode value)
    (healthy : s.network.failed = false)
    (seen : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) :
    s.pendingEnd = none ∧ (s.fact = none ∨ ∃ fact, s.fact = some fact ∧ fact.key = s.key) := by
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have admitted := certified.2.1 ⟨parentEntry, before⟩ seen
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .returnNode value := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  unfold Analysis.configurationAdmitted at admitted
  simp only [notTerminal, Bool.false_eq_true, if_false] at admitted
  split at admitted
  next rejected => contradiction
  next allowed =>
    rw [nodeHere] at admitted
    have noEscape : before.escape = false := by
      cases projected : before.fact <;> simp_all
    have pending : s.pendingEnd = none := by
      cases actual : s.pendingEnd with
      | none => rfl
      | some fact =>
        simp [before, Analysis.normalize, Analysis.refresh, Projection.state, actual] at noEscape
    refine ⟨pending, ?_⟩
    cases actual : s.fact with
    | none => exact Or.inl rfl
    | some fact =>
      right
      by_cases same : fact.key = s.key
      · exact ⟨fact, rfl, same⟩
      · have projected : before.fact = .invalid := by
          simp [before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact, actual, same]
        simp [projected] at allowed

/-- Each dynamic frame retains the reached caller that created its solver entry. -/
inductive SolverFrames {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat)
    (answer : List (Analysis.Configuration count ports))
    (key : Key) (owner : Fin count) (seed : Analysis.State count ports) :
    List (Frame count ports) → Analysis.State count ports → Prop where
  | base : SolverFrames calls fuel answer key owner seed [] seed
  | push (caller : Machine count ports) (parentEntry : Analysis.State count ports)
      (target continuation : Fin count) (context : StaticContext count)
      (inputs : List (Fin ports × Fin ports)) (returnSource returnTarget : Fin ports)
      (node : calls caller.pc = .call target continuation context inputs returnSource returnTarget)
      (sameKey : caller.key = key) (sameOwner : caller.ownerSite = owner)
      (pending : caller.pendingEnd = none) (healthy : caller.network.failed = false)
      (seen : (⟨parentEntry, Analysis.normalize calls fuel (Projection.state calls fuel caller)⟩ :
        Analysis.Configuration count ports) ∈ answer)
      (rest : SolverFrames calls fuel answer key owner seed caller.frames parentEntry) :
      SolverFrames calls fuel answer key owner seed
        (⟨caller.key, caller.pc, target, continuation, caller.context, context,
          inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames)
        (Analysis.normalize calls fuel (Projection.state calls fuel { caller with
          pc := target
          driverSource := none
          driverReturn := none
          resultCases := fun _ ↦ .unknown
          context := context
          fact := none
          receiveInfo := .none
          endValues := fun _ ↦ false
          derived := callInputs inputs caller.derived
          frames := ⟨caller.key, caller.pc, target, continuation, caller.context, context,
            inputs, returnSource, returnTarget, Vector.ofFn caller.derived⟩ :: caller.frames }))

/-- An actual call pushes its reached caller witness and enters the solver callee. -/
theorem certified_stack_call_enters {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (key : Key) (ownerSite : Fin count) (s : Machine count ports) (parentEntry : Analysis.State count ports)
    (target continuation : Fin count) (context : StaticContext count) (inputs : List (Fin ports × Fin ports))
    (returnSource returnTarget : Fin ports)
    (node : calls s.pc = .call target continuation context inputs returnSource returnTarget)
    (sameKey : s.key = key) (sameOwner : s.ownerSite = ownerSite)
    (pending : s.pendingEnd = none) (healthy : s.network.failed = false)
    (witness : SolverFrames calls regionFuel answer.1 key ownerSite seed s.frames parentEntry)
    (seen : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) :
    let after := { s with
      pc := target
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      context := context
      fact := none
      receiveInfo := .none
      endValues := fun _ ↦ false
      derived := callInputs inputs s.derived
      frames := ⟨s.key, s.pc, target, continuation, s.context, context,
        inputs, returnSource, returnTarget, Vector.ofFn s.derived⟩ :: s.frames }
    ∃ entry, SolverFrames calls regionFuel answer.1 key ownerSite seed after.frames entry ∧
      (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  let callee := { s with
    pc := target
    driverSource := none
    driverReturn := none
    resultCases := fun _ ↦ .unknown
    context := context
    fact := none
    receiveInfo := .none
    endValues := fun _ ↦ false
    derived := callInputs inputs s.derived
    frames := ⟨s.key, s.pc, target, continuation, s.context, context,
      inputs, returnSource, returnTarget, Vector.ofFn s.derived⟩ :: s.frames }
  refine ⟨Analysis.normalize calls regionFuel (Projection.state calls regionFuel callee), ?_, ?_⟩
  · exact SolverFrames.push s parentEntry target continuation context inputs returnSource returnTarget
      node sameKey sameOwner pending healthy seen witness
  · exact certified_call_enters calls program bindingChecked regionFuel solverFuel budget seed parentEntry answer
      accepted s target continuation context inputs returnSource returnTarget node pending healthy seen

/-- A matched actual return restores the reached caller saved by its dynamic frame. -/
theorem certified_stack_return_replayed {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (key : Key) (ownerSite : Fin count) (s : Machine count ports)
    (entry : Analysis.State count ports) (frame : Frame count ports) (rest : List (Frame count ports))
    (fact : EndFact count) (node : calls s.pc = .returnNode frame.returnSource)
    (stack : s.frames = frame :: rest) (keySame : s.key = key) (ownerSame : s.ownerSite = ownerSite)
    (context : frame.calleeContext = s.context) (authentic : s.fact = some fact) (owner : fact.key = s.key)
    (pending : s.pendingEnd = none) (healthy : s.network.failed = false)
    (witness : SolverFrames calls regionFuel answer.1 key ownerSite seed s.frames entry)
    (seen : (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) :
    let after := { s with
      pc := frame.continuation
      context := frame.callerContext
      frames := rest
      derived := returnInputs frame.callerDependencies (s.derived frame.returnSource) frame.returnTarget
      endValues := fun port ↦ if port = frame.returnTarget then s.endValues frame.returnSource else false
      resultCases := fun port ↦ if port = frame.returnTarget then s.resultCases frame.returnSource else .unknown
      driverReturn := if rest.isEmpty then some (frame.continuation, frame.returnTarget) else none
      driverSource := none }
    ∃ parentEntry, SolverFrames calls regionFuel answer.1 key ownerSite seed rest parentEntry ∧
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  rw [stack] at witness
  cases witness with
  | push caller parentEntry target continuation calleeContext inputs returnSource returnTarget
      callNode callerKey callerOwner callerPending callerHealthy callerSeen older =>
      have sameKey : s.key = caller.key := keySame.trans callerKey.symm
      have sameOwner : s.ownerSite = caller.ownerSite := ownerSame.trans callerOwner.symm
      have sameContext : s.context = calleeContext := context.symm
      refine ⟨parentEntry, older, ?_⟩
      exact certified_matched_return_replayed calls program bindingChecked regionFuel solverFuel budget seed
        parentEntry answer accepted caller s target continuation calleeContext inputs returnSource returnTarget fact
        callNode node callerPending callerHealthy pending healthy sameKey sameOwner sameContext authentic owner stack
        callerSeen seen

/-- A normal non-End return restores the reached dynamic caller too. -/
theorem certified_stack_normal_return_replayed {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (key : Key) (ownerSite : Fin count) (s : Machine count ports)
    (entry : Analysis.State count ports) (frame : Frame count ports) (rest : List (Frame count ports))
    (node : calls s.pc = .returnNode frame.returnSource)
    (stack : s.frames = frame :: rest) (keySame : s.key = key) (ownerSame : s.ownerSite = ownerSite)
    (context : frame.calleeContext = s.context) (noFact : s.fact = none)
    (pending : s.pendingEnd = none) (healthy : s.network.failed = false)
    (witness : SolverFrames calls regionFuel answer.1 key ownerSite seed s.frames entry)
    (seen : (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) :
    let after := { s with
      pc := frame.continuation
      context := frame.callerContext
      frames := rest
      fact := none
      pendingEnd := none
      receiveInfo := .none
      derived := returnInputs frame.callerDependencies (s.derived frame.returnSource) frame.returnTarget
      endValues := fun _ ↦ false
      resultCases := fun port ↦ if port = frame.returnTarget then s.resultCases frame.returnSource else .unknown
      driverReturn := if rest.isEmpty then some (frame.continuation, frame.returnTarget) else none
      driverSource := none }
    ∃ parentEntry, SolverFrames calls regionFuel answer.1 key ownerSite seed rest parentEntry ∧
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  rw [stack] at witness
  cases witness with
  | push caller parentEntry target continuation calleeContext inputs returnSource returnTarget
      callNode callerKey callerOwner callerPending callerHealthy callerSeen older =>
      have sameKey : s.key = caller.key := keySame.trans callerKey.symm
      have sameOwner : s.ownerSite = caller.ownerSite := ownerSame.trans callerOwner.symm
      have sameContext : s.context = calleeContext := context.symm
      refine ⟨parentEntry, older, ?_⟩
      exact certified_normal_return_replayed calls program bindingChecked regionFuel solverFuel budget seed
        parentEntry answer accepted caller s target continuation calleeContext inputs returnSource returnTarget
        callNode node callerPending callerHealthy pending healthy sameKey sameOwner sameContext noFact stack
        callerSeen seen

/-- A reached actual return cannot disagree with the dynamic frame's return port. -/
theorem certified_stack_return_matches {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (key : Key) (ownerSite : Fin count) (s : Machine count ports)
    (entry : Analysis.State count ports) (frame : Frame count ports) (rest : List (Frame count ports))
    (value : Fin ports) (fact : EndFact count) (node : calls s.pc = .returnNode value)
    (stack : s.frames = frame :: rest) (context : frame.calleeContext = s.context)
    (authentic : s.fact = some fact) (owner : fact.key = s.key) (healthy : s.network.failed = false)
    (witness : SolverFrames calls regionFuel answer.1 key ownerSite seed s.frames entry)
    (seen : (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) : value = frame.returnSource := by
  rw [stack] at witness
  cases witness with
  | push caller parentEntry target continuation calleeContext inputs returnSource returnTarget
      callNode callerKey callerOwner callerPending callerHealthy callerSeen older =>
      exact certified_return_matches calls program bindingChecked regionFuel solverFuel budget seed parentEntry
        answer accepted caller s target continuation calleeContext inputs returnSource returnTarget value fact
        callNode node callerPending callerHealthy healthy context.symm authentic owner callerSeen seen

/-- A non-End return must match the exact dynamic frame port as well. -/
theorem certified_stack_normal_return_matches {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (key : Key) (ownerSite : Fin count) (s : Machine count ports)
    (entry : Analysis.State count ports) (frame : Frame count ports) (rest : List (Frame count ports))
    (value : Fin ports) (node : calls s.pc = .returnNode value)
    (stack : s.frames = frame :: rest) (context : frame.calleeContext = s.context)
    (noFact : s.fact = none) (pending : s.pendingEnd = none) (healthy : s.network.failed = false)
    (witness : SolverFrames calls regionFuel answer.1 key ownerSite seed s.frames entry)
    (seen : (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) : value = frame.returnSource := by
  rw [stack] at witness
  cases witness with
  | push caller parentEntry target continuation calleeContext inputs returnSource returnTarget
      callNode callerKey callerOwner callerPending callerHealthy callerSeen older =>
      exact certified_normal_return_matches calls program bindingChecked regionFuel solverFuel budget seed parentEntry
        answer accepted caller s target continuation calleeContext inputs returnSource returnTarget value
        callNode node callerPending callerHealthy healthy pending context.symm noFact callerSeen seen

/-- No admitted reached return can take the actual mismatched-frame transition. -/
theorem certified_other_return_impossible {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (key : Key) (ownerSite : Fin count) (s : Machine count ports)
    (entry : Analysis.State count ports) (frame : Frame count ports) (rest : List (Frame count ports))
    (value : Fin ports) (node : calls s.pc = .returnNode value) (stack : s.frames = frame :: rest)
    (healthy : s.network.failed = false) (chain : FrameChain s.key s.context s.frames)
    (witness : SolverFrames calls regionFuel answer.1 key ownerSite seed s.frames entry)
    (seen : (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) :
    ¬ ((∃ fact, s.fact = some fact ∧ fact.key ≠ s.key) ∨ s.pendingEnd ≠ none ∨
      frame.key ≠ s.key ∨ frame.calleeContext ≠ s.context ∨ value ≠ frame.returnSource) := by
  obtain ⟨pending, factCase⟩ := certified_return_ready calls program bindingChecked
    regionFuel solverFuel budget seed entry answer accepted s value node healthy seen
  have frameShape : frame.key = s.key ∧ frame.calleeContext = s.context ∧
      FrameChain s.key frame.callerContext rest := by
    simpa [FrameChain, stack] using chain
  have valueMatches : value = frame.returnSource := by
    rcases factCase with noFact | ⟨fact, authentic, owner⟩
    · exact certified_stack_normal_return_matches calls program bindingChecked regionFuel solverFuel budget
        seed answer accepted key ownerSite s entry frame rest value node stack frameShape.2.1 noFact pending healthy witness seen
    · exact certified_stack_return_matches calls program bindingChecked regionFuel solverFuel budget
        seed answer accepted key ownerSite s entry frame rest value fact node stack frameShape.2.1 authentic owner healthy witness seen
  intro mismatch
  rcases mismatch with badFact | badPending | badKey | badContext | badValue
  · rcases badFact with ⟨fact, authentic, wrong⟩
    rcases factCase with noFact | ⟨good, goodPresent, owner⟩
    · simp [noFact] at authentic
    · have same : fact = good := by simpa [authentic] using goodPresent
      subst fact
      exact wrong owner
  · exact badPending pending
  · exact badKey frameShape.1
  · exact badContext frameShape.2.1
  · exact badValue valueMatches

/-- Full-stack nesting is established from an empty stack, without bounding recursion depth. -/
theorem execution_preserves_frame_chain {count ports bindings : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports}
    {program : Fin count → Region.Node count ports bindings} {bindingChecked : Fin bindings → Bool}
    {first last : Machine count ports} (valid : FrameChain first.key first.context first.frames)
    (execution : Execution calls program bindingChecked first last) : FrameChain last.key last.context last.frames := by
  induction execution with
  | refl => exact valid
  | next _ edge ih =>
      cases edge with
      | control control => exact step_preserves_frame_chain ih control
      | dispatch | processing | processingUnverified | unverifiedDispatch | unverifiedCapture | unverified => exact ih

/-- Every concrete frame dependency is included in its finite summary. -/
theorem projection_frame_dependency_subset {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat)
    (s : Machine count ports) (frame : Frame count ports) (member : frame ∈ s.frames) :
    let a := Projection.state calls fuel s
    ∀ port, returnInputs frame.callerDependencies (s.derived frame.returnSource) frame.returnTarget port = true →
      (a.frameDependencies[frame.continuation][port] ||
        (List.finRange ports).any (fun source ↦ a.frameReturns[frame.continuation][port][source] &&
          (Analysis.dependencyClosure a)[source])) = true := by
  dsimp only
  let a := Projection.state calls fuel s
  intro port dependent
  by_cases target : port = frame.returnTarget
  · subst port
    have source : s.derived frame.returnSource = true := by simpa [returnInputs] using dependent
    have current : a.dependencies[frame.returnSource] = true := by
      simpa [a, Projection.state] using source
    have closed := Analysis.dependencyClosure_contains_current a frame.returnSource current
    simp only [Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨frame.returnSource, List.mem_finRange _, ?_⟩
    simp only [Bool.and_eq_true]
    refine ⟨?_, closed⟩
    simp only [Projection.state]
    let rows : Fin count → Vector (Vector Bool ports) ports := fun site ↦
      Vector.ofFn fun target ↦ Vector.ofFn fun source ↦
        s.frames.any (fun f ↦ decide (f.continuation = site ∧ f.returnTarget = target ∧ f.returnSource = source))
    change ((Vector.ofFn rows)[frame.continuation.val]'frame.continuation.isLt)[frame.returnTarget][frame.returnSource] = true
    simp only [Vector.getElem_ofFn]
    let row : Fin ports → Vector Bool ports := fun target ↦ Vector.ofFn fun source ↦
      s.frames.any (fun f ↦ decide (f.continuation = frame.continuation ∧ f.returnTarget = target ∧ f.returnSource = source))
    change ((Vector.ofFn row)[frame.returnTarget.val]'frame.returnTarget.isLt)[frame.returnSource] = true
    simp only [Vector.getElem_ofFn]
    let entries : Fin ports → Bool := fun source ↦ s.frames.any (fun f ↦ decide
      (f.continuation = frame.continuation ∧ f.returnTarget = frame.returnTarget ∧ f.returnSource = source))
    change (Vector.ofFn entries)[frame.returnSource.val]'frame.returnSource.isLt = true
    simp only [Vector.getElem_ofFn]
    apply List.any_eq_true.mpr
    exact ⟨frame, member, by simp⟩
  · have saved : frame.callerDependencies[port] = true := by
      simpa [returnInputs, target] using dependent
    simp only [Bool.or_eq_true]
    left
    simp only [Projection.state]
    let rows : Fin count → Vector Bool ports := fun site ↦ Vector.ofFn fun p ↦
      s.frames.any (fun f ↦ decide (f.continuation = site ∧ f.returnTarget ≠ p) && f.callerDependencies[p])
    change ((Vector.ofFn rows)[frame.continuation.val]'frame.continuation.isLt)[port] = true
    simp only [Vector.getElem_ofFn]
    let entries : Fin ports → Bool := fun p ↦ s.frames.any (fun f ↦ decide
      (f.continuation = frame.continuation ∧ f.returnTarget ≠ p) && f.callerDependencies[p])
    change (Vector.ofFn entries)[port.val]'port.isLt = true
    simp only [Vector.getElem_ofFn]
    apply List.any_eq_true.mpr
    have targetNe : frame.returnTarget ≠ port := Ne.symm target
    exact ⟨frame, member, by simp [targetNe, saved]⟩

/-- A driver check remains valid when dependencies are reduced. -/
theorem driver_check_dependency_subset {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (site : Fin count) (target : Fin ports)
    (smaller larger : Fin ports → Bool)
    (subset : ∀ port, smaller port = true → larger port = true)
    (accepted : Projection.driverCheck calls larger site target = true) :
    Projection.driverCheck calls smaller site target = true := by
  cases node : calls site with
  | matchEnd source yes no =>
      have clean : smaller source = false := by
        cases actual : smaller source with
        | false => rfl
        | true =>
            have large := subset source actual
            simp [Projection.driverCheck, node, large] at accepted
      simp [Projection.driverCheck, node] at accepted ⊢
      exact ⟨⟨accepted.1.1, clean⟩, accepted.2⟩
  | _ => simp [Projection.driverCheck, node] at accepted

theorem normalized_frame_sites_sound {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat) (s : Machine count ports)
    (checked : (Analysis.normalize calls fuel (Projection.state calls fuel s)).suffixSafe = true) :
    Projection.framesSafe calls s fuel = true := by
  let a := Projection.state calls fuel s
  have checkedFull : a.framesValid = true ∧
      Analysis.dependencyStep a.frameReturns (Analysis.dependencyClosure a) = Analysis.dependencyClosure a ∧
      (List.finRange count).all (fun site ↦
        let derived := fun port ↦ a.frameDependencies[site][port] ||
          (List.finRange ports).any (fun source ↦ a.frameReturns[site][port][source] &&
            (Analysis.dependencyClosure a)[source])
        let strict := Suffix.check (Suffix.fromCalls calls) derived fuel site
        (!a.innerSites[site] || strict) &&
          (List.finRange ports).all (fun target ↦
            !a.outerReturns[site][target] || strict || Projection.driverCheck calls derived site target)) = true := by
    simpa [Analysis.normalize, Analysis.refresh, a, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
  have shape : ∀ frame, frame ∈ s.frames → Projection.frameShape calls s.key s.ownerSite frame = true := by
    intro frame member
    exact (List.all_eq_true.mp checkedFull.1) frame member
  have checks := checkedFull.2.2
  unfold Projection.framesSafe
  simp only [Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro frame inner
    have member : frame ∈ s.frames := (List.dropLast_sublist s.frames).subset inner
    have present : a.innerSites[frame.continuation] = true := by
      simp only [a, Projection.state]
      change (Vector.ofFn (fun site ↦ s.frames.dropLast.any (fun f ↦ decide (f.continuation = site))))[frame.continuation.val]'frame.continuation.isLt = true
      simp only [Vector.getElem_ofFn]
      apply List.any_eq_true.mpr
      exact ⟨frame, inner, by simp⟩
    have siteCheck := (List.all_eq_true.mp checks) frame.continuation (List.mem_finRange _)
    simp only [Bool.and_eq_true] at siteCheck
    have strict := siteCheck.1
    simp only [present, Bool.not_true, Bool.false_or] at strict
    simp only [Projection.frameSafe, Bool.and_eq_true]
    refine ⟨shape frame member, ?_⟩
    exact Suffix.check_dependency_subset (Suffix.fromCalls calls) _ _
      (projection_frame_dependency_subset calls fuel s frame member) fuel frame.continuation strict
  · cases last : s.frames.getLast? with
    | none => simp
    | some frame =>
      have member : frame ∈ s.frames := by
        apply List.mem_of_mem_getLast?
        simp [last]
      have present : a.outerReturns[frame.continuation][frame.returnTarget] = true := by
        simp [a, Projection.state, last]
      have siteCheck := (List.all_eq_true.mp checks) frame.continuation (List.mem_finRange _)
      simp only [Bool.and_eq_true] at siteCheck
      have outer := (List.all_eq_true.mp siteCheck.2) frame.returnTarget (List.mem_finRange _)
      simp only [present, Bool.not_true, Bool.false_or, Bool.or_eq_true] at outer
      simp only [Projection.frameSafe, Bool.or_eq_true, Bool.and_eq_true]
      rcases outer with strict | driver
      · left
        refine ⟨shape frame member, ?_⟩
        exact Suffix.check_dependency_subset (Suffix.fromCalls calls) _ _
          (projection_frame_dependency_subset calls fuel s frame member) fuel frame.continuation strict
      · right
        refine ⟨shape frame member, ?_⟩
        exact driver_check_dependency_subset calls frame.continuation frame.returnTarget _ _
          (projection_frame_dependency_subset calls fuel s frame member) driver

/-- The actual unified execution cannot manufacture a successful End origin. -/
theorem execution_preserves_authentication {count ports bindings : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports}
    {program : Fin count → Region.Node count ports bindings} {bindingChecked : Fin bindings → Bool}
    {first last : Machine count ports} (valid : Authenticated first)
    (execution : Execution calls program bindingChecked first last) : Authenticated last := by
  induction execution with
  | refl => exact valid
  | next _ step ih =>
      cases step with
      | control edge => exact step_preserves_authentication ih edge
      | dispatch | processing | processingUnverified | unverifiedDispatch | unverifiedCapture | unverified =>
          refine ⟨ih.1, ?_, ?_⟩ <;> intro fact impossible <;> contradiction

/-- The unified control execution follows real modeled Network transitions. -/
theorem execution_network {count ports bindings : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports}
    {program : Fin count → Region.Node count ports bindings} {bindingChecked : Fin bindings → Bool}
    {first last : Machine count ports} (execution : Execution calls program bindingChecked first last) :
    NetworkTrace first.network last.network := by
  induction execution with
  | refl => exact NetworkTrace.refl _
  | next _ step ih => exact network_trace_trans ih (execution_step_network step)

/-- Acceptance checks the actual finish node and every projected cut component. -/
theorem Projection.accepted_shape {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (a : Analysis.State count ports)
    (accepted : Projection.finishAccepted calls a = true) :
    calls a.control = .finishReceive ∧ (∃ site edge, a.fact = .endFact site edge) ∧
      a.phase = .clear ∧ a.work = .empty ∧ a.escape = false ∧ a.suffixSafe = true ∧
      a.driverSource.isSome = true := by
  cases node : calls a.control <;> simp [Projection.finishAccepted, node] at accepted
  cases fact : a.fact <;> simp [fact] at accepted
  cases phase : a.phase <;> simp [phase] at accepted
  cases work : a.work <;> simp [work] at accepted
  exact ⟨rfl, ⟨_, _, rfl⟩, rfl, rfl, accepted.1.1, accepted.1.2, accepted.2⟩

/-- A failed network cannot grant the modeled finish permission. -/
theorem Projection.failed_finish_refused {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat)
    (s : Machine count ports) (failed : s.network.failed = true) :
    Projection.finishAccepted calls (Projection.state calls fuel s) = false := by
  cases result : Projection.finishAccepted calls (Projection.state calls fuel s) with
  | false => rfl
  | true =>
    have shape := Projection.accepted_shape calls (Projection.state calls fuel s) result
    have escape := shape.2.2.2.2.1
    simp [Projection.state, failed] at escape

/-- Clear phase means no current delivery and no older held delivery. -/
theorem Projection.clear_phase {count ports : Nat} (s : Machine count ports)
    (clear : Projection.phase s = .clear) :
    s.currentDelivery = none ∧ (s.network.channels s.key.lane).held = [] := by
  cases delivery : s.currentDelivery with
  | none =>
      cases held : (s.network.channels s.key.lane).held with
      | nil => exact ⟨rfl, rfl⟩
      | cons first rest => simp [Projection.phase, delivery, held] at clear
  | some current =>
      by_cases held : (s.network.channels s.key.lane).held = [current.entry] <;>
        simp [Projection.phase, delivery, held] at clear

/-- A concrete Message receipt from an admitted receive is a reached solver successor. -/
theorem certified_receive_message {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (message empty endSuccess failedReply : Fin count) (payload : Fin ports)
    (operation : Nat) (entry : Entry) (tail : List Entry)
    (node : calls s.pc = .receive message empty endSuccess failedReply payload) (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := message
      driverSource := none
      driverReturn := none
      endValues := fun _ ↦ false
      resultCases := fun _ ↦ .unknown
      fact := none
      pendingEnd := none
      receiveInfo := .message s.pc message
      currentDelivery := some ⟨entry, s.pc⟩
      derived := fun port ↦ if port = payload then true else s.derived port
      network := s.network.advance s.key.lane
        { s.network.channels s.key.lane with
          received := (s.network.channels s.key.lane).received ++ [entry]
          queue := tail
          held := (s.network.channels s.key.lane).held ++ [entry] } operation }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := message
    driverSource := none
    driverReturn := none
    endValues := fun _ ↦ false
    resultCases := fun _ ↦ .unknown
    fact := none
    pendingEnd := none
    receiveInfo := .message s.pc message
    currentDelivery := some ⟨entry, s.pc⟩
    derived := fun port ↦ if port = payload then true else s.derived port
    network := s.network.advance s.key.lane
      { s.network.channels s.key.lane with
        received := (s.network.channels s.key.lane).received ++ [entry]
        queue := tail
        held := (s.network.channels s.key.lane).held ++ [entry] } operation }
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have admitted := certified.2.1 ⟨parentEntry, before⟩ seen
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .receive message empty endSuccess failedReply payload := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have localAccepted : Analysis.localAdmitted calls program bindingChecked regionFuel before = true := by
    unfold Analysis.configurationAdmitted at admitted
    simp only [notTerminal, Bool.false_eq_true, if_false] at admitted
    split at admitted
    next rejected => contradiction
    next allowed =>
      rw [nodeHere] at admitted
      exact admitted
  have beforeShape : before.phase = .clear ∧ before.work = .empty := by
    simpa only [Analysis.localAdmitted, notTerminal, Bool.false_eq_true, if_false, nodeHere,
      decide_eq_true_eq] using localAccepted
  have shape : Projection.phase s = .clear ∧
      Projection.classifyWork (storeWork s.external (s.network.stores s.key.lane.peer)) = .empty := by
    simpa only [before, Analysis.normalize, Analysis.refresh, Projection.state] using beforeShape
  obtain ⟨noDelivery, noHeld⟩ := Projection.clear_phase s shape.1
  have quiet := Projection.classify_work_sound (storeWork s.external (s.network.stores s.key.lane.peer))
  rw [shape.2] at quiet
  have noRoot : (s.network.stores s.key.lane.peer).active = none := by
    cases active : (s.network.stores s.key.lane.peer).active with
    | none => rfl
    | some root => simp [PortCases.Work.allows, storeWork, active] at quiet
  let candidate := Analysis.refresh { before with
    control := message
    driverSource := none
    driverReturn := none
    endValues := Vector.ofFn fun _ ↦ false
    resultCases := Vector.ofFn fun _ ↦ .unknown
    fact := .message s.pc message
    pending := false
    phase := .processing s.pc
    dependencies := Vector.ofFn fun port ↦ if port = payload then true else before.dependencies[port] }
  have beforeControl : before.control = s.pc := rfl
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    simp [candidate, Analysis.localSuccessors, notTerminal, node, beforeShape.1, beforeControl]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure, Projection.state,
      Projection.phase, Projection.fact, Projection.root, Network.advance, putWorker,
      noDelivery, noHeld, noRoot]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- A concrete Empty receipt is represented by the solver's Empty successor. -/
theorem certified_receive_empty {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (message empty endSuccess failedReply : Fin count) (payload : Fin ports)
    (operation : Nat) (node : calls s.pc = .receive message empty endSuccess failedReply payload)
    (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := empty
      driverSource := none
      driverReturn := none
      endValues := fun _ ↦ false
      resultCases := fun _ ↦ .unknown
      fact := none
      pendingEnd := none
      receiveInfo := .empty s.pc empty
      network := s.network.advance s.key.lane (s.network.channels s.key.lane) operation }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := empty
    driverSource := none
    driverReturn := none
    endValues := fun _ ↦ false
    resultCases := fun _ ↦ .unknown
    fact := none
    pendingEnd := none
    receiveInfo := .empty s.pc empty
    network := s.network.advance s.key.lane (s.network.channels s.key.lane) operation }
  let candidate := Analysis.refresh { before with
    control := empty
    fact := .empty s.pc empty
    pending := false
    driverSource := none
    driverReturn := none
    endValues := Vector.ofFn fun _ ↦ false
    resultCases := Vector.ofFn fun _ ↦ .unknown }
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .receive message empty endSuccess failedReply payload := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have beforeControl : before.control = s.pc := rfl
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    simp [candidate, Analysis.localSuccessors, notTerminal, node, beforeControl]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure, Projection.state,
      Projection.phase, Projection.fact, Projection.root, Network.advance, putWorker]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- Refusal with or without an acquired token reaches the non-End solver edge. -/
theorem certified_receive_failed {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (message empty endSuccess failedReply : Fin count) (payload : Fin ports)
    (operation : Nat) (advance : Bool) (node : calls s.pc = .receive message empty endSuccess failedReply payload)
    (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := failedReply
      driverSource := none
      driverReturn := none
      endValues := fun _ ↦ false
      resultCases := fun _ ↦ .unknown
      fact := none
      pendingEnd := none
      receiveInfo := .none
      network := if advance then s.network.advance s.key.lane (s.network.channels s.key.lane) operation else s.network }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := failedReply
    driverSource := none
    driverReturn := none
    endValues := fun _ ↦ false
    resultCases := fun _ ↦ .unknown
    fact := none
    pendingEnd := none
    receiveInfo := .none
    network := if advance then s.network.advance s.key.lane (s.network.channels s.key.lane) operation else s.network }
  let candidate := Analysis.refresh { before with
    control := failedReply
    fact := .none
    pending := false
    driverSource := none
    driverReturn := none
    endValues := Vector.ofFn fun _ ↦ false
    resultCases := Vector.ofFn fun _ ↦ .unknown }
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .receive message empty endSuccess failedReply payload := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have beforeControl : before.control = s.pc := rfl
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    simp [candidate, Analysis.localSuccessors, notTerminal, node, beforeControl]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    cases advance <;>
      simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure, Projection.state,
        Projection.phase, Projection.fact, Projection.root, Network.advance, putWorker]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- A concrete End observation reaches only the solver's pending-reply state. -/
theorem certified_receive_end_pending {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (message empty endSuccess failedReply : Fin count) (payload : Fin ports)
    (operation : Nat) (node : calls s.pc = .receive message empty endSuccess failedReply payload)
    (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := endSuccess
      driverSource := none
      driverReturn := none
      endValues := fun _ ↦ false
      resultCases := fun _ ↦ .unknown
      fact := none
      pendingEnd := some ⟨s.key, operation, s.pc, endSuccess⟩
      receiveInfo := .none
      network := s.network.advance s.key.lane
        { s.network.channels s.key.lane with observedEnd := true } operation
      events := ⟨⟨s.key, operation, s.pc, endSuccess⟩, s.network.channels s.key.lane⟩ :: s.events }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := endSuccess
    driverSource := none
    driverReturn := none
    endValues := fun _ ↦ false
    resultCases := fun _ ↦ .unknown
    fact := none
    pendingEnd := some ⟨s.key, operation, s.pc, endSuccess⟩
    receiveInfo := .none
    network := s.network.advance s.key.lane
      { s.network.channels s.key.lane with observedEnd := true } operation
    events := ⟨⟨s.key, operation, s.pc, endSuccess⟩, s.network.channels s.key.lane⟩ :: s.events }
  let candidate := Analysis.refresh { before with
    control := endSuccess
    driverSource := none
    driverReturn := none
    endValues := Vector.ofFn fun _ ↦ false
    resultCases := Vector.ofFn fun _ ↦ .unknown
    fact := .endPending s.pc endSuccess
    pending := true }
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .receive message empty endSuccess failedReply payload := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have beforeControl : before.control = s.pc := rfl
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    simp [candidate, Analysis.localSuccessors, notTerminal, node, beforeControl]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure, Projection.state,
      Projection.phase, Projection.fact, Projection.root, Network.advance, putWorker]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- A successful reply to the actual pending End enters the solver's End successor. -/
theorem certified_end_reply {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (next : Fin count) (target : Fin ports) (fact : EndFact count)
    (node : calls s.pc = .endReply next target) (pending : s.pendingEnd = some fact)
    (same : fact.key = s.key) (consistent : ReplyConsistent s) (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := next
      driverSource := none
      driverReturn := none
      resultCases := fun _ ↦ .unknown
      fact := some { fact with resultEdge := next }
      pendingEnd := none
      receiveInfo := .none
      derived := fun port ↦ if port = target then false else s.derived port
      endValues := fun _ ↦ false }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := next
    driverSource := none
    driverReturn := none
    resultCases := fun _ ↦ .unknown
    fact := some { fact with resultEdge := next }
    pendingEnd := none
    receiveInfo := .none
    derived := fun port ↦ if port = target then false else s.derived port
    endValues := fun _ ↦ false }
  have noFact : s.fact = none := by
    rcases consistent with noFact | noPending
    · exact noFact
    · simp [pending] at noPending
  have beforeFact : before.fact = .endPending fact.receiveSite fact.resultEdge := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact, noFact, pending, same]
  let candidate := Analysis.refresh { before with
    control := next
    driverSource := none
    driverReturn := none
    resultCases := Vector.ofFn fun _ ↦ .unknown
    endValues := Vector.ofFn fun _ ↦ false
    fact := .endFact fact.receiveSite next
    pending := false
    dependencies := Vector.ofFn fun port ↦ if port = target then false else before.dependencies[port] }
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .endReply next target := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    simp [candidate, Analysis.localSuccessors, notTerminal, nodeHere, beforeFact]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure,
      Projection.state, Projection.fact, Projection.phase, Projection.root, noFact, pending, same]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- Either actual branch is present in the solver's normal successors. -/
theorem certified_branch_successor {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (operands : List (Fin ports)) (yes no next : Fin count)
    (node : calls s.pc = .branch operands yes no) (selected : next = yes ∨ next = no)
    (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with pc := next, driverSource := none, driverReturn := none }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with pc := next, driverSource := none, driverReturn := none }
  let candidate := Analysis.refresh { before with control := next, driverSource := none, driverReturn := none }
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .branch operands yes no := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    rcases selected with rfl | rfl <;> simp [candidate, Analysis.localSuccessors, notTerminal, nodeHere]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure,
      Projection.state, Projection.fact, Projection.phase, Projection.root]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- Actual forwarding propagates every operand dependency to its destination. -/
theorem certified_forward_successor {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (kind : ForwardKind) (operands : List (Fin ports))
    (target : Fin ports) (next : Fin count)
    (node : calls s.pc = .forward kind operands target next) (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := next
      derived := fun port ↦ if port = target then operands.any s.derived || s.derived port else s.derived port
      endValues := forwardEndValue kind operands target s.endValues
      resultCases := forwardResultCase kind operands target s.resultCases
      driverReturn := none
      driverSource := retainDriverSource target s.driverSource }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := next
    derived := fun port ↦ if port = target then operands.any s.derived || s.derived port else s.derived port
    endValues := forwardEndValue kind operands target s.endValues
    resultCases := forwardResultCase kind operands target s.resultCases
    driverReturn := none
    driverSource := retainDriverSource target s.driverSource }
  let candidate := Analysis.refresh { before with
    control := next
    driverReturn := none
    driverSource := retainDriverSource target before.driverSource
    endValues := Vector.ofFn (forwardEndValue kind operands target (fun port ↦ before.endValues[port]))
    resultCases := Vector.ofFn (forwardResultCase kind operands target (fun port ↦ before.resultCases[port]))
    dependencies := Vector.ofFn fun port ↦ if port = target then
      (operands.any fun operand ↦ before.dependencies[operand]) || before.dependencies[port]
      else before.dependencies[port] }
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .forward kind operands target next := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    simp [candidate, Analysis.localSuccessors, notTerminal, nodeHere]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure,
      Projection.state, Projection.fact, Projection.phase, Projection.root]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- Actual End-shaped and non-End constructors retain distinct provenance. -/
theorem certified_result_successor {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (target : Fin ports) (next : Fin count) (isEnd : Bool)
    (node : calls s.pc = if isEnd then .endResult target next else .otherResult target next)
    (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := next
      derived := fun port ↦ if port = target then false else s.derived port
      endValues := fun port ↦ if port = target then (isEnd && hasCurrentEnd s) else s.endValues port
      resultCases := fun port ↦ if port = target then (if isEnd then .endValue else .otherValue) else s.resultCases port
      driverReturn := none
      driverSource := none }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := next
    derived := fun port ↦ if port = target then false else s.derived port
    endValues := fun port ↦ if port = target then (isEnd && hasCurrentEnd s) else s.endValues port
    resultCases := fun port ↦ if port = target then (if isEnd then .endValue else .otherValue) else s.resultCases port
    driverReturn := none
    driverSource := none }
  let candidate := Analysis.refresh { before with
    control := next
    driverReturn := none
    driverSource := none
    dependencies := Vector.ofFn fun port ↦ if port = target then false else before.dependencies[port]
    endValues := Vector.ofFn fun port ↦ if port = target then (isEnd && hasCurrentEnd s) else before.endValues[port]
    resultCases := Vector.ofFn fun port ↦ if port = target then (if isEnd then .endValue else .otherValue) else before.resultCases[port] }
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = if isEnd then .endResult target next else .otherResult target next := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have endFlag : (match before.fact with | .endFact _ _ => true | _ => false) = hasCurrentEnd s := by
    cases fact : s.fact with
    | none =>
      cases pending : s.pendingEnd with
      | none =>
        cases info : s.receiveInfo <;>
          simp [before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
            hasCurrentEnd, fact, pending, info]
      | some origin =>
        by_cases same : origin.key = s.key <;>
          simp [before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
            hasCurrentEnd, fact, pending, same]
    | some origin =>
      by_cases same : origin.key = s.key <;>
        simp [before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
          hasCurrentEnd, fact, same]
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    cases isEnd <;> simp [candidate, Analysis.localSuccessors, notTerminal, nodeHere, endFlag]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure,
      Projection.state, Projection.fact, Projection.phase, Projection.root]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    cases isEnd <;> simp only [Analysis.configurationSuccessors, nodeHere, Bool.false_eq_true,
      if_false, if_true]
    all_goals exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- The actual oldest-frame match consumes the returned authenticated End value. -/
theorem certified_match_end_yes {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (source : Fin ports) (yes no : Fin count) (fact : EndFact count)
    (node : calls s.pc = .matchEnd source yes no) (value : s.endValues source = true)
    (actual : s.resultCases source = .endValue) (authentic : s.fact = some fact)
    (same : fact.key = s.key) (outer : s.frames = [])
    (returned : s.driverReturn = some (s.pc, source)) (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with pc := yes, driverReturn := none, driverSource := some source }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with pc := yes, driverReturn := none, driverSource := some source }
  let candidate := Analysis.refresh { before with control := yes, driverReturn := none, driverSource := some source }
  have nodeHere : calls before.control = .matchEnd source yes no := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have caseHere : before.resultCases[source] = .endValue := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using actual
  have valueHere : before.endValues[source] = true := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using value
  have factHere : (match before.fact with | .endFact _ _ => true | _ => false) = true := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact, authentic, same]
  have noFrames : ∀ site : Fin count, before.frameSites[site] = false := by
    intro site
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, outer]
  have returnHere : before.driverReturn = some (before.control, source) := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using returned
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    simp [candidate, Analysis.localSuccessors, notTerminal, nodeHere, caseHere, valueHere, factHere,
      noFrames, returnHere]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure,
      Projection.state, Projection.fact, Projection.phase, Projection.root]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- A non-End or unknown value retains the ordinary non-End match arm. -/
theorem certified_match_end_no {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (source : Fin ports) (yes no : Fin count)
    (node : calls s.pc = .matchEnd source yes no) (notEnd : s.resultCases source ≠ .endValue)
    (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    let after := { s with
      pc := no
      fact := none
      pendingEnd := none
      receiveInfo := .none
      driverReturn := none
      driverSource := none }
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 →
      (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let after := { s with
    pc := no
    fact := none
    pendingEnd := none
    receiveInfo := .none
    driverReturn := none
    driverSource := none }
  let candidate := Analysis.refresh { before with
    control := no
    fact := .none
    pending := false
    driverReturn := none
    driverSource := none }
  have nodeHere : calls before.control = .matchEnd source yes no := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have caseHere : before.resultCases[source] = s.resultCases source := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state]
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    simp only [Analysis.localSuccessors, notTerminal, Bool.false_eq_true, if_false, nodeHere, caseHere]
    cases actual : s.resultCases source <;> simp_all [candidate]
  have projected : Analysis.normalize calls regionFuel candidate =
      Analysis.normalize calls regionFuel (Projection.state calls regionFuel after) := by
    simp [candidate, before, after, Analysis.normalize, Analysis.refresh, Analysis.dependencyClosure,
      Projection.state, Projection.fact, Projection.phase, Projection.root]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, congrArg (fun state ↦
      (⟨parentEntry, state⟩ : Analysis.Configuration count ports)) projected⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  exact certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge

/-- An unverified possible End follows the success arm but loses completion authority. -/
theorem certified_match_end_unverified {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (s : Machine count ports) (source : Fin ports) (yes no : Fin count)
    (node : calls s.pc = .matchEnd source yes no) (possibleEnd : s.resultCases source ≠ .otherValue)
    (unverified : ¬ (s.resultCases source = .endValue ∧ s.endValues source = true ∧
      (∃ origin, s.fact = some origin ∧ origin.key = s.key) ∧ s.frames = [] ∧
      s.driverReturn = some (s.pc, source))) (healthy : s.network.failed = false) :
    let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
    (⟨parentEntry, before⟩ : Analysis.Configuration count ports) ∈ answer.1 → False := by
  dsimp only
  intro seen
  let before := Analysis.normalize calls regionFuel (Projection.state calls regionFuel s)
  let candidate := Analysis.refresh { before with
    control := yes
    fact := .none
    driverReturn := none
    driverSource := none
    tainted := true }
  have notTerminal : before.terminal = false := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls before.control = .matchEnd source yes no := by
    simpa [before, Analysis.normalize, Analysis.refresh, Projection.state] using node
  have caseHere : before.resultCases[source] = s.resultCases source := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state]
  have valueHere : before.endValues[source] = s.endValues source := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state]
  have returnHere : before.driverReturn = s.driverReturn ∧ before.control = s.pc := by
    simp [before, Analysis.normalize, Analysis.refresh, Projection.state]
  have factHere : (match before.fact with | .endFact _ _ => true | _ => false) = hasCurrentEnd s := by
    cases fact : s.fact with
    | none =>
      cases pending : s.pendingEnd with
      | none =>
        cases info : s.receiveInfo <;>
          simp [before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
            hasCurrentEnd, fact, pending, info]
      | some origin =>
        by_cases same : origin.key = s.key <;>
          simp [before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
            hasCurrentEnd, fact, pending, same]
    | some origin =>
      by_cases same : origin.key = s.key <;>
        simp [before, Analysis.normalize, Analysis.refresh, Projection.state, Projection.fact,
          hasCurrentEnd, fact, same]
  have authorizedFalse : (decide (before.resultCases[source] = .endValue) && before.endValues[source] &&
      (match before.fact with | .endFact _ _ => true | _ => false) &&
      (List.finRange count).all (fun site ↦ !before.frameSites[site]) &&
      decide (before.driverReturn = some (before.control, source))) = false := by
    cases authorized : (decide (before.resultCases[source] = .endValue) && before.endValues[source] &&
        (match before.fact with | .endFact _ _ => true | _ => false) &&
        (List.finRange count).all (fun site ↦ !before.frameSites[site]) &&
        decide (before.driverReturn = some (before.control, source))) with
    | false => rfl
    | true =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at authorized
      obtain ⟨caseValue, value, fact, frames, returned⟩ := authorized
      have empty : s.frames = [] := by
        cases actualFrames : s.frames with
        | nil => rfl
        | cons head tail =>
          have check := List.all_eq_true.mp frames head.continuation (List.mem_finRange _)
          simp [before, Analysis.normalize, Analysis.refresh, Projection.state, actualFrames] at check
      have origin : ∃ origin, s.fact = some origin ∧ origin.key = s.key := by
        rw [factHere] at fact
        cases present : s.fact with
        | none => simp [hasCurrentEnd, present] at fact
        | some current =>
          refine ⟨current, rfl, ?_⟩
          simpa [hasCurrentEnd, present] using fact
      apply False.elim
      apply unverified
      exact ⟨by simpa [caseHere] using caseValue, by simpa [valueHere] using value,
        origin, empty, by simpa [returnHere.1, returnHere.2] using returned⟩
  have member : candidate ∈ Analysis.localSuccessors calls program bindingChecked regionFuel before := by
    rw [caseHere] at authorizedFalse
    simp only [Analysis.localSuccessors, notTerminal, Bool.false_eq_true, if_false, nodeHere, caseHere]
    cases actual : s.resultCases source with
    | endValue =>
      simp only [actual] at authorizedFalse
      simp only [authorizedFalse]
      simp [candidate, notTerminal]
    | otherValue => exact False.elim (possibleEnd actual)
    | unknown =>
      simp only [actual] at authorizedFalse
      simp only [authorizedFalse]
      simp [candidate, notTerminal]
  have edge : (⟨parentEntry, Analysis.normalize calls regionFuel candidate⟩ :
      Analysis.Configuration count ports) ∈
      Analysis.configurationSuccessors calls program bindingChecked regionFuel answer.2 ⟨parentEntry, before⟩ := by
    simp only [Analysis.configurationSuccessors, nodeHere]
    exact List.mem_map.mpr ⟨candidate, member, rfl⟩
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have reached := certified.2.2.1 ⟨parentEntry, before⟩ seen _ edge
  have admitted := certified.2.1 ⟨parentEntry, Analysis.normalize calls regionFuel candidate⟩ reached
  simp [Analysis.configurationAdmitted, candidate, Analysis.normalize, Analysis.refresh, notTerminal] at admitted

/-- Every healthy actual control step preserves the reached solver configuration. -/
theorem certified_control_successor {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (key : Key) (ownerSite : Fin count) (before after : Machine count ports)
    (entry : Analysis.State count ports) (keySame : before.key = key) (ownerSame : before.ownerSite = ownerSite)
    (healthy : before.network.failed = false) (normal : after.network.failed = false)
    (consistent : ReplyConsistent before) (chain : FrameChain before.key before.context before.frames)
    (witness : SolverFrames calls regionFuel answer.1 key ownerSite seed before.frames entry)
    (seen : (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel before)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) (step : Step calls before after) :
    ∃ nextEntry, SolverFrames calls regionFuel answer.1 key ownerSite seed after.frames nextEntry ∧
      (⟨nextEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  cases step with
  | receiveEnd message empty endSuccess failedReply payload operation node read live committed current running channelHealthy sealed emptyQueue =>
      exact ⟨entry, witness, certified_receive_end_pending calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before message empty endSuccess failedReply payload operation node healthy seen⟩
  | receiveMessage message empty endSuccess failedReply payload operation item tail node read live committed current running channelHealthy head =>
      exact ⟨entry, witness, certified_receive_message calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before message empty endSuccess failedReply payload operation item tail node healthy seen⟩
  | receiveEmpty message empty endSuccess failedReply payload operation node read live committed current running channelHealthy unsealed emptyQueue =>
      exact ⟨entry, witness, certified_receive_empty calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before message empty endSuccess failedReply payload operation node healthy seen⟩
  | receiveFailed message empty endSuccess failedReply payload operation node read noOperation =>
      refine ⟨entry, witness, ?_⟩
      simpa using certified_receive_failed calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before message empty endSuccess failedReply payload operation false node healthy seen
  | receiveFailedToken message empty endSuccess failedReply payload operation node read live committed current running =>
      refine ⟨entry, witness, ?_⟩
      simpa using certified_receive_failed calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before message empty endSuccess failedReply payload operation true node healthy seen
  | call target continuation context inputs returnSource returnTarget node =>
      have pending := certified_call_pending_clear calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before target continuation context inputs returnSource returnTarget node healthy seen
      exact certified_stack_call_enters calls program bindingChecked regionFuel solverFuel budget seed answer
        accepted key ownerSite before entry target continuation context inputs returnSource returnTarget node
        keySame ownerSame pending healthy witness seen
  | forward kind operands target next node =>
      exact ⟨entry, witness, certified_forward_successor calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before kind operands target next node healthy seen⟩
  | branchYes operands yes no node =>
      exact ⟨entry, witness, certified_branch_successor calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before operands yes no yes node (Or.inl rfl) healthy seen⟩
  | branchNo operands yes no node =>
      exact ⟨entry, witness, certified_branch_successor calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before operands yes no no node (Or.inr rfl) healthy seen⟩
  | endReply next target fact node pending same =>
      exact ⟨entry, witness, certified_end_reply calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before next target fact node pending same consistent healthy seen⟩
  | endResult target next node =>
      refine ⟨entry, witness, ?_⟩
      simpa using certified_result_successor calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before target next true (by simpa using node) healthy seen
  | otherResult target next node =>
      refine ⟨entry, witness, ?_⟩
      simpa using certified_result_successor calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before target next false (by simpa using node) healthy seen
  | matchEndYes source yes no fact node value actual authentic same outer returned =>
      exact ⟨entry, witness, certified_match_end_yes calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before source yes no fact node value actual authentic same outer returned healthy seen⟩
  | matchEndNo source yes no node notEnd =>
      exact ⟨entry, witness, certified_match_end_no calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before source yes no node notEnd healthy seen⟩
  | matchEndUnverified source yes no node possibleEnd unverified =>
      exact False.elim (certified_match_end_unverified calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before source yes no node possibleEnd unverified healthy seen)
  | matchedReturn frame rest node stack same context fact authentic owner =>
      have pending : before.pendingEnd = none := by
        rcases consistent with noFact | pending
        · simp [authentic] at noFact
        · exact pending
      exact certified_stack_return_replayed calls program bindingChecked regionFuel solverFuel budget seed answer
        accepted key ownerSite before entry frame rest fact node stack keySame ownerSame context authentic owner
        pending healthy witness seen
  | normalReturn frame rest node stack same context noFact noPending =>
      exact certified_stack_normal_return_replayed calls program bindingChecked regionFuel solverFuel budget seed answer
        accepted key ownerSite before entry frame rest node stack keySame ownerSame context noFact noPending healthy witness seen
  | otherReturn frame rest value node stack unmatched =>
      exact False.elim (certified_other_return_impossible calls program bindingChecked regionFuel solverFuel budget
        seed answer accepted key ownerSite before entry frame rest value node stack healthy chain witness seen unmatched)
  | failure live =>
      simp [Network.fail] at normal
  | invalidate next node =>
      have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
      have admitted := certified.2.1 ⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel before)⟩ seen
      simp [Analysis.configurationAdmitted, Analysis.localAdmitted, Analysis.normalize, Analysis.refresh,
        Projection.state, healthy, node] at admitted

/-- Every healthy actual execution step preserves the reached solver configuration. -/
theorem certified_execution_successor {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (key : Key) (ownerSite : Fin count) (before after : Machine count ports)
    (entry : Analysis.State count ports) (keySame : before.key = key) (ownerSame : before.ownerSite = ownerSite)
    (healthy : before.network.failed = false) (normal : after.network.failed = false)
    (consistent : ReplyConsistent before) (chain : FrameChain before.key before.context before.frames)
    (witness : SolverFrames calls regionFuel answer.1 key ownerSite seed before.frames entry)
    (seen : (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel before)⟩ :
      Analysis.Configuration count ports) ∈ answer.1)
    (step : ExecutionStep calls program bindingChecked before after) :
    ∃ nextEntry, SolverFrames calls regionFuel answer.1 key ownerSite seed after.frames nextEntry ∧
      (⟨nextEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel after)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have admitted := certified.2.1 ⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel before)⟩ seen
  cases step with
  | control edge =>
      exact certified_control_successor calls program bindingChecked regionFuel solverFuel budget seed answer
        accepted key ownerSite before _ entry keySame ownerSame healthy normal consistent chain witness seen edge
  | dispatch next graph item site template capture consumer node constructed delivery live committed networkHealthy running held
      notDispatched identity owned noClause driver admission fresh unique interpretation kind openStore storeHealthy =>
      exact ⟨entry, witness, certified_dispatch_successor calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before next graph item site template capture consumer node healthy delivery
        constructed admission kind seen⟩
  | processing regionEntry next marker item site pre post capture consumer finalDerived node delivery path markerNode
      live committed networkHealthy running found identity owned dispatched active armed noNested storeHealthy =>
      exact ⟨entry, witness, certified_processing_successor calls program bindingChecked regionFuel solverFuel budget
        seed entry answer accepted before regionEntry next marker item site pre post capture consumer finalDerived
        node healthy delivery found active path markerNode seen⟩
  | processingUnverified regionEntry next network external derived node running unverified steps =>
      by_cases checked : Region.check program bindingChecked regionFuel .processing regionEntry = true
      · exact False.elim (Region.checked_excludes_unverified program bindingChecked regionFuel regionEntry checked unverified)
      · have rejected : Region.check program bindingChecked regionFuel .processing regionEntry = false := by
          cases h : Region.check program bindingChecked regionFuel .processing regionEntry <;> simp_all
        simp [Analysis.configurationAdmitted, Analysis.localAdmitted, Analysis.normalize, Analysis.refresh,
          Projection.state, healthy, node, rejected] at admitted
  | unverifiedDispatch next graph network external derived node running rejected steps =>
      simp [Analysis.configurationAdmitted, Analysis.localAdmitted, Analysis.normalize, Analysis.refresh,
        Projection.state, healthy, node, rejected] at admitted
  | unverifiedCapture regionEntry next item site capture consumer network external derived node running delivery active mismatch steps =>
      have invalid : Projection.root before = .invalid := by
        simp only [Projection.root, delivery, active]
        split
        next shape =>
          rcases shape with ⟨branch, owned, armed, nested, kind⟩
          rcases mismatch with badBranch | badOwner | badArmed | badNested | badKind
          · exact False.elim (badBranch branch)
          · exact False.elim (badOwner owned)
          · exact False.elim (badArmed armed)
          · exact False.elim (badNested nested)
          · exact False.elim (badKind kind)
        next => rfl
      cases phase : Projection.phase before <;>
        simp [Analysis.configurationAdmitted, Analysis.localAdmitted, Analysis.normalize, Analysis.refresh,
          Projection.state, healthy, node, invalid, phase] at admitted
  | unverified network external next node running steps =>
      simp [Analysis.configurationAdmitted, Analysis.localAdmitted, Analysis.normalize, Analysis.refresh,
        Projection.state, healthy, node] at admitted

/-- Every healthy actual execution reaches its corresponding solver configuration. -/
theorem certified_execution_reached {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (first last : Machine count ports)
    (seedIs : seed = Analysis.normalize calls regionFuel (Projection.state calls regionFuel first))
    (noFact : first.fact = none) (initialFrames : first.frames = [])
    (execution : Execution calls program bindingChecked first last) :
    last.network.failed = false →
    ∃ entry, SolverFrames calls regionFuel answer.1 first.key first.ownerSite seed last.frames entry ∧
      (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel last)⟩ :
        Analysis.Configuration count ports) ∈ answer.1 := by
  induction execution with
  | refl =>
      intro normal
      have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
      refine ⟨seed, ?_, ?_⟩
      · have empty : SolverFrames calls regionFuel answer.1 first.key first.ownerSite seed [] seed :=
          SolverFrames.base
        simpa [initialFrames] using empty
      · rw [← seedIs]
        exact certified.1
  | @next middle last prior edge ih =>
      intro normal
      have middleHealthy : middle.network.failed = false := by
        cases failed : middle.network.failed with
        | false => rfl
        | true =>
            have remains := Ash.WorkerChannel.terminal_failure_remains failed (execution_step_network edge)
            simp [normal] at remains
      obtain ⟨entry, witness, seen⟩ := ih middleHealthy
      have identity := execution_preserves_identity prior
      have consistent := execution_preserves_reply_consistency (Or.inl noFact) prior
      have initialChain : FrameChain first.key first.context first.frames := by
        simp [FrameChain, initialFrames]
      have chain := execution_preserves_frame_chain initialChain prior
      exact certified_execution_successor calls program bindingChecked regionFuel solverFuel budget seed answer
        accepted first.key first.ownerSite middle last entry identity.1 identity.2 middleHealthy normal
        consistent chain witness seen edge

/-- Every actual execution is either solver-reached or permanently unable to finish. -/
theorem certified_execution_coverage {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (first last : Machine count ports)
    (seedIs : seed = Analysis.normalize calls regionFuel (Projection.state calls regionFuel first))
    (noFact : first.fact = none) (initialFrames : first.frames = [])
    (execution : Execution calls program bindingChecked first last) :
    (last.network.failed = false ∧
      ∃ entry, SolverFrames calls regionFuel answer.1 first.key first.ownerSite seed last.frames entry ∧
        (⟨entry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel last)⟩ :
          Analysis.Configuration count ports) ∈ answer.1) ∨
    (last.network.failed = true ∧ Projection.finishAccepted calls (Projection.state calls regionFuel last) = false) := by
  cases failed : last.network.failed with
  | false =>
    exact Or.inl ⟨rfl, certified_execution_reached calls program bindingChecked regionFuel solverFuel budget
      seed answer accepted first last seedIs noFact initialFrames execution failed⟩
  | true => exact Or.inr ⟨rfl, Projection.failed_finish_refused calls regionFuel last failed⟩

/-- The finite finish predicate can only name a concrete successful End reply. -/
theorem Projection.accepted_end {count ports : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports) (fuel : Nat)
    (s : Machine count ports) (accepted : Projection.finishAccepted calls (Projection.state calls fuel s) = true) :
    ∃ result, s.fact = some result ∧ result.key = s.key := by
  cases projected : Projection.fact s with
  | none | invalid | message _ _ | empty _ _ | endPending _ _ =>
      simp [Projection.finishAccepted, Projection.state, projected] at accepted
  | endFact site edge =>
      cases actual : s.fact with
      | none =>
          cases pending : s.pendingEnd with
          | none =>
              cases info : s.receiveInfo <;> simp [Projection.fact, actual, pending, info] at projected
          | some origin =>
              by_cases same : origin.key = s.key <;> simp [Projection.fact, actual, pending, same] at projected
      | some result =>
          by_cases same : result.key = s.key
          · exact ⟨result, rfl, same⟩
          · simp [Projection.fact, actual, same] at projected

/-- A checked finish reached by unified execution has a genuine End origin. -/
theorem execution_accepted_finish_has_genuine_end {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel : Nat) (first last : Machine count ports)
    (noFact : first.fact = none) (noPending : first.pendingEnd = none) (noEvents : first.events = [])
    (execution : Execution calls program bindingChecked first last)
    (accepted : Projection.finishAccepted calls (Projection.state calls fuel last) = true) :
    ∃ result event, last.fact = some result ∧ result.key = last.key ∧
      event ∈ last.events ∧ event.fact.SameOrigin result ∧ event.Genuine := by
  obtain ⟨result, present, same⟩ := Projection.accepted_end calls fuel last accepted
  have valid := execution_preserves_authentication
    (empty_seed_authenticated first noFact noPending noEvents) execution
  obtain ⟨event, member, origin⟩ := valid.2.1 result present
  exact ⟨result, event, present, same, member, origin, valid.1 event member⟩

/-- Once unsupported work is reached, later modeled control cannot erase its taint. -/
theorem execution_preserves_taint {count ports bindings : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports}
    {program : Fin count → Region.Node count ports bindings} {bindingChecked : Fin bindings → Bool}
    {first last : Machine count ports} (tainted : first.tainted = true)
    (execution : Execution calls program bindingChecked first last) : last.tainted = true := by
  induction execution with
  | refl => exact tainted
  | next _ step ih =>
      cases step with
      | control edge => cases edge <;> first | exact ih | rfl
      | dispatch | processing => exact ih
      | processingUnverified | unverifiedDispatch | unverifiedCapture | unverified => rfl

/-- A checked unified finish has no held delivery and quiet same-Store work. -/
theorem execution_accepted_finish_cut {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel : Nat) (first last : Machine count ports)
    (noFact : first.fact = none) (noPending : first.pendingEnd = none) (noEvents : first.events = [])
    (execution : Execution calls program bindingChecked first last)
    (accepted : Projection.finishAccepted calls (Projection.state calls fuel last) = true) :
    (∃ result event, last.fact = some result ∧ result.key = last.key ∧
      event ∈ last.events ∧ event.fact.SameOrigin result ∧ event.Genuine) ∧
    last.currentDelivery = none ∧ (last.network.channels last.key.lane).held = [] ∧
    PortCases.Work.empty.allows (storeWork last.external (last.network.stores last.key.lane.peer)) ∧
    Projection.framesSafe calls last fuel = true ∧ NetworkTrace first.network last.network := by
  have shape := Projection.accepted_shape calls (Projection.state calls fuel last) accepted
  have clear : Projection.phase last = .clear := shape.2.2.1
  obtain ⟨delivery, held⟩ := Projection.clear_phase last clear
  have work : Projection.classifyWork (storeWork last.external (last.network.stores last.key.lane.peer)) =
      .empty := shape.2.2.2.1
  have quiet := Projection.classify_work_sound (storeWork last.external (last.network.stores last.key.lane.peer))
  rw [work] at quiet
  exact ⟨execution_accepted_finish_has_genuine_end calls program bindingChecked fuel first last
      noFact noPending noEvents execution accepted, delivery, held, quiet, shape.2.2.2.2.2.1,
      execution_network execution⟩

/-- A solver-reached normal finish yields the concrete End and same-Store cut. -/
theorem certified_reached_finish_cut {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed parentEntry : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (first last : Machine count ports)
    (noFact : first.fact = none) (noPending : first.pendingEnd = none) (noEvents : first.events = [])
    (execution : Execution calls program bindingChecked first last)
    (healthy : last.network.failed = false) (finishNode : calls last.pc = .finishReceive)
    (reached : (⟨parentEntry, Analysis.normalize calls regionFuel (Projection.state calls regionFuel last)⟩ :
      Analysis.Configuration count ports) ∈ answer.1) :
    (∃ result event, last.fact = some result ∧ result.key = last.key ∧
      event ∈ last.events ∧ event.fact.SameOrigin result ∧ event.Genuine) ∧
    last.currentDelivery = none ∧ (last.network.channels last.key.lane).held = [] ∧
    PortCases.Work.empty.allows (storeWork last.external (last.network.stores last.key.lane.peer)) ∧
    Projection.framesSafe calls last regionFuel = true ∧ NetworkTrace first.network last.network := by
  let state := Analysis.normalize calls regionFuel (Projection.state calls regionFuel last)
  have certified := Analysis.solveFrom_certified calls program bindingChecked regionFuel solverFuel budget seed answer accepted
  have admitted := certified.2.1 ⟨parentEntry, state⟩ reached
  have notTerminal : state.terminal = false := by
    simp [state, Analysis.normalize, Analysis.refresh, Projection.state, healthy]
  have nodeHere : calls state.control = .finishReceive := by
    simpa [state, Analysis.normalize, Analysis.refresh, Projection.state] using finishNode
  have finish : Projection.finishAccepted calls state = true := by
    unfold Analysis.configurationAdmitted at admitted
    simp only [notTerminal, Bool.false_eq_true, if_false] at admitted
    split at admitted
    next rejected => contradiction
    next allowed =>
      rw [nodeHere] at admitted
      simpa [Analysis.localAdmitted, notTerminal, nodeHere] using admitted
  have shape := Projection.accepted_shape calls state finish
  obtain ⟨site, edge, projectedFact⟩ := shape.2.1
  have rawSuffix := normalized_frame_sites_sound calls regionFuel last shape.2.2.2.2.2.1
  have rawEscape : (Projection.state calls regionFuel last).escape = false := by
    simpa [state, Analysis.normalize, Analysis.refresh, Projection.state, Bool.not_and, Bool.or_assoc] using shape.2.2.2.2.1
  have rawNode : calls (Projection.state calls regionFuel last).control = .finishReceive := finishNode
  have rawFact : (Projection.state calls regionFuel last).fact = .endFact site edge := projectedFact
  have rawPhase : (Projection.state calls regionFuel last).phase = .clear := shape.2.2.1
  have rawWork : (Projection.state calls regionFuel last).work = .empty := shape.2.2.2.1
  have rawFrames : (Projection.state calls regionFuel last).suffixSafe = true := rawSuffix
  have rawDriver : (Projection.state calls regionFuel last).driverSource.isSome = true := by
    simpa [state, Analysis.normalize, Analysis.refresh] using shape.2.2.2.2.2.2
  have rawAccepted : Projection.finishAccepted calls (Projection.state calls regionFuel last) = true := by
    simp only [Projection.finishAccepted, rawNode, rawFact, rawPhase, rawWork, rawEscape, rawFrames,
      rawDriver, Bool.not_false, Bool.true_and]
  exact execution_accepted_finish_cut calls program bindingChecked regionFuel first last
    noFact noPending noEvents execution rawAccepted


/-- An accepted solver yields the exact completion cut at every healthy actual finish. -/
theorem certified_execution_finish {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (regionFuel solverFuel budget : Nat) (seed : Analysis.State count ports)
    (answer : List (Analysis.Configuration count ports) × List (Analysis.ReturnPair count ports))
    (accepted : Analysis.solveFrom calls program bindingChecked regionFuel solverFuel budget seed = some answer)
    (first last : Machine count ports)
    (seedIs : seed = Analysis.normalize calls regionFuel (Projection.state calls regionFuel first))
    (noFact : first.fact = none) (noPending : first.pendingEnd = none) (noEvents : first.events = [])
    (initialFrames : first.frames = []) (execution : Execution calls program bindingChecked first last)
    (healthy : last.network.failed = false) (finishNode : calls last.pc = .finishReceive) :
    (∃ result event, last.fact = some result ∧ result.key = last.key ∧
      event ∈ last.events ∧ event.fact.SameOrigin result ∧ event.Genuine) ∧
    last.currentDelivery = none ∧ (last.network.channels last.key.lane).held = [] ∧
    PortCases.Work.empty.allows (storeWork last.external (last.network.stores last.key.lane.peer)) ∧
    Projection.framesSafe calls last regionFuel = true ∧ NetworkTrace first.network last.network := by
  obtain ⟨entry, witness, reached⟩ := certified_execution_reached calls program bindingChecked
    regionFuel solverFuel budget seed answer accepted first last seedIs noFact initialFrames execution healthy
  exact certified_reached_finish_cut calls program bindingChecked regionFuel solverFuel budget seed entry answer
    accepted first last noFact noPending noEvents execution healthy finishNode reached


/--
For every modeled normal region path to its marker, admission determines the
cleanup ordering and checked older suffixes. The resulting network trace
finishes the exact held entry. C3 representation and the linked-Core mapping
remain separate premises and obligations.
-/
theorem checked_region_marker_finishes {count ports bindings : Nat}
    (program : Fin count → Region.Node count ports bindings) (bindingChecked : Fin bindings → Bool)
    (fuel : Nat) (pc marker : Fin count) (finalStage : Region.Stage)
    (suffix : Fin count → Suffix.Node count ports) (derived : Fin ports → Bool)
    (frames : List (Frame count ports)) (network : Network) (lane : Worker) (entry : Entry)
    (pre post : List Entry) (capture : Capture) (consumer : Consumer)
    (work : PortCases.Work) (escape : Bool) (external : ExternalWork)
    (represented : work.allows (storeWork external (network.stores lane.peer)))
    (admitted : Region.admit program bindingChecked fuel pc suffix derived
      (frames.map Frame.continuation) capture work escape = true)
    (path : Region.Walk program bindingChecked .processing pc finalStage marker)
    (markerNode : program marker = .marker)
    (safe : network.Safe) (live : network.backing = true)
    (committed : network.committed = true) (networkHealthy : network.failed = false)
    (running : network.returned lane.peer = false)
    (found : (network.channels lane).held = pre ++ entry :: post)
    (identity : capture.branch = entry.id) (owned : entry.id ∈ capture.owners)
    (dispatched : network.dispatched lane.peer entry.id = true)
    (active : (network.stores lane.peer).active = some (capture, consumer))
    (healthy : (network.stores lane.peer).failed = false) :
    ∃ final, NetworkTrace network final ∧
      (final.channels lane).held = pre ++ post ∧
      entry.id ∉ (final.channels lane).held.map Entry.id ∧
      PortCases.Work.empty.allows (storeWork external (final.stores lane.peer)) ∧
      (∀ frame, frame ∈ frames → Suffix.check suffix derived fuel frame.continuation = true) ∧
      final = regionFinal network lane entry pre post capture consumer := by
  have shape := Region.admitted_shape program bindingChecked fuel pc suffix derived
    (frames.map Frame.continuation) capture work escape admitted
  obtain ⟨remaining, markerChecked⟩ := Region.checked_walk path fuel shape.2.2.2.2.1
  have finalEq := Region.accepted_marker_follows_cleanup program bindingChecked remaining
    finalStage marker markerNode markerChecked
  subst finalStage
  let second := stageNetwork network lane capture consumer .cleanupReturned
  let final := second.processingFinished lane entry pre post
    (finishStore (second.stores lane.peer) (finishedCapture capture) consumer)
  have beforeMarker : NetworkTrace network second := by
    exact region_walk_network network lane capture consumer live committed networkHealthy running
      active shape.1 shape.2.1 healthy path
  have ready := (cleanup_then_finish (network.stores lane.peer) capture consumer active
    shape.1 shape.2.1 healthy).2.2.1
  have finishStep : NetworkStep second final := by
    apply NetworkStep.finishProcessing second lane entry pre post (finishedCapture capture) consumer
    · simpa [second, stageNetwork, setStore] using live
    · simpa [second, stageNetwork, setStore] using committed
    · simpa [second, stageNetwork, setStore] using running
    · simpa [second, stageNetwork, setStore] using found
    · simpa [finishedCapture] using identity
    · simpa [finishedCapture] using owned
    · simpa [second, stageNetwork, setStore] using dispatched
    · simp [second, stageNetwork, setStore, putWorker, finishedStore]
    · exact ready
    · simpa [second, stageNetwork, setStore, putWorker, finishedStore] using healthy
  have secondSafe := network_trace_safe safe beforeMarker
  have noRepeat := finished_entry_cannot_repeat (second.channels lane) entry pre post
    (secondSafe.1.1 lane) (by simpa [second, stageNetwork, setStore] using found)
  have activeWork : PortCases.Work.activeOnly.allows (storeWork external (network.stores lane.peer)) := by
    simpa [shape.2.2.1] using represented
  have quiet := finished_active_only_is_quiet (storeWork external (network.stores lane.peer)) activeWork
  refine ⟨final, NetworkTrace.next beforeMarker finishStep, ?_, ?_, ?_, ?_, rfl⟩
  · simp [final, Network.processingFinished, finishChannel, putWorker]
  · simpa [final, Network.processingFinished, putWorker] using noRepeat
  · simpa [final, Network.processingFinished, putWorker, second, stageNetwork, setStore,
      finishStore, storeWork, finishedStore, PortCases.ConcreteWork.finishRoot] using quiet
  · intro frame member
    exact Suffix.checked_caller_frame suffix derived fuel frames frame member shape.2.2.2.2.2


namespace Loop

/-- Concrete successors of the selected read operation. -/
def received (network : Network) (lane : Worker) (operation : Nat) (entry : Entry)
    (tail : List Entry) : Network :=
  let channel := network.channels lane
  network.advance lane { channel with
    received := channel.received ++ [entry]
    queue := tail
    held := channel.held ++ [entry] } operation

def emptyRetry (network : Network) (lane : Worker) (operation : Nat) : Network :=
  network.advance lane (network.channels lane) operation

def observedEnd (network : Network) (lane : Worker) (operation : Nat) : Network :=
  network.advance lane { network.channels lane with observedEnd := true } operation

/--
A finite normal run of the restricted modeled loop. The concrete receive and
root-dispatch steps must exist, each Message path must actually reach its
checked marker, and every recursive frame records the same key and actual call.
Failure and unsupported processing have no normal-run constructor.
-/
inductive Run {count ports bindings : Nat}
    (calls : Fin count → Ash.OneWayCompletion.Node count ports)
    (program : Fin count → Region.Node count ports bindings)
    (bindingChecked : Fin bindings → Bool) (suffix : Fin count → Suffix.Node count ports)
    (key : Key) (external : ExternalWork) : Network → List (Frame count ports) → Network → Prop where
  | endObserved (network : Network) (frames : List (Frame count ports)) (operation : Nat)
      (read : key.side = .read)
      (current : network.operations operation = some ⟨key.lane, .read, key.lane.peer⟩)
      (live : network.backing = true) (committed : network.committed = true)
      (running : network.returned key.lane.peer = false)
      (healthy : (network.channels key.lane).failed = false)
      (sealed : (network.channels key.lane).sealed = true)
      (empty : (network.channels key.lane).queue = []) :
      Run calls program bindingChecked suffix key external network frames
        (observedEnd network key.lane operation)
  | retry (network : Network) (frames : List (Frame count ports)) (operation fuel : Nat)
      (frame : Frame count ports) (final : Network)
      (same : frame.key = key) (call : calls frame.callSite = .call frame.target frame.continuation frame.calleeContext frame.inputs frame.returnSource frame.returnTarget)
      (suffixChecked : Suffix.checkFrames suffix (fun _ ↦ false) fuel
        ((frame :: frames).map Frame.continuation) = true)
      (read : key.side = .read)
      (current : network.operations operation = some ⟨key.lane, .read, key.lane.peer⟩)
      (live : network.backing = true) (committed : network.committed = true)
      (running : network.returned key.lane.peer = false)
      (healthy : (network.channels key.lane).failed = false)
      (openSend : (network.channels key.lane).sealed = false)
      (empty : (network.channels key.lane).queue = [])
      (next : Run calls program bindingChecked suffix key external
        (emptyRetry network key.lane operation) (frame :: frames) final) :
      Run calls program bindingChecked suffix key external network frames final
  | message (network : Network) (frames : List (Frame count ports)) (operation fuel : Nat)
      (frame : Frame count ports) (entry : Entry) (tail : List Entry)
      (capture : Capture) (consumer : Consumer) (pc marker : Fin count)
      (finalStage : Region.Stage) (derived : Fin ports → Bool) (escape : Bool)
      (final : Network)
      (same : frame.key = key) (call : calls frame.callSite = .call frame.target frame.continuation frame.calleeContext frame.inputs frame.returnSource frame.returnTarget)
      (read : key.side = .read)
      (head : (network.channels key.lane).queue = entry :: tail)
      (receivedStep : NetworkStep network (received network key.lane operation entry tail))
      (dispatchStep : NetworkStep (received network key.lane operation entry tail)
        ((received network key.lane operation entry tail).dispatch key.lane entry capture consumer))
      (admitted : Region.admit program bindingChecked fuel pc suffix derived
        ((frame :: frames).map Frame.continuation) capture .activeOnly escape = true)
      (path : Region.Walk program bindingChecked .processing pc finalStage marker)
      (markerNode : program marker = .marker)
      (live : ((received network key.lane operation entry tail).dispatch key.lane entry capture consumer).backing = true)
      (committed : ((received network key.lane operation entry tail).dispatch key.lane entry capture consumer).committed = true)
      (networkHealthy : ((received network key.lane operation entry tail).dispatch key.lane entry capture consumer).failed = false)
      (running : ((received network key.lane operation entry tail).dispatch key.lane entry capture consumer).returned key.lane.peer = false)
      (identity : capture.branch = entry.id) (owned : entry.id ∈ capture.owners)
      (dispatched : ((received network key.lane operation entry tail).dispatch key.lane entry capture consumer).dispatched key.lane.peer entry.id = true)
      (active : (((received network key.lane operation entry tail).dispatch key.lane entry capture consumer).stores key.lane.peer).active = some (capture, consumer))
      (healthy : (((received network key.lane operation entry tail).dispatch key.lane entry capture consumer).stores key.lane.peer).failed = false)
      (next : Run calls program bindingChecked suffix key external
        (regionFinal ((received network key.lane operation entry tail).dispatch key.lane entry capture consumer)
          key.lane entry (network.channels key.lane).held [] capture consumer)
        (frame :: frames) final) :
      Run calls program bindingChecked suffix key external network frames final



/-- Every finite normal run ends in this read operation's actual sealed End step. -/
theorem normal_run_end_witness {count ports bindings : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports}
    {program : Fin count → Region.Node count ports bindings} {bindingChecked : Fin bindings → Bool}
    {suffix : Fin count → Suffix.Node count ports} {key : Key} {external : ExternalWork}
    {first last : Network} {frames : List (Frame count ports)}
    (run : Run calls program bindingChecked suffix key external first frames last) :
    ∃ before operation, last = observedEnd before key.lane operation ∧ key.side = .read ∧
      ChannelStep .read (before.channels key.lane)
        { before.channels key.lane with observedEnd := true } ∧
      NetworkStep before last := by
  induction run with
  | endObserved network frames operation read current live committed running healthy sealed empty =>
      refine ⟨network, operation, rfl, read, ?_, ?_⟩
      · exact ChannelStep.observeEnd (network.channels key.lane) healthy sealed empty
      · apply NetworkStep.channel network operation ⟨key.lane, .read, key.lane.peer⟩
          { network.channels key.lane with observedEnd := true } live committed current rfl running
        exact ChannelStep.observeEnd (network.channels key.lane) healthy sealed empty
  | retry => assumption
  | message => assumption

/--
For every finite modeled normal run from a quiet, empty-held entry, End is
observed and the selected channel and Store are quiet. This is conditional on
the explicit modeled Run relation and its checked native/Core correspondence.
-/
theorem normal_run_observes_end {count ports bindings : Nat}
    {calls : Fin count → Ash.OneWayCompletion.Node count ports}
    {program : Fin count → Region.Node count ports bindings} {bindingChecked : Fin bindings → Bool}
    {suffix : Fin count → Suffix.Node count ports} {key : Key} {external : ExternalWork}
    {first last : Network} {frames : List (Frame count ports)}
    (run : Run calls program bindingChecked suffix key external first frames last) :
    first.Safe → (first.channels key.lane).held = [] →
    PortCases.Work.empty.allows (storeWork external (first.stores key.lane.peer)) →
    (last.channels key.lane).observedEnd = true ∧ (last.channels key.lane).held = [] ∧
      PortCases.Work.empty.allows (storeWork external (last.stores key.lane.peer)) ∧ last.Safe := by
  induction run with
  | endObserved network frames operation read current live committed running healthy sealed empty =>
      intro safe noHeld quiet
      have endStep : NetworkStep network (observedEnd network key.lane operation) := by
        apply NetworkStep.channel network operation ⟨key.lane, .read, key.lane.peer⟩
          { network.channels key.lane with observedEnd := true } live committed current rfl running
        exact ChannelStep.observeEnd (network.channels key.lane) healthy sealed empty
      refine ⟨?_, ?_, ?_, network_step_safe safe endStep⟩
      · simp [observedEnd, Network.advance, putWorker]
      · simpa [observedEnd, Network.advance, putWorker] using noHeld
      · simpa [observedEnd, Network.advance] using quiet
  | retry network frames operation fuel frame final same call suffixChecked read current live
      committed running healthy openSend empty next ih =>
      intro safe noHeld quiet
      have idleStep : NetworkStep network (emptyRetry network key.lane operation) := by
        apply NetworkStep.channel network operation ⟨key.lane, .read, key.lane.peer⟩
          (network.channels key.lane) live committed current rfl running
        exact ChannelStep.idle (network.channels key.lane) .read
      apply ih (network_step_safe safe idleStep)
      · simpa [emptyRetry, Network.advance, putWorker] using noHeld
      · simpa [emptyRetry, Network.advance] using quiet
  | message network frames operation fuel frame entry tail capture consumer pc marker finalStage
      derived escape final same call read head receivedStep dispatchStep admitted path markerNode
      live committed networkHealthy running identity owned dispatched active healthy next ih =>
      intro safe noHeld quiet
      let started := (received network key.lane operation entry tail).dispatch key.lane entry capture consumer
      have startedSafe : started.Safe := network_step_safe (network_step_safe safe receivedStep) dispatchStep
      have selectedWork : PortCases.Work.activeOnly.allows (storeWork external (started.stores key.lane.peer)) := by
        rcases quiet with ⟨_, other⟩
        constructor
        · simp [started, Network.dispatch, putWorker, storeWork]
        · simpa [started, received, Network.dispatch, Network.advance, putWorker, storeWork] using other
      have found : (started.channels key.lane).held = (network.channels key.lane).held ++ entry :: [] := by
        simp [started, received, Network.dispatch, Network.advance, putWorker]
      obtain ⟨after, trace, held, removed, afterQuiet, checkedFrames, afterEq⟩ :=
        checked_region_marker_finishes program bindingChecked fuel pc marker finalStage suffix derived
          (frame :: frames) started key.lane entry (network.channels key.lane).held [] capture consumer
          .activeOnly escape external selectedWork admitted path markerNode startedSafe live committed
          networkHealthy running found identity owned dispatched active healthy
      have afterSafe := network_trace_safe startedSafe trace
      have afterHeld : (after.channels key.lane).held = [] := by simpa [noHeld] using held
      subst after
      exact ih afterSafe afterHeld afterQuiet

end Loop

end Processing
end Ash.OneWayCompletion

#print axioms Ash.OneWayCompletion.receive_end_is_channel_step
#print axioms Ash.OneWayCompletion.step_preserves_authentication
#print axioms Ash.OneWayCompletion.trace_preserves_authentication
#print axioms Ash.OneWayCompletion.empty_seed_authenticated
#print axioms Ash.OneWayCompletion.returned_fact_has_genuine_event
#print axioms Ash.OneWayCompletion.Summary.approx_mono
#print axioms Ash.OneWayCompletion.Summary.finite_converges
#print axioms Ash.OneWayCompletion.Summary.no_base_no_returns
#print axioms Ash.OneWayCompletion.Summary.least

#print axioms Ash.OneWayCompletion.Processing.cleanup_then_finish
#print axioms Ash.OneWayCompletion.Processing.finished_active_only_is_quiet
#print axioms Ash.OneWayCompletion.Processing.network_cleanup_then_finish
#print axioms Ash.OneWayCompletion.Processing.receive_dispatch_cleanup_finish
#print axioms Ash.OneWayCompletion.Suffix.checked_forward
#print axioms Ash.OneWayCompletion.Suffix.checked_branch
#print axioms Ash.OneWayCompletion.Suffix.forbidden_rejected
#print axioms Ash.OneWayCompletion.Suffix.dependent_forward_rejected
#print axioms Ash.OneWayCompletion.Suffix.checked_older_frame
#print axioms Ash.OneWayCompletion.step_preserves_frames
#print axioms Ash.OneWayCompletion.trace_preserves_frames
#print axioms Ash.OneWayCompletion.empty_seed_frames
#print axioms Ash.OneWayCompletion.returned_frame_has_matching_call
#print axioms Ash.OneWayCompletion.Region.branch_checks_both
#print axioms Ash.OneWayCompletion.Region.forbidden_rejected
#print axioms Ash.OneWayCompletion.Region.native_requires_binding
#print axioms Ash.OneWayCompletion.Region.admitted_shape
#print axioms Ash.OneWayCompletion.Suffix.checked_caller_frame
#print axioms Ash.OneWayCompletion.Processing.admitted_region_cleanup
#print axioms Ash.OneWayCompletion.Region.check_step
#print axioms Ash.OneWayCompletion.Region.checked_walk
#print axioms Ash.OneWayCompletion.Region.accepted_marker_follows_cleanup
#print axioms Ash.OneWayCompletion.Processing.network_trace_trans
#print axioms Ash.OneWayCompletion.Processing.region_step_network
#print axioms Ash.OneWayCompletion.Processing.region_walk_network
#print axioms Ash.OneWayCompletion.Processing.checked_region_marker_finishes
#print axioms Ash.OneWayCompletion.Processing.finish_store_work
#print axioms Ash.OneWayCompletion.Processing.Loop.normal_run_observes_end
#print axioms Ash.OneWayCompletion.Processing.Loop.normal_run_end_witness
#print axioms Ash.OneWayCompletion.Suffix.step_fact_origin
#print axioms Ash.OneWayCompletion.Suffix.trace_fact_origin
#print axioms Ash.OneWayCompletion.Analysis.join_end_from_both
#print axioms Ash.OneWayCompletion.Analysis.join_context_mismatch
#print axioms Ash.OneWayCompletion.Analysis.join_dependency_from_left
#print axioms Ash.OneWayCompletion.Analysis.join_dependency_from_right
#print axioms Ash.OneWayCompletion.Analysis.joinFrom_end_all
#print axioms Ash.OneWayCompletion.Analysis.joinAll_end_all
#print axioms Ash.OneWayCompletion.Processing.control_step_network
#print axioms Ash.OneWayCompletion.Processing.execution_step_network
#print axioms Ash.OneWayCompletion.Processing.execution_network
#print axioms Ash.OneWayCompletion.Processing.Projection.classify_work_sound

#print axioms Ash.OneWayCompletion.Processing.execution_preserves_authentication
#print axioms Ash.OneWayCompletion.Processing.Projection.accepted_end
#print axioms Ash.OneWayCompletion.Processing.execution_accepted_finish_has_genuine_end

#print axioms Ash.OneWayCompletion.Processing.Projection.accepted_shape
#print axioms Ash.OneWayCompletion.Processing.Projection.clear_phase
#print axioms Ash.OneWayCompletion.Processing.certified_reached_finish_cut
#print axioms Ash.OneWayCompletion.Processing.execution_accepted_finish_cut

#print axioms Ash.OneWayCompletion.Processing.execution_preserves_taint

#print axioms Ash.OneWayCompletion.Suffix.check_dependency_subset
#print axioms Ash.OneWayCompletion.Processing.normalized_frame_sites_sound
#print axioms Ash.OneWayCompletion.Processing.Analysis.normalized_dependency_edge
#print axioms Ash.OneWayCompletion.Processing.Analysis.normalized_dependency_closed
#print axioms Ash.OneWayCompletion.Processing.Analysis.dependencyClosure_contains_current
#print axioms Ash.OneWayCompletion.Processing.Analysis.certified_closed

#print axioms Ash.OneWayCompletion.Processing.execution_preserves_reply_consistency
#print axioms Ash.OneWayCompletion.Processing.execution_preserves_identity
#print axioms Ash.OneWayCompletion.Processing.step_preserves_frame_chain
#print axioms Ash.OneWayCompletion.Processing.execution_preserves_frame_chain

#print axioms Ash.OneWayCompletion.Processing.Analysis.solve_closed

#print axioms Ash.OneWayCompletion.Processing.Analysis.solved_replays

#print axioms Ash.OneWayCompletion.Processing.Analysis.revise_preserves_configuration
#print axioms Ash.OneWayCompletion.Processing.Analysis.solve_preserves_configuration


#print axioms Ash.OneWayCompletion.Processing.Analysis.solve_least

#print axioms Ash.OneWayCompletion.Processing.Analysis.solveFrom_no_base_returns

#print axioms Ash.OneWayCompletion.Processing.Region.checked_excludes_unverified

#print axioms Ash.OneWayCompletion.Processing.Analysis.solveFrom_certified


#print axioms Ash.OneWayCompletion.CapturePlan.admitted_build_shape

#print axioms Ash.OneWayCompletion.Processing.dispatch_successor_is_enumerated
#print axioms Ash.OneWayCompletion.Processing.checked_dispatch_selects_root
#print axioms Ash.OneWayCompletion.Processing.selected_root_matches

#print axioms Ash.OneWayCompletion.Processing.certified_call_enters
#print axioms Ash.OneWayCompletion.Processing.certified_matched_return_replayed
#print axioms Ash.OneWayCompletion.Processing.certified_return_matches
#print axioms Ash.OneWayCompletion.Processing.certified_stack_return_replayed
#print axioms Ash.OneWayCompletion.Processing.certified_stack_call_enters
#print axioms Ash.OneWayCompletion.Processing.certified_stack_return_matches
#print axioms Ash.OneWayCompletion.Processing.certified_call_pending_clear
#print axioms Ash.OneWayCompletion.Processing.certified_return_ready
#print axioms Ash.OneWayCompletion.Processing.certified_other_return_impossible
#print axioms Ash.OneWayCompletion.Processing.certified_control_successor
#print axioms Ash.OneWayCompletion.Processing.certified_execution_successor
#print axioms Ash.OneWayCompletion.Processing.certified_execution_reached
#print axioms Ash.OneWayCompletion.Processing.certified_execution_finish
#print axioms Ash.OneWayCompletion.Processing.matched_return_is_enumerated
#print axioms Ash.OneWayCompletion.Processing.call_successor_is_enumerated
#print axioms Ash.OneWayCompletion.Processing.checked_processing_projection

#print axioms Ash.OneWayCompletion.Region.DataWalk.toWalk

#print axioms Ash.OneWayCompletion.Region.outputs_step
#print axioms Ash.OneWayCompletion.Region.outputs_walk
#print axioms Ash.OneWayCompletion.Region.outputs_marker

#print axioms Ash.OneWayCompletion.Processing.certified_dispatch_successor
#print axioms Ash.OneWayCompletion.Processing.certified_receive_end_pending
#print axioms Ash.OneWayCompletion.Processing.certified_receive_empty
#print axioms Ash.OneWayCompletion.Processing.certified_receive_message
#print axioms Ash.OneWayCompletion.Processing.certified_end_reply
#print axioms Ash.OneWayCompletion.Processing.certified_branch_successor
#print axioms Ash.OneWayCompletion.Processing.certified_forward_successor
#print axioms Ash.OneWayCompletion.Processing.certified_processing_successor
#print axioms Ash.OneWayCompletion.Processing.processing_successor_is_enumerated

#print axioms Ash.OneWayCompletion.Region.countCells_exact
#print axioms Ash.OneWayCompletion.Region.debit_exact
#print axioms Ash.OneWayCompletion.Region.preflight_output_count
#print axioms Ash.OneWayCompletion.Region.preflight_work_exact
#print axioms Ash.OneWayCompletion.Region.outputsBudgeted_exact

#print axioms Ash.OneWayCompletion.Region.outputsBudgeted_marker

#print axioms Ash.OneWayCompletion.Processing.normal_return_is_enumerated
#print axioms Ash.OneWayCompletion.Processing.certified_normal_return_replayed
#print axioms Ash.OneWayCompletion.Processing.certified_normal_return_matches
#print axioms Ash.OneWayCompletion.Processing.certified_stack_normal_return_replayed
#print axioms Ash.OneWayCompletion.Processing.certified_stack_normal_return_matches
#print axioms Ash.OneWayCompletion.Processing.projection_frame_dependency_subset
#print axioms Ash.OneWayCompletion.Processing.driver_check_dependency_subset
#print axioms Ash.OneWayCompletion.Processing.normalized_frame_sites_sound
#print axioms Ash.OneWayCompletion.Processing.certified_receive_failed
#print axioms Ash.OneWayCompletion.Processing.certified_result_successor
#print axioms Ash.OneWayCompletion.Processing.certified_match_end_yes
#print axioms Ash.OneWayCompletion.Processing.certified_match_end_no
#print axioms Ash.OneWayCompletion.Processing.certified_match_end_unverified

#print axioms Ash.OneWayCompletion.Processing.Projection.failed_finish_refused
#print axioms Ash.OneWayCompletion.Processing.certified_execution_coverage
