import NetworkLedgerCoreRecordRegistration
import NetworkLedgerClosureCheck
import NetworkLedgerRetirementCheck
import NetworkLedgerAcknowledgementCheck

/-
Bounded control/history composition. `CheckedReturn` interprets checked
modeled bodies, not Rust. `Step.returned` separately requires the actual Core
normal return, projection and representation, and a correspondence to that
modeled evaluation. That correspondence is a trust/review boundary: this file
does not prove the Rust-to-model or Core-to-schema correspondence.
-/
namespace Ash.NetworkLedger.HistoryControl

open Ash.NetworkLedger
open Ash.NetworkLedger.CoreEval

inductive CheckedReturn : Action → Ledger → Ledger → Prop where
  | registration (plan : Checker.Plan) (defs : List (Checker.LinkedDefinition RegistrationCheck.Body))
      (defn : Checker.LinkedDefinition RegistrationCheck.Body) (fuel : Nat) (l out : Ledger)
      (p : Id) (d : Nat) (bytes : List UInt8) (status : Registration)
      (accepted : Checker.checkLinkedSchema plan defs RegistrationCheck.check = true)
      (resolved : Checker.resolveLinked plan defs = some defn)
      (returns : RegistrationCheck.eval defn.body fuel l p d bytes = some (out, status)) :
      CheckedReturn (.register p d bytes) l out
  | closure (plan : Checker.Plan) (defs : List (Checker.LinkedDefinition ClosureCheck.Body))
      (defn : Checker.LinkedDefinition ClosureCheck.Body) (fuel : Nat) (l out : Ledger) (q : Id)
      (accepted : Checker.checkLinkedSchema plan defs ClosureCheck.check = true)
      (resolved : Checker.resolveLinked plan defs = some defn)
      (returns : ClosureCheck.eval defn.body fuel l q = some out) : CheckedReturn (.close q) l out
  | retirement (plan : Checker.Plan) (defs : List (Checker.LinkedDefinition RetirementCheck.Body))
      (defn : Checker.LinkedDefinition RetirementCheck.Body) (fuel : Nat) (l out : Ledger) (q : Id)
      (accepted : Checker.checkLinkedSchema plan defs RetirementCheck.check = true)
      (resolved : Checker.resolveLinked plan defs = some defn)
      (returns : RetirementCheck.eval defn.body fuel l q = some out) : CheckedReturn (.retire q) l out
  | acknowledgement (plan : Checker.Plan) (defs : List (Checker.LinkedDefinition AcknowledgementCheck.Body))
      (defn : Checker.LinkedDefinition AcknowledgementCheck.Body) (fuel : Nat) (l out : Ledger)
      (p c : Id) (peer : Nat)
      (accepted : Checker.checkLinkedSchema plan defs AcknowledgementCheck.check = true)
      (resolved : Checker.resolveLinked plan defs = some defn)
      (returns : AcknowledgementCheck.eval defn.body fuel l p c peer = some out) :
      CheckedReturn (.ack p c peer) l out

theorem checked_return_history (t : Tracked) (action : Action) (out : Ledger)
    (checked : CheckedReturn action t.ledger out) : (t.run action).ledger = out := by
  cases checked with
  | registration plan defs defn fuel l out p d bytes status accepted resolved returns =>
    have eq := RegistrationCheck.linked_registration_sound plan defs defn fuel t.ledger p d bytes
      (out, status) accepted resolved returns
    simp only [Tracked.run, Tracked.register, ← eq]
    cases status <;> rfl
  | closure plan defs defn fuel l out q accepted resolved returns =>
    exact (ClosureCheck.linked_closure_sound plan defs defn fuel t.ledger q out accepted resolved returns).symm
  | retirement plan defs defn fuel l out q accepted resolved returns =>
    exact (RetirementCheck.linked_retirement_sound plan defs defn fuel t.ledger q out accepted resolved returns).symm
  | acknowledgement plan defs defn fuel l out p c peer accepted resolved returns =>
    exact (AcknowledgementCheck.linked_acknowledgement_sound plan defs defn fuel t.ledger p c peer out accepted resolved returns).symm

/-- A returned value is not current until the actual result is bound. -/
structure Pending where
  call : NodeId
  result : Value
  ledger : Value

structure State where
  activation : Nat
  owner : Nat
  tracked : Tracked
  store : Store
  env : Environment
  port : Option Value
  pending : Option Pending
  observation : Option Value
  point : NodeId
  context : Nat
  role : Binder

def State.Valid (rep : Store → Value → Ledger → Prop) (s : State) : Prop :=
  s.tracked.Valid ∧ s.owner = s.tracked.ledger.owner ∧
    (∀ value, s.port = some value →
      CoreEval.lookup s.env s.role = some value ∧ rep s.store value s.tracked.ledger) ∧
    (∀ value, s.pending = some value → rep s.store value.ledger s.tracked.ledger) ∧
    (∀ value, s.observation = some value → s.port = some value)

inductive ReceiveOutcome where
  | message | empty | ended | failure
  deriving DecidableEq
inductive ReceiveEvent where
  | observed (outcome : ReceiveOutcome)
  | commit | reply (outcome : ReceiveOutcome) | returned
  deriving DecidableEq

/-- The matched return follows the actual ordered receive stages. -/
inductive ReceiveFlow : List ReceiveEvent → Prop where
  | message : ReceiveFlow [.observed .message, .commit, .reply .message, .returned]
  | other (outcome : ReceiveOutcome) (notMessage : outcome ≠ .message) :
      ReceiveFlow [.observed outcome, .reply outcome, .returned]
  | messageFailure : ReceiveFlow [.observed .message, .observed .failure, .reply .failure, .returned]

/--
`inputAt` is the independently reviewed actual-C3 call/argument association.
`receiveEntry` and `receiveReturn` describe the entered and restored frames;
`joinAt` identifies the actual join of its two incoming paths. These are
explicit correspondence interfaces, not equations about ledger successors.
-/
inductive Step (rep : Store → Value → Ledger → Prop) (program : Program)
    (inputAt : Program → Environment → NodeId → Nat → Binder → Value → Prop)
    (exclusive : Nat → Nat → Prop)
    (receiveActual : Nat → NodeId → List ReceiveEvent → State → State → Prop)
    (returnMatch : Nat → State → State → NodeId → Prop)
    (joinAt : State → State → Prop) : State → List Action → State → Prop where
  | returned (s : State) (input result output : Value) (out : Ledger)
      (action : Action) (node : NodeId) (after : Store)
      (owns : exclusive s.activation s.owner) (current : s.port = some input)
      (inputBinding : inputAt program s.env node s.context s.role input)
      (actual : Eval program s.env node s.store result after)
      (modeled : CheckedReturn action s.tracked.ledger out)
      (decoded : rep after output out) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s [action]
        { s with tracked := s.tracked.run action, store := after, port := none,
                 pending := some ⟨node, result, output⟩, observation := none }
  | bindResult (s : State) (p : Pending) (name : Binder) (body : NodeId)
      (pending : s.pending = some p) (shape : program s.point = some (.bind name p.call body))
      (direct : p.result = p.ledger) (owns : exclusive s.activation s.owner) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s []
        { s with env := CoreEval.extend s.env name p.result, port := some p.ledger,
                 pending := none, observation := none, point := body, role := name }
  | matchResult (s : State) (p : Pending) (body : NodeId)
      (bindings : Environment) (name statusName : Binder)
      (pending : s.pending = some p)
      (shape : program s.point = some (.caseMatch p.call
        [(.tuple [.binder name, .binder statusName], body)]))
      (selected : Selected s.store p.result
        [(.tuple [.binder name, .binder statusName], body)] body bindings)
      (distinct : name ≠ statusName)
      (newBinding : CoreEval.lookup bindings.reverse name = some p.ledger)
      (ledgerBinding : CoreEval.lookup (bindings.reverse ++ s.env) name = some p.ledger)
      (owns : exclusive s.activation s.owner) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s []
        { s with env := bindings.reverse ++ s.env, port := some p.ledger,
                 pending := none, observation := none, point := body, role := name }
  | bindAlias (s : State) (name : Binder) (varNode body : NodeId)
      (value : Value) (current : s.port = some value)
      (shape : program s.point = some (.bind name varNode body))
      (variableShape : program varNode = some (.variable s.role))
      (owns : exclusive s.activation s.owner) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s []
        { s with env := CoreEval.extend s.env name value, point := body, role := name }
  | enterCall (s : State) (function argument matchNode scrutinee branch : NodeId)
      (callable value : Value) (tupleAddress tupleResolved : Nat) (values : List Value)
      (afterFunction afterArgument : Store) (parameter ledgerName : Binder)
      (names : List Binder) (ledgerIndex : Nat) (captures bindings : Environment)
      (nextContext : Nat)
      (current : s.port = some value)
      (shape : program s.point = some (.apply function argument))
      (functionEval : Eval program s.env function s.store callable afterFunction)
      (target : CallTarget program afterFunction callable parameter matchNode captures)
      (argumentEval : Eval program s.env argument afterFunction (.location tupleAddress) afterArgument)
      (resolution : Resolve afterArgument tupleAddress tupleResolved)
      (contents : readCell afterArgument tupleResolved = some values)
      (plain : tupleFields values = some values)
      (arity : names.length = values.length) (distinct : names.Nodup)
      (formalField : names[ledgerIndex]? = some ledgerName)
      (actualField : values[ledgerIndex]? = some value)
      (matchShape : program matchNode = some (.caseMatch scrutinee
        [(.tuple (names.map Pattern.binder), branch)]))
      (scrutineeShape : program scrutinee = some (.variable parameter))
      (selected : Selected afterArgument (.location tupleAddress)
        [(.tuple (names.map Pattern.binder), branch)] branch bindings)
      (newBinding : CoreEval.lookup bindings.reverse ledgerName = some value)
      (binding : CoreEval.lookup (bindings.reverse ++ CoreEval.extend captures parameter (.location tupleAddress)) ledgerName = some value)
      (decoded : rep afterArgument value s.tracked.ledger)
      (owns : exclusive s.activation s.owner) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s []
        { s with env := bindings.reverse ++ CoreEval.extend captures parameter (.location tupleAddress), store := afterArgument,
                 point := branch, context := nextContext, role := ledgerName, pending := none, observation := none }
  | observe (s : State) (value : Value) (current : s.port = some value) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s []
        { s with observation := some value }
  | receive (s : State) (value : Value) (witness : Nat) (call resume : NodeId)
      (events : List ReceiveEvent) (current : s.port = some value)
      (owns : exclusive s.activation s.owner) (flow : ReceiveFlow events)
      (actual : receiveActual witness call events s { s with point := resume, observation := none }) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s []
        { s with point := resume, observation := none }
  | callReturn (s saved : State) (value result : Value) (witness : Nat)
      (call body : NodeId) (resultName : Binder)
      (savedValid : saved.Valid rep) (sameActivation : s.activation = saved.activation)
      (sameOwner : s.owner = saved.owner) (sameTracked : s.tracked = saved.tracked)
      (current : s.port = some value) (savedCurrent : saved.port = some value)
      (shape : program saved.point = some (.bind resultName call body))
      (actual : Eval program saved.env call saved.store result s.store)
      (matched : returnMatch witness saved s call)
      (binding : CoreEval.lookup (CoreEval.extend saved.env resultName result) saved.role = some value)
      (owns : exclusive s.activation s.owner) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s []
        { s with env := CoreEval.extend saved.env resultName result, port := some value,
                 pending := none, observation := none, point := body,
                 context := saved.context, role := saved.role }
  | joinKeep (s other : State) (value : Value) (otherValid : other.Valid rep)
      (joined : joinAt s other) (sameActivation : s.activation = other.activation)
      (sameOwner : s.owner = other.owner) (sameTracked : s.tracked = other.tracked)
      (samePoint : s.point = other.point) (sameContext : s.context = other.context)
      (sameRole : s.role = other.role)
      (left : s.port = some value) (right : other.port = some value) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s [] s
  | invalidate (s : State) :
      Step rep program inputAt exclusive receiveActual returnMatch joinAt s []
        { s with port := none, pending := none, observation := none }

/-- The concrete current binder reads the exact tracked value after every rule. -/
theorem step_preserves (rep : Store → Value → Ledger → Prop) (program : Program)
    (inputAt : Program → Environment → NodeId → Nat → Binder → Value → Prop)
    (exclusive : Nat → Nat → Prop)
    (receiveActual : Nat → NodeId → List ReceiveEvent → State → State → Prop)
    (returnMatch : Nat → State → State → NodeId → Prop)
    (joinAt : State → State → Prop) {s t : State} {events : List Action}
    (valid : s.Valid rep)
    (step : Step rep program inputAt exclusive receiveActual returnMatch joinAt s events t) : t.Valid rep := by
  cases step with
  | returned input result output out action node after owns current inputBinding actual modeled decoded =>
    have nextEq := checked_return_history s.tracked action out modeled
    have nextValid := tracked_action_preserves s.tracked action valid.1
    have frame : (s.tracked.run action).ledger.owner = s.tracked.ledger.owner := by
      cases action with
      | register p d bytes =>
        have account := registration_accounting s.tracked.ledger p d bytes
        cases h : register s.tracked.ledger p d bytes with
        | mk next status => cases status <;> simp_all [Tracked.run, Tracked.register]
      | close q => exact (close_counter_frame _ _).1
      | retire q => exact (retire_counter_frame _ _).1
      | ack p c peer => exact (acknowledgement_counter_frame _ _ _ _).1
    refine ⟨nextValid, valid.2.1.trans frame.symm, by simp, ?_, by simp⟩
    intro p equal
    have same : p = ⟨node, result, output⟩ := Option.some.inj equal.symm
    subst p
    simpa [nextEq] using decoded
  | bindResult p name body pending shape direct owns =>
    have represented := valid.2.2.2.1 p pending
    refine ⟨valid.1, valid.2.1, ?_, by simp, by simp⟩
    intro value equal
    have same : value = p.ledger := Option.some.inj equal.symm
    subst value
    constructor
    · simp [CoreEval.lookup, CoreEval.extend, direct]
    · exact represented
  | matchResult p body bindings name statusName pending shape selected distinct newBinding ledgerBinding owns =>
    have represented := valid.2.2.2.1 p pending
    refine ⟨valid.1, valid.2.1, ?_, by simp, by simp⟩
    intro value equal
    have same : value = p.ledger := Option.some.inj equal.symm
    subst value
    exact ⟨ledgerBinding, represented⟩
  | bindAlias name varNode body value current shape variableShape owns =>
    have represented := (valid.2.2.1 value current).2
    refine ⟨valid.1, valid.2.1, ?_, valid.2.2.2.1, valid.2.2.2.2⟩
    intro v equal
    have same : v = value := Option.some.inj (equal.symm.trans current)
    subst v
    exact ⟨by simp [CoreEval.lookup, CoreEval.extend], represented⟩
  | enterCall function argument matchNode scrutinee branch callable value tupleAddress tupleResolved values afterFunction afterArgument parameter ledgerName names ledgerIndex captures bindings nextContext current shape functionEval target argumentEval resolution contents plain arity distinct formalField actualField matchShape scrutineeShape selected newBinding binding decoded owns =>
    refine ⟨valid.1, valid.2.1, ?_, by simp, by simp⟩
    intro v equal
    have same : v = value := Option.some.inj (equal.symm.trans current)
    subst v
    exact ⟨binding, decoded⟩
  | observe value current =>
    exact ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1,
      by intro v h; have same : v = value := Option.some.inj h.symm; subst v; exact current⟩
  | receive => exact ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, by simp⟩
  | callReturn saved value result witness call body resultName savedValid sameActivation sameOwner sameTracked current savedCurrent shape actual matched binding owns =>
    have represented := (valid.2.2.1 value current).2
    refine ⟨valid.1, valid.2.1, ?_, by simp, by simp⟩
    intro v equal
    have same : v = value := Option.some.inj equal.symm
    subst v
    exact ⟨binding, represented⟩
  | joinKeep => exact valid
  | invalidate => exact ⟨valid.1, valid.2.1, by simp, by simp, by simp⟩

inductive Trace (rep : Store → Value → Ledger → Prop) (program : Program)
    (inputAt : Program → Environment → NodeId → Nat → Binder → Value → Prop)
    (exclusive : Nat → Nat → Prop)
    (receiveActual : Nat → NodeId → List ReceiveEvent → State → State → Prop)
    (returnMatch : Nat → State → State → NodeId → Prop)
    (joinAt : State → State → Prop) : State → List Action → State → Prop where
  | refl (s : State) : Trace rep program inputAt exclusive receiveActual returnMatch joinAt s [] s
  | next {s t u : State} {history events : List Action} :
      Trace rep program inputAt exclusive receiveActual returnMatch joinAt s history t →
      Step rep program inputAt exclusive receiveActual returnMatch joinAt t events u →
      Trace rep program inputAt exclusive receiveActual returnMatch joinAt s (history ++ events) u

theorem step_history (rep : Store → Value → Ledger → Prop) (program : Program)
    (inputAt : Program → Environment → NodeId → Nat → Binder → Value → Prop)
    (exclusive : Nat → Nat → Prop)
    (receiveActual : Nat → NodeId → List ReceiveEvent → State → State → Prop)
    (returnMatch : Nat → State → State → NodeId → Prop)
    (joinAt : State → State → Prop) {s t : State} {events : List Action}
    (step : Step rep program inputAt exclusive receiveActual returnMatch joinAt s events t) :
    t.tracked = s.tracked.runAll events ∧ t.activation = s.activation ∧ t.owner = s.owner := by
  cases step <;> exact ⟨rfl, rfl, rfl⟩

theorem runAll_append (tracked : Tracked) (first second : List Action) :
    tracked.runAll (first ++ second) = (tracked.runAll first).runAll second := by
  induction first generalizing tracked with
  | nil => rfl
  | cons action rest ih => simpa [Tracked.runAll] using ih (tracked.run action)

theorem trace_simulation (rep : Store → Value → Ledger → Prop) (program : Program)
    (inputAt : Program → Environment → NodeId → Nat → Binder → Value → Prop)
    (exclusive : Nat → Nat → Prop)
    (receiveActual : Nat → NodeId → List ReceiveEvent → State → State → Prop)
    (returnMatch : Nat → State → State → NodeId → Prop)
    (joinAt : State → State → Prop) {s t : State} {events : List Action}
    (initial : s.Valid rep)
    (trace : Trace rep program inputAt exclusive receiveActual returnMatch joinAt s events t) :
    t.Valid rep ∧ t.tracked = s.tracked.runAll events ∧
      t.activation = s.activation ∧ t.owner = s.owner := by
  induction trace with
  | refl => exact ⟨initial, rfl, rfl, rfl⟩
  | next history step ih =>
    have valid := step_preserves rep program inputAt exclusive receiveActual returnMatch joinAt ih.1 step
    have fact := step_history rep program inputAt exclusive receiveActual returnMatch joinAt step
    refine ⟨valid, ?_, fact.2.1.trans ih.2.2.1, fact.2.2.trans ih.2.2.2⟩
    rw [fact.1, ih.2.1, runAll_append]

theorem initial_root (rep : Store → Value → Ledger → Prop) (activation owner : Nat)
    (store : Store) (env : Environment) (value : Value) (point context : Nat) (role : Binder)
    (binding : CoreEval.lookup env role = some value) (decoded : rep store value (initialRoot owner)) :
    (State.mk activation owner ⟨initialRoot owner, ⟨owner, 0, []⟩⟩ store env
      (some value) none none point context role).Valid rep := by
  exact ⟨⟨initial_root_invariant owner, allocator_initial_valid owner, rfl, rfl⟩,
    rfl, by intro v h; cases h; exact ⟨binding, decoded⟩, by simp, by simp⟩

theorem initial_worker (rep : Store → Value → Ledger → Prop) (activation owner : Nat)
    (store : Store) (env : Environment) (value : Value) (point context : Nat) (role : Binder)
    (binding : CoreEval.lookup env role = some value) (decoded : rep store value (initialWorker owner)) :
    (State.mk activation owner ⟨initialWorker owner, ⟨owner, 0, []⟩⟩ store env
      (some value) none none point context role).Valid rep := by
  exact ⟨⟨initial_worker_invariant owner, allocator_initial_valid owner, rfl, rfl⟩,
    rfl, by intro v h; cases h; exact ⟨binding, decoded⟩, by simp, by simp⟩

end Ash.NetworkLedger.HistoryControl
