import CoreObservation

/-! Finite acquisition history of the independent Core evaluator. This is a
    mathematical counter invariant, not a Rust capacity or target-world theorem. -/
namespace Ash.OneShot.CoreAllocationHistory
open CoreMachine CoreSyntax
set_option linter.unusedSimpArgs false

/-- Historical acquisitions, including resources subsequently released. -/
def acquiredKeys : List Observation → List Nat
  | [] => []
  | .acquired _ key :: rest => key :: acquiredKeys rest
  | _ :: rest => acquiredKeys rest

@[simp] theorem acquiredKeys_append (left right : List Observation) :
    acquiredKeys (left ++ right) = acquiredKeys left ++ acquiredKeys right := by
  induction left with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [acquiredKeys, ih]

/-- Closing consumes captures and emits disposal metadata, never acquisitions. -/
theorem closeFuel_no_acquisition (fuel : Nat) (frames closing : List CoreMachine.Frame)
    (events : List Observation) (closed : closeFuel fuel frames = .ok (closing, events)) :
    acquiredKeys events = [] := by
  induction fuel generalizing frames closing events with
  | zero => simp [closeFuel] at closed
  | succ fuel ih =>
    cases frames with
    | nil => simp [closeFuel] at closed; rcases closed with ⟨rfl, rfl⟩; rfl
    | cons frame rest =>
      cases frame <;> simp only [closeFuel] at closed
      all_goals
        try simp only [Bind.bind, Functor.map, Except.bind, Except.pure, Except.map] at closed
        repeat' (split at closed <;> try simp only [Bind.bind, Functor.map, Except.bind, Except.pure, Except.map] at closed)
        all_goals try first | exact ih _ _ _ closed | simp_all [acquiredKeys]
      all_goals cases hrest : closeFuel fuel rest <;> simp_all [Functor.map, Except.map, Except.bind]
      all_goals
        try split at closed <;> simp_all [Functor.map, Except.map, Except.bind]
      all_goals
        obtain ⟨rfl, rfl⟩ := closed
        have tail := ih rest _ _ hrest
        first
        | exact tail
        | rename_i captureResult result resultEq
          have nested := ih _ _ _ captureResult
          simp [acquiredKeys, tail, nested]

/-- The only possible historical change is allocation at the old counter. -/
def AllocationDelta (before after : CoreMachine.State) : Prop :=
  (after.nextActivation = before.nextActivation ∧
    acquiredKeys after.observations = acquiredKeys before.observations) ∨
  (after.nextActivation = before.nextActivation + 1 ∧
    acquiredKeys after.observations = acquiredKeys before.observations ++ [before.nextActivation])

theorem interpretCell_delta (state after : CoreMachine.State) (cut : CellCut)
    (operation : Nat) (value : CoreMachine.Value)
    (step : interpretCell state cut operation value = .stepped after) : AllocationDelta state after := by
  unfold interpretCell at step
  repeat' split at step
  all_goals try simp_all only [Outcome.stepped.injEq, Outcome.noConfusion]
  all_goals try subst after
  all_goals simp_all [AllocationDelta, acquiredKeys]

theorem returnResume_delta (state after : CoreMachine.State) (handler owner : Nat)
    (value : CoreMachine.Value)
    (step : returnResume state handler owner value = .stepped after) : AllocationDelta state after := by
  unfold returnResume at step
  split at step <;> cases step
  all_goals simp [AllocationDelta, acquiredKeys]

theorem discardOwner_delta (state after : CoreMachine.State) (handler owner : Nat)
    (step : discardOwner state handler owner = .stepped after) : AllocationDelta state after := by
  unfold discardOwner at step
  repeat' split at step
  all_goals try simp_all only [Outcome.stepped.injEq, Outcome.noConfusion]
  all_goals try subst after
  all_goals simp_all [AllocationDelta, acquiredKeys]
  all_goals
    have noAcquisition := closeFuel_no_acquisition _ _ _ _ (by assumption)
    simp_all [noAcquisition]

theorem request_delta (graph : Graph) (state after : CoreMachine.State)
    (effect : Instantiation.Effect) (operation : Nat) (environment : Environment)
    (value : CoreMachine.Value)
    (step : request graph state effect operation environment value = .stepped after) :
    AllocationDelta state after := by
  unfold request at step
  generalize realized : effect.instantiate environment.instantiation = requested at step
  cases requested with
  | cell name =>
    cases name <;> dsimp only at step
    all_goals repeat' split at step
    all_goals first
    | exact interpretCell_delta _ _ _ _ _ step
    | (cases step <;> simp [AllocationDelta, acquiredKeys])
  | user family arguments =>
    dsimp only at step
    repeat' split at step
    all_goals first
    | exact interpretCell_delta _ _ _ _ _ step
    | (cases step <;> simp [AllocationDelta, acquiredKeys])

/-- Exhaustive successful-next analysis, including cleanup and nested closing. -/
theorem next_delta (graph : Graph) (before after : CoreMachine.State)
    (step : CoreMachine.Step graph before after) : AllocationDelta before after := by
  unfold CoreMachine.Step next at step
  repeat' split at step
  all_goals first
  | exact discardOwner_delta _ _ _ _ step
  | (have delta := request_delta _ _ _ _ _ _ _ step; exact delta)
  | (have delta := returnResume_delta _ _ _ _ _ step; exact delta)
  | (cases step <;> simp [AllocationDelta, acquiredKeys])

/-- From initial, every issued activation occurs exactly once, in counter order.
    Release and cleanup do not remove historical entries. -/
def History (state : CoreMachine.State) : Prop :=
  acquiredKeys state.observations = List.range state.nextActivation

theorem initial_history (graph : Graph) : History (initial graph) := rfl

theorem history_step (graph : Graph) (before after : CoreMachine.State)
    (history : History before) (step : CoreMachine.Step graph before after) : History after := by
  rcases next_delta graph before after step with ⟨counter, events⟩ | ⟨counter, events⟩
  · simpa [History, counter, events] using history
  · simp only [History, counter, events]
    rw [history, List.range_succ]

/-- Finite transitions of the evaluator itself, retaining exact step count. -/
inductive Steps (graph : Graph) : Nat → CoreMachine.State → CoreMachine.State → Prop
  | refl (state) : Steps graph 0 state state
  | snoc {count before middle after} : Steps graph count before middle →
      CoreMachine.Step graph middle after → Steps graph (count + 1) before after

theorem steps_history (graph : Graph) {count : Nat} {before after : CoreMachine.State}
    (history : History before) (steps : Steps graph count before after) : History after := by
  induction steps with
  | refl => exact history
  | snoc earlier step ih => exact history_step graph _ _ (ih history) step

theorem initial_steps_history (graph : Graph) {count : Nat} {after : CoreMachine.State}
    (steps : Steps graph count (initial graph) after) : History after :=
  steps_history graph (initial_history graph) steps

theorem history_bounded (state : CoreMachine.State) (history : History state)
    (key : Nat) (issued : key ∈ acquiredKeys state.observations) : key < state.nextActivation := by
  rw [history] at issued
  exact List.mem_range.mp issued

theorem history_nodup (state : CoreMachine.State) (history : History state) :
    (acquiredKeys state.observations).Nodup := by
  rw [history]
  exact List.nodup_range

theorem history_fresh (state : CoreMachine.State) (history : History state) :
    state.nextActivation ∉ acquiredKeys state.observations := by
  intro member
  have := history_bounded state history _ member
  omega

/-- A runner's final state includes exhausted and rejected outcomes; this
    invariant does not require that the run succeeds or even terminates. -/
def resultState : RunResult → CoreMachine.State
  | .done _ state | .stopped _ state | .exhausted state => state

theorem run_history (graph : Graph) (fuel : Nat) (state : CoreMachine.State)
    (history : History state) : History (resultState (run graph fuel state)) := by
  induction fuel generalizing state with
  | zero => exact history
  | succ fuel ih =>
    simp only [run]
    split
    · exact ih _ (history_step graph _ _ history (by assumption))
    · exact history
    · exact history

theorem initial_run_history (graph : Graph) (fuel : Nat) :
    History (resultState (run graph fuel (initial graph))) :=
  run_history graph fuel _ (initial_history graph)

/-- An actual acquired observation at a successful boundary identifies exactly
    the previous counter. No freshness or target-world premise is supplied. -/
theorem acquired_step_exact (graph : Graph) (before after : CoreMachine.State)
    (step : CoreMachine.Step graph before after) (node : NodeRef) (key : Nat)
    (event : after.observations = before.observations ++ [.acquired node key]) :
    key = before.nextActivation ∧ after.nextActivation = before.nextActivation + 1 := by
  have keys : acquiredKeys after.observations = acquiredKeys before.observations ++ [key] := by
    simp [event, acquiredKeys]
  rcases next_delta graph before after step with ⟨counter, same⟩ | ⟨counter, added⟩
  · have length := congrArg List.length (keys.symm.trans same)
    simp at length
  · have one := List.append_cancel_left (keys.symm.trans added)
    simpa using And.intro one counter

theorem acquired_step_fresh (graph : Graph) {count : Nat}
    {before after : CoreMachine.State} (reached : Steps graph count (initial graph) before)
    (step : CoreMachine.Step graph before after) (node : NodeRef) (key : Nat)
    (event : after.observations = before.observations ++ [.acquired node key]) :
    key ∉ acquiredKeys before.observations ∧
      acquiredKeys after.observations = acquiredKeys before.observations ++ [key] ∧
      (acquiredKeys after.observations).Nodup := by
  have history := initial_steps_history graph reached
  obtain ⟨rfl, _⟩ := acquired_step_exact graph before after step node key event
  exact ⟨history_fresh before history, by simp [event, acquiredKeys],
    history_nodup after (history_step graph before after history step)⟩

/-- The target-world connection remains an explicit correspondence obligation:
    it must include all issued activations, not just currently live owners. -/
theorem fresh_in_corresponding_world (graph : Graph) {count : Nat}
    {state : CoreMachine.State} (reached : Steps graph count (initial graph) state)
    (world : List Nat) (worldHistory : world = acquiredKeys state.observations) :
    state.nextActivation ∉ world := by
  rw [worldHistory]
  exact history_fresh state (initial_steps_history graph reached)

/-- Concatenate actual-next sequences without replacing the evaluator. -/
theorem Steps.trans {graph : Graph} {left right : Nat}
    {before middle after : CoreMachine.State} (first : Steps graph left before middle)
    (second : Steps graph right middle after) : Steps graph (left + right) before after := by
  induction second with
  | refl => simpa using first
  | snoc prior step ih => simpa [Nat.add_assoc] using Steps.snoc (ih first) step

/-- The existing actual-snapshot checker exposes the exact finite model trace.
    Its raw snapshot equality obligations remain in CheckedTrace; no claim that
    this theorem establishes a target resource world is added. -/
theorem checkedTrace_steps {graph : Graph} {model : CoreMachine.State}
    {seen : List (List NodeRef × CoreObservation.Environment)}
    {actual : List CoreObservation.Snapshot} {count : Nat}
    (checked : CoreObservation.CheckedTrace graph model seen actual count) :
    ∃ terminal value, Steps graph count model terminal ∧
      CoreMachine.next graph terminal = .done value := by
  induction checked with
  | terminal model seen actual value related metadata done result empty =>
    exact ⟨model, value, .refl model, done⟩
  | step model successor seen actual rest count related metadata annotations transition remaining ih =>
    obtain ⟨terminal, value, suffix, done⟩ := ih
    have firstStep : Steps graph 1 model successor := .snoc (.refl model) transition
    exact ⟨terminal, value, by simpa [Nat.add_comm] using firstStep.trans suffix, done⟩

theorem checked_initial_history {graph : Graph}
    {actual : List CoreObservation.Snapshot} {count : Nat}
    (checked : CoreObservation.CheckedTrace graph (initial graph) [] actual count) :
    ∃ terminal value, Steps graph count (initial graph) terminal ∧
      CoreMachine.next graph terminal = .done value ∧ History terminal ∧
      (acquiredKeys terminal.observations).Nodup := by
  obtain ⟨terminal, value, steps, done⟩ := checkedTrace_steps checked
  have history := initial_steps_history graph steps
  exact ⟨terminal, value, steps, done, history, history_nodup terminal history⟩

/-- An integer-returning resource initializer allocates without any supplied
    freshness premise. Its exact environment and boundary carry the fresh key. -/
theorem resource_acquisition (graph : Graph) {count : Nat} (before : CoreMachine.State)
    (reached : Steps graph count (initial graph) before) (node identity : Nat)
    (handle : Binder) (body : NodeRef) (environment : CoreMachine.Environment)
    (rest : List CoreMachine.Frame) (payload : Int)
    (control : before.control = .returned (.integer payload))
    (frames : before.frames = .resourceInitializer node identity handle body environment :: rest) :
    ∃ after, CoreMachine.Step graph before after ∧
      after.control = .evaluate body (.binding handle.id (.handle before.nextActivation)
        (.resource identity before.nextActivation environment)) ∧
      after.frames = .resourceBoundary node before.nextActivation payload :: rest ∧
      after.observations = before.observations ++ [.acquired node before.nextActivation] ∧
      after.nextActivation = before.nextActivation + 1 ∧
      before.nextActivation ∉ acquiredKeys before.observations ∧ History after := by
  let after : CoreMachine.State := { before with
    control := .evaluate body (.binding handle.id (.handle before.nextActivation)
      (.resource identity before.nextActivation environment))
    frames := .resourceBoundary node before.nextActivation payload :: rest
    observations := before.observations ++ [.acquired node before.nextActivation]
    nextActivation := before.nextActivation + 1 }
  have transition : CoreMachine.Step graph before after := by
    simp [CoreMachine.Step, next, control, frames, after]
  have history := initial_steps_history graph reached
  exact ⟨after, transition, rfl, rfl, rfl, rfl, history_fresh before history,
    history_step graph before after history transition⟩

/-- Execute, release, and reacquire the same static resource node. Dynamic
    history retains both keys even though neither owner remains live. -/
private def twiceGraph : Graph := ⟨[
  ⟨0, .integer, [], none, .integer 0⟩,
  ⟨1, .unit, [], none, .unit⟩,
  ⟨2, .unit, [], none, .resource 0 ⟨0, .reference (.bound 0)⟩ 0 1⟩,
  ⟨3, .unit, [], none, .bind ⟨1, .unit⟩ 2 2⟩], 3⟩

example : acquiredKeys (resultState (run twiceGraph 20 (initial twiceGraph))).observations = [0, 1] := by
  decide +kernel
example : (resultState (run twiceGraph 20 (initial twiceGraph))).nextActivation = 2 := by
  decide +kernel
example : (resultState (run twiceGraph 20 (initial twiceGraph))).frames = [] := by
  decide +kernel
example : History (resultState (run twiceGraph 0 (initial twiceGraph))) :=
  initial_run_history twiceGraph 0
example : History (resultState (run ⟨[], 0⟩ 5 (initial ⟨[], 0⟩))) :=
  initial_run_history ⟨[], 0⟩ 5
example : closeFuel 5 [
    .clauseBoundary 0 0 0 0 (some [.resourceBoundary 2 0 7]),
    .cleanupBoundary 1 .empty 0] =
    .ok ([.resourceBoundary 2 0 7, .cleanupBoundary 1 .empty 0], [.nestedConsumed 0]) := rfl

#print axioms checkedTrace_steps
#print axioms checked_initial_history
#print axioms resource_acquisition

#print axioms closeFuel_no_acquisition
#print axioms next_delta
#print axioms history_step
#print axioms initial_steps_history
#print axioms history_nodup
#print axioms initial_run_history
#print axioms acquired_step_exact
#print axioms acquired_step_fresh
#print axioms fresh_in_corresponding_world

end Ash.OneShot.CoreAllocationHistory
