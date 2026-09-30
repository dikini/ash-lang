import CoreAllocationHistory

/-! Historical dynamic tickets of the independent Core evaluator. This leaf
    concerns successful actual transitions and mathematical counters; it does
    not establish live-owner uniqueness or a target ticket world. -/
namespace Ash.OneShot.CoreTicketHistory
open CoreMachine CoreSyntax
set_option linter.unusedSimpArgs false

/-- All issued capture tickets, including resumed and discarded occurrences. -/
def capturedTickets : List Observation → List Nat
  | [] => []
  | .captured _ ticket :: rest => ticket :: capturedTickets rest
  | _ :: rest => capturedTickets rest

@[simp] theorem capturedTickets_append (left right : List Observation) :
    capturedTickets (left ++ right) = capturedTickets left ++ capturedTickets right := by
  induction left with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [capturedTickets, ih]

/-- Nested closing emits consumption metadata, never new captured occurrences. -/
theorem closeFuel_no_capture (fuel : Nat) (frames closing : List CoreMachine.Frame)
    (events : List Observation) (closed : closeFuel fuel frames = .ok (closing, events)) :
    capturedTickets events = [] := by
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
        all_goals try first | exact ih _ _ _ closed | simp_all [capturedTickets]
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
          simp [capturedTickets, tail, nested]

/-- Only a successful handler capture can add the previous ticket counter. -/
def TicketDelta (before after : CoreMachine.State) : Prop :=
  (after.nextOwner = before.nextOwner ∧
    capturedTickets after.observations = capturedTickets before.observations) ∨
  (after.nextOwner = before.nextOwner + 1 ∧
    capturedTickets after.observations = capturedTickets before.observations ++ [before.nextOwner])

theorem interpretCell_delta (state after : CoreMachine.State) (cut : CellCut)
    (operation : Nat) (value : CoreMachine.Value)
    (step : interpretCell state cut operation value = .stepped after) : TicketDelta state after := by
  unfold interpretCell at step
  repeat' split at step
  all_goals try simp_all only [Outcome.stepped.injEq, Outcome.noConfusion]
  all_goals try subst after
  all_goals simp_all [TicketDelta, capturedTickets]

theorem returnResume_preserves (state after : CoreMachine.State) (handler owner : Nat)
    (value : CoreMachine.Value)
    (step : returnResume state handler owner value = .stepped after) :
    after.nextOwner = state.nextOwner ∧ capturedTickets after.observations = capturedTickets state.observations := by
  unfold returnResume at step
  split at step <;> cases step
  all_goals simp [capturedTickets]

theorem discardOwner_preserves (state after : CoreMachine.State) (handler owner : Nat)
    (step : discardOwner state handler owner = .stepped after) :
    after.nextOwner = state.nextOwner ∧ capturedTickets after.observations = capturedTickets state.observations := by
  unfold discardOwner at step
  repeat' split at step
  all_goals try simp_all only [Outcome.stepped.injEq, Outcome.noConfusion]
  all_goals try subst after
  all_goals simp_all [capturedTickets]
  all_goals
    have noCapture := closeFuel_no_capture _ _ _ _ (by assumption)
    simp_all [noCapture]

theorem returnResume_delta (state after : CoreMachine.State) (handler owner : Nat)
    (value : CoreMachine.Value)
    (step : returnResume state handler owner value = .stepped after) : TicketDelta state after :=
  Or.inl (returnResume_preserves state after handler owner value step)

theorem discardOwner_delta (state after : CoreMachine.State) (handler owner : Nat)
    (step : discardOwner state handler owner = .stepped after) : TicketDelta state after :=
  Or.inl (discardOwner_preserves state after handler owner step)

theorem request_delta (graph : Graph) (state after : CoreMachine.State)
    (effect : Instantiation.Effect) (operation : Nat) (environment : Environment)
    (value : CoreMachine.Value)
    (step : request graph state effect operation environment value = .stepped after) :
    TicketDelta state after := by
  unfold request at step
  generalize realized : effect.instantiate environment.instantiation = requested at step
  cases requested with
  | cell name =>
    cases name <;> dsimp only at step
    all_goals repeat' split at step
    all_goals first
    | exact interpretCell_delta _ _ _ _ _ step
    | (cases step <;> simp [TicketDelta, capturedTickets])
  | user family arguments =>
    dsimp only at step
    repeat' split at step
    all_goals first
    | exact interpretCell_delta _ _ _ _ _ step
    | (cases step <;> simp [TicketDelta, capturedTickets])

/-- Exhaustive successful-next analysis, including cleanup and nested closing. -/
theorem next_delta (graph : Graph) (before after : CoreMachine.State)
    (step : CoreMachine.Step graph before after) : TicketDelta before after := by
  unfold CoreMachine.Step next at step
  repeat' split at step
  all_goals first
  | exact discardOwner_delta _ _ _ _ step
  | (have delta := request_delta _ _ _ _ _ _ _ step; exact delta)
  | (have delta := returnResume_delta _ _ _ _ _ step; exact delta)
  | (cases step <;> simp [TicketDelta, capturedTickets])

/-- Exact counter-ordered history, unaffected by resumption or disposal. -/
def History (state : CoreMachine.State) : Prop :=
  capturedTickets state.observations = List.range state.nextOwner

theorem initial_history (graph : Graph) : History (initial graph) := rfl

theorem history_step (graph : Graph) (before after : CoreMachine.State)
    (history : History before) (step : CoreMachine.Step graph before after) : History after := by
  rcases next_delta graph before after step with ⟨counter, events⟩ | ⟨counter, events⟩
  · simpa [History, counter, events] using history
  · simp only [History, counter, events]
    rw [history, List.range_succ]

/-- Reuse the existing finite actual-next trace, including its step count. -/
theorem steps_history (graph : Graph) {count : Nat} {before after : CoreMachine.State}
    (history : History before) (steps : CoreAllocationHistory.Steps graph count before after) : History after := by
  induction steps with
  | refl => exact history
  | snoc earlier step ih => exact history_step graph _ _ (ih history) step

theorem initial_steps_history (graph : Graph) {count : Nat} {after : CoreMachine.State}
    (steps : CoreAllocationHistory.Steps graph count (initial graph) after) : History after :=
  steps_history graph (initial_history graph) steps

theorem history_bounded (state : CoreMachine.State) (history : History state)
    (ticket : Nat) (issued : ticket ∈ capturedTickets state.observations) : ticket < state.nextOwner := by
  rw [history] at issued
  exact List.mem_range.mp issued

theorem history_nodup (state : CoreMachine.State) (history : History state) :
    (capturedTickets state.observations).Nodup := by
  rw [history]
  exact List.nodup_range

theorem history_fresh (state : CoreMachine.State) (history : History state) :
    state.nextOwner ∉ capturedTickets state.observations := by
  intro member
  have := history_bounded state history _ member
  omega

/-- Counter monotonicity and historical append preservation need no initial
    invariant; each local change is derived from the actual evaluator. -/
theorem steps_monotone (graph : Graph) {count : Nat} {before after : CoreMachine.State}
    (steps : CoreAllocationHistory.Steps graph count before after) :
    before.nextOwner ≤ after.nextOwner ∧
      ∃ added, capturedTickets after.observations = capturedTickets before.observations ++ added := by
  induction steps with
  | refl => exact ⟨Nat.le_refl _, [], by simp⟩
  | snoc earlier step ih =>
    obtain ⟨bound, added, events⟩ := ih
    rcases next_delta graph _ _ step with ⟨counter, same⟩ | ⟨counter, captured⟩
    · exact ⟨by omega, added, same.trans events⟩
    · exact ⟨by omega, added ++ [_], by rw [captured, events, List.append_assoc]⟩

/-- An observed capture in an actual Step carries precisely the old counter. -/
theorem captured_step_exact (graph : Graph) (before after : CoreMachine.State)
    (step : CoreMachine.Step graph before after) (occurrence ticket : Nat)
    (event : after.observations = before.observations ++ [.captured occurrence ticket]) :
    ticket = before.nextOwner ∧ after.nextOwner = before.nextOwner + 1 := by
  have tickets : capturedTickets after.observations = capturedTickets before.observations ++ [ticket] := by
    simp [event, capturedTickets]
  rcases next_delta graph before after step with ⟨counter, same⟩ | ⟨counter, added⟩
  · have length := congrArg List.length (tickets.symm.trans same)
    simp at length
  · have one := List.append_cancel_left (tickets.symm.trans added)
    simpa using And.intro one counter

theorem captured_step_fresh (graph : Graph) {count : Nat}
    {before after : CoreMachine.State}
    (reached : CoreAllocationHistory.Steps graph count (initial graph) before)
    (step : CoreMachine.Step graph before after) (occurrence ticket : Nat)
    (event : after.observations = before.observations ++ [.captured occurrence ticket]) :
    ticket ∉ capturedTickets before.observations ∧
      capturedTickets after.observations = capturedTickets before.observations ++ [ticket] ∧
      (capturedTickets after.observations).Nodup := by
  have history := initial_steps_history graph reached
  obtain ⟨rfl, _⟩ := captured_step_exact graph before after step occurrence ticket event
  exact ⟨history_fresh before history, by simp [event, capturedTickets],
    history_nodup after (history_step graph before after history step)⟩

/-- The finite snapshot checker supplies an actual trace, not a target-world
    premise. Its structural snapshot obligations remain in CheckedTrace. -/
theorem checked_initial_history {graph : Graph}
    {actual : List CoreObservation.Snapshot} {count : Nat}
    (checked : CoreObservation.CheckedTrace graph (initial graph) [] actual count) :
    ∃ terminal value, CoreAllocationHistory.Steps graph count (initial graph) terminal ∧
      CoreMachine.next graph terminal = .done value ∧ History terminal ∧
      (capturedTickets terminal.observations).Nodup := by
  obtain ⟨terminal, value, steps, done⟩ := CoreAllocationHistory.checkedTrace_steps checked
  have history := initial_steps_history graph steps
  exact ⟨terminal, value, steps, done, history, history_nodup terminal history⟩

/-- Exhaustion and rejection retain the last actual state. No successful
    outcome premise is needed for the history of that state. -/
theorem run_history (graph : Graph) (fuel : Nat) (state : CoreMachine.State)
    (history : History state) : History (CoreAllocationHistory.resultState (run graph fuel state)) := by
  induction fuel generalizing state with
  | zero => exact history
  | succ fuel ih =>
    simp only [run]
    split
    · exact ih _ (history_step graph _ _ history (by assumption))
    · exact history
    · exact history

theorem initial_run_history (graph : Graph) (fuel : Nat) :
    History (CoreAllocationHistory.resultState (run graph fuel (initial graph))) :=
  run_history graph fuel _ (initial_history graph)

/-- Two captures by the same static handler and clause owner, during one
    handler activation. Resumption restores the second request's suffix; it
    does not reuse the first dynamic ticket. This is a small model fixture,
    not authenticated Rust export or a target ownership proof. -/
private def twiceGraph : Graph := ⟨[
  ⟨0, .unit, [], none, .unit⟩,
  ⟨1, .unit, [.user 0 []], none, .request (.user 0 []) 0 0⟩,
  ⟨2, .unit, [.user 0 []], none, .bind ⟨1, .unit⟩ 1 1⟩,
  ⟨3, .unit, [], none, .resume 0 0 .consumed 0⟩,
  ⟨4, .unit, [], none, .handler 0 (.user 0 []) 2 [⟨0, .binder ⟨2, .unit⟩, 0, 3⟩]⟩], 4⟩

example : checkShape twiceGraph = .ok () := rfl
example : (CoreAllocationHistory.resultState (run twiceGraph 40 (initial twiceGraph))).nextOwner = 2 := by
  decide +kernel
example : capturedTickets (CoreAllocationHistory.resultState (run twiceGraph 40 (initial twiceGraph))).observations = [0, 1] := by
  decide +kernel
example : (CoreAllocationHistory.resultState (run twiceGraph 40 (initial twiceGraph))).observations.filter
    (fun event => match event with | .captured _ _ => true | _ => false) =
    [.captured 0 0, .captured 0 1] := by
  decide +kernel
example : (match run twiceGraph 40 (initial twiceGraph) with | .done .unit _ => true | _ => false) = true := by
  decide +kernel
example : (CoreAllocationHistory.resultState (run twiceGraph 40 (initial twiceGraph))).frames = [] := by
  decide +kernel

/-- Rejected dispatch has no actual Step; no ticket is issued by a missing
    clause. The original history is retained by the stopped runner. -/
private def missingClauseGraph : Graph := ⟨[
  ⟨0, .unit, [], none, .unit⟩,
  ⟨1, .unit, [.user 0 []], none, .request (.user 0 []) 0 0⟩,
  ⟨2, .unit, [], none, .handler 0 (.user 0 []) 1 []⟩], 2⟩
example : (match run missingClauseGraph 20 (initial missingClauseGraph) with
    | .stopped (.missingClause 0) _ => true | _ => false) = true := by
  decide +kernel
example : capturedTickets (CoreAllocationHistory.resultState (run missingClauseGraph 20 (initial missingClauseGraph))).observations = [] := by
  decide +kernel
example : (CoreAllocationHistory.resultState (run missingClauseGraph 20 (initial missingClauseGraph))).nextOwner = 0 := by
  decide +kernel

#print axioms closeFuel_no_capture
#print axioms returnResume_preserves
#print axioms discardOwner_preserves
#print axioms next_delta
#print axioms history_step
#print axioms initial_steps_history
#print axioms history_nodup
#print axioms history_fresh
#print axioms steps_monotone
#print axioms captured_step_exact
#print axioms captured_step_fresh
#print axioms checked_initial_history
#print axioms initial_run_history

end Ash.OneShot.CoreTicketHistory
