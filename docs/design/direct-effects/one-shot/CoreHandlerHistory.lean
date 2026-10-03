import CoreTicketHistory

/-! Historical handler activations of the independent Core evaluator. This leaf
    concerns successful actual transitions and mathematical counters; it does
    not establish rich installation-list provenance or Rust capacity. -/
namespace Ash.OneShot.CoreHandlerHistory
open CoreMachine CoreSyntax
set_option linter.unusedSimpArgs false

/-- All entered handler activations, including boundaries subsequently returned. -/
def enteredHandlers : List Observation → List Nat
  | [] => []
  | .handlerEntered _ ticket :: rest => ticket :: enteredHandlers rest
  | _ :: rest => enteredHandlers rest

@[simp] theorem enteredHandlers_append (left right : List Observation) :
    enteredHandlers (left ++ right) = enteredHandlers left ++ enteredHandlers right := by
  induction left with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [enteredHandlers, ih]

/-- Nested closing emits consumption metadata, never new handler installations. -/
theorem closeFuel_no_handler (fuel : Nat) (frames closing : List CoreMachine.Frame)
    (events : List Observation) (closed : closeFuel fuel frames = .ok (closing, events)) :
    enteredHandlers events = [] := by
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
        all_goals try first | exact ih _ _ _ closed | simp_all [enteredHandlers]
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
          simp [enteredHandlers, tail, nested]

/-- Only actual handler entry can add the previous handler counter. -/
def HandlerDelta (before after : CoreMachine.State) : Prop :=
  (after.nextHandler = before.nextHandler ∧
    enteredHandlers after.observations = enteredHandlers before.observations) ∨
  (after.nextHandler = before.nextHandler + 1 ∧
    enteredHandlers after.observations = enteredHandlers before.observations ++ [before.nextHandler])

theorem interpretCell_delta (state after : CoreMachine.State) (cut : CellCut)
    (operation : Nat) (value : CoreMachine.Value)
    (step : interpretCell state cut operation value = .stepped after) : HandlerDelta state after := by
  unfold interpretCell at step
  repeat' split at step
  all_goals try simp_all only [Outcome.stepped.injEq, Outcome.noConfusion]
  all_goals try subst after
  all_goals simp_all [HandlerDelta, enteredHandlers]

theorem returnResume_preserves (state after : CoreMachine.State) (handler owner : Nat)
    (value : CoreMachine.Value)
    (step : returnResume state handler owner value = .stepped after) :
    after.nextHandler = state.nextHandler ∧ enteredHandlers after.observations = enteredHandlers state.observations := by
  unfold returnResume at step
  split at step <;> cases step
  all_goals simp [enteredHandlers]

theorem discardOwner_preserves (state after : CoreMachine.State) (handler owner : Nat)
    (step : discardOwner state handler owner = .stepped after) :
    after.nextHandler = state.nextHandler ∧ enteredHandlers after.observations = enteredHandlers state.observations := by
  unfold discardOwner at step
  repeat' split at step
  all_goals try simp_all only [Outcome.stepped.injEq, Outcome.noConfusion]
  all_goals try subst after
  all_goals simp_all [enteredHandlers]
  all_goals
    have noCapture := closeFuel_no_handler _ _ _ _ (by assumption)
    simp_all [noCapture]

theorem returnResume_delta (state after : CoreMachine.State) (handler owner : Nat)
    (value : CoreMachine.Value)
    (step : returnResume state handler owner value = .stepped after) : HandlerDelta state after :=
  Or.inl (returnResume_preserves state after handler owner value step)

theorem discardOwner_delta (state after : CoreMachine.State) (handler owner : Nat)
    (step : discardOwner state handler owner = .stepped after) : HandlerDelta state after :=
  Or.inl (discardOwner_preserves state after handler owner step)

theorem request_delta (graph : Graph) (state after : CoreMachine.State)
    (effect : Instantiation.Effect) (operation : Nat) (environment : Environment)
    (value : CoreMachine.Value)
    (step : request graph state effect operation environment value = .stepped after) :
    HandlerDelta state after := by
  unfold request at step
  generalize realized : effect.instantiate environment.instantiation = requested at step
  cases requested with
  | cell name =>
    cases name <;> dsimp only at step
    all_goals repeat' split at step
    all_goals first
    | exact interpretCell_delta _ _ _ _ _ step
    | (cases step <;> simp [HandlerDelta, enteredHandlers])
  | user family arguments =>
    dsimp only at step
    repeat' split at step
    all_goals first
    | exact interpretCell_delta _ _ _ _ _ step
    | (cases step <;> simp [HandlerDelta, enteredHandlers])

/-- Exhaustive successful-next analysis, including cleanup and nested closing. -/
theorem next_delta (graph : Graph) (before after : CoreMachine.State)
    (step : CoreMachine.Step graph before after) : HandlerDelta before after := by
  unfold CoreMachine.Step next at step
  repeat' split at step
  all_goals first
  | exact discardOwner_delta _ _ _ _ step
  | (have delta := request_delta _ _ _ _ _ _ _ step; exact delta)
  | (have delta := returnResume_delta _ _ _ _ _ step; exact delta)
  | (cases step <;> simp [HandlerDelta, enteredHandlers])

/-- Exact counter-ordered history, unaffected by handler return or disposal. -/
def History (state : CoreMachine.State) : Prop :=
  enteredHandlers state.observations = List.range state.nextHandler

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
    (ticket : Nat) (issued : ticket ∈ enteredHandlers state.observations) : ticket < state.nextHandler := by
  rw [history] at issued
  exact List.mem_range.mp issued

theorem history_nodup (state : CoreMachine.State) (history : History state) :
    (enteredHandlers state.observations).Nodup := by
  rw [history]
  exact List.nodup_range

theorem history_fresh (state : CoreMachine.State) (history : History state) :
    state.nextHandler ∉ enteredHandlers state.observations := by
  intro member
  have := history_bounded state history _ member
  omega

/-- Counter monotonicity and historical append preservation need no initial
    invariant; each local change is derived from the actual evaluator. -/
theorem steps_monotone (graph : Graph) {count : Nat} {before after : CoreMachine.State}
    (steps : CoreAllocationHistory.Steps graph count before after) :
    before.nextHandler ≤ after.nextHandler ∧
      ∃ added, enteredHandlers after.observations = enteredHandlers before.observations ++ added := by
  induction steps with
  | refl => exact ⟨Nat.le_refl _, [], by simp⟩
  | snoc earlier step ih =>
    obtain ⟨bound, added, events⟩ := ih
    rcases next_delta graph _ _ step with ⟨counter, same⟩ | ⟨counter, captured⟩
    · exact ⟨by omega, added, same.trans events⟩
    · exact ⟨by omega, added ++ [_], by rw [captured, events, List.append_assoc]⟩

/-- A forged current-counter membership contradicts the actual historical bound. -/
theorem current_counter_not_member (state : CoreMachine.State) (history : History state)
    (installations : List Nat) (original : installations ⊆ enteredHandlers state.observations) :
    state.nextHandler ∉ installations := by
  intro member
  exact history_fresh state history (original member)

#print axioms closeFuel_no_handler
#print axioms interpretCell_delta
#print axioms returnResume_preserves
#print axioms discardOwner_preserves
#print axioms request_delta
#print axioms next_delta
#print axioms initial_history
#print axioms history_step
#print axioms steps_history
#print axioms initial_steps_history
#print axioms history_bounded
#print axioms history_nodup
#print axioms history_fresh
#print axioms steps_monotone
#print axioms current_counter_not_member
end Ash.OneShot.CoreHandlerHistory
