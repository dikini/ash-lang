import Admission

/-!
Progress for completion, ready resumption, and structurally prepared disposal
in the one-shot machine. No theorem assumes its next step exists. General
progress and preservation of source admission remain open.
-/

namespace Ash.OneShot.Progress
open Syntax Execution Typing Joint Admission

/-- Returning at a live boundary would leave its ticket unconsumed. The saved
    capture cannot consume that ticket, and unique ownership excludes an alias
    in the caller tail. -/
theorem value_cannot_return_through_live
    (usage : ConfigurationUsage policy tickets
      ⟨value, scope, .live owner input answer capture caller tail⟩)
    (isValue : value.IsValue) : False := by
  obtain ⟨current, demand, code, control, accessible, balance, unique⟩ := usage
  have empty := code_demand_value_is_empty code isValue
  subst current
  cases control with
  | live known callerKnown saved rest =>
      have absent : owner ∉ ownedTickets capture ++ ownedTickets tail :=
        (List.nodup_cons.mp unique).1
      have required : owner ∈ _ := balance.mem_iff.mpr (List.mem_cons_self)
      simp only [List.nil_append] at required
      rcases List.mem_append.mp required with inside | outside
      · rcases List.mem_append.mp (stack_demand_access_bound saved inside) with owned | external
        · exact absent (List.mem_append_left _ owned)
        · simp only [List.append_nil] at external
          exact absent (List.mem_append_right _ (active_tickets_owned _ external))
      · have owned := stack_demand_access_bound rest outside
        simp only [List.append_nil] at owned
        exact absent (List.mem_append_right _ owned)

theorem at_type_value_is_closed
    (typed : AtType signature tickets scope value type) (isValue : value.IsValue) : ClosedValue value := by
  cases typed with
  | checked scope typed => exact typed_value_is_closed typed isValue

/-- Every typed value with nonempty control has an actual completion step.
    Unit-input completion frames use canonical forms; a live boundary is
    excluded by the independent consumption judgment. -/
theorem value_raw_progress
    (typed : ConfigurationTyped signature effectTickets before result)
    (usage : ConfigurationUsage policy usageTickets before)
    (isValue : before.expression.IsValue) :
    before.stack = .nil ∨ ∃ after discharged, RawStep before after [] discharged := by
  obtain ⟨value, scope, stack⟩ := before
  obtain ⟨input, expression, control⟩ := typed
  have closed := at_type_value_is_closed expression isValue
  cases stack with
  | nil => exact Or.inl rfl
  | live owner input answer capture caller tail =>
      exact False.elim (value_cannot_return_through_live usage isValue)
  | spent owner answer caller tail =>
      exact Or.inr ⟨_, [], .leaveClause owner answer value closed scope caller tail⟩
  | push frame tail =>
      right
      cases control with
      | push frameTyped rest =>
          cases frame with
          | plain plain => exact ⟨_, [], .plug plain value closed scope tail⟩
          | handler handler => exact ⟨_, [], .leaveHandler handler value closed scope tail⟩
          | cell identity payload savedScope answer =>
              exact ⟨_, [.resource identity], .leaveCell identity payload answer savedScope scope value closed tail⟩
          | armed action => exact ⟨_, [], .startCleanup action value closed scope tail⟩
          | running action saved savedClosed =>
              have unit : value = .unit := typed_unit_value (at_type_closed_value expression closed) isValue
              subst value
              exact ⟨_, [.cleanup action.identity], .finishCleanup action saved savedClosed scope tail⟩
          | closing identity savedScope =>
              have unit : value = .unit := typed_unit_value (at_type_closed_value expression closed) isValue
              subst value
              exact ⟨_, [.close identity], .finishClose identity scope savedScope tail⟩
          | retiring owner =>
              have unit : value = .unit := typed_unit_value (at_type_closed_value expression closed) isValue
              subst value
              exact ⟨_, [.ticket owner], .retire owner scope tail⟩

/-- Completion progress with preservation: the witness is an admitted named
    step carrying the same registry and all six invariant fields. No freshness
    or access-check premise is required for these nonallocating transitions. -/
theorem value_progress
    (valid : Valid signature policy registry ambient before result outgoing)
    (isValue : before.execution.configuration.expression.IsValue) :
    before.execution.configuration.stack = .nil ∨
    ∃ after, NamedAccessStep ambient before after ∧
      Valid signature policy registry ambient after result outgoing := by
  have typed := effect_configuration_has_types valid.effects
  rcases value_raw_progress typed valid.usage isValue with terminal | step
  · exact Or.inl terminal
  · obtain ⟨after, discharged, raw⟩ := step
    obtain ⟨input, expression, control⟩ := typed
    exact Or.inr ⟨_, value_event_preserves raw (at_type_value_is_closed expression isValue) valid⟩

/-- Empty control has discharged every issued owner exactly once, by the
    conserved ledger. This does not assert termination of arbitrary execution. -/
theorem terminal_ledger_settled
    (valid : Valid signature policy registry ambient before result outgoing)
    (terminal : before.execution.configuration.stack = .nil) :
    before.execution.issued.Perm before.execution.completed ∧ before.execution.completed.Nodup := by
  have balance := valid.ledger.1
  have unique := valid.ledger.2
  simp only [RunState.erase, terminal, Stack.erase, Control.owners, List.nil_append] at balance
  exact ⟨balance, balance.nodup unique⟩

/-- Active accessibility produces an actual live boundary on the active spine;
    dormant captures are never searched. -/
theorem active_ticket_has_boundary (present : owner ∈ activeTickets stack) :
    ∃ (front : Stack), ∃ input answer capture caller tail,
      stack = front.append (.live owner input answer capture caller tail) := by
  induction stack with
  | nil => cases present
  | push frame rest ih =>
      obtain ⟨front, input, answer, capture, caller, tail, same⟩ := ih present
      exact ⟨.push frame front, input, answer, capture, caller, tail, by simp [Stack.append, same]⟩
  | live name input answer capture caller rest ihCapture ihRest =>
      rcases List.mem_cons.mp present with same | later
      · subst name
        exact ⟨.nil, input, answer, capture, caller, rest, rfl⟩
      · obtain ⟨front, q, a, saved, savedCaller, tail, same⟩ := ihRest later
        exact ⟨.live name input answer capture caller front, q, a, saved, savedCaller, tail,
          by simp [Stack.append, same]⟩
  | spent name answer caller rest ih =>
      obtain ⟨front, input, a, capture, savedCaller, tail, same⟩ := ih present
      exact ⟨.spent name answer caller front, input, a, capture, savedCaller, tail,
        by simp [Stack.append, same]⟩

theorem resume_demand_supplies_owner
    (checked : CodeDemand policy tickets scope (.resume binder value) demand) :
    ∃ owner, scope.resolve binder = some owner ∧ demand = [owner] := by
  cases checked with
  | idle scope used => cases used
  | consume known used => cases used with
      | resume permitted operand => exact ⟨_, by simp [Scope.resolve], rfl⟩

/-- A fully evaluated resume operand can always resume. Both lexical resolution
    and the active boundary are derived from usage, rather than supplied as
    premises. Full clause-prefix restoration preserves the same registry. -/
theorem resume_value_progress
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : value.IsValue) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Valid signature policy registry ambient after result outgoing := by
  obtain ⟨current, demand, code, control, accessible, balance, unique⟩ := valid.usage
  obtain ⟨owner, resolved, same⟩ := resume_demand_supplies_owner code
  have present : owner ∈ activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := active_ticket_has_boundary present
  subst stack
  have typed := effect_configuration_has_types valid.effects
  obtain ⟨type, expression, ports⟩ := typed
  have closed : ClosedValue value := by
    cases expression with
    | checked scope typed => cases typed with
        | resume operand effects => exact typed_value_is_closed operand isValue
  refine ⟨_, resume_preserves_joint_configuration valid resolved closed ?_⟩
  exact Syntax.UsageExecutionExamples.ordinary_access_checks (by intro h; cases h)
    (by intros; intro h; cases h) (by intro other h; cases h)

def ownerNumber : Owner → Nat
  | .resource identity | .cleanup identity | .close identity | .ticket identity => identity

def aboveOwners : List Owner → Nat
  | [] => 0
  | owner :: rest => max (ownerNumber owner + 1) (aboveOwners rest)

theorem owner_number_below (present : owner ∈ issued) : ownerNumber owner < aboveOwners issued := by
  induction issued with
  | nil => cases present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with same | later
      · subst owner
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih later) (Nat.le_max_right _ _)

/-- An administrative close can always choose a fresh identity from finite
    issued history. Source resource binders still need fresh instantiation. -/
theorem fresh_close_exists (unique : issued.Nodup) :
    ∃ identity, (issued ++ [Owner.close identity]).Nodup := by
  refine ⟨aboveOwners issued, List.nodup_append.mpr ⟨unique, by simp, ?_⟩⟩
  intro old present new singleton same
  simp only [List.mem_singleton] at singleton
  subst new
  subst old
  exact (Nat.lt_irrefl _) (owner_number_below present)

theorem discard_demand_supplies_owner
    (checked : CodeDemand policy tickets scope (.discard binder) demand) :
    ∃ owner, scope.resolve binder = some owner ∧ demand = [owner] := by
  cases checked with
  | idle scope used => cases used
  | consume known used => cases used with
      | discard permitted => exact ⟨_, by simp [Scope.resolve], rfl⟩

/-- A closed discard with structurally prepared retained captures takes an
    admitted step preserving the joint invariant. The proof derives the live
    boundary, successful plan, outside compatibility, and a fresh close owner.
    Preservation of PreparedCaptures itself is a separate obligation. -/
theorem prepared_discard_progress
    (valid : Valid signature policy registry []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ result [])
    (prepared : PreparedCaptures signature registry stack) :
    ∃ after, NamedAccessStep []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Valid signature policy registry [] after result [] := by
  obtain ⟨current, demand, code, control, accessible, balance, unique⟩ := valid.usage
  obtain ⟨owner, resolved, same⟩ := discard_demand_supplies_owner code
  have present : owner ∈ activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := active_ticket_has_boundary present
  subst stack
  obtain ⟨contract, effectKnown, rfl, rfl⟩ := active_live_contract valid.effects
  obtain ⟨record, known, ⟨certificate⟩⟩ := prepared_capture_for_discard prepared code resolved
  have recordKnown : registry.effects owner = some record.contract := by simp [Registry.effects, known]
  have sameContract := Option.some.inj (effectKnown.symm.trans recordKnown)
  cases sameContract
  obtain ⟨closeId, fresh⟩ := fresh_close_exists valid.ledger.2
  exact ⟨_, discard_preserves_joint_configuration valid recordKnown resolved certificate.built certificate.typed
    fresh (prepared_discard_access_checks valid prepared)⟩

namespace Examples

theorem disposal_initial_prepared :
    PreparedCaptures RetainedExamples.userAndCells Joint.Examples.disposalRegistry
      Joint.Examples.disposalInitial.execution.configuration.stack :=
  .live rfl (fun _ => ⟨ClosingExamples.preparedCell⟩) (.push (.push (.push .nil))) .nil

/-- A concrete resource-bearing state inhabits the added readiness judgment,
    so the disposal progress theorem is not vacuous. -/
theorem resource_disposal_progress :
    ∃ after, NamedAccessStep [] Joint.Examples.disposalInitial after ∧
      Valid RetainedExamples.userAndCells ControlUsageExamples.policy Joint.Examples.disposalRegistry [] after .unit [] :=
  prepared_discard_progress Joint.Examples.disposal_initial_valid disposal_initial_prepared

/-- Protected running cleanup may still be captured for resumption; the
    certificate judgment does not impose disposal on resume-only records. -/
theorem protected_resume_capture_needs_no_disposal_plan :
    PreparedCaptures RetainedExamples.userAndCells Joint.Examples.resumeOnlyRegistry
      DisposalGap.initial.execution.configuration.stack :=
  .live (record := ⟨Joint.Examples.disposalRecord.contract, ⟨true, false⟩⟩) rfl
    (by intro impossible; cases impossible) (.push (.push (.push .nil))) .nil

theorem protected_disposal_not_prepared :
    ¬ PreparedCaptures RetainedExamples.userAndCells Joint.Examples.disposalRegistry
      DisposalGap.initial.execution.configuration.stack := by
  intro checked
  cases checked with
  | live known ready saved rest =>
      have same := Option.some.inj
        ((show Joint.Examples.disposalRegistry 3 = some Joint.Examples.disposalRecord from rfl).symm.trans known)
      cases same
      exact DisposalGap.protected_discard_cannot_be_prepared (ready rfl)

end Examples

end Ash.OneShot.Progress

#print axioms Ash.OneShot.Progress.value_cannot_return_through_live
#print axioms Ash.OneShot.Progress.value_raw_progress
#print axioms Ash.OneShot.Progress.value_progress
#print axioms Ash.OneShot.Progress.terminal_ledger_settled
#print axioms Ash.OneShot.Progress.active_ticket_has_boundary
#print axioms Ash.OneShot.Progress.resume_value_progress
#print axioms Ash.OneShot.Progress.fresh_close_exists
#print axioms Ash.OneShot.Progress.prepared_discard_progress
#print axioms Ash.OneShot.Progress.Examples.resource_disposal_progress
#print axioms Ash.OneShot.Progress.Examples.protected_resume_capture_needs_no_disposal_plan
#print axioms Ash.OneShot.Progress.Examples.protected_disposal_not_prepared
