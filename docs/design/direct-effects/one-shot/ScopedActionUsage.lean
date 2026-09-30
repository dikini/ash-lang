import ScopedActions

/-! Track the actions required by each selected clause independently of the
runtime's granted permissions. The existing structural usage judgment checks
this second registry on the same code, scopes, saved stacks and owner identities.
Nested clauses keep the original policy. Capture installs a least action bound;
all later steps preserve it rather than recomputing it from the current head.
-/
namespace Ash.OneShot.ScopedActionUsage
open ScopedExpressions ScopedExecution
open Syntax (UsageTickets UsageExtension)

/-- Only a new capture changes the action registry. The substituted clause has
exactly the same enclosing requirements as its source body. -/
def advance (tickets : UsageTickets) (after : Configuration) (created : List Owner) : UsageTickets :=
  match created with
  | [.ticket owner] => tickets.insert owner after.expression.requiredActions
  | _ => tickets

theorem advance_extends
    (fresh : ∀ owner, Owner.ticket owner ∈ created → tickets owner = none) :
    UsageExtension tickets (advance tickets after created) := by
  unfold advance
  split
  next remaining owner => exact Syntax.fresh_usage_insert_extends (fresh owner (by simp_all))
  next => exact fun _ _ known => known

/-- Reuse capture decomposition and least enclosing actions. No stack or usage
induction is repeated, and no closing certificate is assumed here. -/
theorem capture_preserves
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (before : ConfigurationUsage policy tickets
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩)
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    ConfigurationUsage policy (tickets.insert owner body.requiredActions)
      ⟨body.subst parameter operand, .ticket binder owner,
        .live owner input handler.answer capture handler.scope tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  have clauses := (handler_cut_checked_usage cut control).2
  have least := (scoped_least_enclosing_actions (selected_clause_usage selected clauses)).1
  exact capture_preserves_configuration_usage_with_rights cut least
    ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ isValue fresh

theorem raw_step_preserves
    (step : RawStep before after created discharged) (checks : UsageChecks tickets before created)
    (checked : ConfigurationUsage policy tickets before) :
    ConfigurationUsage policy (advance tickets after created) after := by
  have actual := step
  cases step with
  | capture requested operation parameter binder owner operand body scope whole capture tail handler
      input cut selected closed environment =>
      simpa only [advance, Code.substitution_required_actions body parameter closed.1] using
        (capture_preserves cut selected checked closed.1 (checks.allocation owner (by simp)))
  | focus | plug | bind | beta | ifTrue | ifFalse | enterHandler | leaveHandler | enterCell
  | leaveCell | enterCleanup | startCleanup | finishCleanup | resume | discard | leaveClause
  | finishClose | retire | readCell | writeCell =>
      simpa only [advance, advanceUsageTickets] using
        (raw_step_preserves_configuration_usage actual checks checked)

theorem raw_step_preserves_history
    (step : RawStep before after created discharged)
    (history : UsageRegistryHistory tickets issued) :
    UsageRegistryHistory (advance tickets after created) (issued ++ created) := by
  have actual := step
  cases step with
  | capture requested operation parameter binder owner operand body scope whole capture tail handler
      input cut selected closed environment =>
      intro name
      by_cases same : name = owner
      · subst name
        simp [advance, UsageTickets.insert]
      · simpa [advance, UsageTickets.insert, same] using history name
  | focus | plug | bind | beta | ifTrue | ifFalse | enterHandler | leaveHandler | enterCell
  | leaveCell | enterCleanup | startCleanup | finishCleanup | resume | discard | leaveClause
  | finishClose | retire | readCell | writeCell =>
      simpa [UsageRegistryHistory, advance] using history

/-- The same actual access-checked step preserves the independently checked
registry, including entries belonging to dormant and already consumed owners. -/
theorem named_step_preserves
    (step : NamedAccessStep ambient before after)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (history : UsageRegistryHistory tickets before.execution.issued) :
    ∃ next, ConfigurationUsage policy next after.execution.configuration ∧
      UsageRegistryHistory next after.execution.issued ∧ UsageExtension tickets next := by
  cases step with
  | mk execution access => cases execution with
      | event after created discharged raw freshOwners freshHandlers =>
          have checks := usage_checks_from_allocation_and_access history freshOwners access
          exact ⟨_, raw_step_preserves raw checks usage, raw_step_preserves_history raw history,
            advance_extends checks.allocation⟩

/-- An actual discard must be included in the retained action bound, regardless
of any larger runtime permission grant. -/
theorem discard_requires_action
    (checked : CodeDemand policy tickets scope (.discard binder) demand) :
    ∃ owner rights, tickets owner = some rights ∧ scope.resolve binder = some owner ∧
      demand = [owner] ∧ rights.dispose = true := by
  cases checked with
  | idle scope checked => cases checked
  | consume known checked => cases checked with
      | discard permitted => exact ⟨_, _, known, by simp [Execution.Scope.resolve], rfl, permitted⟩

/-- A resume-only clause is checked under its smaller action bound even when
the runtime policy grants both actions. A nested disposing clause still keeps
its own original policy check. -/
theorem nested_resume_uses_only_resume :
    Uses (fun _ => ⟨true, true⟩) (.ticket 9 ActionRequirements.resumeOnly)
      .available ActionExamples.sharedBinderBody .consumed := by
  have clauses := ActionExamples.shared_binder_both_checked
  cases clauses with
  | cons body rest => exact (scoped_least_enclosing_actions body).1

end Ash.OneShot.ScopedActionUsage

#print axioms Ash.OneShot.ScopedActionUsage.advance_extends
#print axioms Ash.OneShot.ScopedActionUsage.capture_preserves
#print axioms Ash.OneShot.ScopedActionUsage.raw_step_preserves
#print axioms Ash.OneShot.ScopedActionUsage.raw_step_preserves_history
#print axioms Ash.OneShot.ScopedActionUsage.named_step_preserves
#print axioms Ash.OneShot.ScopedActionUsage.discard_requires_action
#print axioms Ash.OneShot.ScopedActionUsage.nested_resume_uses_only_resume
