import SourceAnnotatedExecutionResourceEntry

/-! Handler and cleanup entry authenticate concrete runtime fields using source
hints. Updated proof registries are constructed by preservation, not supplied by
an event as a future-validity witness. -/
namespace Ash.OneShot.SourceAnnotatedRuntime

theorem Handler.data_ext {first second : Handler}
    (activation : first.activation = second.activation) (effect : first.effectInst = second.effectInst)
    (clauses : first.clauses = second.clauses) (scope : first.scope = second.scope)
    (answer : first.answer = second.answer) : first = second := by
  cases first
  cases second
  simp_all

theorem Action.data_ext {first second : Action}
    (identity : first.identity = second.identity) (callback : first.action = second.action)
    (scope : first.scope = second.scope) (answer : first.answer = second.answer)
    (requests : first.requests = second.requests) : first = second := by
  cases first
  cases second
  simp_all

end Ash.OneShot.SourceAnnotatedRuntime

namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)

/-- Authenticate the callback's request list and the enclosing expression's
answer port from their actual finite source hints. -/
def checkCleanupPorts (hint : Instantiation.ValueType) (action : SourceAnnotatedRuntime.Action) : Bool :=
  checkEntryPort hint action.answer &&
    decide (SourceFocusHints.inputPort Instantiation.Environment.empty action.action.hint =
      some (.function .unit .unit action.requests))

theorem checkCleanupPorts_iff : checkCleanupPorts hint action = true ↔
    SourceFocusHints.inputPort Instantiation.Environment.empty hint = some (ScopedPorts.eraseType action.answer) ∧
    SourceFocusHints.inputPort Instantiation.Environment.empty action.action.hint =
      some (.function .unit .unit action.requests) := by
  simp [checkCleanupPorts, checkEntryPort]

/-- Every supplied concrete handler with a fresh activation and matching answer
hint admits source-derived proof registries and a preserved runtime. -/
theorem AtPlan.handler_entry_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []] {handler : SourceAnnotatedRuntime.Handler}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, stack⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (fresh : handler.activation ∉ activations) (ports : checkEntryPort hint handler.answer = true) :
    ∃ table clauseFamilies declarationRequirements, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, stack⟩,
          issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, handler.scope, .push (.handler handler) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand row bound evidence ∧
      SourceBoundSnapshots.EnteredHandler handler.effectInst table declarationRequirements actualPlans snapshot nextSnapshot ∧
      (∃ answer residual, answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧
        SourceAnnotatedSources.Declarations operations policy contracts (ScopedTyping.resourceWorld issued)
          (fun _ => none) residual handler.effectInst answer handler.clauses table actualPlans) := by
  have retainedActivations : stack.erase.erase.activations ⊆ activations := by
    intro activation member
    exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
      (run.current.names.handlers activation))
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, portKnown, admitted⟩ :=
    SourceAnnotatedRuntimeHandlers.handler_annotations_exact_snapshot snapshot source retainedActivations
  have answerSame : ScopedPorts.eraseType handler.answer = answerPort :=
    Option.some.inj ((checkEntryPort_iff.mp ports).symm.trans portKnown)
  obtain ⟨generated, nextSnapshot, actualPlans, activationSame, typeSame, clausesSame, scopeSame, effectSame, raw, next, moved, clauseSource⟩ :=
    admitted handler.activation handler.answer fresh answerSame
  have same := SourceAnnotatedRuntime.Handler.data_ext activationSame
    (freeze_effect_injective effectSame) clausesSame scopeSame typeSame
  subst generated
  let after : SourceAnnotatedRuntime.Configuration := ⟨body, handler.scope, .push (.handler handler) stack⟩
  have results := DeclaredExecution.handler_step_results raw run.current.results
    ⟨Instantiation.freezeEffect handler.effectInst, body.erase, handler.clauses.erase, rfl⟩
  have checks : AccessChecks
      ⟨.handle (Instantiation.freezeEffect handler.effectInst) body.erase handler.clauses.erase, handler.scope, stack.erase⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨.handle (Instantiation.freezeEffect handler.effectInst) body.erase handler.clauses.erase, handler.scope, stack.erase⟩ after.erase).Nodup := by
    change (activations ++ [handler.activation]).Nodup
    apply List.nodup_append.mpr ⟨run.current.names.unique, by simp, ?_⟩
    intro old present new singleton same
    simp only [List.mem_singleton] at singleton
    subst new
    subst old
    exact fresh present
  have actual : RawStep
      (SourceAnnotatedRuntime.Configuration.erase
        ⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, stack⟩)
      after.erase [] [] := raw
  refine ⟨table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans,
    ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, moved, clauseSource⟩
  apply assemble_entry_atPlan (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil, after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
      SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase] using results
  · rfl
  · simp

theorem Run.handler_entry
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []] {handler : SourceAnnotatedRuntime.Handler}
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, stack⟩,
        issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (fresh : handler.activation ∉ activations) (ports : checkEntryPort hint handler.answer = true) :
    ∃ table clauseFamilies declarationRequirements, ∃ saved : Saved,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, stack⟩,
          issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, handler.scope, .push (.handler handler) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      Run operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) saved.forest output demand row bound evidence := by
  obtain ⟨dependencies, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, plan, .absent, _, _, forest, .absent forest⟩
  obtain ⟨table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, step, next, moved, _⟩ :=
    AtPlan.handler_entry_snapshot snapshot indexed fresh ports
  exact ⟨table, clauseFamilies, declarationRequirements, ⟨_, _, nextSnapshot.forest⟩, step, next.run⟩

/-- Every supplied concrete cleanup action passing the finite hint guard
preserves the runtime. Its callback and scope are the actual source fields. -/
theorem AtPlan.cleanup_entry_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification] {action : SourceAnnotatedRuntime.Action}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (freshOwners : (issued ++ [Owner.cleanup action.identity]).Nodup)
    (ports : checkCleanupPorts hint action = true) :
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, action.scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨answerPort, requests, portKnown, requestsKnown, admitted⟩ :=
    SourceAnnotatedRuntimeEntries.cleanup_annotations_exact_snapshot snapshot source action.closed.1
  obtain ⟨answerGuard, requestsGuard⟩ := checkCleanupPorts_iff.mp ports
  have answerSame : ScopedPorts.eraseType action.answer = answerPort := Option.some.inj (answerGuard.symm.trans portKnown)
  have requestsSame : requests = action.requests :=
    (ScopedPorts.Port.function.inj (Option.some.inj (requestsKnown.symm.trans requestsGuard))).2.2
  obtain ⟨generated, nextSnapshot, identitySame, typeSame, declaredRequests, callbackSame, scopeSame, raw, next, installed⟩ :=
    admitted action.identity action.answer answerSame
  have same := SourceAnnotatedRuntime.Action.data_ext identitySame callbackSame scopeSame typeSame (declaredRequests.trans requestsSame)
  subst generated
  let after : SourceAnnotatedRuntime.Configuration := ⟨body, action.scope, .push (.armed action) stack⟩
  have results := DeclaredExecution.cleanup_step_results raw run.current.results
  have checks : AccessChecks ⟨.cleanup action.action.erase body.erase, action.scope, stack.erase⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.cleanup action.action.erase body.erase, action.scope, stack.erase⟩ after.erase).Nodup := by
    simpa [enteredActivations, SourceAnnotatedRuntime.NamedState.erase] using run.current.names.unique
  have actual : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.cleanup hint action.action body, action.scope, stack⟩)
      after.erase [.cleanup action.identity] [] := raw
  refine ⟨nextSnapshot, ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, installed⟩
  apply assemble_entry_atPlan (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa [after, ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

theorem Run.cleanup_entry
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification] {action : SourceAnnotatedRuntime.Action}
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (freshOwners : (issued ++ [Owner.cleanup action.identity]).Nodup)
    (ports : checkCleanupPorts hint action = true) :
    ∃ saved : Saved,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, action.scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) saved.forest output demand row bound evidence := by
  obtain ⟨_, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, plan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
  obtain ⟨nextSnapshot, step, next, _⟩ := AtPlan.cleanup_entry_snapshot snapshot indexed freshOwners ports
  exact ⟨⟨_, _, nextSnapshot.forest⟩, step, next.run⟩

namespace CleanupPortExamples

def callback : SourceAnnotatedCode.Term := .lambda (.function .unit .unit [] []) 0 (.unit .unit)
def action : SourceAnnotatedRuntime.Action :=
  ⟨0, callback, by simp [callback, SourceAnnotatedCode.Term.erase, ClosedValue, Code.IsValue,
    Code.ResourceClosed, Code.dependencies, Code.freeNames, Syntax.without], .none, .unit, []⟩

theorem correct_requests_and_fabricated_requests :
    checkCleanupPorts .unit action = true ∧
    checkCleanupPorts .unit { action with requests := [.user 7 []] } = false := by decide

end CleanupPortExamples

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedRuntime.Handler.data_ext
#print axioms Ash.OneShot.SourceAnnotatedRuntime.Action.data_ext
#print axioms Ash.OneShot.SourceAnnotatedExecution.checkCleanupPorts_iff
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.handler_entry
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.cleanup_entry

#print axioms Ash.OneShot.SourceAnnotatedExecution.CleanupPortExamples.correct_requests_and_fabricated_requests

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.cleanup_entry_snapshot

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.handler_entry_snapshot
