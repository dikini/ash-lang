import SourceAnnotatedStoredExecutionEntries
import SourceAnnotatedExecutionCheckedEntries

/-! Supplied entry events retain their exact handler or cleanup action. Finite
source hints authenticate their fields; preservation constructs proof registries
and joint packet/source evidence for that same event target. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceConsumingStoredBounds (StackBounds HandlerBounds)

theorem AtPackets.handler_entry_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []] {handler : SourceAnnotatedRuntime.Handler}
    {families : SourceDependencyFrames.Families}
    {stored : StackBounds families stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, stack⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (fresh : handler.activation ∉ activations) (ports : checkEntryPort hint handler.answer = true) :
    ∃ table clauseFamilies declarationRequirements, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
    ∃ packet : HandlerBounds (SourceScheduledHandlers.register families handler.activation clauseFamilies) handler,
    ∃ nextStored : StackBounds (SourceScheduledHandlers.register families handler.activation clauseFamilies) (.push (.handler handler) stack),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, stack⟩,
          issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, handler.scope, .push (.handler handler) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand row bound nextStored evidence ∧
      SourceBoundSnapshots.EnteredHandler handler.effectInst table declarationRequirements actualPlans snapshot nextSnapshot ∧
      SourceBoundSnapshots.HandlerPacketFrom handler table declarationRequirements actualPlans snapshot packet ∧
      (∃ freshStack : handler.activation ∉ stack.erase.erase.activations,
        nextStored = .push (.handler packet) (stored.registries_congr (SourceScheduledHandlers.register_agrees freshStack))) := by
  have retainedActivations : stack.erase.erase.activations ⊆ activations := by
    intro activation member
    exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
      (run.current.names.handlers activation))
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, portKnown, admitted⟩ :=
    SourceAnnotatedStoredHandlers.handler_annotations_exact_snapshot snapshot source retainedActivations
  have answerSame : ScopedPorts.eraseType handler.answer = answerPort :=
    Option.some.inj ((checkEntryPort_iff.mp ports).symm.trans portKnown)
  obtain ⟨generated, nextSnapshot, actualPlans, packet, nextStored, activationSame, typeSame, clausesSame, scopeSame, effectSame, raw, next, moved, origin, packetShape⟩ :=
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
  refine ⟨table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, packet, nextStored,
    ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, moved, origin, packetShape⟩
  apply assemble_entry_atPackets (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil, after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
      SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase] using results
  · rfl
  · simp

theorem AtPackets.cleanup_entry_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification] {action : SourceAnnotatedRuntime.Action}
    {families : SourceDependencyFrames.Families}
    {stored : StackBounds families stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (freshOwners : (issued ++ [Owner.cleanup action.identity]).Nodup)
    (ports : checkCleanupPorts hint action = true) :
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, action.scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound (.push .armed stored) evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨answerPort, requests, portKnown, requestsKnown, admitted⟩ :=
    SourceAnnotatedStoredEntries.cleanup_annotations_exact_snapshot snapshot source action.closed.1
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
  apply assemble_entry_atPackets (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa [after, ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.handler_entry_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.cleanup_entry_snapshot
