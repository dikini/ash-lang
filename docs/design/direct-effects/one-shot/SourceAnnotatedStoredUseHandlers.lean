import SourceConsumingUseAlignedSnapshots
import SourceAnnotatedStoredExecution

/-! Handler entry derives the consuming child from its original source record
at the same actual successor as typed packet installation. Existing runtime
ownership, names, access and completion proofs supply the execution step. -/
namespace Ash.OneShot.SourceAnnotatedStoredHandlers
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledHandlers (register register_agrees)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  {evidence : SourcePlannedFrames.DeclarationEvidence}
  [SourceStructuralHandlerEntry.DeclarationRetention admission evidence outward]
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {sourceHints : Hints sourceScope} {frontHints : Hints frontScope}
  {sourceWhole : Forest sourceHints} {front : Forest frontHints}

/-- The selected source is a conclusion at the actual installed handler. No
saved-source check at the intermediate caller is added to the premises. -/
theorem handler_annotations_use_source_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (sourceContext : SourceConsumingCleanupAdmission.Context world owner outward actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces world front)
    (record : SourceConsumingCleanupAdmission.UseAlignedBody resumeRequired closeRequired
      sourceContext cut caller snapshot.current snapshot.pending)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.handle hint requested code clauses) stack snapshot.plan snapshot.forest output demand row stored evidence)
    (retained : stack.erase.erase.activations ⊆ history) :
    ∃ answerPort : ScopedPorts.Port, ∃ table clauseFamilies declarationRequirements,
    SourceFocusHints.inputPort Instantiation.Environment.empty hint = some answerPort ∧
    ∀ activation answerType, activation ∉ history → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
    ∃ packet : SourceConsumingStoredBounds.HandlerBounds (register families handler.activation clauseFamilies) handler,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds (register families handler.activation clauseFamilies)
      (.push (.handler handler) stack),
      handler.activation = activation ∧ handler.answer = answerType ∧
      handler.clauses = clauses ∧ handler.scope = scope ∧ Instantiation.freezeEffect handler.effectInst = requested ∧
      RawStep ⟨.handle requested code.erase clauses.erase, scope, stack.erase⟩
        ⟨code.erase, scope, .push (.handler handler.erase) stack.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        (register families handler.activation clauseFamilies) (register required handler.activation declarationRequirements)
        actions annotations world outward outside scope code (.push (.handler handler) stack) nextSnapshot.plan nextSnapshot.forest output demand row nextStored evidence ∧
      SourceBoundSnapshots.EnteredHandler handler.effectInst table declarationRequirements actualPlans snapshot nextSnapshot ∧
      SourceBoundSnapshots.HandlerPacketFrom handler table declarationRequirements actualPlans snapshot packet ∧
      (∃ freshStack : handler.activation ∉ stack.erase.erase.activations,
        nextStored = .push (.handler packet) (stored.registries_congr (register_agrees freshStack))) ∧
      ∃ child : SourceConsumingCleanupAdmission.UseAlignedBody resumeRequired closeRequired sourceContext
        (.handler (effect := handler.effectInst) (table := table) (families := clauseFamilies)
          (required := declarationRequirements) cut) (.handler _ caller)
        nextSnapshot.current (.handler (effect := handler.effectInst) (table := table) (families := clauseFamilies)
          (required := declarationRequirements) snapshot.pending),
        nextSnapshot = ⟨_, nextSnapshot.plan, child.source.body.boundAnnotation, _, _,
          .handler (effect := handler.effectInst) (table := table) (families := clauseFamilies)
            (required := declarationRequirements) snapshot.forest, .handler snapshot.pending⟩ := by
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, portKnown, entered⟩ :=
    handler_annotations_exact_snapshot snapshot state retained
  refine ⟨answerPort, table, clauseFamilies, declarationRequirements, portKnown, ?_⟩
  intro activation answerType fresh answerSame
  obtain ⟨handler, nextSnapshot, actualPlans, packet, nextStored, activationSame, typeSame,
    clausesSame, scopeSame, effectSame, raw, next, moved, origin, packetShape⟩ :=
    entered activation answerType fresh answerSame
  obtain ⟨child, aligned⟩ := record.handler_entered moved
  exact ⟨handler, nextSnapshot, actualPlans, packet, nextStored, activationSame, typeSame,
    clausesSame, scopeSame, effectSame, raw, next, moved, origin, packetShape, child, aligned⟩

end Ash.OneShot.SourceAnnotatedStoredHandlers

#print axioms Ash.OneShot.SourceAnnotatedStoredHandlers.handler_annotations_use_source_snapshot

namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingStoredBounds (StackBounds HandlerBounds)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {sourceHints : Hints sourceScope} {frontHints : Hints frontScope}
  {sourceWhole : Forest sourceHints} {front : Forest frontHints}

/-- Use the same action witness in typed entry and source descent. Existing
entry assembly supplies runtime ownership and completion at that successor. -/
theorem AtPackets.handler_annotations_use_source_step {actions : Syntax.UsageTickets}
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (sourceContext : SourceConsumingCleanupAdmission.Context (ScopedTyping.resourceWorld issued) owner [] actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces (ScopedTyping.resourceWorld issued) front)
    (record : SourceConsumingCleanupAdmission.UseAlignedBody resumeRequired closeRequired
      sourceContext cut caller snapshot.current snapshot.pending)
    (initial : ConfigurationUsage policy actions
        (SourceAnnotatedRuntime.Configuration.erase ⟨.handle hint requested body clauses, scope, stack⟩) ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope (.handle hint requested body clauses) stack
        snapshot.plan snapshot.forest output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
        registry actions stack.erase)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence) :
    ∃ answerPort : ScopedPorts.Port, ∃ table clauseFamilies declarationRequirements,
    ∀ activation answerType, activation ∉ activations → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
    ∃ packet : HandlerBounds (SourceScheduledHandlers.register families handler.activation clauseFamilies) handler,
    ∃ nextStored : StackBounds (SourceScheduledHandlers.register families handler.activation clauseFamilies) (.push (.handler handler) stack),
      handler.activation = activation ∧ handler.answer = answerType ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand row bound nextStored evidence ∧
      SourceBoundSnapshots.EnteredHandler handler.effectInst table declarationRequirements actualPlans snapshot nextSnapshot ∧
      SourceBoundSnapshots.HandlerPacketFrom handler table declarationRequirements actualPlans snapshot packet ∧
      (∃ freshStack : handler.activation ∉ stack.erase.erase.activations,
        nextStored = .push (.handler packet) (stored.registries_congr (SourceScheduledHandlers.register_agrees freshStack))) ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts
        (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements)
        actions annotations (ScopedTyping.resourceWorld issued) [] [] scope body (.push (.handler handler) stack)
        nextSnapshot.plan nextSnapshot.forest output demand row nextStored evidence ∧
      ∃ child : SourceConsumingCleanupAdmission.UseAlignedBody resumeRequired closeRequired sourceContext
        (.handler (effect := handler.effectInst) (table := table) (families := clauseFamilies)
          (required := declarationRequirements) cut) (.handler _ caller)
        nextSnapshot.current (.handler (effect := handler.effectInst) (table := table) (families := clauseFamilies)
          (required := declarationRequirements) snapshot.pending),
        nextSnapshot = ⟨_, nextSnapshot.plan, child.source.body.boundAnnotation, _, _,
          .handler (effect := handler.effectInst) (table := table) (families := clauseFamilies)
            (required := declarationRequirements) snapshot.forest, .handler snapshot.pending⟩ := by
  have retainedActivations : stack.erase.erase.activations ⊆ activations := by
    intro activation member
    exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
      (run.current.names.handlers activation))
  obtain ⟨usage, history, source, retained⟩ := initial
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, _, admitted⟩ :=
    SourceAnnotatedStoredHandlers.handler_annotations_use_source_snapshot snapshot sourceContext cut caller record source retainedActivations
  refine ⟨answerPort, table, clauseFamilies, declarationRequirements, ?_⟩
  intro activation answerType freshActivation answerSame
  obtain ⟨handler, nextSnapshot, actualPlans, packet, nextStored, activationSame, typeSame, _, _, _, raw, next, moved, origin, packetShape, child, aligned⟩ := admitted activation answerType freshActivation answerSame
  have fresh : handler.activation ∉ activations := activationSame ▸ freshActivation
  let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.handler handler) stack⟩
  have results := DeclaredExecution.handler_step_results raw run.current.results ⟨requested, body.erase, clauses.erase, rfl⟩
  have checks : AccessChecks ⟨.handle requested body.erase clauses.erase, scope, stack.erase⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨.handle requested body.erase clauses.erase, scope, stack.erase⟩ after.erase).Nodup := by
    change (activations ++ [handler.activation]).Nodup
    apply List.nodup_append.mpr ⟨run.current.names.unique, by simp, ?_⟩
    intro old present new singleton same
    simp only [List.mem_singleton] at singleton
    subst new
    subst old
    exact fresh present
  have actual : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.handle hint requested body clauses, scope, stack⟩)
      after.erase [] [] := raw
  refine ⟨handler, nextSnapshot, actualPlans, packet, nextStored, activationSame, typeSame,
    ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, moved, origin, packetShape, next, child, aligned⟩
  apply assemble_entry_atPackets (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil, after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
      SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase] using results
  · rfl
  · simp

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.handler_annotations_use_source_step
