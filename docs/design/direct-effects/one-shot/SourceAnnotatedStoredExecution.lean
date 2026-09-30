import SourceAnnotatedStoredHandlers
import SourceAnnotatedExecutionEntries

/-! The combined runtime invariant keeps installed packets paired with their
actual typed frames. Entry assembly reuses the existing ledger, access, names,
action history and retained completion proofs. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Annotations)
open SourceConsumingStoredBounds (StackBounds HandlerBounds)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

structure AtPackets [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (declarations : Instantiation.DeclarationRegistry)
    (policy : Syntax.TicketPolicy) (contracts : Contracts) (registry : CoherentSourceTypes.Owners.Registry)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (annotations : Annotations) (state : SourceAnnotatedRuntime.NamedState)
    {dependencies : SourceDependencyAnnotations.Dependencies} (plan : SourceDeclarationPlans.Plan dependencies)
    {receiving : SourceDependencyCapture.Scope} {hints : Hints receiving} (forest : Forest hints)
    (output : Value) (demand : List Nat) (row : Footprint) (resultBound : CallableContracts.Contract)
    (stored : StackBounds families state.execution.configuration.stack)
    (evidence : SourcePlannedFrames.DeclarationEvidence := SourcePlannedFrames.recipeEvidence) : Prop where
  coherent : contracts.erase.erase = registry.contracts
  current : DeclaredExecution.Valid operations.erase.erase declarations policy registry tables [] [] state.erase output.erase.erase demand row resultBound
  annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ state.execution.issued
  actions : ∃ tickets,
    ConfigurationUsage policy tickets state.execution.configuration.erase ∧
    UsageRegistryHistory tickets state.execution.issued ∧
    SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required tickets annotations
      (ScopedTyping.resourceWorld state.execution.issued) [] [] state.execution.configuration.scope
      state.execution.configuration.expression state.execution.configuration.stack plan forest output demand row stored evidence ∧
    DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld state.execution.issued)
      registry tickets state.execution.configuration.stack.erase


/-- Project the original combined invariant without choosing another source. -/
theorem AtPackets.atPlan
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      state plan forest output demand row resultBound stored evidence) :
    AtPlan operations declarations policy contracts registry tables families required annotations
      state plan forest output demand row resultBound evidence := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  exact ⟨run.coherent, run.current, run.annotationHistory, actions, usage, history, source.atPlan, retained⟩

theorem assemble_entry_atPackets [SourceScheduledChecks.DeclarationProjection admission certification]
    {nextFamilies : SourceDependencyFrames.Families} {after : SourceAnnotatedRuntime.Configuration}
    {stored : StackBounds nextFamilies after.stack}
    (coherent : contracts.erase.erase = registry.contracts)
    (current : DeclaredExecution.Valid operations.erase.erase declarations policy registry tables [] [] before.erase output.erase.erase demand row resultBound)
    (raw : RawStep before.execution.configuration.erase after.erase created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration.erase after.erase).Nodup)
    (checks : AccessChecks before.execution.configuration.erase [])
    (usage : ConfigurationUsage policy actions before.execution.configuration.erase)
    (history : UsageRegistryHistory actions before.execution.issued)
    (annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ before.execution.issued)
    (retained : DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld before.execution.issued)
      registry actions before.execution.configuration.stack.erase)
    (source : SourceAnnotatedRuntimeState.AtPackets operations policy contracts nextTables nextFamilies nextRequired
      (ScopedActionUsage.advance actions after.erase created) annotations (ScopedTyping.resourceWorld (before.execution.issued ++ created)) [] []
      after.scope after.expression after.stack plan forest output nextDemand nextRow stored evidence)
    (results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld (before.execution.issued ++ created)) after.erase resultBound)
    (update : registry.runtime.joint.usage = advanceUsageTickets policy registry.runtime.joint.usage after.erase created)
    (noTickets : ∀ owner, Owner.ticket owner ∉ created) :
    AtPackets operations declarations policy contracts registry nextTables nextFamilies nextRequired annotations
      (SourceAnnotatedRuntime.advanceState before after created discharged) plan forest output nextDemand nextRow resultBound stored evidence := by
  have existing := assemble_entry_atPlan coherent current raw freshOwners freshHandlers checks usage history
    annotationHistory retained source.atPlan results update noTickets
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners checks
  have extension := ScopedActionUsage.advance_extends (after := after.erase) usageChecks.allocation
  have unique : (ownedTickets after.stack.erase).Nodup := by
    cases source with
    | checked _ _ _ _ _ _ _ unique _ _ _ => exact unique
  have larger : ScopedTyping.resourceWorld before.execution.issued ⊆
      ScopedTyping.resourceWorld (before.execution.issued ++ created) := by
    rw [ScopedTyping.resource_world_append]
    exact List.subset_append_left _ _
  exact ⟨coherent, existing.current, existing.annotationHistory,
    _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
    ScopedActionUsage.raw_step_preserves_history raw history, source,
    DeclaredClosingInvariant.raw_step_preserves_retained raw retained (fun _ _ known => known)
      extension larger (.none noTickets) unique⟩

theorem AtPackets.handler_annotations_snapshot
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
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
        nextStored = .push (.handler packet) (stored.registries_congr (SourceScheduledHandlers.register_agrees freshStack))) := by
  have retainedActivations : stack.erase.erase.activations ⊆ activations := by
    intro activation member
    exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
      (run.current.names.handlers activation))
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, _, admitted⟩ :=
    SourceAnnotatedStoredHandlers.handler_annotations_exact_snapshot snapshot source retainedActivations
  refine ⟨answerPort, table, clauseFamilies, declarationRequirements, ?_⟩
  intro activation answerType freshActivation answerSame
  obtain ⟨handler, nextSnapshot, actualPlans, packet, nextStored, activationSame, typeSame, _, _, _, raw, next, moved, origin, packetShape⟩ := admitted activation answerType freshActivation answerSame
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
    ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, moved, origin, packetShape⟩
  apply assemble_entry_atPackets (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil, after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
      SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase] using results
  · rfl
  · simp

/-- Start joint packet tracking at the original empty-stack runtime invariant. -/
theorem AtPlan.empty_packets
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, .nil⟩, issued, completed⟩, activations⟩ plan forest output demand row bound evidence) :
    AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, .nil⟩, issued, completed⟩, activations⟩ plan forest output demand row bound .nil evidence := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  exact ⟨run.coherent, run.current, run.annotationHistory, actions, usage, history, source.empty_packets, retained⟩

theorem AtPackets.handler_annotations_snapshot_admitted
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]
    [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    (transport : ∀ {before after families required}
      {first : SourceDeclarationPlans.ClausePlans before families} {second : SourceDeclarationPlans.ClausePlans after families},
      nested.accepts required first → SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
        nested.accepts required second)
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (snapshotAdmitted : snapshot.Admitted)
    {stored : StackBounds families stack}
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
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
      nextSnapshot.Admitted ∧
      nextStored.Admitted (ScopedTyping.resourceWorld issued)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) ∧
      SourceBoundSnapshots.HandlerPacketFrom handler table declarationRequirements actualPlans snapshot packet ∧
      (∃ freshStack : handler.activation ∉ stack.erase.erase.activations,
        nextStored = .push (.handler packet) (stored.registries_congr (SourceScheduledHandlers.register_agrees freshStack))) := by
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, admitted⟩ :=
    AtPackets.handler_annotations_snapshot snapshot run
  refine ⟨answerPort, table, clauseFamilies, declarationRequirements, ?_⟩
  intro activation answerType fresh answerSame
  obtain ⟨handler, nextSnapshot, actualPlans, packet, nextStored, activationSame, typeSame, step, next, moved, origin, packetShape⟩ :=
    admitted activation answerType fresh answerSame
  have packets : nextStored.Admitted (ScopedTyping.resourceWorld issued)
      (SourceScheduledHandlers.register required handler.activation declarationRequirements) := by
    obtain ⟨freshStack, same⟩ := packetShape
    rw [same]
    exact .push (.handler (origin.admitted transport snapshotAdmitted))
      (storedAdmitted.registries_congr (SourceScheduledHandlers.register_agrees freshStack)
        (SourceScheduledHandlers.register_agrees freshStack))
  exact ⟨handler, nextSnapshot, actualPlans, packet, nextStored, activationSame, typeSame, step, next,
    moved, moved.admitted snapshotAdmitted, packets, origin, packetShape⟩

theorem AtPackets.handler_progress_snapshot_admitted
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]
    [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    (transport : ∀ {before after families required}
      {first : SourceDeclarationPlans.ClausePlans before families} {second : SourceDeclarationPlans.ClausePlans after families},
      nested.accepts required first → SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
        nested.accepts required second)
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (snapshotAdmitted : snapshot.Admitted)
    {stored : StackBounds families stack}
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence) :
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ table clauseFamilies declarationRequirements, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
    ∃ packet : HandlerBounds (SourceScheduledHandlers.register families handler.activation clauseFamilies) handler,
    ∃ nextStored : StackBounds (SourceScheduledHandlers.register families handler.activation clauseFamilies) (.push (.handler handler) stack),
      handler.activation ∉ activations ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand row bound nextStored evidence ∧
      SourceBoundSnapshots.EnteredHandler handler.effectInst table declarationRequirements actualPlans snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧
      nextStored.Admitted (ScopedTyping.resourceWorld issued)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) ∧
      SourceBoundSnapshots.HandlerPacketFrom handler table declarationRequirements actualPlans snapshot packet ∧
      (∃ freshStack : handler.activation ∉ stack.erase.erase.activations,
        nextStored = .push (.handler packet) (stored.registries_congr (SourceScheduledHandlers.register_agrees freshStack))) := by
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, admitted⟩ :=
    AtPackets.handler_annotations_snapshot_admitted transport snapshot snapshotAdmitted storedAdmitted run
  obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name activations
  obtain ⟨handler, nextSnapshot, actualPlans, packet, nextStored, activationSame, _, step, next, moved,
    nextAdmitted, packets, origin, packetShape⟩ :=
    admitted activation (ScopedPorts.embedPort answerPort) fresh (by simp)
  exact ⟨handler, table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, packet, nextStored,
    activationSame ▸ fresh, step, next, moved, nextAdmitted, packets, origin, packetShape⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.atPlan
#print axioms Ash.OneShot.SourceAnnotatedExecution.assemble_entry_atPackets
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.handler_annotations_snapshot

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.empty_packets

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.handler_annotations_snapshot_admitted

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.handler_progress_snapshot_admitted
