import SourceAnnotatedStoredUseEntries
import SourceAnnotatedStoredExecutionEntries

/-! Full cleanup/resource execution retains the source record derived by
entry descent. The existing entry assembly supplies ownership, access, names
and completion; the explicit action witness is shared with source typing. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingCleanupAdmission (Context UseAlignedBody)
open SourceDeclarationPlans (Plan)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {sourceHints : Hints sourceScope} {frontHints : Hints frontScope}
  {sourceWhole : Forest sourceHints} {front : Forest frontHints}

theorem AtPackets.cleanup_use_step {actions : Syntax.UsageTickets}
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (original : Context (ScopedTyping.resourceWorld issued) owner [] actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces (ScopedTyping.resourceWorld issued) front)
    (record : UseAlignedBody resumeRequired closeRequired original cut caller snapshot.current snapshot.pending)
    (initial : ConfigurationUsage policy actions
        (SourceAnnotatedRuntime.Configuration.erase ⟨.cleanup hint callback body, scope, stack⟩) ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope (.cleanup hint callback body) stack
        snapshot.plan snapshot.forest output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
        registry actions stack.erase)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (isValue : callback.erase.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    ∀ identity answerType, (issued ++ [Owner.cleanup identity]).Nodup → ScopedPorts.eraseType answerType = answerPort →
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound (.push .armed stored) evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope body (.push (.armed action) stack)
        nextSnapshot.plan nextSnapshot.forest output demand row (.push .armed stored) evidence ∧
      ∃ needs callbackDependencies, ∃ callbackPlan : Plan callbackDependencies,
      ∃ callbackRequired, ∃ footprint : RequestFootprint callbackPlan callbackRequired,
      ∃ declared : Declared (ScopedTyping.resourceWorld issued) (signature callbackPlan),
      ∃ child : UseAlignedBody resumeRequired closeRequired original
        (.cleanup (needs := needs) (plan := callbackPlan) cut)
        (.cleanup front callbackRequired footprint declared caller)
        nextSnapshot.current (.cleanup (needs := needs) (.absent (plan := callbackPlan)) snapshot.pending),
        nextSnapshot = ⟨_, nextSnapshot.plan, child.source.body.boundAnnotation, _, _,
          .cleanup (needs := needs) callbackPlan snapshot.forest, .cleanup .absent snapshot.pending⟩ ∧
        (SourceScheduledCapabilityAnnotations.Code.operations (forest := .running snapshot.forest) callbackRequired footprint declared).Valid
          [] actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) ∧
        (∀ request ∈ callbackRequired, request.1 ∈ needs) := by
  obtain ⟨usage, history, source, retained⟩ := initial
  obtain ⟨answerPort, requests, _, _, admitted⟩ := SourceAnnotatedStoredUseEntries.cleanup_use_snapshot snapshot original cut caller record source isValue
  refine ⟨answerPort, requests, ?_⟩
  intro identity answerType freshOwners answerSame
  obtain ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, _, _, raw, next, installed, sourceResult⟩ := admitted identity answerType answerSame
  rw [← identitySame] at raw freshOwners
  let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
  have results := DeclaredExecution.cleanup_step_results raw run.current.results
  have checks : AccessChecks ⟨.cleanup callback.erase body.erase, scope, stack.erase⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.cleanup callback.erase body.erase, scope, stack.erase⟩ after.erase).Nodup := by
    simpa [enteredActivations, SourceAnnotatedRuntime.NamedState.erase] using run.current.names.unique
  have actual : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.cleanup hint callback body, scope, stack⟩)
      after.erase [.cleanup action.identity] [] := raw
  refine ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, installed, next, sourceResult⟩
  apply assemble_entry_atPackets (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa [after, ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

theorem AtPackets.resource_use_step {actions : Syntax.UsageTickets}
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (original : Context (ScopedTyping.resourceWorld issued) owner [] actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces (ScopedTyping.resourceWorld issued) front)
    (record : UseAlignedBody resumeRequired closeRequired original cut caller snapshot.current snapshot.pending)
    (initial : ConfigurationUsage policy actions
        (SourceAnnotatedRuntime.Configuration.erase ⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩) ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope (.resource hint binder (.integer initialHint payload) body) stack
        snapshot.plan snapshot.forest output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
        registry actions stack.erase)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (freshOwners : (issued ++ [Owner.resource identity]).Nodup)
    (ports : checkEntryPort hint answer = true) :
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued ++ [identity]), ∃ nextRow,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.resource identity] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.resource identity] []) nextSnapshot.plan nextSnapshot.forest output demand nextRow bound (.push .cell stored) evidence ∧
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued ++ [identity]) [] [] scope
        (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) nextSnapshot.plan nextSnapshot.forest
        output demand nextRow (.push .cell stored) evidence ∧
      ∃ child : UseAlignedBody resumeRequired closeRequired
        (original.world_weaken (List.subset_append_left _ [identity]))
        (.cell (identity := identity) cut) (.cell (caller.world_weaken (List.subset_append_left _ [identity])))
        nextSnapshot.current (.cell (identity := identity) (snapshot.pending.world_weaken (List.subset_append_left _ [identity]))),
        nextSnapshot = ⟨_, nextSnapshot.plan, child.source.body.boundAnnotation, _, _,
          .cell (identity := identity) snapshot.forest,
          .cell (snapshot.pending.world_weaken (List.subset_append_left _ [identity]))⟩ := by
  obtain ⟨usage, history, source, retained⟩ := initial
  have freshWorld : identity ∉ ScopedTyping.resourceWorld issued := by
    intro member
    exact (List.nodup_append.mp freshOwners).2.2 (.resource identity)
      (ScopedTyping.mem_resource_world.mp member) (.resource identity) (by simp) rfl
  obtain ⟨actualPayload, nextSnapshot, nextRow, same, raw, next, included, installed, sourceResult⟩ :=
    SourceAnnotatedStoredUseEntries.resource_use_snapshot snapshot original cut caller record source (by trivial) freshWorld (checkEntryPort_iff.mp ports)
  cases Code.integer.inj same
  let after : SourceAnnotatedRuntime.Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
    .push (.cell identity payload scope answer) stack⟩
  have previousResults := run.current.results
  simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
    SourceAnnotatedCode.Term.erase] at previousResults
  have results := (CompletionFrames.resource_step previousResults freshWorld (answer := answer)).2
  have checks : AccessChecks ⟨.resource binder (.integer payload) body.erase, scope, stack.erase⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resource binder (.integer payload) body.erase, scope, stack.erase⟩ after.erase).Nodup := by
    simpa [enteredActivations, SourceAnnotatedRuntime.NamedState.erase] using run.current.names.unique
  have actual : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩)
      after.erase [.resource identity] [] := by
    simpa only [after, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedCode.Term.erase, SourceAnnotatedCode.Term.erase_instantiate] using raw
  refine ⟨nextSnapshot, nextRow, ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, included, installed, next, sourceResult⟩
  apply assemble_entry_atPackets (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa [after, ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [after, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedCode.Term.erase_instantiate,
      ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.cleanup_use_step
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.resource_use_step
