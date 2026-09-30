import SourceAnnotatedExecutionComputation
import SourceAnnotatedExecutionResumption
import SourceAnnotatedRuntimeResources

/-! Source-derived entry annotations join the shared runtime. Resources use
finite support freshness; handlers update their interpretation registries;
cleanup retains the original callback and its declared requests. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)

theorem Run.resource_annotations
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (isValue : initializer.erase.IsValue) :
    ∃ forbidden : List Nat, ∃ answerPort : ScopedPorts.Port,
    ∀ identity answer, identity ∉ ScopedTyping.resourceWorld issued → identity ∉ forbidden →
      ScopedPorts.eraseType answer = answerPort →
    ∃ payload, ∃ saved : Saved,
      initializer.erase = .integer payload ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.resource identity] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.resource identity] []) saved.forest output demand row bound evidence := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨forbidden, answerPort, admitted⟩ := SourceAnnotatedRuntimeResources.resource_annotations source isValue
  refine ⟨forbidden, answerPort, ?_⟩
  intro identity answer fresh freshRequirements answerSame
  obtain ⟨payload, saved, same, raw, next⟩ := admitted identity answer fresh freshRequirements answerSame
  let after : SourceAnnotatedRuntime.Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
    .push (.cell identity payload scope answer) stack⟩
  have previousResults := run.current.results
  simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
    SourceAnnotatedCode.Term.erase, same] at previousResults
  have results := (CompletionFrames.resource_step previousResults fresh (answer := answer)).2
  have absent : Owner.resource identity ∉ issued := fun member => fresh (ScopedTyping.mem_resource_world.mpr member)
  have unique : issued.Nodup := run.current.ledger.2
  have freshOwners : (issued ++ [Owner.resource identity]).Nodup := by
    apply List.nodup_append.mpr ⟨unique, by simp, ?_⟩
    intro old present new singleton sameOwner
    simp only [List.mem_singleton] at singleton
    subst new
    subst old
    exact absent present
  have checks : AccessChecks ⟨.resource binder initializer.erase body.erase, scope, stack.erase⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resource binder initializer.erase body.erase, scope, stack.erase⟩ after.erase).Nodup := by
    simpa [enteredActivations, SourceAnnotatedRuntime.NamedState.erase] using run.current.names.unique
  have actual : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.resource hint binder initializer body, scope, stack⟩)
      after.erase [.resource identity] [] := by
    simpa only [after, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedCode.Term.erase, SourceAnnotatedCode.Term.erase_instantiate] using raw
  refine ⟨payload, saved, same, ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_entry (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa [after, ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [after, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedCode.Term.erase_instantiate,
      ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

theorem Run.resource_progress
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (isValue : initializer.erase.IsValue) :
    ∃ identity payload answer, ∃ saved : Saved,
      initializer.erase = .integer payload ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.resource identity] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.resource identity] []) saved.forest output demand row bound evidence := by
  obtain ⟨forbidden, answerPort, admitted⟩ := run.resource_annotations isValue
  obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name (ScopedTyping.resourceWorld issued ++ forbidden)
  obtain ⟨payload, saved, same, step, next⟩ := admitted identity (ScopedPorts.embedPort answerPort)
    (fun member => fresh (List.mem_append_left _ member))
    (fun member => fresh (List.mem_append_right _ member)) (by simp)
  exact ⟨identity, payload, _, saved, same, step, next⟩

theorem AtPlan.handler_annotations_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence) :
    ∃ answerPort : ScopedPorts.Port, ∃ table clauseFamilies declarationRequirements,
    ∀ activation answerType, activation ∉ activations → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
      handler.activation = activation ∧ handler.answer = answerType ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.handler handler) stack⟩
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
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, _, admitted⟩ :=
    SourceAnnotatedRuntimeHandlers.handler_annotations_exact_snapshot snapshot source retainedActivations
  refine ⟨answerPort, table, clauseFamilies, declarationRequirements, ?_⟩
  intro activation answerType freshActivation answerSame
  obtain ⟨handler, nextSnapshot, actualPlans, activationSame, typeSame, _, _, _, raw, next, moved, clauseSource⟩ := admitted activation answerType freshActivation answerSame
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
  refine ⟨handler, nextSnapshot, actualPlans, activationSame, typeSame,
    ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, moved, clauseSource⟩
  apply assemble_entry_atPlan (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil, after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
      SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase] using results
  · rfl
  · simp

theorem Run.handler_annotations
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence) :
    ∃ answerPort : ScopedPorts.Port, ∃ table clauseFamilies declarationRequirements,
    ∀ activation answerType, activation ∉ activations → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ saved : Saved,
      handler.activation = activation ∧ handler.answer = answerType ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      Run operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) saved.forest output demand row bound evidence := by
  obtain ⟨dependencies, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, plan, .absent, _, _, forest, .absent forest⟩
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, admitted⟩ :=
    AtPlan.handler_annotations_snapshot snapshot indexed
  refine ⟨answerPort, table, clauseFamilies, declarationRequirements, ?_⟩
  intro activation answerType fresh answerSame
  obtain ⟨handler, nextSnapshot, actualPlans, activationSame, typeSame, step, next, moved, _⟩ :=
    admitted activation answerType fresh answerSame
  exact ⟨handler, ⟨_, _, nextSnapshot.forest⟩, activationSame, typeSame, step, next.run⟩

theorem AtPlan.handler_progress_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence) :
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ table clauseFamilies declarationRequirements, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
      handler.activation ∉ activations ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand row bound evidence ∧
      SourceBoundSnapshots.EnteredHandler handler.effectInst table declarationRequirements actualPlans snapshot nextSnapshot ∧
      (∃ answer residual, answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧
        SourceAnnotatedSources.Declarations operations policy contracts (ScopedTyping.resourceWorld issued)
          (fun _ => none) residual handler.effectInst answer handler.clauses table actualPlans) := by
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, admitted⟩ := AtPlan.handler_annotations_snapshot snapshot run
  obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name activations
  obtain ⟨handler, nextSnapshot, actualPlans, activationSame, _, step, next, moved, clauseSource⟩ := admitted activation (ScopedPorts.embedPort answerPort) fresh (by simp)
  exact ⟨handler, table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, activationSame ▸ fresh, step, next, moved, clauseSource⟩

theorem Run.handler_progress
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence) :
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ table clauseFamilies declarationRequirements, ∃ saved : Saved,
      handler.activation ∉ activations ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      Run operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) saved.forest output demand row bound evidence := by
  obtain ⟨dependencies, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, plan, .absent, _, _, forest, .absent forest⟩
  obtain ⟨handler, table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, fresh, step, next, moved, _⟩ :=
    AtPlan.handler_progress_snapshot snapshot indexed
  exact ⟨handler, table, clauseFamilies, declarationRequirements, ⟨_, _, nextSnapshot.forest⟩, fresh, step, next.run⟩

theorem AtPlan.cleanup_annotations_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : callback.erase.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    ∀ identity answerType, (issued ++ [Owner.cleanup identity]).Nodup → ScopedPorts.eraseType answerType = answerPort →
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨answerPort, requests, _, _, admitted⟩ := SourceAnnotatedRuntimeEntries.cleanup_annotations_exact_snapshot snapshot source isValue
  refine ⟨answerPort, requests, ?_⟩
  intro identity answerType freshOwners answerSame
  obtain ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, _, _, raw, next, installed⟩ := admitted identity answerType answerSame
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
  refine ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, installed⟩
  apply assemble_entry_atPlan (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa [after, ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

theorem Run.cleanup_annotations
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (isValue : callback.erase.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    ∀ identity answerType, (issued ++ [Owner.cleanup identity]).Nodup → ScopedPorts.eraseType answerType = answerPort →
    ∃ action : SourceAnnotatedRuntime.Action, ∃ saved : Saved,
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) saved.forest output demand row bound evidence := by
  obtain ⟨_, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, plan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
  obtain ⟨answerPort, requests, admitted⟩ := AtPlan.cleanup_annotations_snapshot snapshot indexed isValue
  refine ⟨answerPort, requests, ?_⟩
  intro identity answerType freshOwners answerSame
  obtain ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, step, next, _⟩ :=
    admitted identity answerType freshOwners answerSame
  exact ⟨action, ⟨_, _, nextSnapshot.forest⟩, identitySame, typeSame, requestsSame, step, next.run⟩

theorem AtPlan.cleanup_progress_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : callback.erase.IsValue) :
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot := by
  obtain ⟨answerPort, requests, admitted⟩ := AtPlan.cleanup_annotations_snapshot snapshot run isValue
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.cleanup (fun _ => rfl) run.current.ledger.2
  obtain ⟨action, nextSnapshot, _, _, _, step, next, installed⟩ := admitted identity (ScopedPorts.embedPort answerPort) fresh (by simp)
  exact ⟨action, nextSnapshot, step, next, installed⟩

theorem Run.cleanup_progress
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (isValue : callback.erase.IsValue) :
    ∃ action : SourceAnnotatedRuntime.Action, ∃ saved : Saved,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) saved.forest output demand row bound evidence := by
  obtain ⟨_, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, plan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
  obtain ⟨action, nextSnapshot, step, next, _⟩ := AtPlan.cleanup_progress_snapshot snapshot indexed isValue
  exact ⟨action, ⟨_, _, nextSnapshot.forest⟩, step, next.run⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.resource_annotations
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.resource_progress
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.handler_annotations
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.handler_progress
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.cleanup_annotations
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.cleanup_progress

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.cleanup_annotations_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.cleanup_progress_snapshot

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.handler_annotations_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.handler_progress_snapshot
