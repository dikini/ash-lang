import SourceBoundHandlerAdmission
import SourceAnnotatedBoundAdmission

/-! Actual handler entry preserves the admitted current/queued snapshots and
installs the source-derived packet on the same successor. Existing runtime
proofs supply typing, ownership, names, access and completion. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceDeclarationPlans (ClausePlans)
open SourceConsumingStoredBounds (HandlerBounds StackBounds)
open SourceScheduledHandlers (register register_agrees)
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem AtPlan.handler_entry_snapshot_admitted
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []] {handler : SourceAnnotatedRuntime.Handler}
    (transport : ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      nested.accepts required first → SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
        nested.accepts required second)
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families stack)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, stack⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (fresh : handler.activation ∉ activations) (ports : checkEntryPort hint handler.answer = true) :
    ∃ table clauseFamilies declarationRequirements, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
    ∃ packet : HandlerBounds (register families handler.activation clauseFamilies) handler,
    ∃ nextStored : StackBounds (register families handler.activation clauseFamilies) (.push (.handler handler) stack),
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
      nextSnapshot.Admitted ∧
      nextStored.Admitted (ScopedTyping.resourceWorld issued) (register required handler.activation declarationRequirements) ∧
      SourceBoundSnapshots.HandlerPacketFrom handler table declarationRequirements actualPlans snapshot packet ∧
      (∃ freshStack : handler.activation ∉ stack.erase.erase.activations,
        nextStored = .push (.handler packet) (stored.registries_congr (register_agrees freshStack))) ∧
      (∃ answer residual, answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧
        SourceAnnotatedSources.Declarations operations policy contracts (ScopedTyping.resourceWorld issued)
          (fun _ => none) residual handler.effectInst answer handler.clauses table packet.plans) := by
  obtain ⟨table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, step, next, moved, clauseSource⟩ :=
    AtPlan.handler_entry_snapshot snapshot run fresh ports
  have freshStack : handler.activation ∉ stack.erase.erase.activations := by
    intro member
    exact fresh (List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
      (run.current.names.handlers handler.activation)))
  obtain ⟨packet, nextStored, storedSame, nextStoredAdmitted, nextAdmitted, origin⟩ :=
    moved.install_admitted transport admitted stored storedAdmitted freshStack
  obtain ⟨answer, residual, answerSame, source⟩ := clauseSource
  exact ⟨table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, packet, nextStored, step, next, moved, nextAdmitted, nextStoredAdmitted, origin, ⟨freshStack, storedSame⟩, ⟨answer, residual, answerSame, origin.source source⟩⟩

theorem AtPlan.handler_progress_snapshot_admitted
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]
    (transport : ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      nested.accepts required first → SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
        nested.accepts required second)
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families stack)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence) :
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ table clauseFamilies declarationRequirements, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
    ∃ packet : HandlerBounds (register families handler.activation clauseFamilies) handler,
    ∃ nextStored : StackBounds (register families handler.activation clauseFamilies) (.push (.handler handler) stack),
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
      nextSnapshot.Admitted ∧
      nextStored.Admitted (ScopedTyping.resourceWorld issued) (register required handler.activation declarationRequirements) ∧
      SourceBoundSnapshots.HandlerPacketFrom handler table declarationRequirements actualPlans snapshot packet ∧
      (∃ freshStack : handler.activation ∉ stack.erase.erase.activations,
        nextStored = .push (.handler packet) (stored.registries_congr (register_agrees freshStack))) ∧
      (∃ answer residual, answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧
        SourceAnnotatedSources.Declarations operations policy contracts (ScopedTyping.resourceWorld issued)
          (fun _ => none) residual handler.effectInst answer handler.clauses table packet.plans) := by
  obtain ⟨handler, table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, fresh, step, next, moved, clauseSource⟩ :=
    AtPlan.handler_progress_snapshot snapshot run
  have freshStack : handler.activation ∉ stack.erase.erase.activations := by
    intro member
    exact fresh (List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
      (run.current.names.handlers handler.activation)))
  obtain ⟨packet, nextStored, storedSame, nextStoredAdmitted, nextAdmitted, origin⟩ :=
    moved.install_admitted transport admitted stored storedAdmitted freshStack
  obtain ⟨answer, residual, answerSame, source⟩ := clauseSource
  exact ⟨handler, table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, packet, nextStored, fresh, step, next, moved, nextAdmitted, nextStoredAdmitted, origin, ⟨freshStack, storedSame⟩, ⟨answer, residual, answerSame, origin.source source⟩⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.handler_entry_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.handler_progress_snapshot_admitted
