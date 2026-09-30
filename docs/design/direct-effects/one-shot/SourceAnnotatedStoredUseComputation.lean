import SourceConsumingUseAligned
import SourceAnnotatedStoredContextualComputation

/-! Ordinary typed reductions preserve consumption-time source records at
their actual receivers. Source descent reuses the existing four reductions;
execution assembly reuses the established ownership and completion proofs. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeState
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingCleanupAdmission (Context UseAlignedBody)
open SourceBoundSnapshots (Snapshot)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

theorem AtPackets.ordinary_use_snapshot
    {sourceHints : Hints sourceScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {sourceWhole : Forest sourceHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (snapshot : Snapshot world)
    (original : Context world owner outward actions
      (OwnerPhaseTransitions.available (ScopedExecution.ownedTickets stack.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces world front)
    (record : UseAlignedBody resumeRequired closeRequired original cut caller snapshot.current snapshot.pending)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code stack snapshot.plan snapshot.forest output demand row stored evidence)
    (event : SourceAnnotatedCode.Reduction code scope afterCode afterScope) :
    ∃ next : Snapshot world, ∃ remaining nextRow,
    ∃ child : UseAlignedBody resumeRequired closeRequired original cut caller next.current snapshot.pending,
      AtPackets operations policy contracts tables families required actions annotations world outward outside
        afterScope afterCode stack next.plan next.forest output remaining nextRow stored evidence ∧
      record.source.body.Reduction event.rule child.source.body ∧
      SourceBoundSnapshots.Computed event.rule snapshot next ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨nextSnapshot, remaining, nextRow, _, next, moved, accounting, included⟩ :=
    SourceAnnotatedStoredComputation.ordinary_snapshot snapshot state event
  obtain ⟨child, reduced, _⟩ := record.computed moved
  exact ⟨nextSnapshot, remaining, nextRow, child, next, reduced, moved, accounting, included⟩

end Ash.OneShot.SourceAnnotatedRuntimeState

namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingCleanupAdmission (Context UseAlignedBody)
open SourceBoundSnapshots (Snapshot)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Source and runtime use the same initial action witness. The result keeps
that witness, the actual bound transition and the derived source record. -/
theorem AtPackets.ordinary_use_step {actions : Syntax.UsageTickets}
    {sourceHints : Hints sourceScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {sourceWhole : Forest sourceHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (snapshot : Snapshot (ScopedTyping.resourceWorld issued))
    (original : Context (ScopedTyping.resourceWorld issued) owner [] actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces (ScopedTyping.resourceWorld issued) front)
    (record : UseAlignedBody resumeRequired closeRequired original cut caller snapshot.current snapshot.pending)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (initial : ConfigurationUsage policy actions (SourceAnnotatedRuntime.Configuration.erase ⟨code, scope, stack⟩) ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope code stack snapshot.plan snapshot.forest output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
        registry actions stack.erase)
    (event : SourceAnnotatedCode.Reduction code scope afterCode afterScope) :
    ∃ next : Snapshot (ScopedTyping.resourceWorld issued), ∃ remaining nextRow,
    ∃ child : UseAlignedBody resumeRequired closeRequired original cut caller next.current snapshot.pending,
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨afterCode, afterScope, stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output remaining nextRow bound stored evidence ∧
      (ConfigurationUsage policy actions after.erase ∧ UsageRegistryHistory actions issued ∧
        SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
          (ScopedTyping.resourceWorld issued) [] [] afterScope afterCode stack next.plan next.forest output remaining nextRow stored evidence ∧
        DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
          registry actions stack.erase) ∧
      record.source.body.Reduction event.rule child.source.body ∧
      SourceBoundSnapshots.Computed event.rule snapshot next ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨usage, history, source, retained⟩ := initial
  obtain ⟨nextSnapshot, remaining, nextRow, child, next, reduced, moved, accounting, included⟩ :=
    source.ordinary_use_snapshot snapshot original cut caller record event
  have ready : RecursiveExpressions.Ready code.erase := by
    cases event with
    | bind closed environment => exact .bind closed.1
    | beta closed closure => exact .app closed.1
    | ifTrue | ifFalse => exact .branch
  have raw := SourceAnnotatedRuntime.ordinary_executes event stack
  obtain ⟨runtimeRemaining, runtimeRow, step, current, runtimeAccounting, runtimeIncluded⟩ :=
    SourceScheduledExecution.ready_preserves run.atPlan.run.erase ready raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners step.checks
  have nextUsage := ScopedActionUsage.raw_step_preserves raw usageChecks usage
  simp only [ScopedActionUsage.advance] at nextUsage
  refine ⟨nextSnapshot, remaining, nextRow, child, step, ?_,
    ⟨nextUsage, history, next, retained⟩, reduced, moved, accounting, included⟩
  apply assemble_entry_atPackets (after := ⟨afterCode, afterScope, stack⟩) run.coherent run.current raw freshOwners
    current.current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.current.results
  · rfl
  · simp

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.ordinary_use_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.ordinary_use_step
