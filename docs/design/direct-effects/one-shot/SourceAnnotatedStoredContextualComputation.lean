import SourceConsumingAdmissionComputation
import SourceAnnotatedStoredExactControl

/-! Ordinary runtime reductions retain contextual consuming-source admission.
The initial action witness is shared by source typing, usage, completion and
the contextual judgment. Existing execution assembly supplies ownership and
access preservation; no successor source judgment is an event premise. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeState
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingClauseAnnotations (Body)
open SourceConsumingCleanupAdmission (Context At)
open SourceScheduledCapabilityAnnotations (DeclarationLaws)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws nested admission certification outward}
  {project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
    admission.accepts outward required plans → nested.accepts required plans}

/-- Source-level typing and contextual admission select the same subtree at
the actual runtime reduction. The retained source and action map are shared. -/
theorem AtPackets.ordinary_contextual_snapshot
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {plan : Plan dependencies} {body : Body world owner plan}
    (context : Context world owner outward actions
      (OwnerPhaseTransitions.available (ScopedExecution.ownedTickets stack.erase)) whole front saved waiting)
    (pending : SourceBoundSnapshots.Retained world whole)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code stack plan whole output demand row stored evidence)
    (admitted : At laws project body context)
    (nestedSource : body.Nested)
    (checked : body.BoundCheck resumeRequired closeRequired actions
      (OwnerPhaseTransitions.available (ScopedExecution.ownedTickets stack.erase)) wholeScope waitingScope context.before)
    (event : SourceAnnotatedCode.Reduction code scope afterCode afterScope) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBody : Body world owner nextPlan,
    ∃ remaining nextRow,
      AtPackets operations policy contracts tables families required actions annotations world outward outside
        afterScope afterCode stack nextPlan whole output remaining nextRow stored evidence ∧
      At laws project nextBody context ∧
      nextBody.Nested ∧
      nextBody.BoundCheck resumeRequired closeRequired actions
        (OwnerPhaseTransitions.available (ScopedExecution.ownedTickets stack.erase)) wholeScope waitingScope context.before ∧
      body.Reduction event.rule nextBody ∧ demand.Perm remaining ∧ nextRow.Sublist row ∧
      SourceBoundSnapshots.Computed event.rule
        ⟨_, plan, body.boundAnnotation, _, _, whole, pending⟩
        ⟨_, nextPlan, nextBody.boundAnnotation, _, _, whole, pending⟩ := by
  obtain ⟨nextSnapshot, remaining, nextRow, _, next, moved, accounting, included⟩ :=
    SourceAnnotatedStoredComputation.ordinary_snapshot
      ⟨_, plan, body.boundAnnotation, _, _, whole, pending⟩ state event
  obtain ⟨_, nextPlan, nextBody, nextSource, nextChecked, reduced, same⟩ :=
    admitted.computed checked pending moved
  subst nextSnapshot
  exact ⟨_, nextPlan, nextBody, remaining, nextRow, next, nextSource, reduced.nested nestedSource, nextChecked,
    reduced, accounting, included, moved⟩

end Ash.OneShot.SourceAnnotatedRuntimeState

namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingClauseAnnotations (Body)
open SourceConsumingCleanupAdmission (Context At)
open SourceScheduledCapabilityAnnotations (DeclarationLaws)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws nested admission certification []}
  {project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
    admission.accepts [] required plans → nested.accepts required plans}

/-- The same initial witness supplies all action-sensitive premises. Runtime
assembly reuses the existing raw-step ownership, access and completion proofs.
Both the successor runtime and its contextual source are conclusions. -/
theorem AtPackets.ordinary_contextual_step
    {actions : Syntax.UsageTickets}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {plan : Plan dependencies} {body : Body (ScopedTyping.resourceWorld issued) owner plan}
    (context : Context (ScopedTyping.resourceWorld issued) owner [] actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) whole front saved waiting)
    (pending : SourceBoundSnapshots.Retained (ScopedTyping.resourceWorld issued) whole)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ plan whole output demand row bound stored evidence)
    (initial : ConfigurationUsage policy actions (SourceAnnotatedRuntime.Configuration.erase ⟨code, scope, stack⟩) ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope code stack plan whole output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
        registry actions stack.erase)
    (admitted : At laws project body context)
    (nestedSource : body.Nested)
    (checked : body.BoundCheck resumeRequired closeRequired actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) wholeScope waitingScope context.before)
    (event : SourceAnnotatedCode.Reduction code scope afterCode afterScope) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies,
    ∃ nextBody : Body (ScopedTyping.resourceWorld issued) owner nextPlan, ∃ remaining nextRow,
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨afterCode, afterScope, stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextPlan whole output remaining nextRow bound stored evidence ∧
      (ConfigurationUsage policy actions after.erase ∧ UsageRegistryHistory actions issued ∧
        SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
          (ScopedTyping.resourceWorld issued) [] [] afterScope afterCode stack nextPlan whole output remaining nextRow stored evidence ∧
        DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
          registry actions stack.erase) ∧
      At laws project nextBody context ∧
      nextBody.Nested ∧
      nextBody.BoundCheck resumeRequired closeRequired actions
        (OwnerPhaseTransitions.available (ownedTickets stack.erase)) wholeScope waitingScope context.before ∧
      body.Reduction event.rule nextBody ∧ demand.Perm remaining ∧ nextRow.Sublist row ∧
      SourceBoundSnapshots.Computed event.rule
        ⟨_, plan, body.boundAnnotation, _, _, whole, pending⟩
        ⟨_, nextPlan, nextBody.boundAnnotation, _, _, whole, pending⟩ := by
  obtain ⟨usage, history, source, retained⟩ := initial
  obtain ⟨_, nextPlan, nextBody, remaining, nextRow, next, nextSource, nextNested, nextChecked, reduced,
    accounting, included, moved⟩ := source.ordinary_contextual_snapshot context pending admitted nestedSource checked event
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
  refine ⟨_, nextPlan, nextBody, remaining, nextRow, step, ?_,
    ⟨nextUsage, history, next, retained⟩, nextSource, nextNested, nextChecked,
    reduced, accounting, included, moved⟩
  apply assemble_entry_atPackets (after := ⟨afterCode, afterScope, stack⟩) run.coherent run.current raw freshOwners
    current.current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.current.results
  · rfl
  · simp

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.ordinary_contextual_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.ordinary_contextual_step
