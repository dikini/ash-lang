import SourceConsumingUseAligned
import SourceAnnotatedStoredQueuedAdmission

/-! Typed focus and return retain the consumption-time source record. Actual
runtime successors, ownership and completion reuse existing transition proofs;
original captured source stays distinct from its current caller. A retained
neutral expansion connects the source cut to the actual runtime receiver. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExecution (ownedTickets)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceConsumingCleanupAdmission (Context UseAlignedBody UseAlignedFocused)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot)
open SourceScheduledCapabilityAnnotations (DeclarationLaws)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  {laws : DeclarationLaws nested admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → nested.accepts required plans}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {sourceHints : Hints sourceScope} {sourceWhole : Forest sourceHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}

/-- The actual focus split determines which source derivation becomes queued
and which remains current. All ten runtime focus forms use this same result. -/
theorem AtPackets.focus_use_source_snapshot
    [SourceScheduledChecks.DeclarationProjection admission certification] {plain : SourceAnnotatedRuntime.Plain}
    {plan : Plan dependencies} {bounds : Annotation world plan}
    (sourceContext : Context world owner outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase))
      base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces world front)
    (pending : SourceBoundSnapshots.Retained world whole)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      plain.scope code stack plan whole output demand row stored evidence)
    (queued : UseAlignedBody resumeRequired closeRequired sourceContext cut caller bounds pending)
    (position : SourceAnnotatedCode.Focus code child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ childDependencies restDependencies, ∃ childPlan : Plan childDependencies, ∃ restPlan : Plan restDependencies,
    ∃ childBounds : Annotation world childPlan, ∃ restBounds : Annotation world restPlan,
      ScopedExecution.RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨code, plain.scope, stack⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨child, plain.scope, .push (.plain plain) stack⟩) [] [] ∧
      AtPackets operations policy contracts tables families required actions annotations world outward outside
        plain.scope child (.push (.plain plain) stack) childPlan (.plain restPlan whole)
        output demand row (.push .plain stored) evidence ∧
      SourcePlanBounds.Focused world bounds childBounds restBounds ∧
      Nonempty (UseAlignedFocused resumeRequired closeRequired sourceContext cut caller childBounds restBounds pending) ∧
      SourceBoundSnapshots.Focused ⟨_, plan, bounds, _, _, whole, pending⟩
        ⟨_, childPlan, childBounds, _, _, .plain restPlan whole, .plain restBounds pending⟩ := by
  obtain ⟨_, _, childPlan, restPlan, childBounds, restBounds, raw, next, moved⟩ :=
    SourceAnnotatedStoredFocus.focus_snapshot ⟨_, plan, bounds, _, _, whole, pending⟩ state position guard
  exact ⟨_, _, childPlan, restPlan, childBounds, restBounds, raw, next, moved,
    ⟨queued.focused moved⟩, .step _ _ _ moved⟩

/-- Return reuses the source record on the actual top plain frame. Its
recomposed source and all contextual checks are conclusions of the theorem. -/
theorem AtPackets.plug_use_queued_snapshot {plain : SourceAnnotatedRuntime.Plain}
    {plan : Plan dependencies} {bounds : Annotation world plan}
    (sourceContext : Context world owner outward actions (OwnerPhaseTransitions.available (ownedTickets tail.erase))
      base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces world front)
    (pending : SourceBoundSnapshots.Retained world whole)
    (queued : UseAlignedBody resumeRequired closeRequired sourceContext cut caller bounds pending)
    {currentPlan : Plan currentDependencies} (currentBounds : Annotation world currentPlan)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.plain plain) tail) currentPlan (.plain plan whole)
      output demand row (.push .plain stored) evidence)
    (closed : ScopedExpressions.ClosedValue value.erase) :
    ∃ nextQueued : UseAlignedBody resumeRequired closeRequired sourceContext cut caller (bounds.plug plain.context).2.2 pending,
      ScopedExecution.RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨value, scope, .push (.plain plain) tail⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨plain.context.plug value, plain.scope, tail⟩) [] [] ∧
      AtPackets operations policy contracts tables families required actions annotations world outward outside
        plain.scope (plain.context.plug value) tail (bounds.plug plain.context).2.1 whole output demand row stored evidence ∧
      SourceBoundSnapshots.Returned plain.context
        ⟨_, currentPlan, currentBounds, _, _, .plain plan whole, .plain bounds pending⟩
        ⟨_, _, nextQueued.source.body.boundAnnotation, _, _, whole, pending⟩ := by
  obtain ⟨nextSnapshot, raw, next, returned⟩ := SourceAnnotatedStoredReturns.plug_snapshot
    ⟨_, currentPlan, currentBounds, _, _, .plain plan whole, .plain bounds pending⟩ state closed
  obtain ⟨nextQueued, same⟩ := queued.returned plain.context currentBounds returned
  subst nextSnapshot
  exact ⟨nextQueued, raw, next, returned⟩

end Ash.OneShot.SourceAnnotatedRuntimeState

namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceConsumingCleanupAdmission (Context UseAlignedBody UseAlignedFocused)
open SourcePlanBounds (Annotation)
open SourceScheduledCapabilityAnnotations (DeclarationLaws)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws nested admission certification []}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts [] required plans → nested.accepts required plans}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {sourceHints : Hints sourceScope} {sourceWhole : Forest sourceHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}

/-- Runtime ownership and completion come from the existing focus theorem;
the selected source and its exact action witness come from the source split.
The two results share the actual annotated runtime successor. -/
theorem AtPackets.focus_use_source_step {plain : SourceAnnotatedRuntime.Plain} {actions : Syntax.UsageTickets}
    {plan : Plan dependencies} {bounds : Annotation (ScopedTyping.resourceWorld issued) plan}
    (sourceContext : Context (ScopedTyping.resourceWorld issued) owner [] actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces (ScopedTyping.resourceWorld issued) front)
    (pending : SourceBoundSnapshots.Retained (ScopedTyping.resourceWorld issued) whole)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩ plan whole output demand row bound stored evidence)
    (initial : ConfigurationUsage policy actions (SourceAnnotatedRuntime.Configuration.erase ⟨code, plain.scope, stack⟩) ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] plain.scope code stack plan whole output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
        registry actions stack.erase)
    (queued : UseAlignedBody resumeRequired closeRequired sourceContext cut caller bounds pending)
    (position : SourceAnnotatedCode.Focus code child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ childDependencies restDependencies, ∃ childPlan : Plan childDependencies, ∃ restPlan : Plan restDependencies,
    ∃ childBounds : Annotation (ScopedTyping.resourceWorld issued) childPlan,
    ∃ restBounds : Annotation (ScopedTyping.resourceWorld issued) restPlan,
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨child, plain.scope, .push (.plain plain) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) childPlan (.plain restPlan whole)
        output demand row bound (.push .plain stored) evidence ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] plain.scope child (.push (.plain plain) stack)
        childPlan (.plain restPlan whole) output demand row (.push .plain stored) evidence ∧
      SourcePlanBounds.Focused (ScopedTyping.resourceWorld issued) bounds childBounds restBounds ∧
      Nonempty (UseAlignedFocused resumeRequired closeRequired sourceContext cut caller childBounds restBounds pending) ∧
      SourceBoundSnapshots.Focused ⟨_, plan, bounds, _, _, whole, pending⟩
        ⟨_, childPlan, childBounds, _, _, .plain restPlan whole, .plain restBounds pending⟩ := by
  obtain ⟨usage, history, original, retained⟩ := initial
  obtain ⟨_, _, childPlan, restPlan, childBounds, restBounds, raw, next, selected, kept, moved⟩ :=
    original.focus_use_source_snapshot sourceContext cut caller pending queued position guard
  obtain ⟨_, _, _, _, _, _, step, runtime, _⟩ :=
    run.focus_preserves_bounds ⟨_, plan, bounds, _, _, whole, pending⟩ position guard
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨_, _, childPlan, restPlan, childBounds, restBounds, step, ?_, next, selected, kept, moved⟩
  apply assemble_entry_atPackets run.coherent run.current raw freshOwners runtime.current.names.unique
    step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact runtime.current.results
  · rfl
  · simp

/-- Plain return reconstructs the contextual source at the runtime successor.
The existing return theorem supplies ownership and completion preservation. -/
theorem AtPackets.plug_use_queued_step {plain : SourceAnnotatedRuntime.Plain} {actions : Syntax.UsageTickets}
    {plan : Plan dependencies} {bounds : Annotation (ScopedTyping.resourceWorld issued) plan}
    (sourceContext : Context (ScopedTyping.resourceWorld issued) owner [] actions
      (OwnerPhaseTransitions.available (ownedTickets tail.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces (ScopedTyping.resourceWorld issued) front)
    (pending : SourceBoundSnapshots.Retained (ScopedTyping.resourceWorld issued) whole)
    (queued : UseAlignedBody resumeRequired closeRequired sourceContext cut caller bounds pending)
    {currentPlan : Plan currentDependencies} (currentBounds : Annotation (ScopedTyping.resourceWorld issued) currentPlan)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩
      currentPlan (.plain plan whole) output demand row bound (.push .plain stored) evidence)
    (initial : ConfigurationUsage policy actions
        (SourceAnnotatedRuntime.Configuration.erase ⟨value, scope, .push (.plain plain) tail⟩) ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope value (.push (.plain plain) tail)
        currentPlan (.plain plan whole) output demand row (.push .plain stored) evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
        registry actions (SourceAnnotatedRuntime.Stack.erase (.push (.plain plain) tail)))
    (closed : ClosedValue value.erase) :
    ∃ nextQueued : UseAlignedBody resumeRequired closeRequired sourceContext cut caller (bounds.plug plain.context).2.2 pending,
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨plain.context.plug value, plain.scope, tail⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) (bounds.plug plain.context).2.1 whole
        output demand row bound stored evidence ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] plain.scope (plain.context.plug value) tail
        (bounds.plug plain.context).2.1 whole output demand row stored evidence ∧
      SourceBoundSnapshots.Returned plain.context
        ⟨_, currentPlan, currentBounds, _, _, .plain plan whole, .plain bounds pending⟩
        ⟨_, _, nextQueued.source.body.boundAnnotation, _, _, whole, pending⟩ := by
  obtain ⟨usage, history, original, retained⟩ := initial
  obtain ⟨nextQueued, raw, next, moved⟩ := original.plug_use_queued_snapshot sourceContext cut caller pending queued currentBounds closed
  obtain ⟨_, remaining, _, step, runtime, balance, _, _⟩ := run.return_step_snapshot
    ⟨_, currentPlan, currentBounds, _, _, .plain plan whole, .plain bounds pending⟩
    (.plug plain value closed scope tail)
  change demand = remaining at balance
  subst remaining
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨nextQueued, step, ?_, next, moved⟩
  apply assemble_entry_atPackets run.coherent run.current raw freshOwners runtime.current.names.unique
    step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact runtime.current.results
  · rfl
  · simp

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.focus_use_source_snapshot
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.plug_use_queued_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.focus_use_source_step
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.plug_use_queued_step
