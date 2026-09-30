import SourceAnnotatedExecution

/-! Actual access-checked disposal obtains its plan interface from the shared
runtime certificate. The annotated successor retains the original callback
sources, and the runtime ledger and completion proofs are reused. -/
namespace Ash.OneShot.SourceAnnotatedRuntime
open ScopedExpressions ScopedExecution

/-- Recover the actual annotated live cut from a raw disposal event. This
classifies machine syntax; it assumes no source or successor invariant. -/
theorem raw_discard_shape
    (raw : RawStep ⟨.discard binder, scope, stack.erase⟩ after created discharged) :
    ∃ owner closeId caller input answer, ∃ (front capture tail : Stack) (plan : List ScopedExecution.CloseEntry),
      stack = front.append (.live owner input answer capture caller tail) ∧
      scope.resolve binder = some owner ∧ ScopedExecution.makePlan capture.erase = some plan ∧
      after = ⟨.unit, scope, (ScopedExecution.closeControl scope plan).append
        (.push (.closing closeId scope) (front.erase.append (.spent owner answer caller tail.erase)))⟩ ∧
      created = [.close closeId] ∧ discharged = [.ticket owner] := by
  have notFocused : ∀ {expression child context}, ScopedExecution.Focus expression child context →
      expression ≠ .discard binder := by
    intro expression child context focused
    cases focused <;> intro same <;> cases same
  generalize same : (ScopedExecution.Configuration.mk (.discard binder) scope stack.erase) = before at raw
  cases raw <;> simp only [ScopedExecution.Configuration.mk.injEq] at same <;>
    try (exfalso; exact Code.noConfusion same.1)
  case focus plain focused rest =>
    exact False.elim (notFocused focused same.1.symm)
  case plug plain value closed scope tail => rw [← same.1] at closed; simpa [Code.IsValue] using closed.1
  case leaveHandler handler value closed scope tail => rw [← same.1] at closed; simpa [Code.IsValue] using closed.1
  case leaveCell identity payload answer savedScope scope value closed tail => rw [← same.1] at closed; simpa [Code.IsValue] using closed.1
  case startCleanup action saved closed scope tail => rw [← same.1] at closed; simpa [Code.IsValue] using closed.1
  case leaveClause owner answer value closed scope caller tail => rw [← same.1] at closed; simpa [Code.IsValue] using closed.1
  case discard rawBinder owner closeId rawScope caller input answer rawFront rawCapture rawTail plan resolved built =>
    simp only [Code.discard.injEq] at same
    rcases same with ⟨rfl, rfl, stackErasure⟩
    obtain ⟨front, capture, tail, stackSame, frontSame, captureSame, tailSame⟩ := Stack.lift_live stackErasure
    cases frontSame
    cases captureSame
    cases tailSame
    exact ⟨owner, closeId, caller, input, answer, front, capture, tail, plan, stackSame, resolved, built, rfl, rfl, rfl⟩

end Ash.OneShot.SourceAnnotatedRuntime

#print axioms Ash.OneShot.SourceAnnotatedRuntime.raw_discard_shape

namespace Ash.OneShot.SourceAnnotatedExecution

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledSavedPlans (Saved)

/-- The retained certificate is tied to the actual annotated capture, so every
supplied closing plan produces exactly its annotated closing control. -/
theorem AtPlan.discard_at_snapshot {front capture tail : SourceAnnotatedRuntime.Stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound evidence)
    (resolved : scope.resolve binder = some owner)
    (builtAnnotated : SourceAnnotatedRuntime.makePlan capture = some annotatedPlan)
    (freshOwners : (issued ++ [Owner.close identity]).Nodup) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
          issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨.unit .unit, scope,
        (SourceAnnotatedRuntime.closeControl scope annotatedPlan).append
          (.push (.closing identity scope) (front.append (.spent owner answer caller tail)))⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row resultBound evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨_, _, _, admitted, _, _⟩ := DeclaredClosingInvariant.discard_progress run.run.erase.erase.shared.prepared
  have access : AccessChecks
      ⟨.discard binder, scope, (front.append (.live owner input answer capture caller tail)).erase⟩ [] := admitted.checks
  let plan := annotatedPlan.map SourceAnnotatedRuntime.CloseEntry.erase
  have built : makePlan capture.erase = some plan := by
    rw [SourceAnnotatedRuntime.makePlan_erase, builtAnnotated]
    rfl
  obtain ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ := usage
  obtain ⟨actualOwner, rights, actionKnown, actualResolved, _, permitted⟩ := ScopedActionUsage.discard_requires_action code
  cases Option.some.inj (actualResolved.symm.trans resolved)
  have located : SourceTemplates.CapturedIn owner capture.erase
      (front.erase.append (.live owner input answer capture.erase caller tail.erase)) :=
    RecursiveRecords.located_below front.erase .here
  obtain ⟨record, savedRights, known, savedKnown, checked⟩ :=
    retained owner capture.erase (by
      simpa only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using located)
  have sameRights := Option.some.inj (actionKnown.symm.trans savedKnown)
  obtain ⟨certificate⟩ := checked (sameRights ▸ permitted)
  have samePlan := Option.some.inj (certificate.built.symm.trans built)
  have erasedKnown : contracts.erase.erase owner = some record.annotation := by
    rw [run.coherent]
    simp [CoherentSourceTypes.Owners.Registry.contracts, known]
  obtain ⟨annotated, annotatedKnown, annotatedSame⟩ := Option.map_eq_some_iff.mp erasedKnown
  obtain ⟨contract, contractKnown, contractSame⟩ := Option.map_eq_some_iff.mp annotatedKnown
  have combined := (congrArg SourceDependencyAnnotations.Contract.erase contractSame).trans annotatedSame
  have effectsSame := congrArg CoherentSourceTypes.Owners.Contract.closeEffects combined
  change contract.closeEffects = record.annotation.closeEffects at effectsSame
  have typed : ScopedPorts.PlanTyped operations.erase.erase.ports (ScopedTyping.resourceWorld issued) contract.closeEffects plan := by
    rw [effectsSame]
    exact samePlan ▸ certificate.typed
  obtain ⟨restored, remaining, nextSnapshot, restoredSame, actual, successor, accounting, _, _, ⟨actualPlan, actualBuilt, exactRestored⟩, moved⟩ :=
    SourceAnnotatedDisposal.discard_cut_preserves_snapshot snapshot source contractKnown resolved built typed (closeId := identity)
  cases Option.some.inj (actualBuilt.symm.trans builtAnnotated)
  subst restored
  let next : SourceAnnotatedRuntime.Configuration := ⟨.unit .unit, scope,
    (SourceAnnotatedRuntime.closeControl scope annotatedPlan).append
      (.push (.closing identity scope) (front.append (.spent owner answer caller tail)))⟩
  have nextSame : next.erase = ⟨.unit, scope, (closeControl scope plan).append
      (.push (.closing identity scope) (front.erase.append (.spent owner answer caller tail.erase)))⟩ := by
    simp only [next, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase, restoredSame]
  have actualRaw : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.discard hint binder, scope,
        front.append (.live owner input answer capture caller tail)⟩)
      next.erase [.close identity] [.ticket owner] := by
    simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase, next] using actual
  have freshHandlers : (activations ++ enteredActivations
      (SourceAnnotatedRuntime.Configuration.erase ⟨.discard hint binder, scope,
        front.append (.live owner input answer capture caller tail)⟩) next.erase).Nodup := by
    simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.NamedState.erase,
      SourceAnnotatedCode.Term.erase, enteredActivations, List.append_nil]
      using run.current.names.unique
  have previousResults := run.current.results
  simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
    SourceAnnotatedCode.Term.erase, SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] at previousResults
  have results := (CompletionFrames.discard_step resolved built previousResults (closeId := identity)).2
  have joined := assemble_entry_atPlan (after := next) run.coherent run.current actualRaw freshOwners freshHandlers access
    ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ history run.annotationHistory retained
    (by simpa [next, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      ScopedTyping.resource_world_append, ScopedTyping.resourceWorld, ScopedActionUsage.advance] using successor)
    (by simpa [nextSame, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results)
    (by rw [nextSame]; rfl) (by simp)
  exact ⟨remaining, nextSnapshot, ⟨.event _ _ _ _ actualRaw freshOwners freshHandlers, access⟩, joined, accounting, moved⟩

theorem Run.discard_at {front capture tail : SourceAnnotatedRuntime.Stack}
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ forest output demand row resultBound evidence)
    (resolved : scope.resolve binder = some owner)
    (builtAnnotated : SourceAnnotatedRuntime.makePlan capture = some annotatedPlan)
    (freshOwners : (issued ++ [Owner.close identity]).Nodup) :
    ∃ remaining, ∃ nextForest : Saved,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
          issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨.unit .unit, scope,
        (SourceAnnotatedRuntime.closeControl scope annotatedPlan).append
          (.push (.closing identity scope) (front.append (.spent owner answer caller tail)))⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]) nextForest.forest output remaining row resultBound evidence ∧
      demand = owner :: remaining := by
  obtain ⟨dependencies, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨dependencies, plan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
  obtain ⟨remaining, nextSnapshot, step, next, accounting, _⟩ :=
    AtPlan.discard_at_snapshot snapshot indexed resolved builtAnnotated freshOwners
  exact ⟨remaining, ⟨_, _, nextSnapshot.forest⟩, step, next.run, accounting⟩

/-- Every actual access-checked disposal retains the annotated source. The
closing-plan interface is derived from the current runtime certificate. -/
theorem Run.discard_preserves
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row resultBound evidence)
    (step : NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack.erase⟩, issued, completed⟩, activations⟩ after) :
    ∃ successor : SourceAnnotatedRuntime.NamedState, ∃ owner remaining, ∃ nextForest : Saved,
      successor.erase = after ∧
      Run operations declarations policy contracts registry tables families required annotations successor nextForest.forest output remaining row resultBound evidence ∧
      demand = owner :: remaining := by
  cases step with
  | mk execution access => cases execution with
    | event after created discharged raw freshOwners freshHandlers =>
      obtain ⟨owner, identity, caller, input, answer, front, capture, tail, plan,
        stackSame, resolved, built, afterSame, createdSame, dischargedSame⟩ :=
        SourceAnnotatedRuntime.raw_discard_shape raw
      subst stack
      subst after
      subst created
      subst discharged
      obtain ⟨annotatedPlan, actualBuilt, planSame⟩ := SourceAnnotatedRuntime.makePlan_of_raw capture built
      subst plan
      obtain ⟨remaining, nextForest, _, next, accounting⟩ := run.discard_at resolved actualBuilt freshOwners
      refine ⟨_, owner, remaining, nextForest, ?_, next, accounting⟩
      simp only [SourceAnnotatedRuntime.advanceState, SourceAnnotatedRuntime.NamedState.erase,
        SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
        SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase,
        SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedRuntime.closeControl_erase]

/-- A retained certificate supplies an access-checked disposal step, and its
successor is constructed with the same annotated callbacks and owner ledger. -/
theorem Run.discard_progress
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row resultBound evidence) :
    ∃ after : SourceAnnotatedRuntime.NamedState, ∃ owner remaining, ∃ nextForest : Saved,
      NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack.erase⟩, issued, completed⟩, activations⟩ after.erase ∧
      Run operations declarations policy contracts registry tables families required annotations after nextForest.forest output remaining row resultBound evidence ∧
      demand = owner :: remaining := by
  obtain ⟨after, _, _, step, _, _⟩ := DeclaredClosingInvariant.discard_progress run.erase.erase.shared.prepared
  obtain ⟨successor, owner, remaining, nextForest, same, valid, accounting⟩ := run.discard_preserves step
  exact ⟨successor, owner, remaining, nextForest, same ▸ step, valid, accounting⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.discard_preserves
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.discard_progress

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.discard_at

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.discard_at_snapshot
