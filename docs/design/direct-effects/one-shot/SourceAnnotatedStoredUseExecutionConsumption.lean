import SourceAnnotatedStoredUseConsumption
import SourceAnnotatedStoredExecutionResumption
import SourceAnnotatedStoredExecutionDisposal

/-! Full execution activates source at the same consuming successor. Existing
runtime assembly supplies ownership, usage, completion, names and access;
the source record supplies recursive retained source and exact bound alignment. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy)
open SourceConsumingCleanupAdmission (Context UseAlignedBody)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceBoundSnapshots.Retained (ofCapability)

variable [nested : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {front capture tail : SourceAnnotatedRuntime.Stack}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {sourceFrontHints : Hints sourceFrontScope} {sourceFront : Forest sourceFrontHints}
  {sourceWholeHints : Hints sourceWholeScope} {sourceWhole : Forest sourceWholeHints}

/-- The explicit action witness is shared by the source record and runtime
assembly. Actual resumption both moves all existing payloads and constructs
valid retained source at its successor's exact pending snapshot. -/
theorem AtPackets.resume_use_step {actions : Syntax.UsageTickets}
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification [])
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts [] required plans → nested.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (original : Context (ScopedTyping.resourceWorld issued) owner [] actions
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)).erase))
      base baseFront saved waiting)
    (cut : OwnerCut owner sourceWhole sourceFront saved waiting)
    (before : Interfaces (ScopedTyping.resourceWorld issued) sourceFront)
    {bounds : SourcePlanBounds.Annotation (ScopedTyping.resourceWorld issued) (.invoke (key := ⟨owner, .resume⟩))}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds snapshot.pending)
    (initial : ConfigurationUsage policy actions
        (SourceAnnotatedRuntime.Configuration.erase ⟨.resume hint binder value, scope,
          front.append (.live owner inputType answerType capture caller tail)⟩) ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope (.resume hint binder value)
        (front.append (.live owner inputType answerType capture caller tail))
        snapshot.plan snapshot.forest output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
        registry actions (front.append (.live owner inputType answerType capture caller tail)).erase)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (resolved : scope.resolve binder = some owner) (isValue : value.erase.IsValue) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let after : SourceAnnotatedRuntime.Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨.resume hint binder value, scope,
        front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row bound stored.resume evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Resumed owner snapshot nextSnapshot ∧
      (∀ {Payload : SourceBoundSnapshots.RecordFamily.{0} (ScopedTyping.resourceWorld issued)}
        (records : snapshot.pending.Records Payload),
        ∃ nextRecords : nextSnapshot.pending.Records Payload,
          SourceBoundSnapshots.RecordResumption owner Payload records nextRecords) ∧
      ∃ source : Retained (ScopedTyping.resourceWorld issued) nextSnapshot.forest .nil,
        source.Valid [] actions (OwnerPhaseTransitions.available (ownedTickets after.stack.erase)) ∧
        ofCapability source = nextSnapshot.pending ∧
      ∃ records : nextSnapshot.pending.Records (SourceBoundSnapshots.CodeRecord [] actions (OwnerPhaseTransitions.available (ownedTickets after.stack.erase))),
        SourceBoundSnapshots.Retained.Records.AtReceivers [] actions (OwnerPhaseTransitions.available (ownedTickets after.stack.erase)) records .nil := by
  obtain ⟨usage, history, source, retained⟩ := initial
  have previous := run.current
  simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
    SourceAnnotatedCode.Term.erase, SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] at previous
  have closed := (ContinuationBounds.resume_operand_bound (environment := fun _ => .unknown)
    resolved (DeclaredReturnAdmission.ports previous.source) isValue).1
  obtain ⟨remaining, nextSnapshot, next, accounting, moved, activated, ready, kept, covered⟩ :=
    SourceAnnotatedRuntimeState.AtPackets.resume_use_snapshot laws project snapshot original cut before record
      source resolved closed
  obtain ⟨runtimeRemaining, step, current, runtimeAccounting⟩ := DeclaredExecution.resume_preserves previous resolved isValue
  have raw : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩)
      (SourceAnnotatedRuntime.Configuration.erase ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩)
      [] [.ticket owner] := by
    simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using
      RawStep.resume binder owner scope caller inputType answerType front.erase capture.erase tail.erase value.erase closed resolved
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using previous.ledger.2
  have joined := assemble_entry_atPackets run.coherent run.current raw freshOwners
    (by simpa only [ScopedPortJoint.advanceState, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using current.names.unique)
    (by simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using step.checks)
    usage history run.annotationHistory retained
    (by simpa only [ScopedActionUsage.advance, List.append_nil] using next)
    (by simpa only [ScopedPortJoint.advanceState, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using current.results)
    rfl (by simp)
  refine ⟨remaining, nextSnapshot, ?_, joined, accounting, moved,
    (fun records => moved.carry_records records), activated, ready, kept, covered⟩
  simpa only [SourceAnnotatedRuntime.advanceState, ScopedPortJoint.advanceState, SourceAnnotatedRuntime.NamedState.erase,
    SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
    SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using step

/-- Disposal activates checked closing source at the actual successor and
moves every original record through the exact callback filter. Runtime ledger,
completion and access preservation reuse the established assembly. -/
theorem AtPackets.discard_use_step {actions : Syntax.UsageTickets}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families (front.append (.live owner input answer capture caller tail))}
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification [])
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts [] required plans → nested.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (original : Context (ScopedTyping.resourceWorld issued) owner [] actions
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner input answer capture caller tail)).erase))
      base baseFront saved waiting)
    (cut : OwnerCut owner sourceWhole sourceFront saved waiting)
    (before : Interfaces (ScopedTyping.resourceWorld issued) sourceFront)
    {bounds : SourcePlanBounds.Annotation (ScopedTyping.resourceWorld issued) (.invoke (key := ⟨owner, .dispose⟩))}
    (sourceRecord : UseAlignedBody resumeRequired closeRequired original cut before bounds snapshot.pending)
    (initial : ConfigurationUsage policy actions
        (SourceAnnotatedRuntime.Configuration.erase ⟨.discard hint binder, scope,
          front.append (.live owner input answer capture caller tail)⟩) ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope (.discard hint binder)
        (front.append (.live owner input answer capture caller tail))
        snapshot.plan snapshot.forest output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
        registry actions (front.append (.live owner input answer capture caller tail)).erase)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored evidence)
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
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row resultBound (stored.discard scope identity annotatedPlan) evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot ∧
      (∀ {Payload : SourceBoundSnapshots.RecordFamily.{0} (ScopedTyping.resourceWorld issued)}
        (records : snapshot.pending.Records Payload),
        ∃ nextRecords : nextSnapshot.pending.Records Payload,
          SourceBoundSnapshots.RecordDisposal owner Payload records nextRecords) ∧
      ∃ source : Retained (ScopedTyping.resourceWorld issued) nextSnapshot.forest .nil,
        source.Valid [] actions (OwnerPhaseTransitions.available (ownedTickets after.stack.erase)) ∧
        ofCapability source = nextSnapshot.pending ∧
      ∃ records : nextSnapshot.pending.Records (SourceBoundSnapshots.CodeRecord [] actions (OwnerPhaseTransitions.available (ownedTickets after.stack.erase))),
        SourceBoundSnapshots.Retained.Records.AtReceivers [] actions (OwnerPhaseTransitions.available (ownedTickets after.stack.erase)) records .nil := by
  obtain ⟨usage, history, source, retained⟩ := initial
  obtain ⟨_, _, _, admitted, _, _⟩ := DeclaredClosingInvariant.discard_progress run.atPlan.run.erase.erase.shared.prepared
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
  obtain ⟨restored, restoredStored, remaining, nextSnapshot, restoredSame, actual, successor, accounting, _,
    ⟨actualPlan, actualBuilt, exactRestored, packetsSame⟩, moved, activated, ready, kept, covered⟩ :=
    SourceAnnotatedRuntimeState.AtPackets.discard_use_snapshot laws project snapshot original cut before sourceRecord
      source contractKnown resolved built typed (closeId := identity)
  cases Option.some.inj (actualBuilt.symm.trans builtAnnotated)
  subst restored
  cases eq_of_heq packetsSame
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
  have joined := assemble_entry_atPackets (after := next) run.coherent run.current actualRaw freshOwners freshHandlers access
    ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ history run.annotationHistory retained
    (by simpa [next, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      ScopedTyping.resource_world_append, ScopedTyping.resourceWorld, ScopedActionUsage.advance] using successor)
    (by simpa [nextSame, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results)
    (by rw [nextSame]; rfl) (by simp)
  exact ⟨remaining, nextSnapshot, ⟨.event _ _ _ _ actualRaw freshOwners freshHandlers, access⟩,
    joined, accounting, moved, (fun records => moved.carry_records records), activated, ready, kept, covered⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.resume_use_step

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.discard_use_step
