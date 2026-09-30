import SourceAnnotatedStoredUseCapture
import SourceAnnotatedStoredCaptureAssembly
import SourceAnnotatedCodeRecords
import SourcePlanRequirementSites

/-! Full execution reconstructs original capture source from its own recorded
source/action witness and the admitted installed declaration packet. Canonical
bounds and independent capabilities feed the allocator and owner ledger; packet
admission is preserved and selected-clause AtUse remains explicit. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingStoredBounds (StackBounds HandlerBounds)
open SourceScheduledSavedPlans (Saved)

private theorem fresh_action_of_history
    (history : UsageRegistryHistory actions issued)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup) : actions owner = none := by
  cases known : actions owner with
  | none => rfl
  | some rights =>
    have used := (history owner).mp ⟨rights, known⟩
    exact False.elim ((List.nodup_append.mp freshOwners).2.2 (.ticket owner) used
      (.ticket owner) (by simp) rfl)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

omit admission certification [SourceScheduledChecks.DeclarationProjection admission certification] in
private theorem bounded_source_from_stack
    {stored : StackBounds families stack} {packet : HandlerBounds families handler}
    (admitted : stored.Admitted world required)
    (found : stored.handlerAt requested = some ⟨handler, packet⟩)
    (route : packet.admission = .bounded) :
    ∃ source : SourceConsumingClauseAnnotations.Declarations world packet.plans,
      SourceConsumingClauseAnnotations.Bounded packet.bounds source (required handler.erase) := by
  cases admitted.handlerAt found with
  | bounded _ source checked => exact ⟨source, checked⟩
  | inherited inherited _ => cases route.symm.trans inherited

variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

omit nested in
/-- The physical cut and current source checks determine the exact installed
packet's offered mode, saved/waiting plan cut and selected clause body. This
reuses source splitting and ordered lookup; no clause-use check is assumed. -/
theorem AtPackets.capture_plan
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (stored : StackBounds families whole) (packet : HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code) :
    ∃ offered modes, lookup operation (tables handler.erase) = some offered ∧
      SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes ∧
    ∃ savedScope waitingScope, ∃ savedHints : Hints savedScope, ∃ waitingHints : Hints waitingScope,
    ∃ saved : Forest savedHints, ∃ waiting : Forest waitingHints,
      SourceScheduledNeutral.Cut requested operation offered modes snapshot.forest saved waiting ∧
    ∃ family : Nat → SourceDependencyAnnotations.Dependencies, ∃ bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner),
      SourcePlannedRecipeDeclarations.Selected operation savedScope.held packet.plans parameter binder code.erase bodies := by
  rcases snapshot with ⟨dependencies, plan, currentBounds, receiving, hints, forest, bounds⟩
  obtain ⟨actions, _, _, state, _⟩ := run.actions
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    have request : SourceScheduledChecks.Local [] actions
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) (ScopedTyping.resourceWorld issued)
        (.request (effect := requested) (operation := operation)) forest := by
      generalize encoded : Instantiation.freezeEffect requested = syntaxEffect at current
      generalize signatureSame : SourcePlanSignatures.signature plan = currentSignature at current
      cases current with
      | checked checkedHint metadata node => cases node with
        | perform operationKnown admitted operandSource formed =>
          cases freeze_effect_injective encoded
          cases plan with
          | sequence operandPlan requestPlan =>
            cases requestPlan
            cases contextual with
            | sequence operandCheck requestCheck => exact requestCheck
    obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
      capScope, tailScope, savedHints, waitingHints, saved, waiting,
      actualPacket, actualAt, annotation, frame, savedSource, waitingSource,
      sameScope, sameHints, sameForest, sameDemand, sameRecords, selection, evaluation⟩ :=
      SourceAnnotatedStoredTyping.capture_segments cut pending
    have packetSame := stored.handlerAt_unique actualAt packetAt
    cases packetSame
    have found : ∃ offered, lookup operation (tables handler.erase) = some offered := by
      cases frame.forget with
      | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
        obtain ⟨offered, found, _⟩ := SourceTemplates.selected_clause_mode selected.erase modes
        exact ⟨offered, found⟩
    obtain ⟨offered, found⟩ := found
    have guard := SourceDependencyCapture.check_capture_iff.mp
      (SourceDependencySchemes.checked_request request.erase.erase)
    cases declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) with
    | none =>
      have missing : SourceDependencyCapture.select requested operation receiving = none := by
        simpa only [SourceDependencyCapture.chosen, found, declared] using selection operation
      cases guard with
      | builtin actual | handler actual => rw [missing] at actual; cases actual
    | some modes =>
      have located : SourceDependencyCapture.select requested operation receiving =
          some (.handler capScope tailScope offered modes) := by
        simpa only [SourceDependencyCapture.chosen, found, declared] using selection operation
      cases guard with
      | builtin actual => cases Option.some.inj (located.symm.trans actual)
      | handler actual permission row body closing =>
        cases Option.some.inj (located.symm.trans actual)
        obtain ⟨insideHints, outsideHints, selectedCut⟩ := SourcePlannedCuts.of_lookup hints located
        obtain ⟨inside, outside, plannedCut⟩ := SourceScheduledNeutral.of_cut selectedCut forest
        obtain ⟨bodies, chosen⟩ := SourcePlannedRecipeDeclarations.selected_of_lookup
          (declarations := packet.plans) selected.erase (by rw [declared]; exact body)
        exact ⟨offered, modes, found, rfl, _, _, _, _, inside, outside, plannedCut, _, bodies, chosen⟩

/-- Reconstruct original capture/closing source from the runtime state and use
its canonical snapshot in the existing allocator. Capture assembly reuses the
resource support, freshness, ownership, completion, name and access proofs.
The admitted packet supplies the declaration and selected body. The event port lookup fixes the concrete operational successor. The result
returns its actual successor snapshot, its admitted bounds and stored packets,
and its capture relation to the normalized incoming snapshot. Selected-clause
AtUse remains explicit; no
separate source witness or origin equation is an input. -/
theorem AtPackets.capture_use_step
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification [])
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued)) (snapshotAdmitted : snapshot.Admitted)
    (stored : StackBounds families whole)
    (packet : HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (ports : operations.erase.erase.ports requested operation = some (argumentPort, inputPort))
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts [] required plans → nested.accepts required plans)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (boundedRoute : packet.admission = .bounded)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (plannedCut : SourceScheduledNeutral.Cut requested operation offered modes snapshot.forest saved waiting)
    (plannedSelected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held packet.plans parameter binder code.erase bodies) :
    let admittedSource := bounded_source_from_stack storedAdmitted packetAt boundedRoute
    let declarationSource := Classical.choose admittedSource
    let selectedSource := declarationSource.selected_source (owner := owner) plannedSelected
    let body := Classical.choose selectedSource
    let actions := Classical.choose run.actions
    let initial := Classical.choose_spec run.actions
    let freshAction := fresh_action_of_history initial.2.1 freshOwners
    let capabilities := initial.2.2.1.capture_capabilities cut selected found declared plannedCut
    let permits := capabilities.1
    let absent := initial.2.2.1.fresh_action_absent initial.1 freshAction
    let reconstruction := SourceAnnotatedRuntimeState.AtPackets.canonical_capture_source
      project snapshot initial.2.2.1 plannedCut permits
    let source := Classical.choose reconstruction
    let captureSource := Classical.choice (Classical.choose_spec reconstruction).2
    let context := SourceConsumingCleanupAdmission.Context.of_request laws project plannedCut source
      code.erase.requiredActions captureSource permits freshAction absent
    SourceConsumingCleanupAdmission.AtUse [] (actions.insert owner code.erase.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
      context body .nil →
    let after : SourceAnnotatedRuntime.Configuration :=
      ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort inputPort) handler.answer capture handler.scope tail⟩
    ∃ useContract : SourceConsumingClauseAnnotations.Bounds,
      packet.bounds.lookup operation savedScope.held = some useContract ∧
    ∃ (contract : SourcePlannedTyping.Contract) (record : CoherentSourceTypes.Owners.Record)
      (captured : Saved)
      (nextDemand : List Nat) (nextRow : Footprint),
      record.annotation = contract.erase.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
            issued, completed⟩, activations⟩ after.erase [.ticket owner] []) ∧
      (∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer handler.scope) ∧
      AtPackets operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow resultBound nextStored evidence ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy (contracts.insert owner contract) tables families required
        (actions.insert owner code.erase.requiredActions) (annotations.insert owner captured) (ScopedTyping.resourceWorld issued)
        [] [] after.scope after.expression after.stack nextSnapshot.plan
        nextSnapshot.forest output nextDemand nextRow nextStored evidence ∧
      SourceBoundSnapshots.CapturedUseBounds snapshot.normalize context useContract.resume useContract.close nextSnapshot.plan nextSnapshot.forest ∧
      SourceBoundSnapshots.Captured owner snapshot.normalize nextSnapshot ∧ nextSnapshot.Admitted ∧
      nextStored.Admitted (ScopedTyping.resourceWorld (issued ++ [Owner.ticket owner])) required) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  let admittedSource := bounded_source_from_stack storedAdmitted packetAt boundedRoute
  let declarationSource := Classical.choose admittedSource
  have declarationBounded := Classical.choose_spec admittedSource
  let selectedBody := declarationSource.selected_source (owner := owner) plannedSelected
  let body := Classical.choose selectedBody
  have selectedSource := Classical.choose_spec selectedBody
  let actions := Classical.choose run.actions
  have initial := Classical.choose_spec run.actions
  have freshAction := fresh_action_of_history initial.2.1 freshOwners
  let capabilities := initial.2.2.1.capture_capabilities cut selected found declared plannedCut
  let permits := capabilities.1
  have supplied := capabilities.2
  have absent := initial.2.2.1.fresh_action_absent initial.1 freshAction
  let reconstruction := SourceAnnotatedRuntimeState.AtPackets.canonical_capture_source
    project snapshot initial.2.2.1 plannedCut permits
  let source := Classical.choose reconstruction
  let captureSource := Classical.choice (Classical.choose_spec reconstruction).2
  have aligned := (Classical.choose_spec reconstruction).1
  dsimp only
  intro atUse
  obtain ⟨usage, history, state, retained⟩ := initial
  have supported := SourceDependencyState.capture_resource_support cut.erase run.current.support.control (ledger_unique_live run.current.ledger)
  have freshAnnotation : annotations owner = none := by
    cases known : annotations owner with
    | none => rfl
    | some captured =>
        have used := run.annotationHistory owner captured known
        exact False.elim ((List.nodup_append.mp freshOwners).2.2 (.ticket owner) used
          (.ticket owner) (by simp) rfl)
  have fresh : registry owner = none := by
    have absent := ScopedPortJoint.registry_fresh run.current.registry freshOwners
    cases known : registry owner <;>
      simp_all [CoherentSourceTypes.Owners.Registry.runtime, CallableJoint.Registry.joint]
  have freshContract : contracts owner = none := by
    have erased : contracts.erase.erase owner = none := by
      rw [run.coherent]
      simp [CoherentSourceTypes.Owners.Registry.contracts, fresh]
    simpa only [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, Option.map_eq_none_iff] using erased
  obtain ⟨useContract, contractAt, contract, captured, waiting, after, nextDemand, nextRow,
    raw, ⟨dependencies, nextPlan, nextStored, packetsSame, nextSource, payload⟩,
    balance, included, owners, shape, sourceInput⟩ :=
    SourceAnnotatedStoredRuntimeCapture.capture_from_use_source_retaining laws snapshot.normalize snapshotAdmitted.normalize
      stored packet packetAt state cut isValue selected found freshContract freshAction freshAnnotation supported
      declared project declarationSource declarationBounded plannedCut plannedSelected selectedSource
      source captureSource permits supplied absent atUse aligned
  obtain ⟨record, annotation, step, next⟩ :=
    run.assemble_capture usage history state retained cut isValue selected found freshOwners raw nextSource shape sourceInput
  have packetsAdmitted : nextStored.Admitted
      (ScopedTyping.resourceWorld (issued ++ [Owner.ticket owner])) required := by
    cases shape
    have same := eq_of_heq packetsSame
    rw [same]
    simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld]
      using (storedAdmitted.capture cut (owner := owner)
        (input := ScopedPorts.embedPort contract.input.erase.erase.port) (answer := handler.answer) (caller := handler.scope))
  obtain ⟨current, pending, ownerCut, bodyRecord, moved, admitted, retainedRecords, savedBounds,
    pendingSame, resumptionSame, closingSame⟩ := payload
  let nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, nextPlan, current, _, _, .live (owner := owner) captured.forest waiting.forest, pending⟩
  have portKnown := CoherentSourceTypes.port_lookup
    (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase sourceInput.choose_spec))
  have inputSame := (Prod.mk.inj (Option.some.inj (portKnown.symm.trans ports))).2
  rw [inputSame] at shape
  subst after
  exact ⟨useContract, contractAt, contract, record, captured, nextDemand, nextRow,
    annotation, step, ⟨nextSnapshot, nextStored, packetsSame, next, nextSource,
      ⟨current, pending, ownerCut, bodyRecord, moved, admitted, retainedRecords, savedBounds,
        pendingSame, resumptionSame, closingSame⟩, moved, admitted, packetsAdmitted⟩,
    balance, included, owners, sourceInput⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.capture_use_step

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.capture_plan
