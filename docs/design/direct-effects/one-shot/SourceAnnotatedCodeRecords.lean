import SourceCodeRecordReassembly
import SourceScheduledNormalizedRechecking
import SourceAnnotatedStoredState
import SourceCodeCoverage
import SourceAnnotatedStoredComputation
import SourceAnnotatedStoredFocus
import SourceAnnotatedStoredReturns
import SourceAnnotatedStoredCuts
import SourceAnnotatedStoredUseConsumption

/-! Recover capability source from the runtime's own structural checks.
Canonical code coverage and original capture/closing source require no input
source witnesses; exact unnormalized recovery can reuse positioned records. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExpressions ScopedExecution
open SourceBoundSnapshots (CodeRecord)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceBoundSnapshots.Retained.Records (AtReceivers)

variable [SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationPolicy]
  [SourcePlannedChecks.DeclarationPolicy]

/-- Canonical source coverage is derived from the runtime's existing structural
checks. No positioned code records or separate validity witnesses are inputs.
This is coverage at the same receiver, not selected-clause AtUse admission. -/
theorem AtPackets.canonical_code_coverage
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourceScheduledChecks.DeclarationPolicy.accepts outward required plans →
        SourceScheduledCapabilityAnnotations.DeclarationPolicy.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code stack snapshot.plan snapshot.forest output demand row stored evidence) :
    Nonempty (snapshot.normalize.CodeCoverage outward actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase))) := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    obtain ⟨source, ready, origin⟩ :=
      (SourceScheduledCapabilityAnnotations.source_of_schedule_all outward actions project).1
        _ world _ _ contextual snapshot.current
    obtain ⟨retained, retainedReady, retainedOrigin⟩ :=
      (SourceScheduledCapabilityAnnotations.source_of_schedule_all outward actions project).2
        _ world _ _ pending.forget.erase.pending snapshot.pending
    obtain ⟨records, covered⟩ := retained.code_records_at retainedReady retainedOrigin
    exact ⟨⟨source, ready, origin, records, covered⟩⟩

/-- At a request, the runtime state itself supplies the whole original source,
its canonical snapshot origin, and the original disposal-closing source.
No separate source, closing annotation or source/snapshot equation is assumed. -/
theorem AtPackets.canonical_capture_source
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourceScheduledChecks.DeclarationPolicy.accepts outward required plans →
        SourceScheduledCapabilityAnnotations.DeclarationPolicy.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.perform hint (Instantiation.freezeEffect effect) operation operand) stack
      snapshot.plan snapshot.forest output demand row stored evidence)
    {savedHints : SourceContextualHints.Hints savedScope} {waitingHints : SourceContextualHints.Hints waitingScope}
    {saved : SourceRetainedPlans.Forest savedHints} {waiting : SourceRetainedPlans.Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes snapshot.forest saved waiting)
    (permits : rights.dispose = true → offered.dispose = true) :
    ∃ source : SourceScheduledCapabilityAnnotations.Retained world snapshot.forest .nil,
      ofCapability source = snapshot.normalize.pending ∧
      Nonempty (SourceScheduledCapabilityAnnotations.CaptureSource outward actions
        (OwnerPhaseTransitions.available (ownedTickets stack.erase)) cut source rights) := by
  rcases snapshot with ⟨dependencies, plan, currentBounds, receiving, hints, forest, bounds⟩
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    generalize encoded : Instantiation.freezeEffect effect = syntaxEffect at current
    generalize signatureSame : SourcePlanSignatures.signature plan = currentSignature at current
    cases current with
    | checked checkedHint metadata node => cases node with
      | perform operationKnown admitted operandSource formed =>
        cases freeze_effect_injective encoded
        cases plan with
        | sequence operandPlan requestPlan =>
          cases requestPlan
          cases contextual with
          | sequence before requested =>
            exact SourceScheduledCapabilityAnnotations.CaptureSource.of_schedule project cut
              requested pending.forget.erase.pending bounds permits

theorem AtPackets.retained_source
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code stack snapshot.plan snapshot.forest output demand row stored evidence)
    (records : snapshot.pending.Records
      (CodeRecord outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase))))
    (covered : AtReceivers outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) records .nil) :
    ∃ source : SourceScheduledCapabilityAnnotations.Retained world snapshot.forest .nil,
      source.Valid outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) ∧
      ofCapability source = snapshot.pending := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      exact covered.source records pending.forget.erase.pending

end Ash.OneShot.SourceAnnotatedRuntimeState

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.retained_source
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.canonical_code_coverage
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.canonical_capture_source

namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExpressions ScopedExecution
open SourceBoundSnapshots (Snapshot)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The runtime step and its source coverage select the same actual child;
all pending and dormant records retain their existing values. -/
theorem AtPackets.ordinary_code_snapshot
    (snapshot : Snapshot world)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code stack snapshot.plan snapshot.forest output demand row stored evidence)
    (covered : snapshot.CodeCoverage outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)))
    (event : SourceAnnotatedCode.Reduction code scope nextCode nextScope) :
    ∃ next : Snapshot world, ∃ remaining nextRow,
      RawStep ⟨code.erase, scope, stack.erase⟩ ⟨nextCode.erase, nextScope, stack.erase⟩ [] [] ∧
      AtPackets operations policy contracts tables families required actions annotations world outward outside
        nextScope nextCode stack next.plan next.forest output remaining nextRow stored evidence ∧
      SourceBoundSnapshots.Computed event.rule snapshot next ∧ demand.Perm remaining ∧ nextRow.Sublist row ∧
      Nonempty (next.CodeCoverage outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase))) := by
  obtain ⟨next, remaining, nextRow, raw, nextState, moved, accounting, included⟩ :=
    SourceAnnotatedStoredComputation.ordinary_snapshot snapshot state event
  exact ⟨next, remaining, nextRow, raw, nextState, moved, accounting, included, covered.computed moved⟩

/-- Plain return removes the exact queued record and activates its code at
the successor. The phase map is unchanged because plain frames own no tickets. -/
theorem AtPackets.plug_code_snapshot
    (snapshot : Snapshot world)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope value (.push (.plain plain) tail) snapshot.plan snapshot.forest output demand row (.push .plain stored) evidence)
    (covered : snapshot.CodeCoverage outward actions
      (OwnerPhaseTransitions.available (ownedTickets (SourceAnnotatedRuntime.Stack.push (.plain plain) tail).erase)))
    (closed : ClosedValue value.erase) :
    ∃ next : Snapshot world,
      RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨value, scope, .push (.plain plain) tail⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨plain.context.plug value, plain.scope, tail⟩) [] [] ∧
      AtPackets operations policy contracts tables families required actions annotations world outward outside
        plain.scope (plain.context.plug value) tail next.plan next.forest output demand row stored evidence ∧
      SourceBoundSnapshots.Returned plain.context snapshot next ∧
      Nonempty (next.CodeCoverage outward actions (OwnerPhaseTransitions.available (ownedTickets tail.erase))) := by
  obtain ⟨next, raw, nextState, moved⟩ := SourceAnnotatedStoredReturns.plug_snapshot snapshot state closed
  exact ⟨next, raw, nextState, moved, covered.returned moved⟩

variable [SourceScheduledChecks.DeclarationProjection admission certification]

/-- All expression focus forms reuse their existing signature split and
runtime preservation; the source split supplies the complete successor records. -/
theorem AtPackets.focus_code_snapshot
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → nested.accepts required plans)
    {plain : SourceAnnotatedRuntime.Plain}
    (snapshot : Snapshot world)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      plain.scope whole stack snapshot.plan snapshot.forest output demand row stored evidence)
    (covered : snapshot.CodeCoverage outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)))
    (position : SourceAnnotatedCode.Focus whole child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ next : Snapshot world,
      RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨whole, plain.scope, stack⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨child, plain.scope, .push (.plain plain) stack⟩) [] [] ∧
      AtPackets operations policy contracts tables families required actions annotations world outward outside
        plain.scope child (.push (.plain plain) stack) next.plan next.forest output demand row (.push .plain stored) evidence ∧
      SourceBoundSnapshots.Focused snapshot next ∧
      Nonempty (next.CodeCoverage outward actions
        (OwnerPhaseTransitions.available (ownedTickets (SourceAnnotatedRuntime.Stack.push (.plain plain) stack).erase))) := by
  obtain ⟨_, _, childPlan, restPlan, childBounds, restBounds, raw, nextState, selected⟩ :=
    SourceAnnotatedStoredFocus.focus_snapshot snapshot state position guard
  have moved := SourceBoundSnapshots.Focused.step snapshot childBounds restBounds selected
  exact ⟨snapshot.focus childPlan restPlan childBounds restBounds, raw, nextState, moved,
    covered.focused laws project moved⟩

end Ash.OneShot.SourceAnnotatedRuntimeState

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.ordinary_code_snapshot
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.plug_code_snapshot
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.focus_code_snapshot

namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Source ownership is realized by the same runtime stack. Reuse its live
inventory and action registration to exclude a fresh owner from source scope. -/
theorem AtPackets.fresh_action_absent {hints : Hints receiving} {forest : Forest hints}
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code stack plan forest output demand row stored evidence)
    (usage : ConfigurationUsage policy actions ⟨code.erase, scope, stack.erase⟩)
    (fresh : actions owner = none) : owner ∉ SourceDependencyOwners.owners receiving := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    intro member
    have live : owner ∈ stack.erase.erase.liveTickets := by
      simpa only [SourceDependencyOwners.realized_owners pending.forget.erase.source.source.matches.realizes] using member
    obtain ⟨_, _, _, control, _⟩ := usage
    obtain ⟨rights, known⟩ := owned_tickets_registered control ((recursive_live_tickets_sublist stack.erase).subset live)
    rw [fresh] at known
    cases known

/-- The actual stored handler supplies both disposal permission for its
selected clause and its waiting-scope requirements. Selection uniqueness aligns
the physical cut with the source cut; no new capability judgment is assumed. -/
theorem AtPackets.capture_capabilities
    {hints : Hints receiving} {forest : Forest hints}
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code stack plan forest output demand row stored evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested stack capture tail handler)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder body)
    (found : lookup operation (tables handler.erase) = some offered)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (plannedCut : SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting) :
    (body.erase.requiredActions.dispose = true → offered.dispose = true) ∧
      SourceContextualHints.checkRequirements waitingScope (required handler.erase) = true := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
      capScope, tailScope, capturedHints, tailHints, savedForest, waitingForest, packet, packetAt,
      annotation, frame, savedSource, waitingSource, scopeSame, hintsSame, forestSame,
      demandSame, recordsSame, selection, evaluation⟩ :=
      SourceAnnotatedStoredTyping.capture_segments cut pending
    have actual : SourceDependencyCapture.select requested operation receiving =
        some (.handler capScope tailScope offered modes) := by
      simpa only [SourceDependencyCapture.chosen, found, declared] using selection operation
    cases Option.some.inj (plannedCut.erase.lookup.symm.trans actual)
    cases frame.forget with
    | handler scopeKnown annotation clauses coverage unique declarations recipes supplied capabilities clauseModes =>
      obtain ⟨actual, actualFound, permission⟩ := SourceTemplates.selected_clause_mode selected.erase clauseModes
      cases Option.some.inj (found.symm.trans actualFound)
      refine ⟨permission, ?_⟩
      simpa only [SourceDependencyProjection.scope_append_nil] using supplied
end Ash.OneShot.SourceAnnotatedRuntimeState
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.fresh_action_absent
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.capture_capabilities
