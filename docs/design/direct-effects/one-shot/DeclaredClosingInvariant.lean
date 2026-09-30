import DeclaredDisposalAdmissionGap
import ScopedActionInterfaces

/-! Retain structural closing certificates and declared-request typing on the
same scoped machine and coherent registry as hereditary source checking.
Certificate coverage ranges over the existing inductive capture positions in
the current finite control forest. It contains no future-execution premise.
Coverage follows the selected clause's independently checked action bound,
retained through execution on the same owner identities. A larger runtime
permission grant does not create an unused disposal obligation.
-/
namespace Ash.OneShot.DeclaredClosingInvariant
open Instantiation ScopedExpressions ScopedExecution CoherentSourceTypes
open SourceTemplates (CapturedIn)
open ScopedTyping (resourceWorld)

structure Certificate (signature : ScopedPorts.Signature) (world : List Nat)
    (record : Owners.Record) (capture : Stack) where
  plan : List CloseEntry
  built : makePlan capture = some plan
  typed : ScopedPorts.PlanTyped signature world record.annotation.closeEffects plan
  closing : Admission.OpenCloses capture.erase .nil .nil (Admission.outsideResources capture.erase)
    record.annotation.closeEffects (plan.map CloseEntry.erase)
  internal : InternalUses capture.erase.liveTickets capture.erase.pending

def Retained (signature : ScopedPorts.Signature) (world : List Nat) (registry : Owners.Registry)
    (actions : Syntax.UsageTickets) (stack : Stack) : Prop :=
  ∀ owner capture, CapturedIn owner capture stack →
    ∃ record rights, registry owner = some record ∧ actions owner = some rights ∧
      (rights.dispose = true → Nonempty (Certificate signature world record capture))

def certificate_world_weaken (checked : Certificate signature world record capture)
    (larger : world ⊆ next) : Certificate signature next record capture :=
  ⟨checked.plan, checked.built, ScopedPorts.plan_typed_world_weaken checked.typed larger,
    checked.closing, checked.internal⟩

theorem retained_empty : Retained signature world registry actions .nil := by
  intro owner capture located
  cases located

/-- New certificates are checked only at the newly allocated live boundary.
All previously retained certificates are transported by capture provenance. -/
inductive Allocation (signature : ScopedPorts.Signature) (world : List Nat) (registry : Owners.Registry) (actions : Syntax.UsageTickets) :
    List Owner → Stack → Prop where
  | none (absent : ∀ owner, Owner.ticket owner ∉ created) : Allocation signature world registry actions created stack
  | capture (known : registry owner = some record) (actionKnown : actions owner = some rights)
      (checked : rights.dispose = true → Nonempty (Certificate signature world record capture)) :
      Allocation signature world registry actions [.ticket owner] (.live owner input answer capture caller tail)

/-- The allocation guard is exactly the selected body's action requirement.
The runtime record can grant additional permissions without changing it. -/
theorem capture_allocation {operand body : Code}
    (known : registry owner = some record) (isValue : operand.IsValue)
    (checked : body.requiredActions.dispose = true → Nonempty (Certificate signature world record capture)) :
    Allocation signature world registry
      (ScopedActionUsage.advance actions
        ⟨body.subst parameter operand, .ticket binder owner, .live owner input answer capture caller tail⟩ [.ticket owner])
      [.ticket owner] (.live owner input answer capture caller tail) := by
  apply Allocation.capture known (rights := body.requiredActions) _ checked
  simp [ScopedActionUsage.advance, Syntax.UsageTickets.insert,
    Code.substitution_required_actions body parameter isValue]

/-- No certificate is required for a selected clause that cannot dispose.
There is deliberately no premise denying disposal in the runtime policy. -/
theorem resume_only_capture_allocation {operand body : Code}
    (known : registry owner = some record) (isValue : operand.IsValue)
    (noDispose : body.requiredActions.dispose = false) :
    Allocation signature world registry
      (ScopedActionUsage.advance actions
        ⟨body.subst parameter operand, .ticket binder owner, .live owner input answer capture caller tail⟩ [.ticket owner])
      [.ticket owner] (.live owner input answer capture caller tail) := by
  apply capture_allocation known isValue
  intro impossible
  simp [noDispose] at impossible

theorem allocation_at_capture
    (allocation : Allocation signature world registry actions created stack)
    (unique : (ownedTickets stack).Nodup) (fresh : Owner.ticket owner ∈ created)
    (located : CapturedIn owner capture stack) :
    ∃ record rights, registry owner = some record ∧ actions owner = some rights ∧
      (rights.dispose = true → Nonempty (Certificate signature world record capture)) := by
  cases allocation with
  | none absent => exact False.elim (absent owner fresh)
  | capture known actionKnown checked =>
      have sameOwner := Owner.ticket.inj (List.mem_singleton.mp fresh)
      subst owner
      have sameCapture := SourceTemplates.captured_in_unique unique located .here
      subst capture
      exact ⟨_, _, known, actionKnown, checked⟩

/-- Reuse the all-transition provenance theorem. No second induction over
stack forms, cleanup plans or execution transitions is needed. -/
theorem raw_step_preserves_retained
    (step : RawStep before after created discharged)
    (retained : Retained signature world registry actions before.stack)
    (extension : ∀ owner record, registry owner = some record → nextRegistry owner = some record)
    (actionExtension : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld)
    (allocation : Allocation signature nextWorld nextRegistry nextActions created after.stack)
    (unique : (ownedTickets after.stack).Nodup) :
    Retained signature nextWorld nextRegistry nextActions after.stack := by
  intro owner capture located
  by_cases fresh : Owner.ticket owner ∈ created
  · exact allocation_at_capture allocation unique fresh located
  · obtain ⟨record, rights, known, actionKnown, checked⟩ := retained owner capture (SavedCaptureIdentity.raw_step_origin step fresh located)
    refine ⟨record, rights, extension owner record known, actionExtension owner rights actionKnown, ?_⟩
    intro permitted
    obtain ⟨certificate⟩ := checked permitted
    exact ⟨certificate_world_weaken certificate larger⟩

structure Prepared (operations : Operations) (declarations : DeclarationRegistry)
    (policy : Syntax.TicketPolicy) (registry : Owners.Registry) (tables : CallableProtectionFrames.Tables)
    (state : NamedState) (output : Value) (demand : List Nat)
    (row : ProtectionContracts.Footprint) (bound : CallableContracts.Contract) : Prop where
  current : DeclaredExecution.Valid operations declarations policy registry tables [] [] state output demand row bound
  actions : ∃ tickets, ConfigurationUsage policy tickets state.execution.configuration ∧
    UsageRegistryHistory tickets state.execution.issued ∧
    ScopedActionInterfaces.ConfigurationConnected operations.ports registry.contracts.ports tickets
      (resourceWorld state.execution.issued) state.execution.configuration output.port [] ∧
    Retained operations.ports (resourceWorld state.execution.issued) registry tickets state.execution.configuration.stack

/-- The existing initial proof already establishes declared-request typing.
The empty control forest has no closing-certificate obligations. Future capture
admission remains to be derived and is not assumed here. -/
theorem initial_state
    (source : DeclaredSources.Expression operations policy (fun _ => none) [] [] .none Environment.empty
      code output demand requirements)
    (checked : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : ProtectionContracts.checkFootprint [] row = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (support : decide (Syntax.resourceDependencies code.dependencies = []) = true) :
    demand = [] ∧ Prepared operations declarations policy (fun _ => none) tables
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ output [] row bound := by
  obtain ⟨empty, source, runtime⟩ := DeclaredCompletionAdmission.initial_state
    (tables := tables) source checked accepted result signature support
  have history := ScopedPortJoint.usage_history_iff.mpr runtime.joint.registry
  refine ⟨empty, ?_, ⟨_, runtime.joint.usage, history, ?_, retained_empty⟩⟩
  · exact ⟨signature, source, runtime.results, runtime.joint.ledger, runtime.joint.names,
      runtime.joint.support, runtime.joint.usage, runtime.joint.registry, runtime.joint.closed⟩
  · rw [signature]
    apply ScopedActionInterfaces.configuration_from_scoped runtime.joint.effects
    intro owner contract known
    simp [CallableJoint.Registry.joint, ScopedPortJoint.Registry.effects] at known

private theorem discard_preserves_requests
    (raw : RawStep before after [.close identity] [.ticket owner])
    (typed : ScopedActionInterfaces.ConfigurationConnected signature registry.contracts.ports actions world before result [])
    (usage : ConfigurationUsage policy actions before)
    (retained : Retained signature world registry actions before.stack)
    (registered : ∀ owner contract, registry.contracts.ports owner = some contract → ∃ rights, actions owner = some rights) :
    ScopedActionInterfaces.ConfigurationConnected signature registry.contracts.ports actions world after result [] := by
  cases raw with
  | discard binder owner identity scope caller input answer front capture tail plan resolved built =>
      obtain ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ := usage
      obtain ⟨actualOwner, rights, actionKnown, actualResolved, demandSame, permitted⟩ :=
        ScopedActionUsage.discard_requires_action code
      have sameOwner := Option.some.inj (actualResolved.symm.trans resolved)
      subst actualOwner
      obtain ⟨record, savedRights, known, savedKnown, checked⟩ := retained owner capture (RecursiveRecords.located_below front .here)
      have sameRights := Option.some.inj (actionKnown.symm.trans savedKnown)
      obtain ⟨certificate⟩ := checked (sameRights ▸ permitted)
      have samePlan := Option.some.inj (certificate.built.symm.trans built)
      have knownContract : registry.contracts.ports owner = some record.annotation.ports :=
        Owners.ports_lookup (by simp [Owners.Registry.contracts, known])
      exact ScopedActionInterfaces.discard_preserves_configuration knownContract resolved typed built
        (samePlan ▸ certificate.typed) registered

/-- Join the already constructed source/runtime successor with preservation
of the additional request and closing-certificate fields. -/
theorem discard_preserves_prepared
    (before : Prepared operations declarations policy registry tables
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (step : NamedAccessStep []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after)
    (current : DeclaredExecution.Valid operations declarations policy registry tables [] [] after output nextDemand nextRow bound) :
    Prepared operations declarations policy registry tables after output nextDemand nextRow bound := by
  obtain ⟨actions, usage, history, requests, closing⟩ := before.actions
  obtain ⟨nextActions, nextUsage, nextHistory, actionExtension⟩ :=
    ScopedActionUsage.named_step_preserves step usage history
  cases step.execution with
  | event next created discharged raw freshOwners freshHandlers =>
      obtain ⟨owner, identity, remaining, unitSame, scopeSame, source, demandSame, createdSame, dischargedSame, trace⟩ :=
        DeclaredSourceDisposal.discard_step_preserves before.current.source raw
      subst created
      subst discharged
      have requests := discard_preserves_requests raw requests usage closing
        (ScopedActionInterfaces.registered_actions before.current.registry history)
      have unique : (ownedTickets next.stack).Nodup := by
        cases current.source with
        | checked _ _ unique _ _ => exact unique
      refine ⟨current, ⟨nextActions, nextUsage, nextHistory, ?_, ?_⟩⟩
      · simpa [ScopedTyping.resource_world_append, resourceWorld] using
          (ScopedActionInterfaces.configuration_action_extension requests actionExtension)
      · apply raw_step_preserves_retained raw closing (fun _ _ known => known) actionExtension _ (.none (by simp)) unique
        rw [ScopedTyping.resource_world_append]
        exact List.subset_append_left _ _

/-- Current structural evidence constructs disposal and preserves the entire
strengthened state. No earlier state, caller-run history, supplied plan, fresh
identity or successful access check is an extra premise. -/
theorem discard_progress
    (admitted : Prepared operations declarations policy registry tables
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound) :
    ∃ after owner remaining,
      NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Prepared operations declarations policy registry tables after output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨actions, usage, history, requests, closing⟩ := admitted.actions
  obtain ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ := usage
  obtain ⟨owner, rights, actionKnown, resolved, demandSame, permitted⟩ :=
    ScopedActionUsage.discard_requires_action code
  have present : owner ∈ activeTickets stack := accessible (demandSame ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := ScopedPortJoint.active_ticket_has_boundary present
  subst stack
  have located : CapturedIn owner capture (front.append (.live owner input answer capture caller tail)) :=
    RecursiveRecords.located_below front .here
  obtain ⟨record, savedRights, known, savedKnown, checked⟩ := closing owner capture located
  have sameRights := Option.some.inj (actionKnown.symm.trans savedKnown)
  obtain ⟨certificate⟩ := checked (sameRights ▸ permitted)
  obtain ⟨currentType, effects, expression, ports, connected⟩ := requests
  have knownSource : registry.contracts owner = some record.annotation := by
    simp [Owners.Registry.contracts, known]
  have callerRequests := ScopedActionInterfaces.closing_requests (Owners.ports_lookup knownSource)
    actionKnown permitted connected
  obtain ⟨identity, after, remaining, step, current, demandSame⟩ :=
    DeclaredExecution.discard_from_retained_requests admitted.current admitted.current (.refl _) located
      certificate.built certificate.closing certificate.internal resolved callerRequests
  exact ⟨_, owner, remaining, step, discard_preserves_prepared admitted step current, demandSame⟩

/-- Structural closing evidence still excludes the disposal counterexample,
even though unused effect interfaces no longer constrain resumption. -/
theorem excludes_disposal_gap :
    ¬ Prepared DeclaredDisposalAdmissionGap.operations DeclaredDisposalAdmissionGap.declarations
      DeclaredDisposalAdmissionGap.policy DeclaredDisposalAdmissionGap.registry DeclaredDisposalAdmissionGap.tables
      DeclaredDisposalAdmissionGap.state .unit [0] [] (.storage []) := by
  intro admitted
  obtain ⟨after, owner, remaining, step, next, accounting⟩ := discard_progress admitted
  exact DeclaredDisposalAdmissionGap.no_admitted_step ⟨after, step⟩

theorem value_preserves_prepared
    (before : Prepared operations declarations policy registry tables state output demand row bound)
    (isValue : state.execution.configuration.expression.IsValue)
    (step : NamedAccessStep [] state after)
    (current : DeclaredExecution.Valid operations declarations policy registry tables [] [] after output nextDemand nextRow bound) :
    Prepared operations declarations policy registry tables after output nextDemand nextRow bound := by
  obtain ⟨actions, usage, history, requests, closing⟩ := before.actions
  obtain ⟨input, effects, typed, ports, connected⟩ := requests
  have closed := ScopedPorts.typed_value_closed (ScopedPorts.effect_value_closed_type typed isValue) isValue
  obtain ⟨nextActions, nextUsage, nextHistory, actionExtension⟩ :=
    ScopedActionUsage.named_step_preserves step usage history
  cases step.execution with
  | event next created discharged raw freshOwners freshHandlers =>
      have requests := ScopedActionInterfaces.raw_value_preserves_configuration raw closed
        ⟨input, effects, typed, ports, connected⟩
      have unique : (ownedTickets next.stack).Nodup := by
        cases current.source with
        | checked _ _ unique _ _ => exact unique
      have larger : resourceWorld state.execution.issued ⊆ resourceWorld (state.execution.issued ++ created) := by
        rw [ScopedTyping.resource_world_append]
        exact List.subset_append_left _ _
      refine ⟨current, ⟨nextActions, nextUsage, nextHistory,
        ScopedActionInterfaces.configuration_action_extension
          (ScopedActionInterfaces.configuration_world_weaken requests larger) actionExtension, ?_⟩⟩
      apply raw_step_preserves_retained raw closing (fun _ _ known => known) actionExtension larger _ unique
      apply Allocation.none (ScopedPortPrepared.nonrequest_allocates_no_ticket raw ?_)
      intro requested operation operand same
      rw [same] at isValue
      cases isValue

/-- All eight returned-value transitions retain the stronger invariant by
reusing their source/runtime progress and generic effect-preservation proofs. -/
theorem value_progress
    (admitted : Prepared operations declarations policy registry tables before output demand row bound)
    (isValue : before.execution.configuration.expression.IsValue) :
    before.execution.configuration.stack = .nil ∨
    ∃ after discharged remaining,
      NamedAccessStep [] before (ScopedPortJoint.advanceState before after [] discharged) ∧
      Prepared operations declarations policy registry tables
        (ScopedPortJoint.advanceState before after [] discharged) output remaining row bound ∧
      demand = RecursiveCompletion.retiredTickets discharged ++ remaining := by
  rcases DeclaredExecution.value_progress admitted.current isValue with terminal | ⟨after, discharged, remaining, step, current, accounting⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨after, discharged, remaining, step, value_preserves_prepared admitted isValue step current, accounting⟩

/-- Recomposition also retains declared requests and every certificate of a
surviving capture. The existing resume proofs determine the same actual stack. -/
theorem resume_preserves {front capture tail : Stack}
    (admitted : Prepared operations declarations policy registry tables
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ output demand row bound)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) :
    ∃ remaining,
      let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩
      let before : NamedState := ⟨⟨⟨.resume binder value, scope,
        front.append (.live owner input answer capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before (ScopedPortJoint.advanceState before after [] [.ticket owner]) ∧
      Prepared operations declarations policy registry tables
        (ScopedPortJoint.advanceState before after [] [.ticket owner]) output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨remaining, step, current, accounting⟩ := DeclaredExecution.resume_preserves admitted.current resolved isValue
  obtain ⟨sourceRemaining, raw, source, results, demandSame, trace⟩ :=
    DeclaredCompletionAdmission.resume_preserves admitted.current.source admitted.current.results resolved isValue
  have unique : (ownedTickets (capture.append (front.append (.spent owner answer caller tail)))).Nodup := by
    cases current.source with
    | checked _ _ unique _ _ => exact unique
  obtain ⟨actions, usage, history, requests, closing⟩ := admitted.actions
  obtain ⟨nextActions, nextUsage, nextHistory, actionExtension⟩ :=
    ScopedActionUsage.named_step_preserves step usage history
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, usageUnique⟩ := usage
  obtain ⟨rights, actionKnown, permitted⟩ := ScopedActionInterfaces.resume_requires_action code resolved
  have requests := ScopedActionInterfaces.resume_preserves_configuration resolved actionKnown permitted requests isValue
  refine ⟨remaining, step, ⟨current, ⟨nextActions, nextUsage, nextHistory, ?_, ?_⟩⟩, accounting⟩
  · simpa only [ScopedPortJoint.advanceState, List.append_nil] using
      (ScopedActionInterfaces.configuration_action_extension requests actionExtension)
  · simpa only [ScopedPortJoint.advanceState, List.append_nil] using
      (raw_step_preserves_retained raw closing (fun _ _ known => known) actionExtension (List.Subset.refl _)
        (.none (by simp)) unique)

end Ash.OneShot.DeclaredClosingInvariant

#print axioms Ash.OneShot.DeclaredClosingInvariant.certificate_world_weaken
#print axioms Ash.OneShot.DeclaredClosingInvariant.retained_empty
#print axioms Ash.OneShot.DeclaredClosingInvariant.capture_allocation
#print axioms Ash.OneShot.DeclaredClosingInvariant.resume_only_capture_allocation
#print axioms Ash.OneShot.DeclaredClosingInvariant.allocation_at_capture
#print axioms Ash.OneShot.DeclaredClosingInvariant.raw_step_preserves_retained
#print axioms Ash.OneShot.DeclaredClosingInvariant.initial_state
#print axioms Ash.OneShot.DeclaredClosingInvariant.excludes_disposal_gap
#print axioms Ash.OneShot.DeclaredClosingInvariant.discard_preserves_prepared
#print axioms Ash.OneShot.DeclaredClosingInvariant.discard_progress
#print axioms Ash.OneShot.DeclaredClosingInvariant.value_preserves_prepared
#print axioms Ash.OneShot.DeclaredClosingInvariant.value_progress
#print axioms Ash.OneShot.DeclaredClosingInvariant.resume_preserves
