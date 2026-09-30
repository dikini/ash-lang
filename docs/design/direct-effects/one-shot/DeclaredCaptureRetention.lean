import DeclaredInterfaceProgress

/-! Derive the non-disposing allocation guard from the selected source
declaration, then retain closing evidence across that actual capture. The
runtime policy need not deny disposal. This establishes the certificate and
independent-action components; it does not establish capture's effect-interface
connection or disposal-enabled source admission.
-/
namespace Ash.OneShot.DeclaredClosingInvariant
open ScopedExpressions ScopedExecution CoherentSourceTypes

/-- Exact scoped handler metadata is determined by the active ordered cut.
Erasure alone cannot recover the retained clause code. -/
theorem selected_handler_unique
    (first : HandlerCut requested whole capture tail handler)
    (second : HandlerCut requested whole otherCapture otherTail otherHandler) :
    handler = otherHandler := by
  induction first generalizing otherCapture otherTail otherHandler with
  | hit handler tail same => cases second with
      | hit => rfl
      | push frame rest capture tail handler miss next => exact False.elim (miss (by simp [ExecFrame.erase, HandlerData.erase, Frame.target, same]))
  | push frame rest capture tail handler miss next ih => cases second with
      | hit handler tail same => exact False.elim (miss (by simp [ExecFrame.erase, HandlerData.erase, Frame.target, same]))
      | push frame rest capture tail handler otherMiss otherNext => exact ih otherNext
  | live owner input answer saved scope rest capture tail handler next ih => cases second with
      | live owner input answer saved scope rest capture tail handler otherNext => exact ih otherNext
  | spent owner answer scope rest capture tail handler next ih => cases second with
      | spent owner answer scope rest capture tail handler otherNext => exact ih otherNext

/-- The existing checked source cut retains the selected declaration's action
bound. Reuse its decomposition and clause-mode proof, without another induction. -/
theorem selected_source_no_disposal
    (source : DeclaredSourceFrames.Segment operations policy contracts tables world
      whole input output demand requirements records)
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (noDispose : (ProtectionContracts.lookup operation (tables handler)).map
      ProtectionContracts.ClauseContract.dispose = some false) :
    body.requiredActions.dispose = false := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    annotation, selectedFrame, saved, surviving, sameDemand, sameRecords, evaluation⟩ :=
    RecursiveCapture.capture_segments_with_frames cut source
  cases selectedFrame with
  | handler typed annotation declarations capabilities modes =>
      obtain ⟨offered, known, bounded⟩ := SourceTemplates.selected_clause_mode selected modes
      have denied : offered.dispose = false := by simpa only [known, Option.map_some, Option.some.injEq] using noDispose
      cases actual : body.requiredActions.dispose with
      | false => rfl
      | true => have impossible := bounded actual; rw [denied] at impossible; cases impossible

/-- Source selection supplies the fresh allocation certificate guard itself.
Neither a new closing certificate nor a runtime denial is a premise. -/
theorem source_resume_only_allocation
    (source : DeclaredSourceFrames.Segment operations policy contracts tables world
      whole input output demand requirements records)
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (noDispose : (ProtectionContracts.lookup operation (tables handler)).map
      ProtectionContracts.ClauseContract.dispose = some false)
    (known : registry owner = some record) (isValue : operand.IsValue) :
    Allocation signature world registry
      (ScopedActionUsage.advance actions
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner inputType handler.answer capture handler.scope tail⟩ [.ticket owner])
      [.ticket owner] (.live owner inputType handler.answer capture handler.scope tail) :=
  resume_only_capture_allocation known isValue (selected_source_no_disposal source cut selected noDispose)

/-- Join the actual source-selected capture with existing action, history and
capture-provenance preservation. All older records retain their full identity;
the new owner receives the selected clause's least action bound. -/
theorem source_capture_retains_closing
    (source : DeclaredSourceFrames.Segment operations policy registry.contracts tables world
      whole input output demand requirements records)
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (noDispose : (ProtectionContracts.lookup operation (tables handler)).map
      ProtectionContracts.ClauseContract.dispose = some false)
    (closed : ClosedValue operand) (ready : ClosedExcept parameter body)
    (fresh : registry owner = none)
    (checks : UsageChecks actions
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ [.ticket owner])
    (usage : ConfigurationUsage policy actions
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩)
    (history : UsageRegistryHistory actions issued)
    (retained : Retained operations.ports world registry actions whole)
    (unique : (ownedTickets whole).Nodup) :
    let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
      .live owner inputType handler.answer capture handler.scope tail⟩
    let nextActions := ScopedActionUsage.advance actions after [.ticket owner]
    RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
      after [.ticket owner] [] ∧
    ConfigurationUsage policy nextActions after ∧
    UsageRegistryHistory nextActions (issued ++ [.ticket owner]) ∧
    Syntax.UsageExtension actions nextActions ∧
    nextActions owner = some body.requiredActions ∧ body.requiredActions.dispose = false ∧
    Retained operations.ports world (registry.insert owner record) nextActions after.stack ∧
    ownedTickets after.stack = owner :: ownedTickets whole := by
  let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
    .live owner inputType handler.answer capture handler.scope tail⟩
  have raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
      after [.ticket owner] [] :=
    .capture requested operation parameter binder owner operand body scope whole capture tail handler
      inputType cut selected closed ready
  have actionExtension := ScopedActionUsage.advance_extends (after := after) checks.allocation
  have known : (registry.insert owner record) owner = some record := by simp [Owners.Registry.insert]
  have unowned : owner ∉ ownedTickets whole := RecursiveCapture.fresh_unowned source.erase
    (by simp [Owners.Registry.contracts, fresh])
  have accounting : ownedTickets after.stack = owner :: ownedTickets whole := RecursiveCapture.capture_owned cut
  have afterUnique : (ownedTickets after.stack).Nodup := accounting ▸ List.nodup_cons.mpr ⟨unowned, unique⟩
  refine ⟨raw, ScopedActionUsage.raw_step_preserves raw checks usage,
    ScopedActionUsage.raw_step_preserves_history raw history, actionExtension, ?_,
    selected_source_no_disposal source cut selected noDispose, ?_, accounting⟩
  · simp [ScopedActionUsage.advance, Syntax.UsageTickets.insert,
      Code.substitution_required_actions body parameter closed.1]
  · apply raw_step_preserves_retained raw retained ?_ actionExtension (List.Subset.refl _)
      (source_resume_only_allocation source cut selected noDispose known closed.1) afterUnique
    intro old previous found
    by_cases same : old = owner
    · subst old; rw [fresh] at found; cases found
    · simp [Owners.Registry.insert, same, found]

theorem named_event_parts (step : NamedAccessStep ambient before after) :
    ∃ created discharged,
      RawStep before.execution.configuration after.execution.configuration created discharged ∧
      after.execution.issued = before.execution.issued ++ created ∧
      after.execution.completed = discharged ++ before.execution.completed ∧
      (before.execution.issued ++ created).Nodup := by
  cases step with
  | mk execution checks => cases execution with
      | event next created discharged raw freshOwners freshHandlers =>
          exact ⟨created, discharged, raw, rfl, rfl, freshOwners⟩

private theorem raw_non_disposing_capture_retention
    (source : DeclaredSourceStates.CheckedState operations policy registry.contracts tables world outside
      before.scope before.expression before.stack output demand row)
    (raw : RawStep before after [.ticket owner] [])
    (selection : ∀ requested operation operand capture tail handler,
      before.expression = .perform (Instantiation.freezeEffect requested) operation operand →
      HandlerCut requested before.stack capture tail handler →
      (ProtectionContracts.lookup operation (tables handler)).map
        ProtectionContracts.ClauseContract.dispose = some false)
    (fresh : registry owner = none) (checks : UsageChecks actions before [.ticket owner])
    (usage : ConfigurationUsage policy actions before) (history : UsageRegistryHistory actions issued)
    (retained : Retained operations.ports world registry actions before.stack) :
    let nextActions := ScopedActionUsage.advance actions after [.ticket owner]
    ConfigurationUsage policy nextActions after ∧
    UsageRegistryHistory nextActions (issued ++ [.ticket owner]) ∧
    Syntax.UsageExtension actions nextActions ∧
    Retained operations.ports world (registry.insert owner record) nextActions after.stack := by
  cases raw with
  | capture requested operation parameter binder owner operand body scope whole capture tail handler
      input cut selected closed ready =>
      obtain ⟨inputValue, argument, payloadAllowed, requirements, records, disposals, parameter', binder', body',
        offered, offeredRow, requestRow, pendingRow, operationKnown, payload, valueClosed, pending, closing,
        pendingCheck, unique, clause, capabilities, found, mode, availableRow, exported, offeredAccepted,
        pendingAccepted, sameRow⟩ := DeclaredSourceRequests.request_parts source cut closed.1
      obtain ⟨actual, nextUsage, nextHistory, extension, known, noDispose, nextRetained, accounting⟩ :=
        source_capture_retains_closing (record := record) pending cut selected
          (selection _ _ _ _ _ _ rfl cut) closed ready fresh checks usage history retained unique
      exact ⟨nextUsage, nextHistory, extension, nextRetained⟩

/-- The existing source/runtime capture and the certificate/action proof now
describe the same access-checked successor and coherent record. The remaining
effect-interface connection is deliberately absent from this conclusion. -/
theorem resume_only_capture_components
    (before : Prepared operations declarations policy registry tables
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ output demand row bound)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue)
    (noDispose : (ProtectionContracts.lookup operation (tables handler)).map
      ProtectionContracts.ClauseContract.dispose = some false) :
    ∃ (owner : Nat) (record : Owners.Record) (after : Configuration)
      (nextDemand : List Nat) (nextRow : ProtectionContracts.Footprint) (actions : Syntax.UsageTickets),
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let next := ScopedPortJoint.advanceState state after [.ticket owner] []
      record.annotation.closeRow = none ∧
      NamedAccessStep [] state next ∧
      DeclaredExecution.Valid operations declarations policy (registry.insert owner record) tables [] []
        next output nextDemand nextRow bound ∧
      ConfigurationUsage policy actions next.execution.configuration ∧
      UsageRegistryHistory actions next.execution.issued ∧
      Retained operations.ports (ScopedTyping.resourceWorld next.execution.issued)
        (registry.insert owner record) actions next.execution.configuration.stack ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨owner, record, after, nextDemand, nextRow, noClose, step, current, sourceExtension,
    runtimeExtension, demandSame, included, accounting⟩ :=
    DeclaredExecution.resume_only_capture before.current cut isValue noDispose
  obtain ⟨created, discharged, raw, issuedSame, completedSame, freshOwners⟩ := named_event_parts step
  have createdSame : [.ticket owner] = created := List.append_cancel_left issuedSame
  have dischargedSame : [] = discharged := List.append_cancel_right completedSame
  subst created
  subst discharged
  have fresh : registry owner = none := by
    have absent := ScopedPortJoint.registry_fresh before.current.registry freshOwners
    cases found : registry owner <;>
      simp_all [Owners.Registry.runtime, CallableJoint.Registry.joint]
  obtain ⟨actions, usage, history, interfaces, retained⟩ := before.actions
  have checks := usage_checks_from_allocation_and_access history freshOwners step.checks
  have selection : ∀ actualRequested operation' operand' capture' tail' handler',
      (.perform (Instantiation.freezeEffect requested) operation operand : Code) =
        .perform (Instantiation.freezeEffect actualRequested) operation' operand' →
      HandlerCut actualRequested whole capture' tail' handler' →
      (ProtectionContracts.lookup operation' (tables handler')).map
        ProtectionContracts.ClauseContract.dispose = some false := by
    intro actualRequested operation' operand' capture' tail' handler' same actualCut
    obtain ⟨effectSame, operationSame, operandSame⟩ := Code.perform.inj same
    have requestSame : requested = actualRequested := freeze_effect_injective effectSame
    subst actualRequested
    subst operation'
    have handlerSame := selected_handler_unique cut actualCut
    subst handler'
    exact noDispose
  obtain ⟨nextUsage, nextHistory, actionExtension, nextRetained⟩ :=
    raw_non_disposing_capture_retention (record := record) before.current.source raw selection
      fresh checks usage history retained
  refine ⟨owner, record, after, nextDemand, nextRow, _, noClose, step, current,
    nextUsage, nextHistory, ?_, demandSame, included, accounting⟩
  simpa [ScopedPortJoint.advanceState, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using nextRetained

end Ash.OneShot.DeclaredClosingInvariant

#print axioms Ash.OneShot.DeclaredClosingInvariant.selected_source_no_disposal
#print axioms Ash.OneShot.DeclaredClosingInvariant.source_resume_only_allocation
#print axioms Ash.OneShot.DeclaredClosingInvariant.source_capture_retains_closing
#print axioms Ash.OneShot.DeclaredClosingInvariant.selected_handler_unique
#print axioms Ash.OneShot.DeclaredClosingInvariant.resume_only_capture_components
