import RecursiveClauseOwnership
import RecursiveBounds

/-!
Independent structural clause usage supplies the consumed-owner premise for
recursive capture. Existing path, demand-permutation and checked-trace proofs
connect lexical continuation actions to their actual ownership transitions.
-/

namespace Ash.OneShot.RecursiveClauseUsage
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open SourceTemplates (Expression)
open RecursiveRequirements (Requirements Checked Store)
open RecursiveRecords (CheckedState)
open RecursiveClosing (PlanTemplate)
open CallableProtectionFrames (contextOf)
open OwnerPhaseTransitions (available spendAll)
open RecursiveDisposalCapture (directCalls calls_prepend hidden_calls)
open Syntax (ticketDependencies)

/-- Stable summaries have no free continuation dependency. -/
theorem stable_no_tickets (summary : Summary operations world environment allowed code output row) :
    ticketDependencies code.dependencies = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro binder member
  have usage := ClauseProtection.stable_usage (CoherentSourceTypes.protection_summary summary) (fun _ => ⟨true, true⟩) .none .available
  obtain ⟨rights, impossible, completed⟩ := ScopedExpressions.free_ticket_requires_consumption usage
    (Syntax.mem_ticketDependencies.mp member)
  cases impossible

theorem callable_no_tickets
    (summary : SourceTemplates.CallableSummary operations policy contracts world environment allowed code output row) :
    ticketDependencies code.dependencies = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro binder member
  have typed := SourceTemplates.expression_ports (Expression.callable (scope := .none) summary) ScopedPorts.EffectScope.none
  have impossible := ScopedPorts.typed_ticket_known typed (Syntax.mem_ticketDependencies.mp member)
  cases impossible

/-- The reverse of the existing invocation-to-ticket provenance result. -/
theorem ticket_has_call
    (source : Expression operations policy contracts world allowed scope environment code output demand requirements)
    (used : binder ∈ ticketDependencies code.dependencies) :
    ∃ owner, scope.resolve binder = some owner ∧ owner ∈ directCalls requirements := by
  induction source using Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | stable summary => rw [stable_no_tickets summary] at used; cases used
  | callable summary ih => rw [callable_no_tickets summary] at used; cases used
  | lambda body outward formed ih =>
      have typed := SourceTemplates.expression_ports
        (Expression.lambda (allowed := []) (scope := .none) body outward formed) ScopedPorts.EffectScope.none
      have impossible := ScopedPorts.typed_ticket_known typed (Syntax.mem_ticketDependencies.mp used)
      cases impossible
  | purePair left right ihLeft ihRight =>
      simp only [Code.dependencies, tickets_append] at used
      rcases List.mem_append.mp used with first | second
      · obtain ⟨owner, resolved, impossible⟩ := ihLeft first
        cases impossible
      · obtain ⟨owner, resolved, impossible⟩ := ihRight second
        cases impossible
  | pair left right ihLeft ihRight | app left right _ ihLeft ihRight | cleanup left right _ ihLeft ihRight =>
      simp only [Code.dependencies, tickets_append] at used
      rcases List.mem_append.mp used with first | second
      · obtain ⟨owner, resolved, member⟩ := ihLeft first
        exact ⟨owner, resolved, List.mem_append_left _ member⟩
      · obtain ⟨owner, resolved, member⟩ := ihRight second
        exact ⟨owner, resolved, List.mem_append_right _ member⟩
  | bind left right ihLeft ihRight =>
      simp only [Code.dependencies, tickets_append, tickets_without_variable] at used
      rcases List.mem_append.mp used with first | second
      · obtain ⟨owner, resolved, member⟩ := ihLeft first
        exact ⟨owner, resolved, List.mem_append_left _ member⟩
      · obtain ⟨owner, resolved, member⟩ := ihRight second
        exact ⟨owner, resolved, List.mem_append_right _ member⟩
  | branch condition yes no same ihCondition ihYes ihNo =>
      simp only [Code.dependencies, tickets_append] at used
      rcases List.mem_append.mp used with first | third
      · rcases List.mem_append.mp first with first | second
        · obtain ⟨owner, resolved, member⟩ := ihCondition first
          exact ⟨owner, resolved, List.mem_append_left _ member⟩
        · obtain ⟨owner, resolved, member⟩ := ihYes second
          exact ⟨owner, resolved, List.mem_append_right _ (List.mem_append_left _ member)⟩
      · obtain ⟨owner, resolved, member⟩ := ihNo third
        exact ⟨owner, resolved, List.mem_append_right _ (List.mem_append_right _ member)⟩
  | perform known admitted operand formed ih =>
      exact ih (by simpa only [Code.dependencies, tickets_append, tickets_resource_map, List.nil_append] using used)
  | handler body clauses capabilities coverage unique admitted table modes ih =>
      obtain ⟨owner, resolved, member⟩ := ih (by simpa only [Code.dependencies, tickets_append,
        tickets_resource_map, List.nil_append, ScopedPorts.clauses_have_ticket_barrier clauses, List.append_nil] using used)
      exact ⟨owner, resolved, by simpa only [calls_prepend] using member⟩
  | resource initializer body formed effectsBound admitted outward ih ihBody =>
      simp only [Code.dependencies, tickets_append] at used
      rcases List.mem_append.mp used with first | second
      · exact ih first
      · obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
        have empty := callable_no_tickets (body identity fresh)
        rw [ScopedExpressions.instantiation_preserves_ticket_dependencies] at empty
        rw [empty] at second
        cases second
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      simp only [Code.dependencies, tickets_append] at used
      rcases List.mem_append.mp used with first | second
      · obtain ⟨owner, resolved, member⟩ := ihInit first
        exact ⟨owner, resolved, List.mem_append_left _ member⟩
      · obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
        obtain ⟨owner, resolved, member⟩ := ihBody identity fresh
          (by simpa only [ScopedExpressions.instantiation_preserves_ticket_dependencies] using second)
        rw [hidden_calls (hidden identity fresh)] at member
        exact ⟨owner, resolved, List.mem_append_right _ member⟩
  | resume known resolved permission operand admitted formed ih =>
      simp only [Code.dependencies, ticketDependencies] at used
      rcases List.mem_cons.mp used with same | nested
      · subst binder
        exact ⟨_, resolved, List.mem_append_right _ List.mem_cons_self⟩
      · obtain ⟨owner, resolved, member⟩ := ih nested
        exact ⟨owner, resolved, List.mem_append_left _ member⟩
  | discard known resolved permission unprotected admitted =>
      have same := List.mem_singleton.mp used
      subst binder
      exact ⟨_, resolved, List.mem_cons_self⟩
  | _ => intros; trivial

/-- Branch demands already carry the permutation needed for either path. -/
theorem direct_calls_demand (requirements : Requirements demand) : directCalls requirements ⊆ demand := by
  induction requirements with
  | request | retire | spent => exact List.nil_subset _
  | invoke key demand nearer =>
      intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      exact List.mem_cons_self
  | sequence left right ihLeft ihRight => exact ScopedExpressions.append_subset ihLeft ihRight
  | emitAfter body nearer raw ih => exact ih
  | choice left right same ihLeft ihRight =>
      intro owner member
      rcases List.mem_append.mp member with first | second
      · exact ihLeft first
      · exact same.mem_iff.mpr (ihRight second)

theorem consuming_usage_has_ticket
    (usage : Uses policy (.ticket binder rights) .available code .consumed) :
    binder ∈ ticketDependencies code.dependencies := by
  rw [← Code.usage_shape_tickets]
  exact Syntax.mem_ticketDependencies.mpr (Syntax.consuming_use_retains_ticket usage)

theorem consuming_usage_demand
    (source : Expression operations policy contracts world allowed (.ticket binder owner) environment code output demand requirements)
    (usage : Uses policy (.ticket binder rights) .available code .consumed) : owner ∈ demand := by
  obtain ⟨actual, resolved, member⟩ := ticket_has_call source (consuming_usage_has_ticket usage)
  have same := RecursiveClauses.resolved_owner resolved
  subst actual
  exact direct_calls_demand requirements member

/-- An independently checked clause capability determines the actual final
    phase through the existing complete ownership trace. -/
theorem consuming_usage_completed
    (source : Expression operations policy contracts world allowed (.ticket binder owner) environment code output demand requirements)
    (usage : Uses policy (.ticket binder rights) .available code .consumed)
    (checked : Checked store receiving before requirements row) :
    OwnerPhaseTransitions.spendAll before demand owner = .consumed :=
  OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace checked) (consuming_usage_demand source usage)

theorem declared_clause_completed
    (selected : ClauseAt operation clauses parameter binder code)
    (capabilities : ClausesUse policy clauses)
    (source : Expression operations policy contracts world allowed (.ticket binder owner) environment code output demand requirements)
    (checked : Checked store receiving before requirements row) :
    spendAll before demand owner = .consumed :=
  consuming_usage_completed source (ScopedExecution.selected_clause_usage selected capabilities) checked

/-- The table's action bound can replace excess permission on the selected
    ticket. Nested clauses retain their own independently checked policy. -/
theorem selected_clause_permissions
    (selected : ClauseAt operation clauses parameter binder code)
    (capabilities : ClausesUse policy clauses)
    (modes : SourceTemplates.ClauseModes clauses table)
    (known : lookup operation table = some contract) :
    Uses policy (.ticket binder ⟨true, contract.dispose⟩) .available code .consumed := by
  obtain ⟨offered, found, dispose⟩ := SourceTemplates.selected_clause_mode selected modes
  have same : offered = contract := Option.some.inj (found.symm.trans known)
  subst offered
  exact scoped_usage_repermission (selected_clause_usage selected capabilities) .ticket
    ⟨fun _ => rfl, dispose⟩

theorem protected_clause_resume_only
    (selected : ClauseAt operation clauses parameter binder code)
    (capabilities : ClausesUse policy clauses)
    (modes : SourceTemplates.ClauseModes clauses table)
    (known : lookup operation table = some contract)
    (accepted : modeCheck contract.dispose true = true) :
    Uses policy (.ticket binder ActionRequirements.resumeOnly) .available code .consumed := by
  have noDispose : contract.dispose = false := by simpa [modeCheck] using accepted
  simpa only [noDispose, ActionRequirements.resumeOnly] using
    selected_clause_permissions selected capabilities modes known

theorem concealed_disposal_rejected :
    ¬ SourceTemplates.ClauseModes (.cons operation parameter binder (.discard binder) .nil)
      [(operation, ⟨false, freeRow, heldRow⟩)] := by
  intro modes
  cases modes with
  | cons dispose rest => cases dispose rfl

theorem conservative_resume_mode_allowed :
    SourceTemplates.ClauseModes (.cons operation parameter binder (.resume binder .unit) .nil)
      [(operation, ⟨true, freeRow, heldRow⟩)] :=
  .cons (fun _ => rfl) .nil

/-- Existing parametric clause tables already carry the policy's disposal
    flag. Independently checked usage supplies its bound without a new compiler. -/
theorem specialized_schema_modes
    (schemas : ParametricClauseRows.ClausesSchema operations policy environment requested answer clauses schemaTable)
    (capabilities : ClausesUse policy clauses) :
    SourceTemplates.ClauseModes clauses (ParametricClauseRows.specializeTable schemaTable resumeRow closeRow) := by
  induction schemas with
  | nil => exact .nil
  | cons known ordinary protectedMode rest ih => cases capabilities with
    | cons usage remaining => exact .cons (scoped_usage_requires_actions usage).2 (ih remaining)

/-- Port typing alone could admit this clause. The shared handler rule now
    rejects its missing continuation consumption through structural usage. -/
theorem ignored_clause_rejected :
    ¬ Expression operations policy contracts world allowed scope environment
      (.handle requested code (.cons operation parameter binder .unit .nil)) output demand requirements := by
  intro source
  cases source with
  | stable summary => cases summary
  | callable summary => cases summary
  | handler body clauses capabilities coverage unique admitted table modes => cases capabilities with
    | cons usage rest => cases usage

/-- Effect coverage cannot change a directly named continuation, its mode or
    its demand. Recursive record checking preserves the same fact in saved bodies. -/
theorem bounds_invocations (bounded : RecursiveBounds.Bounds actual upper) :
    RecursiveClauseOwnership.directInvocations actual = RecursiveClauseOwnership.directInvocations upper := by
  induction bounded <;> simp_all only [RecursiveClauseOwnership.directInvocations]

theorem bounds_cannot_change_mode :
    ¬ RecursiveBounds.Bounds (.invoke ⟨19, .resume⟩ [] []) (.invoke ⟨19, .dispose⟩ [] []) := by
  intro bounded
  have same := bounds_invocations bounded
  cases same

/-- Declaration capability checking supplies ownership completion. A checked
    upper certificate and structural record/requirement bounds derive the actual
    clause check and effect bound. Source typing and the declaration's upper
    certificate remain inputs. -/
theorem capture_from_handler_usage
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (capabilities : ClausesUse policy handler.clauses)
    (modes : SourceTemplates.ClauseModes handler.clauses (tables handler))
    (operationKnown : operations requested operation = some (argument, input))
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (resumeEffects closeEffects : List Instance) (closingRow : Footprint)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    ∃ (contract : Owners.Contract) (offeredContract : ClauseContract) (offered requestRow tailRow raw : Footprint)
      (tailDemand : List Nat) (closingRequirements : Requirements (OwnerClosingSource.retirements plan)) (store : Store),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = OwnerClosingSource.retirements plan ∧ contract.closeRow = some closingRow ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      PlanTemplate operations policy (contracts.insert owner contract) tables world .none plan raw closingRequirements ∧
      demand = contract.resumeDemand ++ tailDemand ∧
      (tail = .nil → tailDemand = []) ∧
      contract.resumeDemand.Sublist demand ∧
      row = (requestRow ++ contract.resumeRow) ++ tailRow ∧
      lookup operation (tables handler) = some offeredContract ∧
      Uses policy (.ticket binder ⟨true, offeredContract.dispose⟩) .available body .consumed ∧
      modeCheck offeredContract.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offeredContract.row (ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some requestRow ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      (∀ actualRow, contract.closeRow = some actualRow →
        residualize (contextOf tables tail) raw = some closingRow →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) actualRow) ∧
      ∀ (allowed : List Instance) (clauseDemand : List Nat) (upperRow : Footprint)
          (clauseRequirements upperRequirements : Requirements clauseDemand) (upperStore : Store),
        Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements →
        RecursiveBounds.StoreBounds store upperStore →
        RecursiveBounds.Bounds clauseRequirements upperRequirements →
        Checked upperStore
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))) upperRequirements upperRow →
        upperRow ⊆ (requestRow ++ contract.resumeRow) →
        ∃ clauseRow, RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
          ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
        CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
          (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
        (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
        (clauseRow ++ tailRow) ⊆ row ∧
        ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨contract, offeredContract, offered, requestRow, tailRow, raw, tailDemand, closingRequirements, store,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown, offeredMode, offeredRow, offeredExport,
    resumeCheck, disposeCheck, enter⟩ :=
    RecursiveClauseOwnership.capture_from_recursive_clause source cut clause operationKnown isValue fresh
      resumeEffects closeEffects closingRow built internal
  refine ⟨contract, offeredContract, offered, requestRow, tailRow, raw, tailDemand, closingRequirements, store,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown,
    selected_clause_permissions clause capabilities modes offeredKnown, offeredMode, offeredRow, offeredExport,
    resumeCheck, disposeCheck, ?_⟩
  intro allowed clauseDemand upperRow requirements upperRequirements upperStore current recordsBound requirementsBound upperChecked upperBound
  obtain ⟨clauseRow, checked, covered⟩ := RecursiveBounds.checked_below upperChecked recordsBound requirementsBound
  exact ⟨clauseRow, enter allowed clauseDemand clauseRow requirements current checked
    (declared_clause_completed clause capabilities current checked) (EffectBounds.covers_trans upperBound covered)⟩

/-- Chosen-template closing admission and independent clause capabilities feed
    the same capture proof. Actual closing and clause rows are derived from their
    bounds; full declaration-derived source certificates remain to be connected. -/
theorem capture_from_bounded_handler
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (capabilities : ClausesUse policy handler.clauses)
    (modes : SourceTemplates.ClauseModes handler.clauses (tables handler))
    (operationKnown : operations requested operation = some (argument, input))
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (resumeEffects closeEffects : List Instance)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (chosen : PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (closingCovered : EffectBounds.Covers upperClosing raw)
    (closingAdmitted : checkFootprint (contextOf tables tail ++ outside) upperClosing = true) :
    ∃ closingRow, residualize (contextOf tables tail) raw = some closingRow ∧
      checkFootprint outside closingRow = true ∧
    ∃ (contract : Owners.Contract) (offeredContract : ClauseContract) (offered requestRow tailRow : Footprint)
      (tailDemand : List Nat) (store : Store),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = OwnerClosingSource.retirements plan ∧ contract.closeRow = some closingRow ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      PlanTemplate operations policy (contracts.insert owner contract) tables world .none plan raw closingRequirements ∧
      demand = contract.resumeDemand ++ tailDemand ∧
      (tail = .nil → tailDemand = []) ∧
      contract.resumeDemand.Sublist demand ∧
      row = (requestRow ++ contract.resumeRow) ++ tailRow ∧
      lookup operation (tables handler) = some offeredContract ∧
      Uses policy (.ticket binder ⟨true, offeredContract.dispose⟩) .available body .consumed ∧
      modeCheck offeredContract.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offeredContract.row (ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some requestRow ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      (∀ actualRow, contract.closeRow = some actualRow →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) actualRow) ∧
      ∀ (allowed : List Instance) (clauseDemand : List Nat) (upperRow : Footprint)
          (clauseRequirements upperRequirements : Requirements clauseDemand) (upperStore : Store),
        Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements →
        RecursiveBounds.StoreBounds store upperStore →
        RecursiveBounds.Bounds clauseRequirements upperRequirements →
        Checked upperStore
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))) upperRequirements upperRow →
        upperRow ⊆ (requestRow ++ contract.resumeRow) →
        ∃ clauseRow, RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
          ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
        CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
          (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
        (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
        (clauseRow ++ tailRow) ⊆ row ∧
        ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨closingRow, closingExport, closingAccepted, contract, offeredContract, offered, requestRow, tailRow, tailDemand, store,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown, offeredMode, offeredRow, offeredExport,
    resumeCheck, disposeCheck, enter⟩ :=
    RecursiveDisposalCapture.prepare_capture_bounded_closing source cut clause operationKnown isValue fresh
      resumeEffects closeEffects built internal chosen closingCovered closingAdmitted
  refine ⟨closingRow, closingExport, closingAccepted, contract, offeredContract, offered, requestRow, tailRow, tailDemand, store,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown,
    selected_clause_permissions clause capabilities modes offeredKnown, offeredMode, offeredRow, offeredExport,
    resumeCheck, disposeCheck, ?_⟩
  intro allowed clauseDemand upperRow requirements upperRequirements upperStore current recordsBound requirementsBound upperChecked upperBound
  obtain ⟨clauseRow, checked, covered⟩ := RecursiveBounds.checked_below upperChecked recordsBound requirementsBound
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have completed := declared_clause_completed clause capabilities current checked
  have sameClause := RecursiveClauseOwnership.consuming_clause_balance current known checked
    (by simp [available, ownedTickets]) completed balance
  exact ⟨clauseRow, enter allowed clauseDemand clauseRow requirements current checked sameClause
    (EffectBounds.covers_trans upperBound covered)⟩

end Ash.OneShot.RecursiveClauseUsage

#print axioms Ash.OneShot.RecursiveClauseUsage.stable_no_tickets
#print axioms Ash.OneShot.RecursiveClauseUsage.ticket_has_call
#print axioms Ash.OneShot.RecursiveClauseUsage.direct_calls_demand
#print axioms Ash.OneShot.RecursiveClauseUsage.consuming_usage_has_ticket
#print axioms Ash.OneShot.RecursiveClauseUsage.consuming_usage_demand
#print axioms Ash.OneShot.RecursiveClauseUsage.consuming_usage_completed

#print axioms Ash.OneShot.RecursiveClauseUsage.capture_from_handler_usage

#print axioms Ash.OneShot.RecursiveClauseUsage.declared_clause_completed
#print axioms Ash.OneShot.RecursiveClauseUsage.ignored_clause_rejected

#print axioms Ash.OneShot.RecursiveClauseUsage.selected_clause_permissions
#print axioms Ash.OneShot.RecursiveClauseUsage.protected_clause_resume_only
#print axioms Ash.OneShot.RecursiveClauseUsage.concealed_disposal_rejected
#print axioms Ash.OneShot.RecursiveClauseUsage.conservative_resume_mode_allowed

#print axioms Ash.OneShot.RecursiveClauseUsage.specialized_schema_modes

#print axioms Ash.OneShot.RecursiveClauseUsage.callable_no_tickets

#print axioms Ash.OneShot.RecursiveClauseUsage.bounds_invocations
#print axioms Ash.OneShot.RecursiveClauseUsage.bounds_cannot_change_mode

#print axioms Ash.OneShot.RecursiveClauseUsage.capture_from_bounded_handler
