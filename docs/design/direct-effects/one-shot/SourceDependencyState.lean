import SourceDependencySchemes

/-! Shared enriched source and runtime state. All source, annotation, store and
contextual checks refer to the same requirement indices and actual stack.
Initial construction, pure source reduction, disposal runtime progress and
preservation, and disposing capture from the enriched invariant are proved here. Complete source
admission and the other runtime cases remain open. -/
namespace Ash.OneShot.SourceDependencyState
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Operations Contracts Expression Value Environment Dependencies)
open SourceDependencySchemes (Checked Retained)
open RecursiveRequirements (Requirements)

/-- Support depends only on retained resources, so irrelevant ambient entries
can be removed. Dormant captures retain their own enclosing visible suffix. -/
theorem supported_restrict {control : Control} (support : Supported control ambient)
    (keep : ∀ resource, resource ∈ ambient → resource ∈ Execution.retainedResources control → resource ∈ next) :
    Supported control next := by
  induction support generalizing next with
  | nil => exact .nil _
  | push frame rest ambient tail access ih =>
      apply Supported.push frame rest next
      · apply ih
        intro resource outside retained
        exact keep resource outside (List.mem_append_right _ retained)
      · intro resource retained
        rcases List.mem_append.mp (access retained) with visible | outside
        · exact List.mem_append_left _ visible
        · exact List.mem_append_right _ (keep resource outside (List.mem_append_left _ retained))
  | live owner input answer saved rest ambient captured tail ihSaved ihTail =>
      apply Supported.live owner input answer saved rest next
      · apply ihSaved
        intro resource outside retained
        rcases List.mem_append.mp outside with visible | external
        · exact List.mem_append_left _ visible
        · exact List.mem_append_right _ (keep resource external (List.mem_append_left _ retained))
      · apply ihTail
        intro resource outside retained
        exact keep resource outside (List.mem_append_right _ retained)
  | spent owner answer rest ambient tail ih => exact .spent owner answer rest next (ih keep)

/-- Unique ownership separates external support from resources owned inside
the capture. The computed outside interface retains precisely those needs. -/
theorem supported_outside_interface {control : Control} (support : Supported control ambient)
    (separate : ∀ resource ∈ ambient, Owner.resource resource ∉ control.owners) :
    Supported control (Admission.outsideResources control) := by
  apply supported_restrict support
  intro resource outside retained
  exact List.mem_filter.mpr ⟨retained, by simpa using separate resource outside⟩

theorem capture_resource_support
    (cut : HandlerCut requested whole capture tail handler)
    (support : Supported whole.erase []) (unique : Unique whole.erase) :
    Supported capture.erase (Admission.outsideResources capture.erase) := by
  have split := cut_decompose (sourceCut_is_cut (handler_cut_erases cut))
  rw [split] at support
  obtain ⟨captured, outside⟩ := supported_decompose capture.erase support
  have separated : (capture.erase.owners ++ tail.erase.owners).Nodup := by
    simpa only [Unique, split, owners_append] using unique
  apply supported_outside_interface captured
  intro resource visible owned
  have enclosing := Execution.visible_resource_owned (control := tail.erase) (by simpa only [List.append_nil] using visible)
  exact (List.nodup_append.mp separated).2.2 (.resource resource) owned (.resource resource) enclosing rfl

inductive State (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (actions : Syntax.UsageTickets) (annotations : Nat → Option SourceDependencyCapture.Scope)
    (world : List Nat) (outward : List Instance) (outside : ProtectionContracts.Context)
    (scope : Execution.Scope) (code : Code) (stack : Stack) (output : Value)
    (demand : List Nat) (row : Footprint) : Prop where
  | checked
      (current : Expression operations policy contracts world allowed scope Environment.empty
        code input currentDemand currentRequirements dependencies)
      (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports scope ticket)
      (pending : SourceDependencyFrames.Segment operations policy contracts tables families actions world
        stack input output pendingDemand pendingRequirements resumes receiving allowed [])
      (closing : DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world stack disposals)
      (templates : SourceDependencySchemes.Closing.Records operations policy contracts tables annotations world stack disposals)
      (bound : SourceDependencySchemes.Closing.Bound annotations receiving)
      (declarations : SourceDependencySchemes.Stored.Forest outward families stack)
      (contextual : Checked outward actions (OwnerPhaseTransitions.available (ownedTickets stack)) world dependencies receiving)
      (retained : Retained outward actions (OwnerPhaseTransitions.available (ownedTickets stack)) world receiving .nil)
      (unique : (ownedTickets stack).Nodup)
      (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
        (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row)
      (accepted : checkFootprint outside row = true)
      (accounting : demand = currentDemand ++ pendingDemand) :
      State operations policy contracts tables families actions annotations world outward outside scope code stack output demand row

theorem State.erase
    (state : State operations policy contracts tables families actions annotations world outward outside scope code stack output demand row) :
    DeclaredConnectedSources.State operations.erase policy contracts.erase tables actions world outside scope code stack output.erase demand row := by
  cases state with
  | checked current scope pending closing templates bound declarations contextual retained unique evaluated accepted accounting =>
      exact .checked (SourceDependencyAnnotations.expression_erase current) scope pending.erase closing unique evaluated accepted accounting

theorem initial
    (current : Expression operations policy contracts world [] .none Environment.empty code output demand requirements dependencies)
    (empty : demand = [])
    (contextual : Checked outward actions (OwnerPhaseTransitions.available []) world dependencies .nil)
    (evaluated : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : checkFootprint outside row = true) :
    State operations policy contracts tables families actions annotations world outward outside .none code .nil output demand row := by
  subst demand
  have currentCheck := RecursiveRequirements.checked_prepend_iff.mpr
    (show RecursiveRequirements.Checked [] ([] ++ []) (OwnerPhaseTransitions.available []) requirements row from evaluated)
  have pendingCheck : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) (Requirements.request [] []) [] := .request rfl
  simpa only [List.append_nil] using
    (State.checked (tables := tables) current .none (.nil (List.Subset.refl [])) .nil .nil .nil .nil
      contextual .nil (by decide) (RecursiveRequirements.Checked.sequence currentCheck pendingCheck)
      (by simpa only [List.append_nil] using accepted) rfl)

/-- Source replacement keeps the exact pending source, stores and annotations.
Only present expression typing, contextual checking and evaluation are needed. -/
theorem replace_current
    {requirements : Requirements currentDemand}
    (current : Expression operations policy contracts world allowed nextScope Environment.empty
      next input currentDemand reduced dependencies)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports nextScope ticket)
    (pending : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      stack input output pendingDemand pendingRequirements resumes receiving allowed [])
    (closing : DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world stack disposals)
    (templates : SourceDependencySchemes.Closing.Records operations policy contracts tables annotations world stack disposals)
    (bound : SourceDependencySchemes.Closing.Bound annotations receiving)
    (declarations : SourceDependencySchemes.Stored.Forest outward families stack)
    (contextual : Checked outward actions (OwnerPhaseTransitions.available (ownedTickets stack)) world dependencies receiving)
    (retained : Retained outward actions (OwnerPhaseTransitions.available (ownedTickets stack)) world receiving .nil)
    (unique : (ownedTickets stack).Nodup)
    (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
      (.sequence (requirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row)
    (accepted : checkFootprint outside row = true)
    (accounting : demand = currentDemand ++ pendingDemand)
    (same : ∀ store receiving before, RecursiveRequirements.evaluate store receiving before reduced =
      RecursiveRequirements.evaluate store receiving before requirements) :
    State operations policy contracts tables families actions annotations world outward outside nextScope next stack output demand row := by
  apply State.checked current scopeTyped pending closing templates bound declarations contextual retained unique _ accepted accounting
  apply RecursiveRequirements.evaluate_sound
  have original := RecursiveRequirements.checked_complete evaluated
  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend] at original ⊢
  rw [same]
  exact original

theorem bind_preserves
    (state : State operations policy contracts tables families actions annotations world outward outside scope
      (.bind parameter value body) stack output demand row)
    (closed : ClosedValue value) :
    State operations policy contracts tables families actions annotations world outward outside scope
      (body.subst parameter value) stack output demand row := by
  cases state with
  | checked current scope pending closing templates bound declarations contextual retained unique evaluated accepted accounting =>
      obtain ⟨reduced, remaining, replacement, ⟨initialDep, shape, silent⟩, same⟩ :=
        SourceDependencyAnnotations.bind_expression current closed
      rw [shape] at contextual
      have nextChecked := (SourceDependencyChecks.Local.silent_prefix silent).mp contextual
      exact replace_current replacement scope pending closing templates bound declarations nextChecked retained unique evaluated accepted accounting same

theorem beta_preserves
    (state : State operations policy contracts tables families actions annotations world outward outside scope
      (.app (.lambda parameter body) value) stack output demand row)
    (closed : ClosedValue value) :
    State operations policy contracts tables families actions annotations world outward outside .none
      (body.subst parameter value) stack output demand row := by
  cases state with
  | checked current scope pending closing templates bound declarations contextual retained unique evaluated accepted accounting =>
      obtain ⟨reduced, remaining, replacement, ⟨functionDep, argumentDep, shape, functionSilent, argumentSilent⟩, same⟩ :=
        SourceDependencyAnnotations.beta_expression current closed
      rw [shape] at contextual
      have nextChecked := (SourceDependencyChecks.Local.silent_prefix argumentSilent).mp
        ((SourceDependencyChecks.Local.silent_prefix functionSilent).mp contextual)
      exact replace_current replacement .none pending closing templates bound declarations nextChecked retained unique evaluated accepted accounting same


/-- Disposal preserves the shared source state at the actual closing stack.
Plan effect typing remains an admission premise; all other source/store and
contextual successor checks come from the existing recomposition theorem. -/
theorem discard_preserves {front capture tail : Stack}
    (state : State operations policy contracts tables families actions annotations world outward outside caller
      (.discard binder) (front.append (.live owner inputType answerType capture savedCaller tail)) output demand row)
    (known : contracts owner = some contract) (resolved : caller.resolve binder = some owner)
    (built : makePlan capture = some plan)
    (typed : ScopedPorts.PlanTyped operations.erase.ports world contract.closeEffects plan) :
    let restored := (closeControl caller plan).append
      (.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail)))
    ∃ nextDemand,
      RawStep ⟨.discard binder, caller, front.append (.live owner inputType answerType capture savedCaller tail)⟩
        ⟨.unit, caller, restored⟩ [.close closeId] [.ticket owner] ∧
      State operations policy contracts tables families actions annotations world outward outside caller
        .unit restored output nextDemand row ∧
      demand = owner :: nextDemand ∧
      (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail))).Perm
        (owner :: ownedTickets restored) ∧
      OwnerPhaseTransitions.Trace
        (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail))))
        [owner] (OwnerPhaseTransitions.available (ownedTickets restored)) := by
  cases state with
  | checked current scopeTyped pending closing templates bound declarations contextual retained unique evaluated accepted accounting =>
    cases current with
    | discard actualKnown actualResolved permission unprotected admitted =>
      cases Option.some.inj (actualResolved.symm.trans resolved)
      cases Option.some.inj (actualKnown.symm.trans known)
      rename_i allowed ticket pendingDemand pendingRequirements resumes receiving disposals
      obtain ⟨closingRow, pendingRow, currentCheck, pendingCheck, rowSame⟩ :=
        RecursiveRequirements.checked_sequence_parts evaluated
      have invocation := RecursiveRequirements.checked_prepend_iff.mp currentCheck
      simp only [List.append_nil] at invocation
      have action : ∃ rights, actions owner = some rights := by
        obtain ⟨after, checked, retained⟩ := SourceDependencySchemes.checked_dispose contextual
        cases SourceDependencyCapture.check_dispose_iff.mp checked with
        | checked located known permission ready unprotected closes => exact ⟨_, known⟩
      obtain ⟨rights, actionKnown⟩ := action
      obtain ⟨closingScope, waitingScope, raw, closingRequirements, combined, remaining, remainingDisposals,
        step, demandSame, recorded, template, scheduled, selectedCheck, nextPending, nextBound,
        nextRetained, nextLayout, nextTemplates, nextUnique, owners, phases, checkedCombined, evaluation⟩ :=
        SourceDependencySchemes.Closing.recompose pending templates bound contextual closing invocation
          known actionKnown built typed admitted ⟨_, scopeTyped⟩ resolved unique (closeId := closeId)
      have nextCheck := checkedCombined pendingRow (by simpa only [demandSame] using pendingCheck)
      have nextDeclarations : SourceDependencySchemes.Stored.Forest outward families
          ((closeControl caller plan).append
            (.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail)))) := by
        obtain ⟨frontDeclarations, liveDeclarations⟩ := SourceDependencySchemes.Stored.Forest.append_iff.mp declarations
        cases liveDeclarations with
        | live saved outside =>
          exact SourceDependencySchemes.Stored.Forest.append_iff.mpr
            ⟨SourceDependencySchemes.Stored.Forest.close_control plan,
              .push .closing (SourceDependencySchemes.Stored.Forest.append_iff.mpr ⟨frontDeclarations, .spent outside⟩)⟩
      refine ⟨OwnerClosingSource.retirements plan ++ pendingDemand, step, ?_, ?_, owners, phases⟩
      · rw [rowSame]
        refine State.checked (current := Expression.unit) scopeTyped nextPending nextLayout nextTemplates
          nextBound nextDeclarations SourceDependencyChecks.Local.pure nextRetained nextUnique ?_
          (rowSame ▸ accepted) rfl
        have checked := RecursiveRequirements.Checked.sequence
          (before := OwnerPhaseTransitions.available (ownedTickets ((closeControl caller plan).append
            (.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail))))))
          (a := (Requirements.request [] []).prepend (OwnerPhases.ofStack tables
            ((closeControl caller plan).append (.push (.closing closeId caller)
              (front.append (.spent owner answerType savedCaller tail)))))) (firstRow := [])
          (RecursiveRequirements.checked_prepend_iff.mpr (.request (by
            simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty]))) nextCheck
        simpa only [List.nil_append] using checked
      · simp only [accounting, demandSame, List.cons_append]

/-- A supported disposing cut constructs the whole enriched successor from the
same source state. Closing-budget success and internal owner use are derived;
resource support and fresh registry names remain explicit at this layer. -/
theorem capture_preserves
    (state : State operations policy contracts tables families actions annotations world [] outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered) (disposes : offered.dispose = true)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase)) :
    ∃ (contract : SourceDependencyAnnotations.Contract) (capturedScope : SourceDependencyCapture.Scope)
      (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      State operations policy (contracts.insert owner contract) tables families (actions.insert owner code.requiredActions)
        (fun other => if other = owner then some capturedScope else annotations other) world [] outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.port) handler.answer capture handler.scope tail⟩ ∧
      (∀ record : CoherentSourceTypes.Owners.Record, record.annotation = contract.erase →
        Nonempty (DeclaredClosingInvariant.Certificate operations.erase.ports world record capture)) ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  cases state with
  | checked current scopeTyped pending closing templates bound certificates contextual retained unique evaluated accepted accounting =>
    rename_i allowed input currentDemand currentRequirements dependencies ticket pendingDemand pendingRequirements resumes receiving disposals
    have originalCurrent := current
    generalize encoded : Instantiation.freezeEffect requested = syntaxEffect at current
    cases current with
    | perform operationKnown admitted operandSource formed =>
      cases freeze_effect_injective encoded
      have payload := SourceDependencyAnnotations.Values.summary operandSource isValue
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase operandSource)) isValue
      cases empty
      have closed := ScopedPorts.typed_value_closed
        ((DeclaredSourceValues.erase (SourceDependencyFrames.value_erase payload)).ports .none) isValue
      have requestContextual := (SourceDependencySchemes.checked_sequence.mp contextual).2
      have internal := SourceDependencySchemes.capture_internal_uses cut pending requestContextual found disposes
      obtain ⟨requestRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ :=
        RecursiveRequirements.checked_sequence_parts evaluated
      have requestExport := RecursiveRequirements.checked_complete
        (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
      rw [RecursiveDispatch.request_evaluation
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase originalCurrent)) isValue] at requestExport
      have requestCheck : RecursiveRequirements.Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole)
          (OwnerPhaseTransitions.available (ownedTickets whole))
          (.request [] [⟨requested, operation, false⟩]) requestRow :=
        RecursiveRequirements.evaluate_sound (by
          simpa only [RecursiveContexts.evaluate_request, List.nil_append, List.append_nil] using requestExport)
      have available := RecursiveDispatch.cut_residual cut (by
        simpa only [List.append_nil, OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] using requestExport)
      obtain ⟨actualOffer, offeredRow, actualFound, mode, rowKnown, exported⟩ := available
      cases Option.some.inj (actualFound.symm.trans found)
      simp only [Bool.false_or] at rowKnown
      have capabilities : ClausesUse policy handler.clauses := by
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
          capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
          SourceDependencyFrames.capture_segments cut pending
        cases frame with
        | handler scope annotation clauses coverage unique declarations capabilities modes => exact capabilities
      obtain ⟨plan, closingRequirements, capturedScope, built, typedPlan, template, budget, owners⟩ :=
        SourceDependencySchemes.closed_capture_budget cut pending requestContextual found disposes supported
          (outside := outside) (budget := row)
      obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
        resumeEffects, closeEffects, family, captureRow, tailRow, closingRaw, closeReq,
        raw, owned, nextUnique, scopeSame, demandSame, clauseContextual, nextRetained, nextCertificates,
        pendingRowSame, savedCheck, tailCheck, balanced, sourceParts⟩ :=
        SourceDependencySchemes.allocate_capture_source cut pending certificates requestContextual retained
          selected found rowKnown operationKnown payload closed freshContract freshAction closing templates bound freshAnnotation
          built internal (by simpa only [OwnerPhaseTransitions.spendAll] using pendingCheck) unique requestCheck
          (outside := outside) (caller := scope)
      dsimp only at sourceParts
      obtain ⟨body, nextPending, nextBound, nextTemplate, nextLayout, nextTemplates,
        savedAfter, tailAfter, resumeCheck, disposeCheck, clauseReady⟩ := sourceParts
      obtain ⟨clauseDemand, clauseRequirements, clauseRow, expression, clauseCheck, covered⟩ :=
        clauseReady (fun _ => nextTemplate.closed_budget typedPlan)
      let contract : SourceDependencyAnnotations.Contract := ⟨input, answer, capScope.held,
        capDemand, captureRow, OwnerClosingSource.retirements plan,
        RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
          (OwnerPhaseTransitions.available (ownedTickets whole)) closeReq, resumeEffects, closeEffects⟩
      have known : (contracts.insert owner contract) owner = some contract := by simp [SourceDependencyAnnotations.Contracts.insert]
      have erasedKnown := SourceDependencyAnnotations.contract_erase_known known
      have payloadUsage := SourceOwnerClosure.expression_usage
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase payload)) rfl
      have clauseUsage := ScopedExpressions.usage_substitution
        (selected_clause_usage selected capabilities) closed.1 payloadUsage parameter
      have erasedCurrent := DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase expression)
      have completed := RecursiveClauseUsage.consuming_usage_completed erasedCurrent clauseUsage clauseCheck
      have sameDemand := RecursiveClauseOwnership.consuming_clause_balance erasedCurrent erasedKnown clauseCheck
        (by simp [OwnerPhaseTransitions.available, ownedTickets]) completed balanced
      change clauseDemand.Perm (owner :: capDemand) at sameDemand
      have freshErased : contracts.erase owner = none := by simp [SourceDependencyAnnotations.Contracts.erase, freshContract]
      have phaseSame := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.erase.port)
        cut (RecursiveCapture.fresh_unowned pending.erase.source.erase freshErased)
      have consumed := phaseSame ▸ OwnerPhaseTransitions.spend_self
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))) owner
      have afterOwner := OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedAfter) consumed
      have pendingReady : RecursiveRequirements.Checked
          (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes) ++
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closeReq⟩) :: disposals)) []
          (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available
            (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))) clauseDemand)
          (.sequence (.spent owner) tailReq) tailRow := by
        rw [PhaseRechecking.spendAll_permutation sameDemand]
        simpa only [OwnerPhaseTransitions.spendAll, phaseSame, List.nil_append] using
          (RecursiveRequirements.Checked.sequence (RecursiveRequirements.Checked.spent (receiving := []) afterOwner) tailAfter)
      have included : clauseRow ++ tailRow ⊆ row := by
        rw [sameRow, pendingRowSame, ← List.append_assoc]
        exact ScopedExpressions.append_subset covered (List.Subset.refl _)
      refine ⟨contract, capScope, _, clauseDemand ++ tailDemand, clauseRow ++ tailRow, raw, ?_, ?_, included, owned, rfl, ?_, ?_⟩
      · exact State.checked expression (.bound (CoherentSourceTypes.Owners.ports_lookup erasedKnown))
          nextPending nextLayout nextTemplates nextBound nextCertificates clauseContextual nextRetained nextUnique
          (RecursiveRequirements.Checked.sequence
            (RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using clauseCheck)) pendingReady)
          (checked_footprint_subset accepted included) rfl
      · simpa only [accounting, List.nil_append, demandSame, List.cons_append] using sameDemand.append_right tailDemand
      · intro record same
        have guard := SourceDependencyCapture.check_capture_outward_weaken
          (SourceDependencySchemes.checked_request requestContextual) (List.nil_subset record.annotation.closeEffects)
        obtain ⟨_, _, _, _, _, _, _, _, _, _, certificate, _⟩ :=
          SourceDependencyFrames.capture_certificate cut pending guard found disposes supported internal
        exact ⟨certificate⟩
      · exact ⟨_, operationKnown⟩

/-- The old runtime invariant retains resource accounting, access, name history,
completion contracts and usage. The enriched source shares its exact registry. -/
structure Run (operations : Operations) (declarations : Instantiation.DeclarationRegistry)
    (policy : Syntax.TicketPolicy) (contracts : Contracts) (registry : CoherentSourceTypes.Owners.Registry)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (annotations : Nat → Option SourceDependencyCapture.Scope) (state : NamedState)
    (output : Value) (demand : List Nat) (row : Footprint) (resultBound : CallableContracts.Contract) : Prop where
  coherent : contracts.erase = registry.contracts
  current : DeclaredExecution.Valid operations.erase declarations policy registry tables [] [] state output.erase demand row resultBound
  annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ state.execution.issued
  actions : ∃ tickets,
    ConfigurationUsage policy tickets state.execution.configuration ∧
    UsageRegistryHistory tickets state.execution.issued ∧
    State operations policy contracts tables families tickets annotations (ScopedTyping.resourceWorld state.execution.issued)
      [] [] state.execution.configuration.scope state.execution.configuration.expression
      state.execution.configuration.stack output demand row ∧
    DeclaredClosingInvariant.Retained operations.erase.ports (ScopedTyping.resourceWorld state.execution.issued)
      registry tickets state.execution.configuration.stack

theorem Run.erase
    (run : Run operations declarations policy contracts registry tables families annotations state output demand row resultBound) :
    DeclaredConnectedSources.Run operations.erase declarations policy registry tables state output.erase demand row resultBound := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  exact ⟨run.current, actions, usage, history, run.coherent ▸ source.erase, retained⟩

theorem initial_run
    (source : Expression operations policy (fun _ => none) [] [] .none Environment.empty code output demand requirements dependencies)
    (contextual : Checked [] (fun _ => none) (OwnerPhaseTransitions.available []) [] dependencies .nil)
    (evaluated : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : checkFootprint [] row = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code resultBound)
    (signature : operations.erase.ports = DeclarationResults.signature declarations)
    (support : decide (Syntax.resourceDependencies code.dependencies = []) = true) :
    demand = [] ∧ Run operations declarations policy (fun _ => none) (fun _ => none) tables families (fun _ => none)
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ output [] row resultBound := by
  obtain ⟨empty, existing⟩ := DeclaredConnectedSources.initial_run
    (SourceDependencyAnnotations.expression_erase source) evaluated accepted result signature support (tables := tables)
  obtain ⟨actions, usage, history, oldSource, retained⟩ := existing.actions
  have permissions : Syntax.UsageExtension (fun _ => none) actions := by intro owner rights known; cases known
  have checked := SourceDependencySchemes.local_transport contextual (fun _ ready => ready) permissions (List.Subset.refl _)
  exact ⟨empty, rfl, existing.current, (by intro owner captured known; cases known), actions, usage, history,
    empty ▸ initial source empty checked evaluated accepted, retained⟩

/-- Reuse the established runtime assembly for a transition that allocates no
continuation. The enriched source and retained certificates use the same action
map, actual successor and resource world as the runtime invariant. -/
theorem assemble_entry
    (coherent : contracts.erase = registry.contracts)
    (current : DeclaredExecution.Valid operations.erase declarations policy registry tables [] [] before output.erase demand row resultBound)
    (raw : RawStep before.execution.configuration after created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup)
    (checks : AccessChecks before.execution.configuration [])
    (usage : ConfigurationUsage policy actions before.execution.configuration)
    (history : UsageRegistryHistory actions before.execution.issued)
    (annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ before.execution.issued)
    (retained : DeclaredClosingInvariant.Retained operations.erase.ports (ScopedTyping.resourceWorld before.execution.issued)
      registry actions before.execution.configuration.stack)
    (source : State operations policy contracts nextTables families (ScopedActionUsage.advance actions after created)
      annotations (ScopedTyping.resourceWorld (before.execution.issued ++ created)) [] []
      after.scope after.expression after.stack output nextDemand nextRow)
    (results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld (before.execution.issued ++ created)) after resultBound)
    (update : registry.runtime.joint.usage = advanceUsageTickets policy registry.runtime.joint.usage after created)
    (noTickets : ∀ owner, Owner.ticket owner ∉ created) :
    Run operations declarations policy contracts registry nextTables families annotations
      (ScopedPortJoint.advanceState before after created discharged) output nextDemand nextRow resultBound := by
  have existing := DeclaredConnectedSources.assemble_entry current raw freshOwners freshHandlers checks usage history
    retained (coherent ▸ source.erase) results update noTickets
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners checks
  have extension := ScopedActionUsage.advance_extends (after := after) usageChecks.allocation
  have unique : (ownedTickets after.stack).Nodup := by
    cases source with
    | checked _ _ _ _ _ _ _ _ _ unique _ _ _ => exact unique
  have larger : ScopedTyping.resourceWorld before.execution.issued ⊆
      ScopedTyping.resourceWorld (before.execution.issued ++ created) := by
    rw [ScopedTyping.resource_world_append]
    exact List.subset_append_left _ _
  exact ⟨coherent, existing.current,
    (fun owner captured known => List.mem_append_left _ (annotationHistory owner captured known)),
    _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
    ScopedActionUsage.raw_step_preserves_history raw history, source,
    DeclaredClosingInvariant.raw_step_preserves_retained raw retained (fun _ _ known => known)
      extension larger (.none noTickets) unique⟩

/-- Every actual access-checked disposal preserves the shared source/runtime
invariant. Its typed plan comes from the retained certificate, and the existing
completion proof supplies the result contract for the same successor. -/
theorem Run.discard_preserves
    (run : Run operations declarations policy contracts registry tables families annotations
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ output demand row resultBound)
    (step : NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after) :
    ∃ owner remaining,
      Run operations declarations policy contracts registry tables families annotations after output remaining row resultBound ∧
      demand = owner :: remaining := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  cases step with
  | mk execution access => cases execution with
    | event after created discharged raw freshOwners freshHandlers =>
      have actual := raw
      cases raw with
      | focus plain focus tail => cases focus
      | plug plain value impossible scope tail => cases impossible.1
      | leaveHandler handler value impossible scope tail => cases impossible.1
      | leaveCell identity payload answer savedScope scope value impossible tail => cases impossible.1
      | startCleanup action saved impossible scope tail => cases impossible.1
      | leaveClause ticket answer value impossible scope caller tail => cases impossible.1
      | discard binder owner identity scope caller input answer front capture tail plan resolved built =>
        obtain ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ := usage
        obtain ⟨actualOwner, rights, actionKnown, actualResolved, _, permitted⟩ :=
          ScopedActionUsage.discard_requires_action code
        have sameOwner := Option.some.inj (actualResolved.symm.trans resolved)
        subst actualOwner
        obtain ⟨record, savedRights, known, savedKnown, checked⟩ :=
          retained owner capture (RecursiveRecords.located_below front .here)
        have sameRights := Option.some.inj (actionKnown.symm.trans savedKnown)
        obtain ⟨certificate⟩ := checked (sameRights ▸ permitted)
        have samePlan := Option.some.inj (certificate.built.symm.trans built)
        have erasedKnown : contracts.erase owner = some record.annotation := by
          rw [run.coherent]
          simp [CoherentSourceTypes.Owners.Registry.contracts, known]
        obtain ⟨contract, contractKnown, contractSame⟩ := Option.map_eq_some_iff.mp erasedKnown
        have effectsSame := congrArg CoherentSourceTypes.Owners.Contract.closeEffects contractSame
        change contract.closeEffects = record.annotation.closeEffects at effectsSame
        have typed : ScopedPorts.PlanTyped operations.erase.ports (ScopedTyping.resourceWorld issued) contract.closeEffects plan := by
          rw [effectsSame]
          exact samePlan ▸ certificate.typed
        obtain ⟨remaining, _, successor, accounting, _, _⟩ :=
          SourceDependencyState.discard_preserves source contractKnown resolved built typed (closeId := identity)
        have results := (CompletionFrames.discard_step resolved built run.current.results (closeId := identity)).2
        have joined := assemble_entry run.coherent run.current actual freshOwners freshHandlers access
          ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ history run.annotationHistory retained
          (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld,
            ScopedActionUsage.advance] using successor)
          (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results) rfl (by simp)
        exact ⟨owner, remaining, joined, accounting⟩

/-- Source capture, coherent completion records and independent runtime
preservation describe the same allocated owner and actual successor. Name
history supplies all registry freshness; resource support follows from the
existing ledger and access invariant, and source bounds supply internal owner use. -/
theorem Run.capture_preserves
    (run : Run operations declarations policy contracts registry tables families annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ output demand row resultBound)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered) (disposes : offered.dispose = true)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (contract : SourceDependencyAnnotations.Contract) (record : CoherentSourceTypes.Owners.Record)
      (capturedScope : SourceDependencyCapture.Scope) (after : Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      record.annotation = contract.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] []) ∧
      Run operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families (fun other => if other = owner then some capturedScope else annotations other)
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] []) output nextDemand nextRow resultBound ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  have supported := capture_resource_support cut run.current.support.control (ledger_unique_live run.current.ledger)
  have checks := DeclaredExecution.request_access_checks run.current
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners checks
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
    have erased : contracts.erase owner = none := by
      rw [run.coherent]
      simp [CoherentSourceTypes.Owners.Registry.contracts, fresh]
    simpa only [SourceDependencyAnnotations.Contracts.erase, Option.map_eq_none_iff] using erased
  obtain ⟨contract, capturedScope, after, nextDemand, nextRow,
    raw, nextSource, balance, included, owners, shape, certificate, sourceInput⟩ :=
    SourceDependencyState.capture_preserves source cut isValue selected found disposes freshContract
      (usageChecks.allocation owner (by simp)) freshAnnotation supported
  obtain ⟨record, resultBinder, annotation, actualScope, permissions, results, sourceExtension, runtimeExtension⟩ :=
    DeclaredCompletionAdmission.coherent_capture_record (contract := contract.erase)
      run.current.source run.current.results run.current.signature fresh raw
      (by obtain ⟨argument, known⟩ := sourceInput; exact ⟨argument.erase, SourceDependencyAnnotations.operation_erase known⟩)
  have coherent : (contracts.insert owner contract).erase = (registry.insert owner record).contracts := by
    rw [SourceDependencyAnnotations.contracts_erase_insert, CoherentSourceTypes.Owners.registry_insert_contracts,
      annotation, run.coherent]
  have freshHandlers : (activations ++ enteredActivations
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after).Nodup := by
    simpa [enteredActivations] using run.current.names.unique
  have update : (registry.insert owner record).runtime.joint.usage =
      advanceUsageTickets policy registry.runtime.joint.usage after [.ticket owner] := by
    rw [CoherentSourceTypes.Owners.registry_insert_runtime, CallableJoint.joint_insert, ScopedPortJoint.usage_insert]
    simp only [advanceUsageTickets, actualScope, permissions]
  have current := DeclaredExecution.assemble_event run.current raw freshOwners freshHandlers checks
    (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld, coherent]
          using DeclaredSourceInterfaces.source nextSource.erase.shared)
    (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results) update
  have unique : (ownedTickets after.stack).Nodup := by
    cases nextSource with
    | checked _ _ _ _ _ _ _ _ _ unique _ _ _ => exact unique
  have allocation : DeclaredClosingInvariant.Allocation operations.erase.ports (ScopedTyping.resourceWorld issued)
      (registry.insert owner record) (ScopedActionUsage.advance actions after [.ticket owner]) [.ticket owner] after.stack := by
    rw [shape]
    exact DeclaredClosingInvariant.capture_allocation
      (by simp [CoherentSourceTypes.Owners.Registry.insert]) isValue (fun _ => certificate record annotation)
  have nextRetained := DeclaredClosingInvariant.raw_step_preserves_retained raw retained
    (nextRegistry := registry.insert owner record)
    (by
      intro old previous known
      by_cases same : old = owner
      · subst old; rw [fresh] at known; cases known
      · simp [CoherentSourceTypes.Owners.Registry.insert, same, known])
    (ScopedActionUsage.advance_extends usageChecks.allocation) (List.Subset.refl _) allocation unique
  refine ⟨contract, record, capturedScope, after, nextDemand, nextRow, annotation,
    ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    ⟨coherent, current, ?_, _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
      ScopedActionUsage.raw_step_preserves_history raw history, ?_, ?_⟩, balance, included, owners⟩
  · intro other saved known
    by_cases same : other = owner
    · subst other; simp [ScopedPortJoint.advanceState]
    · have old : annotations other = some saved := by simpa only [if_neg same] using known
      exact List.mem_append_left _ (run.annotationHistory other saved old)
  · simpa [ScopedPortJoint.advanceState, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld,
      List.append_nil, ScopedActionUsage.advance, shape, Code.substitution_required_actions code parameter isValue] using nextSource
  · simpa [ScopedPortJoint.advanceState, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld,
      List.append_nil] using nextRetained

/-- The existing finite name ledger chooses an owner. The strengthened runtime
invariant supplies annotation freshness for that same choice. -/
theorem Run.capture_progress
    (run : Run operations declarations policy contracts registry tables families annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ output demand row resultBound)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered) (disposes : offered.dispose = true) :
    ∃ (owner : Nat) (contract : SourceDependencyAnnotations.Contract) (record : CoherentSourceTypes.Owners.Record)
      (capturedScope : SourceDependencyCapture.Scope) (after : Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      record.annotation = contract.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] []) ∧
      Run operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families (fun other => if other = owner then some capturedScope else annotations other)
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] []) output nextDemand nextRow resultBound ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) run.current.ledger.2
  exact ⟨owner, run.capture_preserves cut isValue selected found disposes fresh⟩

/-- Structural retained evidence supplies the disposal step; preservation
retains the enriched source rather than only its erased runtime judgment. -/
theorem Run.discard_progress
    (run : Run operations declarations policy contracts registry tables families annotations
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ output demand row resultBound) :
    ∃ after owner remaining,
      NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Run operations declarations policy contracts registry tables families annotations after output remaining row resultBound ∧
      demand = owner :: remaining := by
  obtain ⟨after, _, _, step, _, _⟩ := DeclaredClosingInvariant.discard_progress run.erase.shared.prepared
  obtain ⟨owner, remaining, successor, accounting⟩ := run.discard_preserves step
  exact ⟨after, owner, remaining, step, successor, accounting⟩

end Ash.OneShot.SourceDependencyState

#print axioms Ash.OneShot.SourceDependencyState.State.erase
#print axioms Ash.OneShot.SourceDependencyState.initial
#print axioms Ash.OneShot.SourceDependencyState.replace_current
#print axioms Ash.OneShot.SourceDependencyState.bind_preserves
#print axioms Ash.OneShot.SourceDependencyState.beta_preserves
#print axioms Ash.OneShot.SourceDependencyState.Run.erase
#print axioms Ash.OneShot.SourceDependencyState.initial_run

#print axioms Ash.OneShot.SourceDependencyState.discard_preserves
#print axioms Ash.OneShot.SourceDependencyState.capture_preserves
#print axioms Ash.OneShot.SourceDependencyState.assemble_entry
#print axioms Ash.OneShot.SourceDependencyState.Run.discard_preserves
#print axioms Ash.OneShot.SourceDependencyState.Run.discard_progress
#print axioms Ash.OneShot.SourceDependencyState.Run.capture_preserves
#print axioms Ash.OneShot.SourceDependencyState.Run.capture_progress
#print axioms Ash.OneShot.SourceDependencyState.supported_restrict
#print axioms Ash.OneShot.SourceDependencyState.supported_outside_interface
#print axioms Ash.OneShot.SourceDependencyState.capture_resource_support
