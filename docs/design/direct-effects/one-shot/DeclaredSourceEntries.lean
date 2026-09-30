import DeclaredSourceStates
import RecursiveEntries

/-! Cleanup and resource installation retain hereditary source and frame
judgments. Existing finite-check freshness and local discharge proofs apply
without changing the evaluation or resource-world semantics. -/
namespace Ash.OneShot.DeclaredSourceEntries
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSources (Expression)
open DeclaredSourceFrames (Segment)
open DeclaredSourceStates (CheckedState)
open DeclaredSourceClosing (Records)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (available spendAll)
open RecursiveEntries (armed_context)
open RecursiveHandlerTables (register register_agrees context_congr registered_lookup checked_activation)
open DeclaredSourceClosing (records_congr)

theorem cleanup_parts
    (source : Expression operations policy contracts world allowed scope environment
      (.cleanup callback body) output demand requirements)
    (isValue : callback.IsValue) :
    ∃ requests latent, ∃ bodyRequirements : Requirements demand,
      DeclaredSourceValues.ValueSummary operations policy contracts world environment [] callback (.function .unit .unit requests latent) ∧
      Expression operations policy contracts world allowed scope environment body output demand bodyRequirements ∧
      requests ⊆ allowed ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before bodyRequirements)
          (OwnerSource.exportAt receiving (spendAll before demand) (qualify true latent)) := by
  cases source with
  | stable summary => cases summary with
    | cleanup callback body admitted =>
        have empty := value_row callback isValue
        subst_vars
        refine ⟨_, _, _, DeclaredSourceValues.from_legacy (value_allowed callback isValue []), .stable body, admitted, ?_⟩
        intros
        simp only [List.nil_append, RecursiveContexts.evaluate_request, spendAll, RecursiveContexts.export_rows]
  | callable summary => cases summary with
    | summaryCleanup callback body admitted =>
        have empty := CallableSources.value_row callback.to_generic isValue
        subst_vars
        refine ⟨_, _, _, DeclaredSourceValues.change_allowed callback isValue [], .callable body, admitted, ?_⟩
        intros
        simp only [List.nil_append, RecursiveContexts.evaluate_request, spendAll, RecursiveContexts.export_rows]
  | cleanup callback body admitted =>
      have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase callback) isValue
      subst_vars
      refine ⟨_, _, _, DeclaredSourceValues.change_allowed (DeclaredSourceValues.value_summary callback isValue) isValue [], body, admitted, ?_⟩
      intros
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase callback) isValue, spendAll, List.nil_append,
        RecursiveRecomposition.merge_empty_left]

theorem cleanup_preserves
    (source : CheckedState operations policy contracts tables world outside scope
      (.cleanup callback body) stack output demand row)
    (isValue : callback.IsValue) (identity : Nat) :
    ∃ action : ActionData,
      action.identity = identity ∧
      RawStep ⟨.cleanup callback body, scope, stack⟩
        ⟨body, scope, .push (.armed action) stack⟩ [.cleanup identity] [] ∧
      CheckedState operations policy contracts tables world outside scope body
        (.push (.armed action) stack) output demand row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets stack)) []
        (available (ownedTickets (.push (.armed action) stack))) := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements
        obtain ⟨requests, latent, bodyRequirements, callbackSource, bodySource, admitted, evaluation⟩ := cleanup_parts current isValue
        have closed := ScopedPorts.typed_value_closed ((DeclaredSourceValues.erase callbackSource).ports .none) isValue
        let action : ActionData := ⟨identity, callback, closed, scope, ScopedPorts.embedPort input.port, requests⟩
        have frame : DeclaredSourceFrames.Frame operations policy contracts tables world (.armed action) input input []
            (.request [] (qualify true latent)) :=
          .armed ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩ callbackSource (by simp [action])
        refine ⟨action, rfl, .enterCleanup action body stack, ?_, .nil⟩
        apply DeclaredSourceStates.check_state (.checked bodySource scopeTyped (DeclaredSourceFrames.push frame pending)) (.push closing) unique _ accepted
        have original := RecursiveRequirements.checked_complete checked
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          List.append_nil] at original
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          RecursiveContexts.evaluate_request, armed_context, List.append_nil,
          RecursiveContexts.evaluate_plain, ownedTickets, spendAll]
        simpa only [merge_assoc] using original

/-- Value initialization exposes a uniformly discharged body requirement.
    The opened body may consume an enclosing continuation. -/
theorem resource_parts
    (source : Expression operations policy contracts world allowed scope environment
      (.resource binder initializer body) output demand requirements)
    (isValue : initializer.IsValue) :
    ∃ payload, ∃ outward : Requirements demand,
      initializer = .integer payload ∧
      (∀ identity, identity ∉ world → ∃ requests, ∃ opened : Requirements demand,
        Expression operations policy contracts (world ++ [identity]) requests scope environment
          (body.instantiate (Instantiation.Environment.empty.bind binder identity)) output demand opened ∧
        ResourceRequirements.Hides identity opened outward ∧ identity ∉ output.port.resources ∧
        requests ⊆ .cell identity :: allowed) ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        evaluate store receiving before outward := by
  cases source with
  | stable summary => cases summary with
    | resource initial opened formed effectsBound admitted outward =>
        rename_i initialRow residual raw bodyRow
        obtain ⟨payload, same⟩ := ScopedPorts.typed_integer_value (port_typing initial .none) isValue
        have empty := value_row initial isValue
        refine ⟨payload, .request [] raw, same, ?_, ?_⟩
        · intro identity fresh
          refine ⟨_, _, .stable (opened identity fresh), ?_, fun member => fresh (formed member),
            List.cons_subset_cons _ admitted⟩
          rw [← outward identity fresh]
          exact .request
        · intros
          simp only [empty, List.nil_append]
  | callable summary => cases summary with
    | summaryResource initial opened formed effectsBound admitted outward =>
        rename_i initialRow residual raw bodyRow
        obtain ⟨payload, same⟩ := ScopedPorts.typed_integer_value ((DeclaredSourceValues.erase (CallableSources.value_row initial.to_generic isValue ▸ initial)).ports .none) isValue
        have empty := CallableSources.value_row initial.to_generic isValue
        refine ⟨payload, .request [] raw, same, ?_, ?_⟩
        · intro identity fresh
          refine ⟨_, _, .callable (opened identity fresh), ?_, fun member => fresh (formed member),
            List.cons_subset_cons _ admitted⟩
          rw [← outward identity fresh]
          exact .request
        · intros
          simp only [empty, List.nil_append]
  | resource initial opened formed effectsBound admitted outward =>
      have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase initial) isValue
      subst demand
      rename_i residual raw bodyRow requirements
      obtain ⟨payload, same⟩ := ScopedPorts.typed_integer_value
        ((DeclaredSourceValues.erase (DeclaredSourceValues.value_summary initial isValue)).ports .none) isValue
      refine ⟨payload, .request [] raw, same, ?_, ?_⟩
      · intro identity fresh
        refine ⟨_, _, .callable (opened identity fresh), ?_, fun member => fresh (formed member),
          List.cons_subset_cons _ admitted⟩
        rw [← outward identity fresh]
        exact .request
      · intros
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase initial) isValue,
          spendAll, RecursiveRecomposition.merge_empty_left, RecursiveContexts.evaluate_request, List.nil_append]
  | scopedResource initial opened formed effectsBound admitted hidden =>
      have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase initial) isValue
      subst_vars
      rename_i bodyDemand residual outward bodyRequirements initialRequirements
      obtain ⟨payload, same⟩ := ScopedPorts.typed_integer_value
        ((DeclaredSourceValues.erase (DeclaredSourceValues.value_summary initial isValue)).ports .none) isValue
      refine ⟨payload, outward, same, ?_, ?_⟩
      · intro identity fresh
        exact ⟨_, _, opened identity fresh, hidden identity fresh, fun member => fresh (formed member),
          List.cons_subset_cons _ admitted⟩
      · intros
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase initial) isValue,
          spendAll, RecursiveRecomposition.merge_empty_left]

/-- Freshness excludes the finite demands observed by the existing recursive
    check. No separate successor admission or continuation capability is supplied. -/
theorem resource_preserves
    (source : CheckedState operations policy contracts tables world outside scope
      (.resource binder initializer body) stack output demand row)
    (isValue : initializer.IsValue) :
    ∃ identity payload answer,
      identity ∉ world ∧ initializer = .integer payload ∧
      RawStep ⟨.resource binder initializer body, scope, stack⟩
        ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack⟩ [.resource identity] [] ∧
      CheckedState operations policy contracts tables (world ++ [identity]) outside scope
        (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) output demand row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets stack)) []
        (available (ownedTickets (.push (.cell identity payload scope answer) stack))) := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements
        obtain ⟨payload, outward, same, openings, evaluation⟩ := resource_parts current isValue
        subst initializer
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ :=
          RecursiveRequirements.checked_sequence_parts checked
        have currentAt := RecursiveRequirements.checked_prepend_iff.mp currentCheck
        simp only [List.append_nil] at currentAt
        have outwardCheck := RecursiveRequirements.evaluate_sound ((evaluation _ _ _).symm.trans
          (RecursiveRequirements.checked_complete currentAt))
        obtain ⟨forbidden, preserved⟩ := ResourceRequirements.checked_open_resource outwardCheck
        obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name (world ++ forbidden)
        have freshWorld : identity ∉ world := fun member => fresh (List.mem_append_left _ member)
        obtain ⟨requests, opened, bodySource, hidden, noEscape, admitted⟩ := openings identity freshWorld
        have bodyChecked := preserved identity (fun member => fresh (List.mem_append_right _ member)) opened hidden
        let answer := ScopedPorts.embedPort input.port
        have frame : DeclaredSourceFrames.Frame operations policy contracts tables (world ++ [identity])
            (.cell identity payload scope answer) input input [] (.request [] []) :=
          .cell ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩
            (by simpa only [answer, ScopedPorts.erase_embed_port] using noEscape)
            (by simp only [answer, ScopedPorts.erase_embed_port])
        have ready := ScopedPorts.typed_resource_closed (SourceTemplates.expression_ports (DeclaredSources.expression_erase current) scopeTyped)
        refine ⟨identity, payload, answer, freshWorld, rfl,
          .enterCell binder identity payload body scope answer stack ready, ?_, .nil⟩
        apply DeclaredSourceStates.check_state
          (.checked bodySource scopeTyped (DeclaredSourceFrames.push frame
            (DeclaredSourceFrames.segment_world_weaken pending (List.subset_append_left _ _))))
          (.push (DeclaredSourceClosing.records_world_weaken closing (List.subset_append_left _ _))) unique _ accepted
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          OwnerPhases.ofStack, OwnerPhases.frameEntry, List.append_nil,
          RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, ownedTickets, spendAll]
        rw [RecursiveRequirements.checked_complete bodyChecked, RecursiveRequirements.checked_complete pendingCheck]
        rfl


theorem handler_entry_with_frame
    (body : Expression operations policy contracts world (effect :: residual) scope Environment.empty
      code answer bodyDemand bodyRequirements)
    (declarations : DeclaredSources.Declarations operations policy contracts world Environment.empty residual
      effect answer clauses table)
    (capabilities : ClausesUse policy clauses)
    (modes : SourceTemplates.ClauseModes clauses table)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (clausesTyped : ScopedPorts.ClausesTyped operations.ports world ScopedPorts.TypeEnv.empty effect answer.port residual clauses)
    (coverage : ScopedPorts.Covers operations.ports effect clauses)
    (clauseUnique : (ScopedTyping.clauseKeys clauses).Nodup)
    (pending : Segment operations policy contracts tables world stack answer output tailDemand tailRequirements resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (bodyCheck : Checked (resumes ++ disposals)
      (.ordinary (.handler effect 0 table) :: OwnerPhases.ofStack tables stack)
      (OwnerPhaseTransitions.available (ownedTickets stack)) bodyRequirements bodyRow)
    (tailCheck : Checked (resumes ++ disposals) []
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack)) bodyDemand) tailRequirements tailRow)
    (accepted : checkFootprint outside (bodyRow ++ tailRow) = true)
    (retained : stack.erase.activations ⊆ history) :
    ∃ handler : HandlerData, handler.activation ∉ history ∧
      register tables handler.activation table handler = table ∧
      RawStep ⟨.handle (Instantiation.freezeEffect effect) code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      CheckedState operations policy contracts (register tables handler.activation table) world outside scope
        code (.push (.handler handler) stack) output (bodyDemand ++ tailDemand) (bodyRow ++ tailRow) ∧
      ownedTickets (.push (.handler handler) stack) = ownedTickets stack ∧
      handler.clauses = clauses ∧ handler.effectInst = effect ∧
      DeclaredSourceFrames.Frame operations policy contracts (register tables handler.activation table) world (.handler handler) answer answer [] (.request [] []) := by
  obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name history
  let handler : HandlerData := ⟨activation, effect, clauses, scope, ScopedPorts.embedPort answer.port,
    ScopedPorts.clauses_have_ticket_barrier clausesTyped⟩
  let next := register tables activation table
  have agree : ∀ actual, actual.activation ∈ stack.erase.activations → tables actual = next actual :=
    register_agrees (fun member => fresh (retained member))
  have sameContext := context_congr agree
  have installed : next handler = table := registered_lookup rfl
  have sameOwners : ownedTickets (.push (.handler handler) stack) = ownedTickets stack := rfl
  have frame : DeclaredSourceFrames.Frame operations policy contracts (register tables handler.activation table) world (.handler handler) answer answer [] (.request [] []) :=
    .handler (.handler (ScopedPorts.effect_scope_has_types scopeTyped |> fun known => ⟨_, known⟩)
      (by simpa only [handler, ScopedPorts.erase_embed_port] using clausesTyped) coverage clauseUnique)
      (by simp only [handler, ScopedPorts.erase_embed_port])
      (by
        change DeclaredSources.Declarations operations policy contracts world Environment.empty residual effect answer clauses (next handler)
        rw [installed]
        exact declarations) capabilities (by
        change SourceTemplates.ClauseModes clauses (next handler)
        rw [installed]
        exact modes)
  have source := DeclaredSourceFrames.push frame (DeclaredSourceFrames.segment_tables_congr pending agree)
  have current : Checked (resumes ++ disposals) (OwnerPhases.ofStack next (.push (.handler handler) stack))
      (OwnerPhaseTransitions.available (ownedTickets stack)) bodyRequirements bodyRow := by
    have relocated := checked_activation bodyCheck (front := []) (tail := OwnerPhases.ofStack tables stack) (second := activation) rfl
    simpa only [List.nil_append, OwnerPhases.ofStack, OwnerPhases.frameEntry, installed, handler, sameContext] using relocated
  have afterBody : Checked (resumes ++ disposals) []
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack)) bodyDemand)
      (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack next stack)) tailRequirements) tailRow :=
    .sequence (firstRow := []) (secondRow := tailRow)
      (.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) tailCheck
  have prefixed : Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
      (bodyRequirements.prepend (OwnerPhases.ofStack next (.push (.handler handler) stack))) bodyRow :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using current)
  refine ⟨handler, fresh, installed, .enterHandler handler code stack, ?_, sameOwners, rfl, rfl, frame⟩
  exact .checked (.checked body scopeTyped source) (.push (records_congr closing)) unique
    (.sequence prefixed afterBody) accepted

theorem handler_preserves
    (source : CheckedState operations policy contracts tables world outside scope
      (.handle requested code clauses) stack output demand row)
    (retained : stack.erase.activations ⊆ history) :
    ∃ handler : HandlerData, ∃ table,
      handler.activation ∉ history ∧
      register tables handler.activation table handler = table ∧
      RawStep ⟨.handle requested code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      CheckedState operations policy contracts (register tables handler.activation table)
        world outside scope code (.push (.handler handler) stack) output demand row ∧
      ownedTickets (.push (.handler handler) stack) = ownedTickets stack := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨effect, residual, table, bodyRequirements, rfl, rfl, body, clausesTyped, capabilities,
          coverage, clauseUnique, admitted, modes, declarations⟩ := DeclaredSources.handler_parts current
        obtain ⟨bodyRow, tailRow, currentCheck, tailCheck, sameRow⟩ := RecursiveRequirements.checked_sequence_parts checked
        have bodyCheck := RecursiveRequirements.checked_prepend_iff.mp
          (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
        simp only [List.append_nil, List.cons_append, List.nil_append] at bodyCheck
        obtain ⟨handler, fresh, installed, step, successor, owners, clausesSame, effectSame, frame⟩ :=
          handler_entry_with_frame body declarations capabilities modes scopeTyped clausesTyped coverage clauseUnique pending
            closing unique bodyCheck tailCheck (sameRow ▸ accepted) retained
        exact ⟨handler, table, fresh, installed, step, sameRow.symm ▸ successor, owners⟩


end Ash.OneShot.DeclaredSourceEntries

#print axioms Ash.OneShot.DeclaredSourceEntries.cleanup_parts
#print axioms Ash.OneShot.DeclaredSourceEntries.cleanup_preserves
#print axioms Ash.OneShot.DeclaredSourceEntries.resource_parts
#print axioms Ash.OneShot.DeclaredSourceEntries.resource_preserves
#print axioms Ash.OneShot.DeclaredSourceEntries.handler_entry_with_frame
#print axioms Ash.OneShot.DeclaredSourceEntries.handler_preserves
