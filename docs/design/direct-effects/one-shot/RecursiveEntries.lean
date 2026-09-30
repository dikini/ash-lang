import RecursiveHandlerTables

/-!
Installation transitions for the state with authenticated resume and disposal
records. Cleanup installation reuses neutral-frame interpretation. Resource
installation reuses structural local discharge, finite checking freshness, and world transport.
Both derive the successor check from the existing source judgment.
-/

namespace Ash.OneShot.RecursiveEntries
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open SourceTemplates (Expression Segment)
open RecursiveRecords (Records CheckedState)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (available spendAll)

theorem cleanup_parts
    (source : Expression operations policy contracts world allowed scope environment
      (.cleanup callback body) output demand requirements)
    (isValue : callback.IsValue) :
    ∃ requests latent, ∃ bodyRequirements : Requirements demand,
      SourceTemplates.ValueSummary operations policy contracts world environment [] callback (.function .unit .unit requests latent) ∧
      Expression operations policy contracts world allowed scope environment body output demand bodyRequirements ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before bodyRequirements)
          (OwnerSource.exportAt receiving (spendAll before demand) (qualify true latent)) := by
  cases source with
  | stable summary => cases summary with
    | cleanup callback body admitted =>
        have empty := value_row callback isValue
        subst_vars
        refine ⟨_, _, _, SourceTemplates.ValueSummary.stable (value_allowed callback isValue []), .stable body, ?_⟩
        intros
        simp only [List.nil_append, RecursiveContexts.evaluate_request, spendAll, RecursiveContexts.export_rows]
  | callable summary => cases summary with
    | summaryCleanup callback body admitted =>
        have empty := CallableSources.value_row callback isValue
        subst_vars
        refine ⟨_, _, _, SourceTemplates.ValueSummary.callable (CallableSources.value_allowed callback isValue []), .callable body, ?_⟩
        intros
        simp only [List.nil_append, RecursiveContexts.evaluate_request, spendAll, RecursiveContexts.export_rows]
  | cleanup callback body admitted =>
      have empty := SourceTemplates.expression_value_demand callback isValue
      subst_vars
      refine ⟨_, _, _, (RecursiveRecomposition.value_summary callback isValue).change_allowed isValue [], body, ?_⟩
      intros
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.value_evaluation callback isValue, spendAll, List.nil_append,
        RecursiveRecomposition.merge_empty_left]

theorem armed_context (action : ActionData) :
    OwnerPhases.ofStack tables (.push (.armed action) tail) =
      .ordinary (.barrier false) :: OwnerPhases.ofStack tables tail := rfl

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
        obtain ⟨requests, latent, bodyRequirements, callbackSource, bodySource, evaluation⟩ := cleanup_parts current isValue
        have closed := ScopedPorts.typed_value_closed (callbackSource.ports .none) isValue
        let action : ActionData := ⟨identity, callback, closed, scope, ScopedPorts.embedPort input.port, requests⟩
        have frame : SourceTemplates.Frame operations policy contracts world (.armed action) input input []
            (.request [] (qualify true latent)) :=
          .armed ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩ callbackSource (by simp [action])
        refine ⟨action, rfl, .enterCleanup action body stack, ?_, .nil⟩
        apply RecursiveExecution.check_state (.checked bodySource scopeTyped (.push frame pending)) (.push closing) unique _ accepted
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
        ResourceRequirements.Hides identity opened outward ∧ identity ∉ output.port.resources) ∧
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
          refine ⟨_, _, .stable (opened identity fresh), ?_, fun member => fresh (formed member)⟩
          rw [← outward identity fresh]
          exact .request
        · intros
          simp only [empty, List.nil_append]
  | callable summary => cases summary with
    | summaryResource initial opened formed effectsBound admitted outward =>
        rename_i initialRow residual raw bodyRow
        obtain ⟨payload, same⟩ := ScopedPorts.typed_integer_value ((SourceTemplates.ValueSummary.callable (CallableSources.value_row initial isValue ▸ initial)).ports .none) isValue
        have empty := CallableSources.value_row initial isValue
        refine ⟨payload, .request [] raw, same, ?_, ?_⟩
        · intro identity fresh
          refine ⟨_, _, .callable (opened identity fresh), ?_, fun member => fresh (formed member)⟩
          rw [← outward identity fresh]
          exact .request
        · intros
          simp only [empty, List.nil_append]
  | resource initial opened formed effectsBound admitted outward =>
      have empty := SourceTemplates.expression_value_demand initial isValue
      subst demand
      rename_i residual raw bodyRow requirements
      obtain ⟨payload, same⟩ := ScopedPorts.typed_integer_value
        ((RecursiveRecomposition.value_summary initial isValue).ports .none) isValue
      refine ⟨payload, .request [] raw, same, ?_, ?_⟩
      · intro identity fresh
        refine ⟨_, _, .callable (opened identity fresh), ?_, fun member => fresh (formed member)⟩
        rw [← outward identity fresh]
        exact .request
      · intros
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRecomposition.value_evaluation initial isValue,
          spendAll, RecursiveRecomposition.merge_empty_left, RecursiveContexts.evaluate_request, List.nil_append]
  | scopedResource initial opened formed effectsBound admitted hidden =>
      have empty := SourceTemplates.expression_value_demand initial isValue
      subst_vars
      rename_i bodyDemand residual outward bodyRequirements initialRequirements
      obtain ⟨payload, same⟩ := ScopedPorts.typed_integer_value
        ((RecursiveRecomposition.value_summary initial isValue).ports .none) isValue
      refine ⟨payload, outward, same, ?_, ?_⟩
      · intro identity fresh
        exact ⟨_, _, opened identity fresh, hidden identity fresh, fun member => fresh (formed member)⟩
      · intros
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation initial isValue,
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
        obtain ⟨requests, opened, bodySource, hidden, noEscape⟩ := openings identity freshWorld
        have bodyChecked := preserved identity (fun member => fresh (List.mem_append_right _ member)) opened hidden
        let answer := ScopedPorts.embedPort input.port
        have frame : SourceTemplates.Frame operations policy contracts (world ++ [identity])
            (.cell identity payload scope answer) input input [] (.request [] []) :=
          .cell ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩
            (by simpa only [answer, ScopedPorts.erase_embed_port] using noEscape)
            (by simp only [answer, ScopedPorts.erase_embed_port])
        have ready := ScopedPorts.typed_resource_closed (SourceTemplates.expression_ports current scopeTyped)
        refine ⟨identity, payload, answer, freshWorld, rfl,
          .enterCell binder identity payload body scope answer stack ready, ?_, .nil⟩
        apply RecursiveExecution.check_state
          (.checked bodySource scopeTyped (.push frame
            (SourceTemplates.segment_world_weaken pending (List.subset_append_left _ _))))
          (.push (RecursiveRecords.records_world_weaken closing (List.subset_append_left _ _))) unique _ accepted
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          OwnerPhases.ofStack, OwnerPhases.frameEntry, List.append_nil,
          RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, ownedTickets, spendAll]
        rw [RecursiveRequirements.checked_complete bodyChecked, RecursiveRequirements.checked_complete pendingCheck]
        rfl

namespace Examples
open RecursiveRecords.Examples (operations policy tables contracts stack admitted_discard)

def callback : Code := .lambda 99 .unit

theorem callback_source : Summary operations [] Environment.empty allowed callback (.function .unit .unit [] []) [] :=
  .lambda .unit (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

/-- Reuse the admitted disposal of owner 23 and its dormant owner 19. -/
theorem nested_initial : CheckedState operations policy contracts tables [] [] (.ticket 0 23)
    (.cleanup callback (.discard 0)) stack .unit [23, 19] [] := by
  have source := admitted_discard
  generalize [23, 19] = demand at source ⊢
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        apply RecursiveExecution.check_state
          (.checked (.cleanup (.stable callback_source) current (List.nil_subset _)) scopeTyped pending) closing unique _ accepted
        have original := RecursiveRequirements.checked_complete checked
        simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          RecursiveRequirements.evaluate_emit, RecursiveContexts.evaluate_request, qualify,
          OwnerSource.exportAt, residual_empty, spendAll, List.nil_append, List.map_nil,
          RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right] using original

/-- The existing ledger and disposal-preservation lemmas apply immediately
    after installation, including the nested owner's later retirement demand. -/
theorem nested_install_and_discard :
    ∃ action : ActionData, ∃ next : Configuration,
      RunStep ⟨⟨.cleanup callback (.discard 0), .ticket 0 23, stack⟩, [.ticket 23, .ticket 19], []⟩
        ⟨⟨.discard 0, .ticket 0 23, .push (.armed action) stack⟩, [.ticket 23, .ticket 19, .cleanup 7], []⟩ ∧
      Ledger (⟨⟨.discard 0, .ticket 0 23, .push (.armed action) stack⟩,
        [.ticket 23, .ticket 19, .cleanup 7], []⟩ : RunState).erase ∧
      CheckedState operations policy contracts tables [] [] (.ticket 0 23) (.discard 0)
        (.push (.armed action) stack) .unit [23, 19] [] ∧
      RawStep ⟨.discard 0, .ticket 0 23, .push (.armed action) stack⟩ next [.close 41] [.ticket 23] ∧
      CheckedState operations policy contracts tables [] [] next.scope next.expression next.stack .unit [19] [] := by
  obtain ⟨action, identity, step, installed, trace⟩ := cleanup_preserves nested_initial (by trivial) 7
  have named : RunStep ⟨⟨.cleanup callback (.discard 0), .ticket 0 23, stack⟩, [.ticket 23, .ticket 19], []⟩
      ⟨⟨.discard 0, .ticket 0 23, .push (.armed action) stack⟩, [.ticket 23, .ticket 19, .cleanup 7], []⟩ :=
    .event ⟨⟨.cleanup callback (.discard 0), .ticket 0 23, stack⟩, [.ticket 23, .ticket 19], []⟩
      _ [.cleanup 7] [] step (by decide)
  have ledger : Ledger (⟨⟨.cleanup callback (.discard 0), .ticket 0 23, stack⟩,
      [.ticket 23, .ticket 19], []⟩ : RunState).erase := ⟨.refl _, by decide⟩
  obtain ⟨next, owner, remaining, disposed, checked, demand, consumed⟩ := RecursiveConsumption.discard_preserves installed 41
  have owners := List.cons.inj demand
  have sameOwner := owners.1.symm
  have sameDemand := owners.2.symm
  subst owner remaining
  exact ⟨action, next, named, run_step_preserves_ledger named ledger, installed, disposed, checked⟩

end Examples

namespace ResourceOwnerExamples
open RecursiveRecords.Examples

def program : Code := .resource 8 (.integer 17) (.discard 0)

theorem initial_checked : CheckedState operations policy contracts tables [] [] (.ticket 0 23)
    program stack .unit [23, 19] [] := by
  have current : Expression operations policy contracts [] [] (.ticket 0 23) Environment.empty program .unit [23, 19]
      (.sequence (.request [] []) (.invoke ⟨23, .dispose⟩ [19] [])) :=
    .scopedResource (residual := []) (.stable .integer)
      (fun identity fresh => .discard outer_known rfl rfl rfl (by simp [outer, inner]))
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
      (List.Subset.refl []) (List.Subset.refl []) (fun _ _ => .invoke)
  have currentCheck : Checked (resumes ++ disposals) [] (available (ownedTickets stack))
      ((Requirements.sequence (.request [] []) (.invoke ⟨23, .dispose⟩ [19] [])).prepend (OwnerPhases.ofStack tables stack)) [] := by
    rw [RecursiveRequirements.checked_prepend_iff]
    exact .sequence (firstRow := []) (secondRow := []) (.request (by simp [OwnerSource.exportAt, residual_empty]))
      (by simpa only [List.nil_append, List.append_nil, stack, capture, ownedTickets, spendAll] using outer_checked)
  have pendingCheck : Checked (resumes ++ disposals) [] (spendAll (available (ownedTickets stack)) [23, 19]) outerRequirements [] :=
    .sequence (.spent (by decide)) (.request (by simp [OwnerSource.exportAt, residual_empty]))
  exact .checked (.checked current (.bound (Owners.ports_lookup outer_known)) outer_source) outer_closing
    (by decide) (.sequence currentCheck pendingCheck) (by decide)

/-- Entry keeps the cell in the caller while disposal consumes the enclosing
    owner and schedules its dormant owner. Both successor checks are derived. -/
theorem enter_then_dispose :
    ∃ identity answer, ∃ next : Configuration,
      RawStep ⟨program, .ticket 0 23, stack⟩
        ⟨.discard 0, .ticket 0 23, .push (.cell identity 17 (.ticket 0 23) answer) stack⟩ [.resource identity] [] ∧
      CheckedState operations policy contracts tables [identity] [] (.ticket 0 23) (.discard 0)
        (.push (.cell identity 17 (.ticket 0 23) answer) stack) .unit [23, 19] [] ∧
      RawStep ⟨.discard 0, .ticket 0 23, .push (.cell identity 17 (.ticket 0 23) answer) stack⟩ next [.close 41] [.ticket 23] ∧
      CheckedState operations policy contracts tables [identity] [] next.scope next.expression next.stack .unit [19] [] := by
  obtain ⟨identity, payload, answer, unused, same, entered, opened, ownerTrace⟩ := resource_preserves initial_checked (by trivial)
  have value : payload = 17 := (Code.integer.inj same).symm
  subst payload
  obtain ⟨next, owner, remaining, disposed, checked, demand, consumed⟩ := RecursiveConsumption.discard_preserves opened 41
  obtain ⟨sameOwner, sameDemand⟩ := List.cons.inj demand
  subst owner remaining
  exact ⟨identity, answer, next, entered, opened, disposed, checked⟩

end ResourceOwnerExamples

namespace ResourceHandlerExamples
open RecursiveHandlerTables.Examples (initialHandler initialHandlerRequirements initial_handler_source)
open RecursiveClauseOwnership.ResourceClauseExamples (contracts)
open RecursiveDisposalCapture.Examples (operations tables effect)
open RecursiveRecords.Examples (policy)

def program : Code := .resource 8 (.integer 17) initialHandler

theorem initial_checked : CheckedState operations policy contracts tables [] [] .none program .nil .unit [] [] := by
  have current : Expression operations policy contracts [] [] .none Environment.empty program .unit []
      (.sequence (.request [] []) (.emitAfter (.request [] []) [] [])) :=
    .scopedResource (residual := []) (.stable .integer)
      (fun identity fresh => initial_handler_source [identity] [.cell identity] .none)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
      (List.Subset.refl []) (List.Subset.refl []) (fun identity fresh => by
        exact ResourceRequirements.Hides.emitThrough
          (layers := [.handler effect 0 [(0, ⟨true, some [], some []⟩)]]) (raw := [⟨effect, 0, false⟩])
          (ResourceRequirements.Hides.requestThrough
            (layers := [.handler effect 0 [(0, ⟨true, some [], some []⟩)]]) (raw := []) (interpreted := []) (by decide))
          (interpreted := []) (by decide))
  have currentCheck : Checked [] [] (available [])
      ((Requirements.sequence (.request [] []) (.emitAfter (.request [] []) [] [])).prepend []) [] := by
    apply RecursiveRequirements.checked_prepend_iff.mpr
    exact .sequence (firstRow := []) (secondRow := []) (.request (by simp [OwnerSource.exportAt, residual_empty]))
      (.emitAfter (bodyRow := []) (requestRow := []) (.request (by simp [OwnerSource.exportAt, residual_empty]))
        (by simp [OwnerSource.exportAt, residual_empty]))
  exact .checked (.checked current .none .nil) .nil (by decide)
    (.sequence (firstRow := []) (secondRow := []) currentCheck
      (.request (by simp [OwnerSource.exportAt, residual_empty]))) (by decide)

theorem enter_resource_then_handler : ∃ identity answer handler table,
    RawTrace ⟨program, .none, .nil⟩
      ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none,
        .push (.handler handler) (.push (.cell identity 17 .none answer) .nil)⟩ [.resource identity] [] ∧
    CheckedState operations policy contracts (RecursiveHandlerTables.register tables handler.activation table) [identity] [] .none
      (.perform (Instantiation.freezeEffect effect) 0 .unit)
      (.push (.handler handler) (.push (.cell identity 17 .none answer) .nil)) .unit [] [] := by
  obtain ⟨identity, payload, answer, fresh, same, entered, opened, trace⟩ := resource_preserves initial_checked (by trivial)
  have samePayload : payload = 17 := (Code.integer.inj same).symm
  subst payload
  obtain ⟨handler, table, freshHandler, installed, successor, owners, capabilities, modes⟩ :=
    RecursiveHandlerTables.handler_preserves opened (history := []) (List.Subset.refl [])
  exact ⟨identity, answer, handler, table, .next entered (.next installed (.refl _)), successor⟩

end ResourceHandlerExamples

end Ash.OneShot.RecursiveEntries

#print axioms Ash.OneShot.RecursiveEntries.cleanup_parts
#print axioms Ash.OneShot.RecursiveEntries.armed_context
#print axioms Ash.OneShot.RecursiveEntries.cleanup_preserves
#print axioms Ash.OneShot.RecursiveEntries.resource_parts
#print axioms Ash.OneShot.RecursiveEntries.resource_preserves
#print axioms Ash.OneShot.RecursiveEntries.ResourceOwnerExamples.initial_checked
#print axioms Ash.OneShot.RecursiveEntries.ResourceOwnerExamples.enter_then_dispose
#print axioms Ash.OneShot.RecursiveEntries.Examples.callback_source
#print axioms Ash.OneShot.RecursiveEntries.Examples.nested_initial
#print axioms Ash.OneShot.RecursiveEntries.Examples.nested_install_and_discard

#print axioms Ash.OneShot.RecursiveEntries.ResourceHandlerExamples.initial_checked
#print axioms Ash.OneShot.RecursiveEntries.ResourceHandlerExamples.enter_resource_then_handler
