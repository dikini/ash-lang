import RecursiveClauses

/-!
Actual handler selection and request binding joined to recursive clause checks.
The selected table supplies the request residual. Structural admission must still
prove each selected clause's derivation and its bound by that residual together
with the authenticated saved computation. No successor check is assumed.
-/

namespace Ash.OneShot.RecursiveDispatch
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open SourceTemplates (Expression Segment)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (Phases available spendAll)
open CallableProtectionFrames (Tables contextOf pushContext)

theorem request_evaluation
    (source : Expression operations policy contracts world allowed scope environment
      (.perform (Instantiation.freezeEffect requested) operation operand) result demand requirements)
    (isValue : operand.IsValue) :
    evaluate records receiving before requirements =
      OwnerSource.exportAt receiving before [⟨requested, operation, false⟩] := by
  generalize encoded : Instantiation.freezeEffect requested = effect at source
  cases source with
  | stable summary => cases summary with
    | perform known admitted operand formed =>
        cases freeze_effect_injective encoded
        have empty := CoherentSourceTypes.value_row operand isValue
        simp only [empty, List.nil_append, RecursiveContexts.evaluate_request]
  | callable summary => cases summary with
    | summaryPerform known admitted operand formed =>
        cases freeze_effect_injective encoded
        have empty := CallableSources.value_row operand isValue
        simp only [empty, List.nil_append, RecursiveContexts.evaluate_request]
  | perform known admitted operand formed =>
      cases freeze_effect_injective encoded
      have empty := SourceTemplates.expression_value_demand operand isValue
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRecomposition.value_evaluation operand isValue,
        empty, spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left]

theorem residual_push_miss (tables : Tables) (frame : ExecFrame) (context : ProtectionContracts.Context)
    (miss : frame.erase.target ≠ some requested) :
    residualize (pushContext tables frame context) [⟨requested, operation, incoming⟩] =
      residualize context [⟨requested, operation, incoming || ProtectionContexts.frameProtected frame.erase⟩] := by
  cases frame <;> simp_all [pushContext, residualize, throughLayer, demandThrough, merge,
    ExecFrame.erase, HandlerData.erase, Frame.target, ProtectionContexts.frameProtected,
    PlainData.erase, ActionData.erase, eq_comm]

/-- Follow the actual cut through ordinary frames and retained live owners.
    The exported row is the selected offer interpreted through the actual tail. -/
theorem cut_residual
    (cut : HandlerCut requested whole capture tail handler)
    (exported : residualize (contextOf tables whole) [⟨requested, operation, incoming⟩] = some row) :
    ∃ contract offered, lookup operation (tables handler) = some contract ∧
      modeCheck contract.dispose (incoming || ProtectionContexts.protectedMode capture.erase) = true ∧
      contract.row (incoming || ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some row := by
  induction cut generalizing incoming with
  | hit handler tail same =>
      simp only [contextOf, pushContext, residualize, throughLayer, demandThrough, same, if_true] at exported
      cases known : lookup operation (tables handler) with
      | none => simp [known, merge] at exported
      | some contract =>
          cases permitted : modeCheck contract.dispose incoming with
          | false => simp [known, permitted, merge] at exported
          | true =>
              cases offered : contract.row incoming with
              | none => simp [known, permitted, offered, merge] at exported
              | some outside =>
                  refine ⟨contract, outside, rfl, ?_, ?_, ?_⟩
                  · simpa [Stack.erase, ExecFrame.erase, HandlerData.erase, ProtectionContexts.protectedMode,
                      ProtectionContexts.frameProtected] using permitted
                  · simpa [Stack.erase, ExecFrame.erase, HandlerData.erase, ProtectionContexts.protectedMode,
                      ProtectionContexts.frameProtected] using offered
                  · simpa [known, permitted, offered, merge] using exported
  | push frame rest cap tail handler miss next ih =>
      rw [contextOf, residual_push_miss tables frame _ miss] at exported
      obtain ⟨contract, offered, known, permitted, rowKnown, residual⟩ := ih exported
      exact ⟨contract, offered, known,
        by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using permitted,
        by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using rowKnown, residual⟩
  | live owner input answer saved scope rest cap tail handler next ih =>
      change residualize (contextOf tables rest)
        [⟨requested, operation, incoming || ProtectionContexts.protectedMode saved.erase⟩] = some row at exported
      obtain ⟨contract, offered, known, permitted, rowKnown, residual⟩ := ih exported
      exact ⟨contract, offered, known,
        by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using permitted,
        by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using rowKnown, residual⟩
  | spent owner answer scope rest cap tail handler next ih => exact ih exported


/-- Capture computes the shared continuation contract and exact selected offer.
    A structural derivation of the actual clause, bounded by the offered request
    residual and saved computation, then constructs the checked raw successor.
    Handler installation must supply that derivation and bound. -/
theorem capture_from_structural_clause
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (resumeEffects : List Instance) :
    ∃ (contract : Owners.Contract) (offeredContract : ClauseContract) (offered requestRow tailRow : Footprint),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeRow = none ∧ contract.resumeEffects = resumeEffects ∧
      contract.resumeDemand.Sublist demand ∧
      row = (requestRow ++ contract.resumeRow) ++ tailRow ∧
      lookup operation (tables handler) = some offeredContract ∧
      modeCheck offeredContract.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offeredContract.row (ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some requestRow ∧
      ∀ (allowed : List Instance) (after : Phases) (clauseDemand : List Nat) (clauseRow : Footprint),
        Owners.Derives operations policy (contracts.insert owner contract)
          (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) world
          (Environment.empty.extend parameter argument) allowed (.ticket binder owner)
          (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          body after contract.answer clauseDemand clauseRow →
        after owner = .consumed → clauseRow ⊆ (requestRow ++ contract.resumeRow) →
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
          ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
        SourceTemplates.CheckedConfiguration operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
          (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          output (owner :: demand) (clauseRow ++ tailRow) ∧
        (clauseRow ++ tailRow) ⊆ row ∧
        ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨actualArgument, knownOperation, operandSummary, empty⟩ := RecursiveCapture.request_operand current isValue
        obtain ⟨sameArgument, sameInput⟩ := Prod.mk.inj (Option.some.inj (knownOperation.symm.trans operationKnown))
        subst_vars
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ := RecursiveRequirements.checked_sequence_parts checked
        have requestExport := RecursiveRequirements.checked_complete (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
        rw [request_evaluation current isValue] at requestExport
        simp only [List.append_nil, OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] at requestExport
        obtain ⟨offeredContract, offered, offeredKnown, offeredMode, offeredRow, offeredExport⟩ := cut_residual cut requestExport
        simp only [Bool.false_or] at offeredMode offeredRow
        obtain ⟨contract, capReq, tailDemand, tailReq, tailRow, inputSame, annotation, closeDemandSame, closeRowSame,
          resumeEffectsSame, closeEffectsSame, sameDemand, capturedRow, boundary, capCheck, tailCheck, afterUnique, map⟩ :=
          RecursiveCapture.capture_record cut pending pendingCheck unique fresh [] none resumeEffects []
        have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
        have totalRow : row = (currentRow ++ contract.resumeRow) ++ tailRow := by
          simp only [sameRow, capturedRow, List.append_assoc]
        have closed : ClosedValue operand :=
          ScopedPorts.typed_value_closed (operandSummary.ports .none) isValue
        have ready : ClosedExcept parameter body := by
          obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (SourceTemplates.segment_ports pending)
          cases handlerTyped with
          | handler scopeKnown clauses coverage unique =>
              obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed clause clauses
              exact ScopedPorts.typed_suffix_ready bodyTyped
        refine ⟨contract, offeredContract, offered, currentRow, tailRow, inputSame, annotation, closeRowSame,
          resumeEffectsSame, (by simpa only [sameDemand, List.nil_append] using List.sublist_append_left contract.resumeDemand tailDemand), totalRow, offeredKnown, offeredMode, offeredRow, offeredExport, ?_⟩
        intro allowed after clauseDemand clauseRow bodySource completed bounded
        have included : (clauseRow ++ tailRow) ⊆ row := by
          rw [totalRow]
          intro request member
          rcases List.mem_append.mp member with current | remaining
          · exact List.mem_append_left _ (bounded current)
          · exact List.mem_append_right _ remaining
        have afterChecked := RecursiveClauses.fresh_substituted_clause_configuration known boundary capCheck tailCheck
          (RecursiveCapture.capture_phase_consumed cut (RecursiveCapture.fresh_unowned pending fresh)) afterUnique closeRowSame
          bodySource ((operandSummary.change_allowed isValue allowed).extension (Owners.insert_extends contracts fresh)) closed
          completed (checked_footprint_subset accepted included)
        refine ⟨.capture requested operation parameter binder owner operand body scope whole capture tail handler
          _ cut clause closed ready, ?_, included, RecursiveCapture.capture_owned cut⟩
        simpa only [sameDemand, List.nil_append, List.cons_append] using afterChecked


namespace Examples
open SharedSourceSegments.Examples (operations policy contracts effect operation_known plain)
open RecursiveClauses.Examples (clause raw)

def handler : HandlerData := ⟨73, effect, .cons 0 2 7 clause .nil, .none, .boolean, rfl⟩
def capture : Stack := .push (.plain plain) (.push (.handler handler) .nil)
def tables : Tables := fun _ => [(0, ⟨false, some (raw ++ raw), some (raw ++ raw)⟩)]
def outside : ProtectionContracts.Context := [.handler effect 74 [(0, ⟨false, some [], some []⟩)]]
def capturedRequirements : Requirements [] :=
  .sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (.push (.handler handler) .nil)))
    (.sequence ((Requirements.request [] []).prepend []) (.request [] []))
def requestRequirements : Requirements [] := .emitAfter (.request [] []) [] [⟨effect, 0, false⟩]

theorem handler_typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types [] (.handler handler) := by
  have request {environment : ScopedPorts.TypeEnv} {ticket : ScopedPorts.Ticket} : ScopedPorts.Typed operations.ports [] environment ticket [effect]
      (.perform (Instantiation.freezeEffect effect) 0 .unit) .integer :=
    .perform (port_lookup operation_known) List.mem_cons_self .unit (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources])
  have resume {environment : ScopedPorts.TypeEnv} {value : Int} : ScopedPorts.Typed operations.ports [] environment (.bound 7 .integer .boolean [effect] [effect]) [effect]
      (.resume 7 (.integer value)) .boolean :=
    .resume .integer (fun _ member => member) (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources])
  refine .handler (residual := [effect]) ⟨.none, .none⟩
    (.cons (port_lookup operation_known) (.bind request (.bind (.branch .boolean resume resume) (.bind request .boolean))) .nil) ?_ (by decide)
  intro operation input output known
  by_cases same : operation = 0
  · subst operation
    simp [handler, ScopedTyping.clauseKeys]
  · simp [Operations.ports, SharedSourceSegments.Examples.operations, same, handler] at known

theorem captured_source : Segment operations policy contracts tables [] capture .integer .boolean [] capturedRequirements [] := by
  have pending : SourceTemplates.Context operations policy contracts [] Environment.empty [] .none
      (.bind 8 (.boolean true)) .integer .boolean [] (.request [] []) := .bind (.stable .boolean)
  exact .push (.plain (plain := plain) pending .none rfl rfl) (.push (.handler handler_typed rfl) .nil)

theorem captured_check : Checked [] receiving before capturedRequirements [] := by
  apply RecursiveRequirements.evaluate_sound
  simp only [capturedRequirements, RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
    RecursiveRecomposition.evaluate_empty, merge, List.nil_append]

theorem request_checked : SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside .none
    (.perform (Instantiation.freezeEffect effect) 0 .unit) capture .boolean [] (raw ++ raw) := by
  have current : Expression operations policy contracts [] [effect] .none Environment.empty
      (.perform (Instantiation.freezeEffect effect) 0 .unit) .integer [] requestRequirements :=
    .perform operation_known List.mem_cons_self (.stable .unit) (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  have currentCheck : Checked [] (OwnerPhases.ofStack tables capture) (available (ownedTickets capture)) requestRequirements (raw ++ raw) :=
    .emitAfter (bodyRow := []) (requestRow := raw ++ raw)
      (Checked.request (raw := []) (nearer := []) (row := []) (by simp [OwnerSource.exportAt, residual_empty])) (by decide)
  have prefixed : Checked [] [] (available (ownedTickets capture))
      (requestRequirements.prepend (OwnerPhases.ofStack tables capture)) (raw ++ raw) :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)
  exact .checked (.checked current .none captured_source) (by decide)
    (by simpa only [List.append_nil] using Checked.sequence prefixed (captured_check (receiving := []))) (by decide)

theorem selected_cut : HandlerCut effect capture capture .nil handler :=
  .push (.plain plain) (.push (.handler handler) .nil) (.push (.handler handler) .nil) .nil handler
    (by decide) (.hit handler .nil rfl)

theorem clause_source (contract : Owners.Contract)
    (input : contract.input = .integer) (answer : contract.answer = .boolean)
    (demand : contract.resumeDemand = []) (row : contract.resumeRow = []) (effects : contract.resumeEffects = []) :
    Owners.Derives operations policy (contracts.insert 23 contract)
      (OwnerPhases.ofStack tables (.live 23 .integer .boolean capture .none .nil)) []
      environment [effect] (.ticket 7 23) (available (ownedTickets (.live 23 .integer .boolean capture .none .nil)))
      clause OwnerPhaseTransitions.empty .boolean [23] (raw ++ raw) := by
  have request {environment : Environment} {phases : Phases} : Owners.Derives operations policy (contracts.insert 23 contract)
      (OwnerPhases.ofStack tables (.live 23 .integer .boolean capture .none .nil)) [] environment [effect] (.ticket 7 23)
      phases (.perform (Instantiation.freezeEffect effect) 0 .unit) phases .integer [] raw := by
    refine .perform operation_known List.mem_cons_self
      (.stable (row := []) .unit (by simp [OwnerSource.exportAt, residual_empty]))
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]) ?_
    change residualize (if phases 23 = .available then [.barrier false] else []) raw = some raw
    split <;> rfl
  have resumed {environment : Environment} {value : Int} : Owners.Derives operations policy (contracts.insert 23 contract)
      (OwnerPhases.ofStack tables (.live 23 .integer .boolean capture .none .nil)) [] environment [effect] (.ticket 7 23)
      (available (ownedTickets (.live 23 .integer .boolean capture .none .nil))) (.resume 7 (.integer value))
      OwnerPhaseTransitions.empty .boolean [23] [] := by
    have known : (contracts.insert 23 contract) 23 = some contract := by simp [Owners.Contracts.insert]
    have operand : Owners.Derives operations policy (contracts.insert 23 contract)
        (OwnerPhases.ofStack tables (.live 23 .integer .boolean capture .none .nil)) [] environment [effect] (.ticket 7 23)
        (available (ownedTickets (.live 23 .integer .boolean capture .none .nil))) (.integer value)
        (available (ownedTickets (.live 23 .integer .boolean capture .none .nil))) contract.input [] [] :=
      input.symm ▸ .stable (row := []) .integer (by simp [OwnerSource.exportAt, residual_empty])
    have transition : OwnerPhaseTransitions.Trace (available (ownedTickets (.live 23 .integer .boolean capture .none .nil)))
        (23 :: contract.resumeDemand) OwnerPhaseTransitions.empty := by
      rw [demand]
      exact OwnerPhaseTransitions.trace_all_owned (List.Perm.refl _) (by decide)
    simpa only [answer, demand, row, List.nil_append] using
      (Owners.Derives.resume (policy := policy) known (by simp [Execution.Scope.resolve]) rfl operand transition
        (effects.symm ▸ List.nil_subset [effect]) (answer.symm ▸ (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])))
  exact .bind request (.bind (.branch (.stable (row := []) .boolean (by simp [OwnerSource.exportAt, residual_empty])) resumed resumed)
    (.bind request (.stable (row := []) .boolean (by simp [OwnerSource.exportAt, residual_empty]))))


theorem capture_preserved : ∃ contract : Owners.Contract,
    RawStep ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, capture⟩
      ⟨clause, .ticket 7 23, .live 23 .integer .boolean capture .none .nil⟩ [.ticket 23] [] ∧
    SourceTemplates.CheckedConfiguration operations policy (contracts.insert 23 contract) tables [] outside (.ticket 7 23)
      clause (.live 23 .integer .boolean capture .none .nil) .boolean [23] (raw ++ raw) := by
  obtain ⟨contract, offeredContract, offered, requestRow, tailRow, input, annotation, closing, effects,
    capturedDemand, totalRow, knownOffer, permitted, offeredRow, exported, dispatch⟩ :=
    capture_from_structural_clause request_checked selected_cut (.hit) operation_known (by trivial) (owner := 23) (by decide) []
  have offerSame : offeredContract = ⟨false, some (raw ++ raw), some (raw ++ raw)⟩ := by
    simpa only [tables, lookup, if_true, Option.some.injEq] using knownOffer.symm
  cases offerSame
  change some (raw ++ raw) = some offered at offeredRow
  have offeredSame := Option.some.inj offeredRow
  change some offered = some requestRow at exported
  have requestSame : requestRow = raw ++ raw := (Option.some.inj exported).symm.trans offeredSame.symm
  have lengths := congrArg List.length totalRow
  simp only [requestSame, List.length_append] at lengths
  have capturedRow : contract.resumeRow = [] := List.length_eq_zero_iff.mp (by omega)
  have tailEmpty : tailRow = [] := List.length_eq_zero_iff.mp (by omega)
  have emptyDemand : contract.resumeDemand = [] := List.sublist_nil.mp capturedDemand
  have answer : contract.answer = .boolean := by
    change contract.answer.port = .boolean at annotation
    cases same : contract.answer <;> simp_all [Value.port]
  have body := clause_source (environment := Environment.empty.extend 2 .unit) contract input answer emptyDemand capturedRow effects
  have bounded : (raw ++ raw) ⊆ (requestRow ++ contract.resumeRow) := by
    simp only [requestSame, capturedRow, List.append_nil]
    exact fun _ member => member
  obtain ⟨step, checked, included, owned⟩ := dispatch [effect] OwnerPhaseTransitions.empty [23] (raw ++ raw)
    (by simpa only [answer, handler, Value.port, ScopedPorts.embedPort] using body) rfl bounded
  refine ⟨contract, ?_, ?_⟩
  · simpa [clause, Code.subst, handler, Value.port, ScopedPorts.embedPort] using step
  · simpa [tailEmpty, clause, Code.subst, handler, Value.port, ScopedPorts.embedPort] using checked

theorem understated_offer_rejected : ¬ (raw ++ raw) ⊆ ([] ++ ([] : Footprint)) := by decide


/-- Obligation rows do not impose execution order or count alternative paths.
    The structural clause proof retains those distinctions separately. -/
theorem interleaved_obligations :
    let first : Demand := ⟨.user 81 [], 0, false⟩
    let saved : Demand := ⟨.user 82 [], 0, false⟩
    let last : Demand := ⟨.user 83 [], 0, false⟩
    ¬ [first, saved, last].Sublist [first, last, saved] ∧
      [first, saved, last] ⊆ [first, last, saved] := by decide

theorem alternative_obligations :
    ¬ (raw ++ raw).Sublist raw ∧ (raw ++ raw) ⊆ raw := by decide

end Examples

end Ash.OneShot.RecursiveDispatch

#print axioms Ash.OneShot.RecursiveDispatch.request_evaluation
#print axioms Ash.OneShot.RecursiveDispatch.residual_push_miss
#print axioms Ash.OneShot.RecursiveDispatch.cut_residual
#print axioms Ash.OneShot.RecursiveDispatch.capture_from_structural_clause
#print axioms Ash.OneShot.RecursiveDispatch.Examples.handler_typed
#print axioms Ash.OneShot.RecursiveDispatch.Examples.captured_source
#print axioms Ash.OneShot.RecursiveDispatch.Examples.captured_check
#print axioms Ash.OneShot.RecursiveDispatch.Examples.request_checked
#print axioms Ash.OneShot.RecursiveDispatch.Examples.selected_cut
#print axioms Ash.OneShot.RecursiveDispatch.Examples.clause_source
#print axioms Ash.OneShot.RecursiveDispatch.Examples.capture_preserved
#print axioms Ash.OneShot.RecursiveDispatch.Examples.understated_offer_rejected

#print axioms Ash.OneShot.RecursiveDispatch.Examples.interleaved_obligations
#print axioms Ash.OneShot.RecursiveDispatch.Examples.alternative_obligations
