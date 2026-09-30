import DeclaredConnectedResumption

/-! Builtin cell transitions retain the same structural source/effect segment.
The existing cell-selection induction and source request/ownership proofs apply. -/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSourceClosing (Records)
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available spendAll)
open RecursiveCells (update_context)
open DeclaredSourceClosing (update_records)

theorem update_segment
    (update : CellUpdate identity old new before after)
    (source : Segment operations policy contracts tables actions world before input output demand requirements records incoming outgoing) :
    Segment operations policy contracts tables actions world after input output demand requirements records incoming outgoing := by
  induction update generalizing input demand requirements records incoming with
  | hit => cases source with
    | push head rest bound => cases head with
      | retained kind source interface => cases source with
        | cell scopeKnown noEscape annotation => cases interface with
          | cell scopeTyped excluded =>
              exact .push (.retained .cell (.cell scopeKnown noEscape annotation) (.cell scopeTyped excluded)) rest bound
  | push miss next ih => cases source with
    | push head rest bound =>
        simpa only [update_context next] using Segment.push head (ih rest) bound
  | live next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface rest resume close bound =>
        exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface (ih rest) resume close bound
  | spent next ih => cases source with
    | spent known annotation scope rest bound => exact .spent known annotation scope (ih rest) bound

theorem request_reply
    (source : State operations policy contracts tables actions world outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) operation operand) before output demand row)
    (update : CellUpdate identity old new before after)
    (isValue : operand.IsValue)
    (response : ∀ input result, operations (.cell identity) operation = some (input, result) →
      DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty [] reply result)
    (replyValue : reply.IsValue) :
    ∃ nextRow,
      State operations policy contracts tables actions world outside scope reply after output demand nextRow ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before)) [] (available (ownedTickets after)) := by
  cases source with
  | checked current scopeTyped pending closing unique checked accepted accounting =>
        subst demand
        obtain ⟨argument, known, operandSource, noDemand⟩ := RecursiveCapture.request_operand (DeclaredSources.expression_erase current) isValue
        subst_vars
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
        have included := List.sublist_append_right currentRow pendingRow
        have owners := cell_update_owned_tickets update
        refine ⟨pendingRow, ?_, included, owners ▸ .nil⟩
        apply value_configuration (response _ _ known) replyValue scopeTyped (update_segment update pending)
          (update_records update closing) (owners ▸ unique) _ (checked_footprint_subset accepted included.subset)
        simpa only [spendAll, owners] using pendingCheck

theorem read_preserves
    (signature : operations.ports (.cell identity) 0 = some (.reference identity, .integer))
    (source : State operations policy contracts tables actions world outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity))) before output demand row)
    (selected : CellUpdate identity payload payload before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩
        ⟨.integer payload, scope, after⟩ [] [] ∧
      State operations policy contracts tables actions world outside scope (.integer payload) after output demand nextRow ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before)) [] (available (ownedTickets after)) := by
  obtain ⟨nextRow, checked, included, trace⟩ := request_reply source selected (by trivial) (reply := .integer payload) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (port_lookup known)))).2
    cases result <;> cases output
    exact .summaryInteger) trivial
  exact ⟨nextRow, .readCell identity payload scope before after selected, checked, included, trace⟩

theorem write_preserves
    (signature : operations.ports (.cell identity) 1 = some (.product (.reference identity) .integer, .unit))
    (source : State operations policy contracts tables actions world outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new))) before output demand row)
    (selected : CellUpdate identity old new before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩
        ⟨.unit, scope, after⟩ [] [] ∧
      State operations policy contracts tables actions world outside scope .unit after output demand nextRow ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before)) [] (available (ownedTickets after)) := by
  obtain ⟨nextRow, checked, included, trace⟩ := request_reply source selected (by trivial) (reply := .unit) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (port_lookup known)))).2
    cases result <;> cases output
    exact .summaryUnit) trivial
  exact ⟨nextRow, .writeCell identity old new scope before after selected, checked, included, trace⟩


theorem builtin_step_source
    (signature : operations.ports = ScopedPorts.withCellSignatures users)
    (source : State operations policy contracts tables actions world outside
      before.scope before.expression before.stack output demand row)
    (raw : RawStep before after [] [])
    (same : before.expression = .perform effect operation operand) (isValue : operand.IsValue) :
    ∃ nextRow, State operations policy contracts tables actions world outside
      after.scope after.expression after.stack output demand nextRow ∧ nextRow.Sublist row := by
  have ordinary := ScopedPortProgress.nonallocating_request_is_ordinary raw same isValue
  cases ordinary with
  | bind | beta | ifTrue | ifFalse => cases same
  | read selected =>
      obtain ⟨nextRow, step, next, included, trace⟩ :=
        read_preserves (by rw [signature]; rfl) source selected
      exact ⟨nextRow, next, included⟩
  | write selected =>
      obtain ⟨nextRow, step, next, included, trace⟩ :=
        write_preserves (by rw [signature]; rfl) source selected
      exact ⟨nextRow, next, included⟩

theorem builtin_step_preserves
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      output demand row bound)
    (isValue : operand.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩ after [] []) :
    ∃ nextRow,
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output demand nextRow bound ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  obtain ⟨nextRow, next, included⟩ := builtin_step_source before.current.signature source raw rfl isValue
  obtain ⟨runtimeRow, step, current, runtimeIncluded⟩ := DeclaredExecution.builtin_step_preserves before.current isValue raw
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  refine ⟨nextRow, step, ?_, included⟩
  apply assemble_entry before.current raw freshOwners current.names.unique step.checks usage history retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem request_selection
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      output demand row bound)
    (isValue : operand.IsValue) :
    (∃ after nextRow,
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output demand nextRow bound ∧ nextRow.Sublist row) ∨
    (∃ capture tail handler, HandlerCut requested stack capture tail handler) := by
  rcases RecursiveRequestProgress.request_selection before.current.signature
      (DeclaredSourceStates.checked_state_erase before.current.source) isValue with
    ⟨after, nextRow, raw, source, included⟩ | selected
  · obtain ⟨nextRow, step, next, included⟩ := builtin_step_preserves before isValue raw
    exact Or.inl ⟨after, nextRow, step, next, included⟩
  · exact Or.inr selected

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.update_segment
#print axioms Ash.OneShot.DeclaredConnectedSources.request_reply
#print axioms Ash.OneShot.DeclaredConnectedSources.read_preserves
#print axioms Ash.OneShot.DeclaredConnectedSources.write_preserves

#print axioms Ash.OneShot.DeclaredConnectedSources.builtin_step_source
#print axioms Ash.OneShot.DeclaredConnectedSources.builtin_step_preserves
#print axioms Ash.OneShot.DeclaredConnectedSources.request_selection
