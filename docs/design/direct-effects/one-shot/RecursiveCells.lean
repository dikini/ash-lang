import RecursiveEntries

/-!
Builtin cell transitions preserve the recursive source and both authenticated
continuation stores. The canonical builtin signature is the existing port
signature; request decomposition and ownership transport are reused.
-/

namespace Ash.OneShot.RecursiveCells
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open SourceTemplates (Expression Segment)
open RecursiveRecords (Records CheckedState)
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available spendAll)

theorem update_context (update : CellUpdate identity old new before after) :
    OwnerPhases.ofStack tables before = OwnerPhases.ofStack tables after := by
  induction update with
  | hit => rfl
  | push miss next ih | live next ih | spent next ih => simp only [OwnerPhases.ofStack, ih]

theorem update_segment
    (update : CellUpdate identity old new before after)
    (source : Segment operations policy contracts tables world before input output demand requirements records) :
    Segment operations policy contracts tables world after input output demand requirements records := by
  induction update generalizing input demand requirements records with
  | hit => cases source with
    | push head rest => cases head with
      | cell scopeKnown noEscape annotation => exact .push (.cell scopeKnown noEscape annotation) rest
  | push miss next ih => cases source with
    | push head rest =>
        simpa only [update_context next] using Segment.push head (ih rest)
  | live next ih => cases source with
    | live known inputAnnotation answerAnnotation scopeKnown held saved rest =>
        exact .live known inputAnnotation answerAnnotation scopeKnown held saved (ih rest)
  | spent next ih => cases source with
    | spent known answerAnnotation scopeKnown rest => exact .spent known answerAnnotation scopeKnown (ih rest)

theorem update_records
    (update : CellUpdate identity old new before after)
    (source : Records operations policy contracts tables world before records) :
    Records operations policy contracts tables world after records := by
  induction update generalizing records with
  | hit => cases source with
    | push rest => exact .push rest
  | push miss next ih => cases source with
    | push rest => exact .push (ih rest)
  | live next ih => cases source with
    | unclosable blocked saved rest => exact .unclosable blocked saved (ih rest)
    | external outside saved rest => exact .external outside saved (ih rest)
    | close built internal template saved rest => exact .close built internal template saved (ih rest)
  | spent next ih => cases source with
    | spent rest => exact .spent (ih rest)

/-- A selected builtin reply replaces only the current, zero-demand request.
    The response type follows from the canonical operation signature below. -/
theorem request_reply
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) operation operand) before output demand row)
    (update : CellUpdate identity old new before after)
    (isValue : operand.IsValue)
    (response : ∀ input result, operations (.cell identity) operation = some (input, result) →
      Summary operations world Environment.empty [] reply result []) :
    ∃ nextRow,
      CheckedState operations policy contracts tables world outside scope reply after output demand nextRow ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before)) [] (available (ownedTickets after)) := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨argument, known, operandSource, noDemand⟩ := RecursiveCapture.request_operand current isValue
        subst_vars
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
        have included := List.sublist_append_right currentRow pendingRow
        have owners := cell_update_owned_tickets update
        refine ⟨pendingRow, ?_, included, owners ▸ .nil⟩
        apply RecursiveExecution.value_configuration (response _ _ known) scopeTyped (update_segment update pending)
          (update_records update closing) (owners ▸ unique) _ (checked_footprint_subset accepted included.subset)
        simpa only [spendAll, owners] using pendingCheck

theorem read_preserves
    (signature : operations.ports (.cell identity) 0 = some (.reference identity, .integer))
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity))) before output demand row)
    (selected : CellUpdate identity payload payload before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩
        ⟨.integer payload, scope, after⟩ [] [] ∧
      CheckedState operations policy contracts tables world outside scope (.integer payload) after output demand nextRow ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before)) [] (available (ownedTickets after)) := by
  obtain ⟨nextRow, checked, included, trace⟩ := request_reply source selected (by trivial) (reply := .integer payload) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (port_lookup known)))).2
    cases result <;> cases output
    exact .integer)
  exact ⟨nextRow, .readCell identity payload scope before after selected, checked, included, trace⟩

theorem write_preserves
    (signature : operations.ports (.cell identity) 1 = some (.product (.reference identity) .integer, .unit))
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new))) before output demand row)
    (selected : CellUpdate identity old new before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩
        ⟨.unit, scope, after⟩ [] [] ∧
      CheckedState operations policy contracts tables world outside scope .unit after output demand nextRow ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before)) [] (available (ownedTickets after)) := by
  obtain ⟨nextRow, checked, included, trace⟩ := request_reply source selected (by trivial) (reply := .unit) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (port_lookup known)))).2
    cases result <;> cases output
    exact .unit)
  exact ⟨nextRow, .writeCell identity old new scope before after selected, checked, included, trace⟩

namespace Examples
open SharedClosingSource.Examples (operations policy contracts tables action callback operation_known)

def cellTail : Stack := .push (.cell 4 17 .none .unit) (.push (.retiring 19) .nil)
def initialStack : Stack := .push (.armed action) cellTail
def running : Stack := .push (.running action .unit CallableProtection.Examples.unit_closed) cellTail
def readCode : Code := .perform (Instantiation.freezeEffect (.cell 4)) 0 (.resourceRef (.activation 4))

/-- Continue the previously checked materialized disposal plan: invoke its
    callback, read the still-enclosing cell, then release and retire. -/
theorem cleanup_read_then_retire :
    RawTrace ⟨.unit, .none, initialStack⟩ ⟨.unit, .none, .nil⟩ [] [.ticket 19, .resource 4, .cleanup 7] ∧
    CheckedState operations policy contracts tables [4] [] .none .unit .nil .unit [] [] := by
  have integerClosed : ClosedValue (.integer 17) := ⟨trivial, rfl, by intro dependency member; cases member⟩
  have initial : CheckedState operations policy contracts tables [4] [] .none .unit initialStack .unit [19] [] :=
    RecursiveRecords.existing_state RecursiveClosing.Examples.nested_materialized
  have started : CheckedState operations policy contracts tables [4] [] .none (.app callback .unit) running .unit [19] [] :=
    RecursiveExecution.start_cleanup initial CallableProtection.Examples.unit_closed
  have body : CheckedState operations policy contracts tables [4] [] .none (.bind 1 readCode .unit) running .unit [19] [] :=
    RecursiveExecution.beta_preserves started CallableProtection.Examples.unit_closed
  obtain ⟨plain, focusStep, focused, contextSame, scopeSame, unchanged⟩ :=
    RecursiveExecution.focus_preserves body (Focus.bind (by intro impossible; cases impossible))
  have selected : CellUpdate 4 17 17 (.push (.plain plain) running) (.push (.plain plain) running) :=
    .push (by simp [ExecFrame.erase, PlainData.erase, Frame.target]) (.push (by decide) .hit)
  obtain ⟨nextRow, readStep, readChecked, included, readOwners⟩ := read_preserves (port_lookup operation_known) focused selected
  have empty := List.sublist_nil.mp included
  subst nextRow
  have plugged : CheckedState operations policy contracts tables [4] [] .none (.bind 1 (.integer 17) .unit) running .unit [19] [] := by
    have result := RecursiveExecution.plug_preserves readChecked integerClosed
    simpa only [scopeSame, contextSame, Context.plug] using result
  have returned : CheckedState operations policy contracts tables [4] [] .none .unit running .unit [19] [] :=
    RecursiveExecution.bind_preserves plugged integerClosed
  have finished : CheckedState operations policy contracts tables [4] [] .none .unit cellTail .unit [19] [] :=
    RecursiveExecution.finish_cleanup returned
  have released : CheckedState operations policy contracts tables [4] [] .none .unit (.push (.retiring 19) .nil) .unit [19] [] :=
    RecursiveExecution.leave_cell finished trivial
  have retired : CheckedState operations policy contracts tables [4] [] .none .unit .nil .unit [] [] := by
    obtain ⟨remaining, demand, checked, trace⟩ := RecursiveExecution.retire released
    have empty : remaining = [] := (List.cons.inj demand).2.symm
    exact empty ▸ checked
  refine ⟨?_, retired⟩
  have plugStep : RawStep ⟨.integer 17, .none, .push (.plain plain) running⟩
      ⟨.bind 1 (.integer 17) .unit, .none, running⟩ [] [] := by
    simpa only [scopeSame, contextSame, Context.plug] using
      RawStep.plug plain (.integer 17) integerClosed .none running
  exact .next (.startCleanup action .unit CallableProtection.Examples.unit_closed .none cellTail)
    (.next (.beta 0 _ .unit .none running CallableProtection.Examples.unit_closed action.closed)
      (.next focusStep (.next readStep (.next plugStep
        (.next (.bind 1 (.integer 17) .unit .none running integerClosed (by intro name member; cases member))
          (.next (.finishCleanup action .unit CallableProtection.Examples.unit_closed .none cellTail)
            (.next (.leaveCell 4 17 .unit .none .none .unit CallableProtection.Examples.unit_closed (.push (.retiring 19) .nil))
              (.next (.retire 19 .none .nil) (.refl _)))))))))

def initialRun : RunState := ⟨⟨.unit, .none, initialStack⟩, [.cleanup 7, .resource 4, .ticket 19], []⟩
def finalRun : RunState := ⟨⟨.unit, .none, .nil⟩, [.cleanup 7, .resource 4, .ticket 19], [.ticket 19, .resource 4, .cleanup 7]⟩

theorem cleanup_execution : RunSteps initialRun finalRun ∧ finalRun.completed.Nodup := by
  have execution : RunSteps initialRun finalRun := raw_trace_enacts cleanup_read_then_retire.1
    (issued := [.cleanup 7, .resource 4, .ticket 19]) (completed := []) (by decide)
  have ledger : Ledger initialRun.erase := ⟨.refl _, by decide⟩
  exact ⟨execution, ledger_no_double_completion (run_steps_preserve_ledger execution ledger)⟩

def writableOperations : Operations
  | .cell identity, 0 => some (.reference identity, .integer)
  | .cell identity, 1 => some (.pair (.reference identity) .integer, .unit)
  | _, _ => none

def writeCode : Code := .perform (Instantiation.freezeEffect (.cell 4)) 1
  (.pair (.resourceRef (.activation 4)) (.integer 18))
def writeBefore : Stack := .push (.cell 4 17 .none .unit) .nil
def writeAfter : Stack := .push (.cell 4 18 .none .unit) .nil

theorem write_initial : CheckedState writableOperations policy contracts tables [4] [] .none writeCode writeBefore .unit [] [] := by
  have current : Expression writableOperations policy contracts [4] [.cell 4] .none Environment.empty writeCode .unit []
      (.request [] [⟨.cell 4, 1, false⟩]) :=
    .stable (.perform rfl List.mem_cons_self (.pair (.reference List.mem_cons_self) .integer)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
  exact RecursiveExecution.check_state
    (.checked current .none (.push (.cell ⟨.none, .none⟩ (by decide) rfl) .nil)) (.push .nil)
    (by decide) (by
      apply RecursiveRequirements.checked_complete
      simp only [Requirements.prepend]
      exact Checked.sequence (Checked.request (row := []) rfl)
        (Checked.sequence (Checked.request (row := []) rfl) (Checked.request (row := []) rfl))) (by decide)

theorem write_changes_payload :
    RawStep ⟨writeCode, .none, writeBefore⟩ ⟨.unit, .none, writeAfter⟩ [] [] ∧
    CheckedState writableOperations policy contracts tables [4] [] .none .unit writeAfter .unit [] [] := by
  obtain ⟨nextRow, step, checked, included, trace⟩ := write_preserves rfl write_initial (CellUpdate.hit)
  have empty := List.sublist_nil.mp included
  exact ⟨step, empty ▸ checked⟩

end Examples

end Ash.OneShot.RecursiveCells

#print axioms Ash.OneShot.RecursiveCells.update_context
#print axioms Ash.OneShot.RecursiveCells.update_segment
#print axioms Ash.OneShot.RecursiveCells.update_records
#print axioms Ash.OneShot.RecursiveCells.request_reply
#print axioms Ash.OneShot.RecursiveCells.read_preserves
#print axioms Ash.OneShot.RecursiveCells.write_preserves
#print axioms Ash.OneShot.RecursiveCells.Examples.cleanup_read_then_retire
#print axioms Ash.OneShot.RecursiveCells.Examples.cleanup_execution
#print axioms Ash.OneShot.RecursiveCells.Examples.write_initial
#print axioms Ash.OneShot.RecursiveCells.Examples.write_changes_payload
