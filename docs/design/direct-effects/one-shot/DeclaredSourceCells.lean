import DeclaredSourceStates
import RecursiveCells

/-! Builtin cell transitions retain hereditary source evidence. Existing cell
selection, record transport, request decomposition and ownership proofs apply. -/
namespace Ash.OneShot.DeclaredSourceCells
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSourceFrames (Segment)
open DeclaredSourceStates (CheckedState)
open DeclaredSourceClosing (Records)
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available spendAll)
open RecursiveCells (update_context)
open DeclaredSourceClosing (update_records)

theorem update_segment
    (update : CellUpdate identity old new before after)
    (source : Segment operations policy contracts tables world before input output demand requirements records) :
    Segment operations policy contracts tables world after input output demand requirements records := by
  induction update generalizing input demand requirements records with
  | hit => cases source with
    | push head erasedHead rest => cases head with
      | cell scopeKnown noEscape annotation => exact DeclaredSourceFrames.push (.cell scopeKnown noEscape annotation) rest
  | push miss next ih => cases source with
    | push head erasedHead rest =>
        simpa only [update_context next] using DeclaredSourceFrames.push head (ih rest)
  | live next ih => cases source with
    | live known inputAnnotation answerAnnotation scopeKnown held saved rest =>
        exact .live known inputAnnotation answerAnnotation scopeKnown held saved (ih rest)
  | spent next ih => cases source with
    | spent known answerAnnotation scopeKnown rest => exact .spent known answerAnnotation scopeKnown (ih rest)

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
        obtain ⟨argument, known, operandSource, noDemand⟩ := RecursiveCapture.request_operand (DeclaredSources.expression_erase current) isValue
        subst_vars
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
        have included := List.sublist_append_right currentRow pendingRow
        have owners := cell_update_owned_tickets update
        refine ⟨pendingRow, ?_, included, owners ▸ .nil⟩
        apply DeclaredSourceStates.value_configuration (response _ _ known) scopeTyped (update_segment update pending)
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


end Ash.OneShot.DeclaredSourceCells

#print axioms Ash.OneShot.DeclaredSourceCells.update_segment
#print axioms Ash.OneShot.DeclaredSourceCells.request_reply
#print axioms Ash.OneShot.DeclaredSourceCells.read_preserves
#print axioms Ash.OneShot.DeclaredSourceCells.write_preserves
