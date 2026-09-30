import SourceScheduledResources

/-! Builtin cell replies retain the same scheduled source forest. Payload
updates reuse the established interpretation, ownership and capture-origin
proofs; only the performed request's checked row is removed. -/
namespace Ash.OneShot.SourceScheduledCells
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedSources (ValueSummary)
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available spendAll)

theorem update_segment {hints : SourceContextualHints.Hints receiving} {forest : SourceRetainedPlans.Forest hints}
    (update : CellUpdate identity old new before after)
    (source : SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      before input output demand requirements records forest outside incoming outgoing) :
    SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      after input output demand requirements records forest outside incoming outgoing := by
  induction update generalizing input demand requirements records receiving incoming with
  | hit => cases source with
    | push head rest bound => cases head with
      | cell scopeKnown noEscape annotation interface => cases interface with
        | cell scopeTyped excluded =>
          exact .push (.cell scopeKnown noEscape annotation (.cell scopeTyped excluded)) rest bound
  | push miss next ih => cases source with
    | push head rest bound =>
      simpa only [RecursiveCells.update_context next] using SourceScheduledFrames.Segment.push head (ih rest) bound
  | live next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound rest resume close bound =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound (ih rest) resume close bound
  | spent next ih => cases source with
    | spent known annotation scope rest bound => exact .spent known annotation scope (ih rest) bound

theorem request_reply
    (source : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) operation operand) before forest output demand row evidence)
    (update : CellUpdate identity old new before after)
    (isValue : operand.IsValue)
    (response : ∀ input result, operations (.cell identity) operation = some (input, result) →
      ValueSummary operations policy contracts world (fun _ => none) [] reply result)
    (replyValue : reply.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) operation operand, scope, before⟩
      ⟨reply, scope, after⟩ [] []) :
    ∃ nextRow,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        scope reply after forest output demand nextRow evidence ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before)) [] (available (ownedTickets after)) := by
  cases source with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    generalize frozen : Instantiation.freezeEffect (.cell identity) = actualEffect at current
    generalize planSignature : SourcePlanSignatures.signature plan = checking at current
    cases current with
    | perform known admitted operandSource formed =>
      cases freeze_effect_injective frozen
      have erasedOperand := DeclaredSources.expression_erase
        (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase operandSource))
      have empty := SourceTemplates.expression_value_demand erasedOperand isValue
      cases empty
      simp only [List.nil_append] at accounting
      subst demand
      obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      have included := List.sublist_append_right currentRow pendingRow
      have owners := cell_update_owned_tickets update
      have pendingAfter := update_segment update pending
      rw [owners] at pendingAfter
      have closingAfter := DeclaredSourceClosing.update_records update closing
      have templatesAfter := templates.after_step closingAfter (List.Subset.refl _) raw (by intro owner; simp) unique
      refine ⟨pendingRow, ?_, included, owners ▸ .nil⟩
      apply SourceScheduledValues.value_configuration (response _ _ known) replyValue scopeTyped pendingAfter
        closingAfter templatesAfter matched (owners ▸ unique) _ (checked_footprint_subset accepted included.subset)
      simpa only [spendAll, owners] using pendingCheck

theorem read_preserves
    (signature : operations.erase.erase.ports (.cell identity) 0 = some (.reference identity, .integer))
    (source : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity))) before forest output demand row evidence)
    (selected : CellUpdate identity payload payload before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩
        ⟨.integer payload, scope, after⟩ [] [] ∧
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        scope (.integer payload) after forest output demand nextRow evidence ∧ nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before)) [] (available (ownedTickets after)) := by
  have raw := RawStep.readCell identity payload scope before after selected
  obtain ⟨nextRow, checked, included, trace⟩ := request_reply source selected (by trivial) (reply := .integer payload) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (CoherentSourceTypes.port_lookup
      (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known)))))).2
    cases result <;> cases output
    exact .integer) trivial raw
  exact ⟨nextRow, raw, checked, included, trace⟩

theorem write_preserves
    (signature : operations.erase.erase.ports (.cell identity) 1 = some (.product (.reference identity) .integer, .unit))
    (source : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new))) before forest output demand row evidence)
    (selected : CellUpdate identity old new before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩
        ⟨.unit, scope, after⟩ [] [] ∧
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        scope .unit after forest output demand nextRow evidence ∧ nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before)) [] (available (ownedTickets after)) := by
  have raw := RawStep.writeCell identity old new scope before after selected
  obtain ⟨nextRow, checked, included, trace⟩ := request_reply source selected (by trivial) (reply := .unit) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (CoherentSourceTypes.port_lookup
      (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known)))))).2
    cases result <;> cases output
    exact .unit) trivial raw
  exact ⟨nextRow, raw, checked, included, trace⟩

theorem builtin_step_preserves
    (signature : operations.erase.erase.ports = ScopedPorts.withCellSignatures users)
    (source : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      before.scope before.expression before.stack forest output demand row evidence)
    (raw : RawStep before after [] [])
    (same : before.expression = .perform effect operation operand) (isValue : operand.IsValue) :
    ∃ nextRow, SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      after.scope after.expression after.stack forest output demand nextRow evidence ∧ nextRow.Sublist row := by
  have ordinary := ScopedPortProgress.nonallocating_request_is_ordinary raw same isValue
  cases ordinary with
  | bind | beta | ifTrue | ifFalse => cases same
  | read selected =>
    obtain ⟨nextRow, step, next, included, trace⟩ := read_preserves (by rw [signature]; rfl) source selected
    exact ⟨nextRow, next, included⟩
  | write selected =>
    obtain ⟨nextRow, step, next, included, trace⟩ := write_preserves (by rw [signature]; rfl) source selected
    exact ⟨nextRow, next, included⟩

end Ash.OneShot.SourceScheduledCells

#print axioms Ash.OneShot.SourceScheduledCells.update_segment
#print axioms Ash.OneShot.SourceScheduledCells.request_reply
#print axioms Ash.OneShot.SourceScheduledCells.read_preserves
#print axioms Ash.OneShot.SourceScheduledCells.write_preserves
#print axioms Ash.OneShot.SourceScheduledCells.builtin_step_preserves
