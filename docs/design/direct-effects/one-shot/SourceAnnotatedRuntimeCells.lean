import SourceAnnotatedRuntimeEntries

/-! Builtin selection preserves annotated frames and dormant continuations.
The selected cell changes only its payload; source handler blockers remain exact. -/
namespace Ash.OneShot.SourceAnnotatedRuntime

/-- Exact builtin selection updates only the active cell. A nearer matching
    source handler blocks it, and dormant captures are not searched. -/
inductive CellUpdate (identity : Nat) (old new : Int) : Stack → Stack → Prop where
  | hit : CellUpdate identity old new (.push (.cell identity old scope answer) tail)
      (.push (.cell identity new scope answer) tail)
  | push (miss : frame.erase.erase.target ≠ some (.cell identity))
      (next : CellUpdate identity old new before after) :
      CellUpdate identity old new (.push frame before) (.push frame after)
  | live (next : CellUpdate identity old new before after) :
      CellUpdate identity old new (.live ticket q a saved scope before) (.live ticket q a saved scope after)
  | spent (next : CellUpdate identity old new before after) :
      CellUpdate identity old new (.spent ticket a scope before) (.spent ticket a scope after)


theorem CellUpdate.erase (update : CellUpdate identity old new before after) :
    ScopedExecution.CellUpdate identity old new before.erase after.erase := by
  induction update with
  | hit => exact .hit
  | push miss next ih => exact .push miss ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

/-- Cell updates leave every dormant annotated capture unchanged. -/
theorem CellUpdate.capture_origin (update : CellUpdate identity old new before after)
    (located : CapturedIn owner capture after) : CapturedIn owner capture before := by
  induction update with
  | hit => cases located with | push located => exact .push located
  | push miss next ih => cases located with | push located => exact .push (ih located)
  | live next ih => cases located with
      | here => exact .here
      | saved located => exact .saved located
      | tail located => exact .tail (ih located)
  | spent next ih => cases located with | spent located => exact .spent (ih located)

/-- Any existing raw selection lifts while retaining the actual annotated
frames and recursively saved segments. -/
theorem CellUpdate.of_raw
    (update : ScopedExecution.CellUpdate identity old new before.erase rawAfter) :
    ∃ after, CellUpdate identity old new before after ∧ after.erase = rawAfter := by
  generalize same : before.erase = rawBefore at update
  induction update generalizing before with
  | hit =>
      cases before <;> simp [Stack.erase] at same
      rename_i frame tail
      cases frame <;> simp [Frame.erase] at same
      rcases same with ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
      exact ⟨_, .hit, rfl⟩
  | push miss next ih =>
      cases before <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl⟩
      obtain ⟨after, selected, rfl⟩ := ih rfl
      exact ⟨_, .push miss selected, rfl⟩
  | live next ih =>
      cases before <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      obtain ⟨after, selected, rfl⟩ := ih rfl
      exact ⟨_, .live selected, rfl⟩
  | spent next ih =>
      cases before <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨after, selected, rfl⟩ := ih rfl
      exact ⟨_, .spent selected, rfl⟩

end Ash.OneShot.SourceAnnotatedRuntime

namespace Ash.OneShot.SourceAnnotatedRuntimeCells

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceAnnotatedSources (ValueSummary)
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available spendAll)

theorem update_segment {hints : SourceContextualHints.Hints receiving} {forest : SourceRetainedPlans.Forest hints}
    (update : SourceAnnotatedRuntime.CellUpdate identity old new before after)
    (source : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      before input output demand requirements records forest outside incoming outgoing) :
    SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      after input output demand requirements records forest outside incoming outgoing := by
  induction update generalizing input demand requirements records receiving incoming with
  | hit => cases source with
    | push head rest bound => cases head with
      | cell scopeKnown noEscape annotation interface => cases interface with
        | cell scopeTyped excluded =>
          exact .push (.cell scopeKnown noEscape annotation (.cell scopeTyped excluded)) rest bound
  | push miss next ih => cases source with
    | push head rest bound =>
      simpa only [RecursiveCells.update_context next.erase] using SourceAnnotatedRuntimeTyping.Segment.push head (ih rest) bound
  | live next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound rest resume close bound =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound (ih rest) resume close bound
  | spent next ih => cases source with
    | spent known annotation scope rest bound => exact .spent known annotation scope (ih rest) bound

theorem request_reply_atPlan {plan : SourceDeclarationPlans.Plan dependencies}
    (source : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect (.cell identity)) operation operand) before plan forest output demand row evidence)
    (update : SourceAnnotatedRuntime.CellUpdate identity old new before after)
    (isValue : operand.erase.IsValue)
    (response : ∀ input result, operations (.cell identity) operation = some (input, result) →
      ValueSummary operations policy contracts world (fun _ => none) [] reply result)
    (replyValue : reply.erase.IsValue)
    (_raw : RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) operation operand.erase, scope, before.erase⟩
      ⟨reply.erase, scope, after.erase⟩ [] []) :
    ∃ nextRow,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        scope reply after .pure forest output demand nextRow evidence ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before.erase)) [] (available (ownedTickets after.erase)) := by
  cases source with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    generalize frozen : Instantiation.freezeEffect (.cell identity) = actualEffect at current
    generalize planSignature : SourcePlanSignatures.signature plan = checking at current
    cases current with
    | checked hint metadata node => cases node with
      | perform known admitted operandSource formed =>
        cases freeze_effect_injective frozen
        have erasedOperand := DeclaredSources.expression_erase
          (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase operandSource.erase))
        have empty := SourceTemplates.expression_value_demand erasedOperand isValue
        cases empty
        simp only [List.nil_append] at accounting
        subst demand
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
        have included := List.sublist_append_right currentRow pendingRow
        have owners := cell_update_owned_tickets update.erase
        have pendingAfter := update_segment update pending
        rw [owners] at pendingAfter
        have closingAfter := DeclaredSourceClosing.update_records update.erase closing
        have templatesAfter := templates.after_step (nextRoot := after) closingAfter (List.Subset.refl _)
          (fun _ _ located => update.capture_origin located) unique
        refine ⟨pendingRow, ?_, included, owners ▸ .nil⟩
        apply SourceAnnotatedRuntimeReturns.value_configuration_atPlan (response _ _ known) replyValue scopeTyped pendingAfter
          closingAfter templatesAfter matched (owners ▸ unique) _ (checked_footprint_subset accepted included.subset)
        simpa only [spendAll, owners] using pendingCheck

theorem request_reply
    (source : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect (.cell identity)) operation operand) before forest output demand row evidence)
    (update : SourceAnnotatedRuntime.CellUpdate identity old new before after)
    (isValue : operand.erase.IsValue)
    (response : ∀ input result, operations (.cell identity) operation = some (input, result) →
      ValueSummary operations policy contracts world (fun _ => none) [] reply result)
    (replyValue : reply.erase.IsValue)
    (_raw : RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) operation operand.erase, scope, before.erase⟩
      ⟨reply.erase, scope, after.erase⟩ [] []) :
    ∃ nextRow,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        scope reply after forest output demand nextRow evidence ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before.erase)) [] (available (ownedTickets after.erase)) := by
  obtain ⟨_, _, indexed⟩ := source.atPlan
  obtain ⟨nextRow, next, included, trace⟩ := request_reply_atPlan indexed update isValue response replyValue _raw
  exact ⟨nextRow, next.state, included, trace⟩

theorem read_preserves_atPlan {plan : SourceDeclarationPlans.Plan dependencies}
    (signature : operations.erase.erase.ports (.cell identity) 0 = some (.reference identity, .integer))
    (source : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef referenceHint (.activation identity))) before plan forest output demand row evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity payload payload before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before.erase⟩
        ⟨.integer payload, scope, after.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        scope (.integer .integer payload) after .pure forest output demand nextRow evidence ∧ nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before.erase)) [] (available (ownedTickets after.erase)) := by
  have raw := RawStep.readCell identity payload scope before.erase after.erase selected.erase
  obtain ⟨nextRow, checked, included, trace⟩ := request_reply_atPlan source selected (by trivial) (reply := .integer .integer payload) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (CoherentSourceTypes.port_lookup
      (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known)))))).2
    cases result <;> cases output
    exact .checked rfl rfl .integer) trivial raw
  exact ⟨nextRow, raw, checked, included, trace⟩

theorem read_preserves
    (signature : operations.erase.erase.ports (.cell identity) 0 = some (.reference identity, .integer))
    (source : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef referenceHint (.activation identity))) before forest output demand row evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity payload payload before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before.erase⟩
        ⟨.integer payload, scope, after.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        scope (.integer .integer payload) after forest output demand nextRow evidence ∧ nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before.erase)) [] (available (ownedTickets after.erase)) := by
  obtain ⟨_, _, indexed⟩ := source.atPlan
  obtain ⟨nextRow, raw, next, included, trace⟩ := read_preserves_atPlan signature indexed selected
  exact ⟨nextRow, raw, next.state, included, trace⟩

theorem write_preserves_atPlan {plan : SourceDeclarationPlans.Plan dependencies}
    (signature : operations.erase.erase.ports (.cell identity) 1 = some (.product (.reference identity) .integer, .unit))
    (source : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect (.cell identity)) 1
        (.pair pairHint (.resourceRef referenceHint (.activation identity)) (.integer integerHint new))) before plan forest output demand row evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity old new before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before.erase⟩
        ⟨.unit, scope, after.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        scope (.unit .unit) after .pure forest output demand nextRow evidence ∧ nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before.erase)) [] (available (ownedTickets after.erase)) := by
  have raw := RawStep.writeCell identity old new scope before.erase after.erase selected.erase
  obtain ⟨nextRow, checked, included, trace⟩ := request_reply_atPlan source selected (by trivial) (reply := .unit .unit) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (CoherentSourceTypes.port_lookup
      (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known)))))).2
    cases result <;> cases output
    exact .checked (by decide) (by decide) .unit) trivial raw
  exact ⟨nextRow, raw, checked, included, trace⟩

theorem write_preserves
    (signature : operations.erase.erase.ports (.cell identity) 1 = some (.product (.reference identity) .integer, .unit))
    (source : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect (.cell identity)) 1
        (.pair pairHint (.resourceRef referenceHint (.activation identity)) (.integer integerHint new))) before forest output demand row evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity old new before after) :
    ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before.erase⟩
        ⟨.unit, scope, after.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        scope (.unit .unit) after forest output demand nextRow evidence ∧ nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before.erase)) [] (available (ownedTickets after.erase)) := by
  obtain ⟨_, _, indexed⟩ := source.atPlan
  obtain ⟨nextRow, raw, next, included, trace⟩ := write_preserves_atPlan signature indexed selected
  exact ⟨nextRow, raw, next.state, included, trace⟩

/-- Every nonallocating raw reply to a ready request constructs an annotated
successor under the authenticated builtin signatures. -/
theorem builtin_step_preserves_atPlan {plan : SourceDeclarationPlans.Plan dependencies}
    (signature : operations.erase.erase.ports = ScopedPorts.withCellSignatures users)
    (source : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope (.perform hint effect operation operand) before plan forest output demand row evidence)
    (raw : RawStep ⟨.perform effect operation operand.erase, scope, before.erase⟩ rawAfter [] [])
    (isValue : operand.erase.IsValue) :
    ∃ next : SourceAnnotatedRuntime.Configuration, ∃ nextRow,
      next.erase = rawAfter ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack .pure forest output demand nextRow evidence ∧ nextRow.Sublist row := by
  have ordinary := ScopedPortProgress.nonallocating_request_is_ordinary raw rfl isValue
  generalize same : (Configuration.mk (.perform effect operation operand.erase) scope before.erase) = rawBefore at ordinary
  have requested : rawBefore.expression = .perform effect operation operand.erase := by rw [← same]
  cases ordinary <;> try cases requested
  case read selected =>
    simp only [Configuration.mk.injEq, Code.perform.injEq] at same
    rcases same with ⟨⟨rfl, rfl, operandSame⟩, rfl, rfl⟩
    cases operand <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at operandSame
    cases operandSame
    obtain ⟨after, lifted, rfl⟩ := SourceAnnotatedRuntime.CellUpdate.of_raw selected
    obtain ⟨nextRow, step, next, included, trace⟩ := read_preserves_atPlan (by rw [signature]; rfl) source lifted
    exact ⟨⟨_, _, _⟩, nextRow, rfl, next, included⟩
  case write selected =>
    simp only [Configuration.mk.injEq, Code.perform.injEq] at same
    rcases same with ⟨⟨rfl, rfl, operandSame⟩, rfl, rfl⟩
    cases operand <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at operandSame
    rename_i pairHint reference integer
    simp only [Code.pair.injEq] at operandSame
    obtain ⟨referenceSame, integerSame⟩ := operandSame
    cases reference <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at referenceSame
    cases referenceSame
    cases integer <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at integerSame
    cases integerSame
    obtain ⟨after, lifted, rfl⟩ := SourceAnnotatedRuntime.CellUpdate.of_raw selected
    obtain ⟨nextRow, step, next, included, trace⟩ := write_preserves_atPlan (by rw [signature]; rfl) source lifted
    exact ⟨⟨_, _, _⟩, nextRow, rfl, next, included⟩

theorem builtin_step_preserves
    (signature : operations.erase.erase.ports = ScopedPorts.withCellSignatures users)
    (source : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.perform hint effect operation operand) before forest output demand row evidence)
    (raw : RawStep ⟨.perform effect operation operand.erase, scope, before.erase⟩ rawAfter [] [])
    (isValue : operand.erase.IsValue) :
    ∃ next : SourceAnnotatedRuntime.Configuration, ∃ nextRow,
      next.erase = rawAfter ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack forest output demand nextRow evidence ∧ nextRow.Sublist row := by
  obtain ⟨_, _, indexed⟩ := source.atPlan
  obtain ⟨next, nextRow, same, typed, included⟩ := builtin_step_preserves_atPlan signature indexed raw isValue
  exact ⟨next, nextRow, same, typed.state, included⟩

end Ash.OneShot.SourceAnnotatedRuntimeCells

#print axioms Ash.OneShot.SourceAnnotatedRuntime.CellUpdate.erase
#print axioms Ash.OneShot.SourceAnnotatedRuntime.CellUpdate.capture_origin
#print axioms Ash.OneShot.SourceAnnotatedRuntime.CellUpdate.of_raw
#print axioms Ash.OneShot.SourceAnnotatedRuntimeCells.update_segment
#print axioms Ash.OneShot.SourceAnnotatedRuntimeCells.request_reply

#print axioms Ash.OneShot.SourceAnnotatedRuntimeCells.read_preserves
#print axioms Ash.OneShot.SourceAnnotatedRuntimeCells.write_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeCells.builtin_step_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeCells.request_reply_atPlan

#print axioms Ash.OneShot.SourceAnnotatedRuntimeCells.read_preserves_atPlan

#print axioms Ash.OneShot.SourceAnnotatedRuntimeCells.write_preserves_atPlan

#print axioms Ash.OneShot.SourceAnnotatedRuntimeCells.builtin_step_preserves_atPlan
