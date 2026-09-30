import SourceAnnotatedStoredResumption
import SourceAnnotatedRuntimeCells

/-! Cell operations change only the selected cell payload. Installed handler
packets and dormant captures are retained at their actual source interfaces. -/
namespace Ash.OneShot.SourceAnnotatedRuntime
open SourceConsumingStoredBounds (StackBounds)

inductive CellPackets {families : SourceDependencyCapture.Families} :
    {identity : Nat} → {old new : Int} → {before after : Stack} →
    CellUpdate identity old new before after → StackBounds families before → StackBounds families after → Prop where
  | hit : CellPackets (.hit (identity := identity) (old := old) (new := new) (scope := scope) (answer := answer) (tail := tail))
      (.push .cell stored) (.push .cell stored)
  | push : CellPackets update stored nextStored →
      CellPackets (.push miss update) (.push packet stored) (.push packet nextStored)
  | live : CellPackets update stored nextStored →
      CellPackets (.live (ticket := ticket) (q := q) (a := a) (scope := scope) update)
        (.live saved stored) (.live saved nextStored)
  | spent : CellPackets update stored nextStored →
      CellPackets (.spent (ticket := ticket) (a := a) (scope := scope) update) (.spent stored) (.spent nextStored)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem CellPackets.admitted (moved : CellPackets update stored nextStored)
    (admitted : stored.Admitted world required) : nextStored.Admitted world required := by
  induction moved with
  | hit => cases admitted with
    | push head tail => exact .push .cell tail
  | push moved ih => cases admitted with
    | push head tail => exact .push head (ih tail)
  | live moved ih => cases admitted with
    | live saved tail => exact .live saved (ih tail)
  | spent moved ih => cases admitted with
    | spent tail => exact .spent (ih tail)

end Ash.OneShot.SourceAnnotatedRuntime

namespace Ash.OneShot.SourceAnnotatedStoredCells

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceAnnotatedSources (ValueSummary)
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available spendAll)

theorem update_segment {hints : SourceContextualHints.Hints receiving} {forest : SourceRetainedPlans.Forest hints}
    (update : SourceAnnotatedRuntime.CellUpdate identity old new before after)
    (source : SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      before input output demand requirements records forest outside incoming outgoing stored) :
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after,
    SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      after input output demand requirements records forest outside incoming outgoing nextStored ∧ SourceAnnotatedRuntime.CellPackets update stored nextStored := by
  induction update generalizing input demand requirements records receiving incoming with
  | hit => cases source with
    | push head rest bound =>
      rcases head with ⟨head, packetSource⟩
      cases packetSource
      cases head with
      | cell scopeKnown noEscape annotation interface => cases interface with
        | cell scopeTyped excluded =>
          exact ⟨_, .push ⟨.cell scopeKnown noEscape annotation (.cell scopeTyped excluded), .cell⟩ rest bound, .hit⟩
  | push miss next ih => cases source with
    | push head rest bound =>
      obtain ⟨nextStored, checked, moved⟩ := ih rest
      refine ⟨_, ?_, .push (miss := miss) moved⟩
      simpa only [RecursiveCells.update_context next.erase] using SourceAnnotatedStoredTyping.Segment.push head checked bound
  | live next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound rest resume close bound =>
      obtain ⟨nextStored, checked, moved⟩ := ih rest
      exact ⟨_, .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound checked resume close bound, .live moved⟩
  | spent next ih => cases source with
    | spent known annotation scope rest bound =>
      obtain ⟨nextStored, checked, moved⟩ := ih rest
      exact ⟨_, .spent known annotation scope checked bound, .spent moved⟩
theorem request_reply_atPackets {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before}
    {plan : SourceDeclarationPlans.Plan dependencies}
    (source : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect (.cell identity)) operation operand) before plan forest output demand row stored evidence)
    (update : SourceAnnotatedRuntime.CellUpdate identity old new before after)
    (isValue : operand.erase.IsValue)
    (response : ∀ input result, operations (.cell identity) operation = some (input, result) →
      ValueSummary operations policy contracts world (fun _ => none) [] reply result)
    (replyValue : reply.erase.IsValue)
    (_raw : RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) operation operand.erase, scope, before.erase⟩
      ⟨reply.erase, scope, after.erase⟩ [] []) :
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after, ∃ nextRow,
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        scope reply after .pure forest output demand nextRow nextStored evidence ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before.erase)) [] (available (ownedTickets after.erase)) ∧
      SourceAnnotatedRuntime.CellPackets update stored nextStored := by
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
        obtain ⟨nextStored, pendingAfter, packets⟩ := update_segment update pending
        rw [owners] at pendingAfter
        have closingAfter := DeclaredSourceClosing.update_records update.erase closing
        have templatesAfter := templates.after_step (nextRoot := after) closingAfter (List.Subset.refl _)
          (fun _ _ located => update.capture_origin located) unique
        refine ⟨nextStored, pendingRow, ?_, included, owners ▸ .nil, packets⟩
        apply SourceAnnotatedStoredResumption.value_configuration_atPackets (response _ _ known) replyValue scopeTyped pendingAfter
          closingAfter templatesAfter matched (owners ▸ unique) _ (checked_footprint_subset accepted included.subset)
        simpa only [spendAll, owners] using pendingCheck

theorem read_preserves_atPackets {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before}
    {plan : SourceDeclarationPlans.Plan dependencies}
    (signature : operations.erase.erase.ports (.cell identity) 0 = some (.reference identity, .integer))
    (source : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef referenceHint (.activation identity))) before plan forest output demand row stored evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity payload payload before after) :
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after, ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before.erase⟩
        ⟨.integer payload, scope, after.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        scope (.integer .integer payload) after .pure forest output demand nextRow nextStored evidence ∧ nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before.erase)) [] (available (ownedTickets after.erase)) ∧
      SourceAnnotatedRuntime.CellPackets selected stored nextStored := by
  have raw := RawStep.readCell identity payload scope before.erase after.erase selected.erase
  obtain ⟨nextStored, nextRow, checked, included, trace, packets⟩ := request_reply_atPackets source selected (by trivial) (reply := .integer .integer payload) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (CoherentSourceTypes.port_lookup
      (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known)))))).2
    cases result <;> cases output
    exact .checked rfl rfl .integer) trivial raw
  exact ⟨nextStored, nextRow, raw, checked, included, trace, packets⟩

theorem write_preserves_atPackets {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before}
    {plan : SourceDeclarationPlans.Plan dependencies}
    (signature : operations.erase.erase.ports (.cell identity) 1 = some (.product (.reference identity) .integer, .unit))
    (source : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect (.cell identity)) 1
        (.pair pairHint (.resourceRef referenceHint (.activation identity)) (.integer integerHint new))) before plan forest output demand row stored evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity old new before after) :
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after, ∃ nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before.erase⟩
        ⟨.unit, scope, after.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        scope (.unit .unit) after .pure forest output demand nextRow nextStored evidence ∧ nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets before.erase)) [] (available (ownedTickets after.erase)) ∧
      SourceAnnotatedRuntime.CellPackets selected stored nextStored := by
  have raw := RawStep.writeCell identity old new scope before.erase after.erase selected.erase
  obtain ⟨nextStored, nextRow, checked, included, trace, packets⟩ := request_reply_atPackets source selected (by trivial) (reply := .unit .unit) (by
    intro input result known
    have output := (Prod.mk.inj (Option.some.inj (signature.symm.trans (CoherentSourceTypes.port_lookup
      (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known)))))).2
    cases result <;> cases output
    exact .checked (by decide) (by decide) .unit) trivial raw
  exact ⟨nextStored, nextRow, raw, checked, included, trace, packets⟩

theorem builtin_step_preserves_atPackets {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before}
    {plan : SourceDeclarationPlans.Plan dependencies}
    (signature : operations.erase.erase.ports = ScopedPorts.withCellSignatures users)
    (source : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.perform hint effect operation operand) before plan forest output demand row stored evidence)
    (raw : RawStep ⟨.perform effect operation operand.erase, scope, before.erase⟩ rawAfter [] [])
    (isValue : operand.erase.IsValue) :
    ∃ next : SourceAnnotatedRuntime.Configuration,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families next.stack, ∃ nextRow,
      next.erase = rawAfter ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack .pure forest output demand nextRow nextStored evidence ∧ nextRow.Sublist row ∧
      (∃ identity old new, ∃ update : SourceAnnotatedRuntime.CellUpdate identity old new before next.stack,
        SourceAnnotatedRuntime.CellPackets update stored nextStored) := by
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
    obtain ⟨nextStored, nextRow, step, next, included, trace, packets⟩ := read_preserves_atPackets (by rw [signature]; rfl) source lifted
    exact ⟨⟨_, _, _⟩, nextStored, nextRow, rfl, next, included, ⟨_, _, _, lifted, packets⟩⟩
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
    obtain ⟨nextStored, nextRow, step, next, included, trace, packets⟩ := write_preserves_atPackets (by rw [signature]; rfl) source lifted
    exact ⟨⟨_, _, _⟩, nextStored, nextRow, rfl, next, included, ⟨_, _, _, lifted, packets⟩⟩

end Ash.OneShot.SourceAnnotatedStoredCells

#print axioms Ash.OneShot.SourceAnnotatedRuntime.CellPackets.admitted
#print axioms Ash.OneShot.SourceAnnotatedStoredCells.update_segment
#print axioms Ash.OneShot.SourceAnnotatedStoredCells.request_reply_atPackets
#print axioms Ash.OneShot.SourceAnnotatedStoredCells.read_preserves_atPackets
#print axioms Ash.OneShot.SourceAnnotatedStoredCells.write_preserves_atPackets
#print axioms Ash.OneShot.SourceAnnotatedStoredCells.builtin_step_preserves_atPackets
