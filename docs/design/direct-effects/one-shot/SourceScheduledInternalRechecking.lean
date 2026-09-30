import SourceScheduledBypassedRechecking

/-! A request selected inside an unchanged prefix retains its actual capture.
Only the waiting receiver changes. Exact cuts, guards and source footprint
evidence reuse the existing selection and source-rechecking proofs. -/
namespace Ash.OneShot.SourceScheduledNeutral
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Appending a receiver preserves the exact selected capture. Reconstruct
the original cut and reuse waiting replacement and ordered associativity. -/
theorem Cut.suffix
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : Cut effect operation contract modes whole saved waiting)
    {outsideHints : Hints outsideScope} (outside : Forest outsideHints) :
    Cut effect operation contract modes (whole.append outside) saved (waiting.append outside) := by
  apply (SourceScheduledRecomposition.predicate_congr cut.erase.reconstruct_scope cut.erase.hints cut.forest
    (fun before => Cut effect operation contract modes (before.append outside) saved (waiting.append outside))).mpr
  apply (SourceScheduledRecomposition.predicate_congr
    (SourceDependencyChecks.scope_append_assoc _ _ _)
    (SourcePlannedRecomposition.hints_append_assoc _ _ _)
    (SourceScheduledRecomposition.forest_append_assoc saved waiting outside)
    (fun before => Cut effect operation contract modes before saved (waiting.append outside))).mpr
  exact SourceScheduledHandlerRequests.replace_waiting cut (waiting.append outside)

/-- Recover the actual internal cut from an existing whole-source selection.
The prefix stops lookup, so the outside suffix cannot provide the selection.
Existing hint/forest uniqueness authenticates the same saved plan and the exact
waiting decomposition; no replacement cut is assumed. -/
theorem Cut.drop_suffix
    {frontHints : Hints frontScope} {outsideHints : Hints outsideScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {front : Forest frontHints} {outside : Forest outsideHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : Cut effect operation contract modes (front.append outside) saved waiting)
    (stopped : SourceHandlerRequirements.reaches effect frontScope = false) :
    ∃ localScope, ∃ localHints : Hints localScope, ∃ middle : Forest localHints,
      Cut effect operation contract modes front saved middle ∧
      waitingScope = localScope.append outsideScope ∧
      HEq waitingHints (localHints.append outsideHints) ∧ HEq waiting (middle.append outside) := by
  have chosen := cut.erase.lookup
  rw [SourceHandlerSelection.select_append, stopped, if_neg Bool.false_ne_true] at chosen
  cases localFound : SourceDependencyCapture.select effect operation frontScope with
  | none => simp only [localFound, Option.map_none] at chosen; cases chosen
  | some selected => cases selected with
    | builtin identity =>
        simp only [localFound, Option.map_some, SourceHandlerSelection.appendWaiting] at chosen
        cases chosen
    | handler captured tail selectedContract selectedModes =>
        simp only [localFound, Option.map_some, SourceHandlerSelection.appendWaiting, Option.some.injEq] at chosen
        cases chosen
        obtain ⟨insideHints, localHints, selected⟩ := SourcePlannedCuts.of_lookup frontHints localFound
        obtain ⟨inside, middle, localCut⟩ := SourceScheduledNeutral.of_cut selected front
        have extended := localCut.suffix outside
        obtain ⟨rfl, rfl⟩ := extended.erase.unique cut.erase.hints
        obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (extended.forest.symm.trans cut.forest))
        exact ⟨_, _, middle, localCut, rfl, HEq.rfl, HEq.rfl⟩

end Ash.OneShot.SourceScheduledNeutral

namespace Ash.OneShot.SourceRequestFootprints

/-- Weakening may add conservative requirements but cannot omit the actual
atomic request. This follows the same source induction as no_invocation. -/
theorem Footprint.request_member {checking : SourcePlanSignatures.Signature dependencies}
    (footprint : Footprint checking required) (same : dependencies = .request effect operation) :
    (effect, operation) ∈ required := by
  induction footprint with
  | request => cases same; exact List.mem_cons_self
  | pure | handledRequest | sequence | choice | handler | cleanup | resource => cases same
  | weaken body included ih => exact included (ih same)

end Ash.OneShot.SourceRequestFootprints

namespace Ash.OneShot.SourceContextualClauses
open SourceDependencyCapture (select)

/-- Both-mode availability belongs to the unchanged selected contract, not
its waiting receiver. No ordering or interpretation exchange is involved. -/
theorem RequestCapability.same_contract
    (capability : RequestCapability effect operation before)
    (oldFound : select effect operation before = some (.handler saved waiting contract modes))
    (nextFound : select effect operation after = some (.handler nextSaved nextWaiting contract modes)) :
    RequestCapability effect operation after := by
  cases capability with
  | builtin found => cases Option.some.inj (found.symm.trans oldFound)
  | handler found denied rows bodies =>
      cases Option.some.inj (found.symm.trans oldFound)
      exact .handler nextFound denied rows bodies

end Ash.OneShot.SourceContextualClauses

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceDependencyOwners (PendingWithin owners)

variable [DeclarationPolicy]

/-- The operation-only atomic case derives its precise target capability from
original source evidence. Conservative unused requirements need not survive. -/
theorem Expression.internal_operations
    {frontHints : Hints frontScope} {front : Forest frontHints}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes front saved waiting)
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {nextHints : Hints nextScope} (next : Forest nextHints)
    {footprint : RequestFootprint (.request (effect := effect) (operation := operation)) required}
    {declared : SourceScheduledSourceInterfaces.Declared world
      (SourcePlanSignatures.signature (.request (effect := effect) (operation := operation)))}
    (ready : (Code.operations (forest := front.append outside) required footprint declared).Valid outward actions phases) :
    Expression outward actions phases (Code.operations (forest := front.append outside) required footprint declared)
      (front.append next) := by
  have supplied := SourceContextualRequirements.check_requirements_iff.mp ready _ (footprint.request_member rfl)
  exact .capability (supplied.same_contract (cut.suffix outside).erase.lookup (cut.suffix next).erase.lookup)

/-- Selected requests inside callback-local scopes are the unchanged-capture
case, even when the outer receiver changes arbitrarily behind those scopes. -/
theorem Expression.internal_selected
    {frontHints : Hints frontScope} {front : Forest frontHints}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes front saved waiting)
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {nextHints : Hints nextScope} (next : Forest nextHints)
    {oldBound : contract.dispose = true → PendingWithin world (owners savedScope) savedScope}
    {oldClosing : contract.dispose = true →
      Retained world saved.forClosing (.running (waiting.append outside))}
    (ready : (Code.selected (cut.suffix outside) oldBound oldClosing).Valid outward actions phases)
    (closing : ∀ disposes, ReceiverChange outward actions phases (oldClosing disposes)
      (.running (waiting.append next))) :
    Expression outward actions phases (Code.selected (cut.suffix outside) oldBound oldClosing) (front.append next) :=
  .same_capture_selected (cut.suffix next) ready closing

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledNeutral.Cut.suffix
#print axioms Ash.OneShot.SourceScheduledNeutral.Cut.drop_suffix
#print axioms Ash.OneShot.SourceRequestFootprints.Footprint.request_member
#print axioms Ash.OneShot.SourceContextualClauses.RequestCapability.same_contract
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.internal_operations
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.internal_selected
