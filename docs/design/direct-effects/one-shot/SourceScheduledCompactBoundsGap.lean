import SourceScheduledNormalizedRechecking

/-! Compact operation annotations have no constructor spine in their bound
projection. Exact equality to that projection can forbid a sound structural
rechecking after an external operation changes to a disposing interpretation. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies disposeTable disposeDependencies)
open SourceRequestFootprints (Footprint)

def plan := Plan.sequence (.request (effect := effectE) (operation := 0)) .pure
def before : Forest (Hints.handler (effect := effectE) (table := resumeTable)
    (families := resumeDependencies) [] .nil) := .handler .nil
def after := Forest.handler (effect := effectE) (table := disposeTable)
  (families := disposeDependencies) (required := []) before
def compact : Code [] plan before :=
  .operations [(effectE, 0)] (.sequence .request .pure) (.sequence .request .pure)
def expanded : Code [] plan before :=
  .sequence (.operations [(effectE, 0)] .request .request) (.operations [] .pure .pure)
def actions : Syntax.UsageTickets := fun _ => none
def phases := OwnerPhaseTransitions.available []

theorem original_valid : compact.Valid [] actions phases ∧ expanded.Valid [] actions phases :=
  ⟨rfl, rfl, rfl⟩

private theorem request_member
    {checking : SourcePlanSignatures.Signature dependencies}
    (footprint : Footprint checking required) (same : dependencies = .request effect operation) :
    (effect, operation) ∈ required := by
  induction footprint with
  | request => cases same; exact List.mem_cons_self
  | weaken body included ih => exact included (ih same)
  | pure | handledRequest | sequence | choice | handler | cleanup | resource => cases same

private theorem sequence_request_member
    {checking : SourcePlanSignatures.Signature dependencies}
    (footprint : Footprint checking required)
    (same : dependencies = .sequence (.request effect operation) .pure) :
    (effect, operation) ∈ required := by
  induction footprint with
  | sequence first second ihFirst ihSecond =>
      cases same
      exact List.mem_append_left _ (request_member first rfl)
  | weaken body included ih => exact included (ih same)
  | pure | request | handledRequest | choice | handler | cleanup | resource => cases same

/-- This is an obstruction for every target annotation with the compact bound
shape, not only for the current rechecking algorithm's chosen output. -/
theorem no_compact_target (annotation : Code [] plan after)
    (same : SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode compact) :
    ¬ annotation.Valid [] actions phases := by
  intro ready
  cases annotation with
  | operations required footprint declared =>
      have capability := SourceContextualRequirements.check_requirements_iff.mp ready _
        (sequence_request_member footprint rfl)
      have impossible := SourceContextualRequirements.check_capability_iff.mpr capability
      change false = true at impossible
      cases impossible
  | sequence first second => cases same

theorem no_exact_rechecking : ¬ Expression [] actions phases compact after := by
  intro changed
  obtain ⟨annotation, ready, kept⟩ := changed.compile_retaining
    (recipeLaws []) (fun evidence => evidence) original_valid.1
  exact no_compact_target annotation kept ready

/-- The same computation is admitted when its original annotation exposes
sequencing. Fresh capture uses the existing empty callback derivation. -/
theorem expanded_rechecked : Expression [] actions phases expanded after :=
  .sequence (.freshInterfaces (.plain (.hit rfl rfl)) (.plain (.handler .nil))
    (.plain (.handler .nil)) (.plain (.handler .nil)) (fun _ => rfl)
    (by decide) (fun _ => .plain .pure (.handler .nil))) (.operations rfl)

theorem expanded_generated : ∃ annotation : Code [] plan after,
    annotation.Valid [] actions phases ∧
    SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode expanded :=
  expanded_rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) original_valid.2

theorem bound_shapes_differ : SourcePlanBounds.ofCode compact ≠ SourcePlanBounds.ofCode expanded := by
  intro same
  cases same

/-- The representation change loses no recorded handler-bound observation. -/
theorem bound_observations_same (path : SourcePlanBounds.Path) :
    (SourcePlanBounds.ofCode compact).lookup path operation held =
      (SourcePlanBounds.ofCode expanded).lookup path operation held := by
  cases path <;> rfl

/-- Any normalization output with the canonical spine supports the existing
recursive rules. The proof does not choose the compiler's annotation shape. -/
theorem canonical_rechecked (source : Code [] plan before)
    (spine : SourcePlanBounds.ofCode source = SourcePlanBounds.ofCode expanded) :
    Expression [] actions phases source after := by
  cases source with
  | operations required footprint declared => cases spine
  | sequence first second =>
      apply Expression.sequence
      · exact .freshInterfaces (.plain (.hit rfl rfl)) (.plain (.handler .nil))
          (.plain (.handler .nil)) (.plain (.handler .nil)) (fun _ => rfl)
          (by decide) (fun _ => .plain .pure (.handler .nil))
      · cases second with
        | operations required footprint declared => exact .reinterface .pure rfl

/-- Use the actual generated normal form of the compact original source. -/
theorem normalized_rechecked : Expression [] actions phases
    (compact.normalized (fun evidence => evidence) original_valid.1) after :=
  canonical_rechecked _ (compact.normalized_bounds (fun evidence => evidence) original_valid.1)

/-- Normalization followed by rechecking fixes the counterexample while
preserving every original bound observation. Exact equality is retained to
the canonical spine, never asserted between unequal representations. -/
theorem normalized_generated : ∃ annotation : Code [] plan after,
    annotation.Valid [] actions phases ∧
    SourcePlanBounds.ofCode annotation = (SourcePlanBounds.ofCode compact).normalize ∧ annotation.Expanded ∧
    ∀ path operation held,
      (SourcePlanBounds.ofCode annotation).lookup path operation held =
        (SourcePlanBounds.ofCode compact).lookup path operation held :=
  compact.recheck_normalized (recipeLaws []) (fun evidence => evidence) original_valid.1 normalized_rechecked

/-- A retained compact annotation can already have canonical metadata. Its
shape must therefore be proved separately from normalization of its bounds. -/
def compactRetained : SourceScheduledCapabilityAnnotations.Retained [] (Forest.plain Plan.pure .nil) .nil :=
  .operations (.plain .nil [] .pure .pure .nil)

theorem canonical_metadata_insufficient :
    compactRetained.Valid [] actions phases ∧
    SourceBoundSnapshots.Retained.ofCapability compactRetained =
      (SourceBoundSnapshots.Retained.ofCapability compactRetained).normalize ∧
    ¬ compactRetained.Expanded :=
  ⟨rfl, rfl, fun impossible => impossible⟩

end Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.no_compact_target
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.no_exact_rechecking
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.expanded_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.expanded_generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.bound_shapes_differ
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.bound_observations_same

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.canonical_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.normalized_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.normalized_generated

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.CompactBoundsGap.canonical_metadata_insufficient
