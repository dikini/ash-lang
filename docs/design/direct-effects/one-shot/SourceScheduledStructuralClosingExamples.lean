import SourceConsumingStructuralCapture
import SourceScheduledRetainedRecompositionExamples

/-! Canonical closing retains explicit callback bounds and dormant order,
and rechecks a callback that invokes an outside one-shot owner. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceScheduledSourceRechecking (Closing Expression)
open SourceScheduledSourceRechecking
open SourceBoundSnapshots.Retained (ofCapability)

def actions : Syntax.UsageTickets := fun _ => none
def phases := OwnerPhaseTransitions.empty

/-- Both dormant and waiting callbacks retain their own nested handler bounds. -/
theorem dormant_closing : Closing [] actions phases RecompositionExamples.liveSource .nil :=
  .live (.cleanup (.handler rfl (.operations rfl)) .empty)
    (.cleanup (.handler rfl (.operations rfl)) .empty)

theorem dormant_compiled :
    ∃ annotation : Retained [] (Forest.live (owner := 37)
        RecompositionExamples.callbackSegment RecompositionExamples.callbackSegment).forClosing .nil,
      annotation.Valid [] actions phases ∧
      ofCapability annotation = (ofCapability RecompositionExamples.liveSource).forClosing ∧
      (ofCapability annotation).Admitted :=
  dormant_closing.compile_admitted (recipeLaws []) (fun evidence => evidence)
    RecompositionExamples.live_valid RecompositionExamples.live_bounds

/-- Structural closing also handles free one-shot uses, not just effect interfaces. -/
def outerActions : Syntax.UsageTickets := fun owner => if owner = 37 then some ⟨true, false⟩ else none
def outerPhases := OwnerPhaseTransitions.available [37]
def outerWaiting := Forest.live (owner := 37) .nil .nil
def invokePlan := Plan.invoke (key := ⟨37, .resume⟩)
def invoking : Code [] invokePlan (.running outerWaiting) :=
  .resume (.running .hit) (.operations .nil) (.running (.operations .nil)) (.operations .nil)
def invokingSource : Retained [] (.cleanup (needs := []) invokePlan .nil) outerWaiting :=
  .cleanup invoking (.operations .nil)

theorem invoking_valid : invokingSource.Valid [] outerActions outerPhases :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem invoking_closing : Closing [] outerActions outerPhases invokingSource (.running outerWaiting) :=
  .cleanup (.resume (.running (.running .hit)) .empty (.protect .same) .same) .empty

theorem invoking_compiled :
    ∃ annotation : Retained [] (Forest.cleanup (needs := []) invokePlan .nil).forClosing (.running outerWaiting),
      annotation.Valid [] outerActions outerPhases ∧
      ofCapability annotation = (ofCapability invokingSource).forClosing :=
  invoking_closing.compile_retaining (recipeLaws []) (fun evidence => evidence) invoking_valid

/-- The source-validity premise cannot grant a second use of the outside owner. -/
theorem spent_outside_owner_rejected :
    ¬ invokingSource.Valid [] outerActions (OwnerPhaseTransitions.spend outerPhases 37) := by
  intro ready
  have available := ready.1.2.1
  simp [OwnerPhaseTransitions.spend] at available

/-- An actual capture cut with a bounded callback on each side. -/
def effect : Instance := .user 71 []
def contract : ProtectionContracts.ClauseContract := ⟨true, some [], some []⟩
def table := [(0, contract)]
def family (_owner : Nat) : SourceDependencyAnnotations.Dependencies := .pure
def families : SourceDependencyAnnotations.ClauseDependencies := [(0, some family, some family)]
def delimiter : Forest (Hints.handler (effect := effect) (table := table) (families := families) [] .nil) := .handler .nil
def saved := Forest.cleanup (needs := []) RecompositionExamples.plan delimiter
def waiting := RecompositionExamples.callbackSegment
def whole := saved.append waiting

def inside : Retained [] saved waiting :=
  .cleanup (RecompositionExamples.annotated (.running (delimiter.append waiting))) (.handler (.operations .nil))
def after : Retained [] waiting .nil :=
  .cleanup (RecompositionExamples.annotated (.running .nil)) (.operations .nil)

theorem inside_valid : inside.Valid [] actions phases := ⟨RecompositionExamples.annotated_valid _, rfl, rfl⟩
theorem after_valid : after.Valid [] actions phases := ⟨RecompositionExamples.annotated_valid _, rfl⟩
theorem inside_closing : Closing [] actions phases inside (.running waiting) :=
  .cleanup (.handler rfl (.operations rfl)) (.handler .empty)

def snapshot : SourceBoundSnapshots.Snapshot [] :=
  ⟨_, .request (effect := effect) (operation := 0), .absent, _, _, whole,
    (ofCapability inside).append (ofCapability after)⟩

theorem snapshot_admitted : snapshot.Admitted :=
  ⟨.absent .request, .cleanup (RecompositionExamples.annotated_bounds _)
    (.handler (.cleanup (RecompositionExamples.annotated_bounds _) .nil))⟩

theorem cut : SourceScheduledNeutral.Cut effect 0 contract (some family, some family) whole saved waiting :=
  .cleanup (.hit rfl rfl)

/-- Structural closing derives capture and canonical disposal correspondence. -/
theorem capture_disposal_correspondence :
    ∃ context : Context [] 19 [] (actions.insert 19 ⟨true, true⟩) (OwnerPhaseTransitions.introduce phases 19)
        (.live (owner := 19) saved waiting) .nil saved waiting,
      let captured : SourceBoundSnapshots.Snapshot [] :=
        ⟨_, Plan.pure, SourcePlanBounds.Annotation.absent, _, _, .live (owner := 19) saved waiting,
          .live (ofCapability inside) (ofCapability context.after)⟩
      SourceBoundSnapshots.Captured 19 snapshot captured ∧ captured.Admitted ∧
      (∀ permission, ofCapability (context.resumption permission).val = ofCapability inside) ∧
      ∀ permission,
        let closed := SourceBoundSnapshots.Snapshot.value
          ((ofCapability (context.closing permission).val).append
            (.running (.spent (owner := 19) (ofCapability context.after))))
        SourceBoundSnapshots.Discarded 19 captured closed ∧ closed.Admitted := by
  exact Context.capture_structural_snapshot (recipeLaws []) (fun evidence => evidence)
    inside after inside_valid (fun _ => inside_closing) (fun _ => ⟨rfl, by decide⟩)
    after_valid rfl (by decide) snapshot snapshot_admitted cut HEq.rfl
    (SourcePlanBounds.Annotation.absent (plan := Plan.pure)) (.absent .pure)

/-- Closing cannot silently replace the callback's explicit bounds by absence. -/
theorem closing_bounds_not_absent :
    (ofCapability inside).forClosing ≠ SourceBoundSnapshots.Retained.absent saved.forClosing := by
  intro same
  cases same

end Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.dormant_closing
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.dormant_compiled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.invoking_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.invoking_closing
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.invoking_compiled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.spent_outside_owner_rejected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.inside_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.after_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.inside_closing
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.snapshot_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.cut
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.capture_disposal_correspondence
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ClosingExamples.closing_bounds_not_absent
