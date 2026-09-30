import SourceConsumingContextualCaptureExamples
import SourceScheduledRetainedRecompositionExamples

/-! Nonempty bound data in callbacks, dormant work and both sides of a capture
must survive the source split and the actual contextual resumption evidence. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (Code Retained CaptureSource recipeLaws)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceScheduledSourceRechecking

/-- Splitting a recomposed callback/dormant forest retains its entire snapshot. -/
theorem callback_dormant_roundtrip :
    ∃ source : Retained [] (RecompositionExamples.front.append RecompositionExamples.suffix) .nil,
      source.Valid [] CaptureExamples.actions CaptureExamples.phases ∧
      ∃ inside : Retained [] RecompositionExamples.front (RecompositionExamples.suffix.append .nil), ∃ tail : Retained [] RecompositionExamples.suffix .nil,
        inside.Valid [] CaptureExamples.actions CaptureExamples.phases ∧ tail.Valid [] CaptureExamples.actions CaptureExamples.phases ∧
        (ofCapability inside).append (ofCapability tail) = (ofCapability RecompositionExamples.frontSource).append (ofCapability RecompositionExamples.suffixSource) := by
  obtain ⟨source, valid, joined⟩ := RecompositionExamples.joined_bounds (actions := CaptureExamples.actions) (phases := CaptureExamples.phases)
  obtain ⟨inside, tail, insideReady, tailReady, split⟩ :=
    SourceScheduledCapabilityAnnotations.retained_split_retaining RecompositionExamples.front RecompositionExamples.suffix source valid
  exact ⟨source, valid, inside, tail, insideReady, tailReady, split.trans joined⟩

/-- A receiver-only spent marker leaves callback and dormant metadata intact. -/
theorem callback_dormant_receiver :
    ∃ next : Retained [] RecompositionExamples.front (.spent (owner := 19) (RecompositionExamples.suffix.append .nil)),
      next.Valid [] CaptureExamples.actions CaptureExamples.phases ∧ ofCapability next = ofCapability RecompositionExamples.frontSource :=
  RecompositionExamples.frontSource.expand_receiver_retaining (recipeLaws []) (fun evidence => evidence) RecompositionExamples.front_valid (.history .refl)

def waiting := RecompositionExamples.suffix
def saved := Forest.plain RecompositionExamples.plan CaptureExamples.saved
def whole := saved.append waiting

def source : Retained [] whole .nil :=
  .plain (RecompositionExamples.annotated (CaptureExamples.saved.append waiting)) (.handler RecompositionExamples.suffixSource)

/-- Replacing the source snapshot with all-absent metadata is observably wrong. -/
theorem source_bounds_not_absent : ofCapability source ≠ SourceBoundSnapshots.Retained.absent whole := by
  intro same
  cases same

theorem source_valid : source.Valid [] CaptureExamples.actions CaptureExamples.phases :=
  ⟨RecompositionExamples.annotated_valid _, rfl, RecompositionExamples.suffix_valid⟩

theorem cut : SourceScheduledNeutral.Cut CaptureExamples.outer 0 CaptureExamples.offered (some CaptureExamples.family, some CaptureExamples.family)
    whole saved waiting := .plain (.hit rfl rfl)

def request : Code [] (.request (effect := CaptureExamples.outer) (operation := 0)) whole :=
  .selected cut (fun impossible => Bool.noConfusion impossible) (fun impossible => Bool.noConfusion impossible)

theorem request_valid : request.Valid [] CaptureExamples.actions CaptureExamples.phases :=
  ⟨by decide, fun impossible => Bool.noConfusion impossible⟩

def snapshot : SourceBoundSnapshots.Snapshot [] :=
  ⟨_, .request (effect := CaptureExamples.outer) (operation := 0), .absent, _, _, whole, ofCapability source⟩

theorem snapshot_admitted : snapshot.Admitted :=
  ⟨.absent .request, .plain (RecompositionExamples.annotated_bounds _) (.handler (.plain (RecompositionExamples.annotated_bounds _) .nil))⟩

theorem absent : 19 ∉ SourceDependencyOwners.owners snapshot.scope := by decide

noncomputable def captureSource : CaptureSource [] CaptureExamples.actions CaptureExamples.phases cut source
    CaptureExamples.raw.requiredActions := CaptureSource.without_disposal cut source source_valid
      (SourceDependencyCapture.check_capture_iff.mp (by decide)) rfl

noncomputable def context := Context.of_request (recipeLaws []) (fun evidence => evidence)
  cut source CaptureExamples.raw.requiredActions captureSource CaptureExamples.permits CaptureExamples.fresh absent

/-- A nonempty saved plan and nonempty waiting plan both keep their bound data.
The actual context's resumptions use the saved component of this runtime capture. -/
theorem context_matches_capture :
    ∃ savedBounds : SourceBoundSnapshots.Retained [] saved,
      let captured : SourceBoundSnapshots.Snapshot [] :=
        ⟨_, Plan.pure, SourcePlanBounds.Annotation.absent, _, _, .live (owner := 19) saved waiting,
          .live savedBounds (ofCapability context.after)⟩
      SourceBoundSnapshots.Captured 19 snapshot captured ∧ captured.Admitted ∧
      ∀ permission, ofCapability (context.resumption permission).val = savedBounds :=
  by
    obtain ⟨savedBounds, moved, admitted, kept, _⟩ := Context.of_request_snapshot (plan := Plan.pure)
      (recipeLaws []) (fun evidence => evidence) snapshot snapshot_admitted
      cut source CaptureExamples.raw.requiredActions captureSource
      CaptureExamples.permits CaptureExamples.fresh absent rfl .absent (.absent .pure)
    exact ⟨savedBounds, moved, admitted, kept⟩

/-- Exact source pieces can also be used directly, without choosing a context. -/
theorem valid_pieces_match_capture :
    ∃ inside : Retained [] saved waiting, ∃ tail : Retained [] waiting .nil,
      inside.Valid [] CaptureExamples.actions CaptureExamples.phases ∧ tail.Valid [] CaptureExamples.actions CaptureExamples.phases ∧
      SourceBoundSnapshots.Captured 19 snapshot
        ⟨_, Plan.pure, SourcePlanBounds.Annotation.absent, _, _, .live (owner := 19) saved waiting,
          .live (ofCapability inside) (ofCapability tail)⟩ ∧
      (ofCapability inside).Admitted ∧ (ofCapability tail).Admitted :=
  SourceScheduledCapabilityAnnotations.capture_source_snapshot_admitted snapshot snapshot_admitted
    cut source source_valid rfl .absent (.absent .pure)

end Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.callback_dormant_roundtrip
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.callback_dormant_receiver
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.source_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.cut
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.request_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.snapshot_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.absent
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.context_matches_capture
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.valid_pieces_match_capture

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RetentionExamples.source_bounds_not_absent
