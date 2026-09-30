import SourceScheduledCaptureSourceTransport
import SourceConsumingContextualCapture
import SourceScheduledRetainedRecompositionExamples

/-! A disposal-enabled request with explicit callback bounds on both sides of
its handler cut reuses the current request’s checked closing annotation for selected code,
capture and disposal snapshots. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledCapabilityAnnotations (Code Retained CaptureSource recipeLaws)
open SourceScheduledSourceRechecking (Closing)
open SourceScheduledSourceRechecking
open SourceConsumingClauseAnnotations (Body Declarations ClauseBounds Bounded SelectedSource Generated)
open SourceBoundSnapshots.Retained (ofCapability)

def actions : Syntax.UsageTickets := fun _ => none
def phases := OwnerPhaseTransitions.empty
def effect : Instance := .user 71 []
def contract : ProtectionContracts.ClauseContract := ⟨true, some [], some []⟩
def table := [(0, contract)]
def raw : ScopedExpressions.Code := .discard 9
def clauses : ScopedExpressions.Clauses := .cons 0 1 9 raw .nil
def family (owner : Nat) : SourceDependencyAnnotations.Dependencies := .invoke ⟨owner, .dispose⟩
def families : SourceDependencyAnnotations.ClauseDependencies := [(0, some family, some family)]
def bodies (owner : Nat) : Plan (family owner) := .invoke
def plans : ClausePlans clauses families := .cons (.available bodies) (.available bodies) .nil
def body (owner : Nat) : Body [] owner (bodies owner) := .dispose
def declarations : Declarations [] plans := .cons (.available body) (.available body) .nil
def bounds : ClauseBounds plans := .cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil

theorem bounded : Bounded bounds declarations [] :=
  .cons (.available (.available (fun _ => .dispose rfl)) (fun _ => .dispose))
    (.available (.available (fun _ => .dispose rfl)) (fun _ => .dispose)) .nil

def delimiter : Forest (Hints.handler (effect := effect) (table := table) (families := families) [] .nil) := .handler .nil
def saved := Forest.cleanup (needs := []) RecompositionExamples.plan delimiter
def waiting := RecompositionExamples.callbackSegment
def whole := saved.append waiting

def inside : Retained [] saved waiting :=
  .cleanup (RecompositionExamples.annotated (.running (delimiter.append waiting))) (.handler (.operations .nil))
def after : Retained [] waiting .nil :=
  .cleanup (RecompositionExamples.annotated (.running .nil)) (.operations .nil)
def source : Retained [] whole .nil :=
  .cleanup (RecompositionExamples.annotated (.running (delimiter.append waiting))) (.handler after)

theorem inside_valid : inside.Valid [] actions phases := ⟨RecompositionExamples.annotated_valid _, rfl, rfl⟩
theorem after_valid : after.Valid [] actions phases := ⟨RecompositionExamples.annotated_valid _, rfl⟩
theorem source_valid : source.Valid [] actions phases := ⟨RecompositionExamples.annotated_valid _, rfl, after_valid⟩
theorem closing : Closing [] actions phases inside (.running waiting) :=
  .cleanup (.handler rfl (.operations rfl)) (.handler .empty)

theorem cut : SourceScheduledNeutral.Cut effect 0 contract (some family, some family) whole saved waiting :=
  .cleanup (.hit rfl rfl)

theorem capture_source_exists : ∃ captured : CaptureSource [] actions phases cut source raw.requiredActions,
    ofCapability captured.inside = ofCapability inside ∧ ofCapability captured.after = ofCapability after := by
  obtain ⟨annotation, ready, canonical⟩ := closing.compile_retaining (recipeLaws []) (fun evidence => evidence) inside_valid
  have requested : (Code.selected cut (fun _ => .cleanup (.handler .nil)) (fun _ => annotation)).Valid [] actions phases :=
    ⟨by decide, fun _ => ready⟩
  exact CaptureSource.of_selected cut (fun _ => .cleanup (.handler .nil)) (fun _ => annotation) requested
    source source_valid (ofCapability inside) (ofCapability after) HEq.rfl
    (fun _ => rfl) (fun _ => canonical)

noncomputable def captureSource : CaptureSource [] actions phases cut source raw.requiredActions :=
  Classical.choose capture_source_exists

def snapshot : SourceBoundSnapshots.Snapshot [] :=
  ⟨_, .request (effect := effect) (operation := 0), .absent, _, _, whole, ofCapability source⟩
theorem snapshot_admitted : snapshot.Admitted :=
  ⟨.absent .request, .cleanup (RecompositionExamples.annotated_bounds _)
    (.handler (.cleanup (RecompositionExamples.annotated_bounds _) .nil))⟩

theorem fresh : actions 19 = none := rfl
theorem absent : 19 ∉ SourceDependencyOwners.owners snapshot.scope := by decide
theorem permits : raw.requiredActions.dispose = true → contract.dispose = true := fun _ => rfl
noncomputable def context := Context.of_request (recipeLaws []) (fun evidence => evidence)
  cut source raw.requiredActions captureSource permits fresh absent

theorem selected : SourcePlannedRecipeDeclarations.Selected 0 false plans 1 9 raw bodies := .ordinary
theorem selected_source : SelectedSource 19 declarations selected (body 19) := .ordinary
theorem contextual : At (recipeLaws []) (fun evidence => evidence) (body 19) context := .dispose

/-- The same generated disposal clause, captured snapshot and actual closing
context share canonical metadata. Both callbacks keep their explicit bounds. -/
theorem capture_and_disposal :
    ∃ annotation : Code [] (bodies 19) (.live (owner := 19) saved waiting),
      (SourceScheduledCaptureAnnotations.Capture.site cut selected annotation).Valid [] actions phases ∧
      Generated (actions.insert 19 raw.requiredActions) context.continuationBounds (body 19) annotation ∧
      ∃ savedBounds : SourceBoundSnapshots.Retained [] saved,
        let captured : SourceBoundSnapshots.Snapshot [] :=
          ⟨_, bodies 19, SourcePlanBounds.ofCode annotation, _, _, .live (owner := 19) saved waiting,
            .live savedBounds (ofCapability context.after)⟩
        SourceBoundSnapshots.Captured 19 snapshot captured ∧ captured.Admitted ∧
        (∀ permission, context.continuationBounds.resumption permission = savedBounds) ∧
        ∀ permission,
          let closed := SourceBoundSnapshots.Snapshot.value
            ((ofCapability (context.closing permission).val).append
              (.running (.spent (owner := 19) (ofCapability context.after))))
          SourceBoundSnapshots.Discarded 19 captured closed ∧ closed.Admitted :=
  SelectedSource.capture_source_snapshot (recipeLaws []) (fun evidence => evidence) snapshot snapshot_admitted
    bounded cut selected selected_source source captureSource permits rfl
    fresh absent contextual rfl

/-- The actual request context cannot erase the bounded captured callback. -/
theorem closing_not_absent :
    ofCapability (context.closing (by rfl)).val ≠ SourceBoundSnapshots.Retained.absent saved.forClosing := by
  obtain ⟨savedBounds, original, _, closed⟩ := Context.of_request_bounds
    (recipeLaws []) (fun evidence => evidence) cut source raw.requiredActions captureSource permits fresh absent
  intro erased
  have erasedCanonical := (closed (by rfl)).symm.trans erased
  cases savedBounds with
  | cleanup callback delimiterBounds =>
      cases delimiterBounds with
      | handler empty =>
          cases empty
          have callbackSame := (SourceBoundSnapshots.Retained.cleanup.inj (eq_of_heq original)).1
          have callbackAbsent := (SourceBoundSnapshots.Retained.cleanup.inj erasedCanonical).1
          rw [callbackSame] at callbackAbsent
          cases callbackAbsent

def extraActions := actions.insert 88 ⟨true, true⟩
def extraPhases := OwnerPhaseTransitions.available [88]

/-- The new request evidence composes real permission/phase changes with
world extension, retaining the original callback metadata and closing validity. -/
noncomputable def transported : CaptureSource [] extraActions extraPhases cut
    (source.world_weaken (List.nil_subset [4])) raw.requiredActions :=
  (captureSource.transport (Syntax.fresh_usage_insert_extends (by rfl))
    (fun name _ available => by cases available)).world_weaken (List.nil_subset [4])

theorem transported_closing :
    ∃ annotation : Retained [4] saved.forClosing (.running waiting),
      annotation.Valid [] extraActions extraPhases ∧
      ofCapability annotation = (ofCapability transported.inside).forClosing :=
  transported.closing rfl

theorem transported_saved_bounds : ofCapability transported.inside =
    (ofCapability inside).world_weaken (List.nil_subset [4]) := by
  change ofCapability (captureSource.inside.world_weaken (List.nil_subset [4])) = _
  rw [Retained.ofCapability_world_weaken, captureSource, (Classical.choose_spec capture_source_exists).1]

end Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.bounded
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.inside_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.after_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.source_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.closing
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.cut
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.captureSource
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.snapshot_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.fresh
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.absent
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.permits
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.selected_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.contextual
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.capture_and_disposal

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.closing_not_absent

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.transported_closing

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.transported_saved_bounds

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CanonicalRequestExamples.capture_source_exists
