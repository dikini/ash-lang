import SourceConsumingContextualCapture

/-! Capture selects a handler-bearing source clause, generates its capability
certificate, and keeps its exact nested bounds and original retained snapshot.
Both offered modes and skipped operations retain their actual source witness. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples
open SourceConsumingClauseAnnotations (Body Declarations ClauseBounds Bounded SelectedSource)
open SourceScheduledCapabilityAnnotations (Code Retained CaptureSource recipeLaws)
open SourceScheduledSourceRechecking (ReceiverChange)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceContextualHints (Hints)
open SourcePlannedRecipeDeclarations (Selected)

def outer : Instance := .user 71 []
def inner : Instance := .user 72 []
def raw : ScopedExpressions.Code := .handle (Instantiation.freezeEffect inner) (.resume 9 .unit) .nil
def clauses : ScopedExpressions.Clauses := .cons 0 1 9 raw .nil
def family (owner : Nat) : SourceDependencyAnnotations.Dependencies := .handler inner [] [] (.invoke ⟨owner, .resume⟩)
def families : SourceDependencyAnnotations.ClauseDependencies := [(0, some family, some family)]
def bodies (owner : Nat) : Plan (family owner) := .handler [] .nil .invoke
def plans : ClausePlans clauses families := .cons (.available bodies) (.available bodies) .nil
def body (owner : Nat) : Body [] owner (bodies owner) := .handler .nil .nil .resume
def declarations : Declarations [] plans := .cons (.available body) (.available body) .nil
def bounds : ClauseBounds plans := .cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil

theorem bounded : Bounded bounds declarations [] :=
  .cons (.available (.available (fun _ => .handler (.resume rfl) rfl rfl))
      (fun _ => .handler .nil .nil .resume))
    (.available (.available (fun _ => .handler (.resume rfl) rfl rfl))
      (fun _ => .handler .nil .nil .resume)) .nil

def offered : ProtectionContracts.ClauseContract := ⟨false, some [], some []⟩
def table := [(0, offered)]
def saved : Forest (Hints.handler (effect := outer) (table := table) (families := families) [] .nil) := .handler .nil
def snapshot : SourceBoundSnapshots.Snapshot [] := ⟨_, .request (effect := outer) (operation := 0),
  .absent, _, _, saved, .handler .nil⟩
theorem snapshot_admitted : snapshot.Admitted := ⟨.absent .request, .handler .nil⟩
def source : Retained [] saved .nil := .handler (.operations .nil)
def actions : Syntax.UsageTickets := fun _ => none
def phases := OwnerPhaseTransitions.empty
theorem source_valid : source.Valid [] actions phases := ⟨rfl, rfl⟩

theorem cut : SourceScheduledNeutral.Cut outer 0 offered (some family, some family) saved saved .nil := .hit rfl rfl

def request : Code [] (.request (effect := outer) (operation := 0)) saved :=
  .selected cut (fun impossible => Bool.noConfusion impossible) (fun impossible => Bool.noConfusion impossible)
theorem request_valid : request.Valid [] actions phases := ⟨by decide, fun impossible => Bool.noConfusion impossible⟩
theorem selected : Selected 0 false plans 1 9 raw bodies := .ordinary
theorem selected_source : SelectedSource 19 declarations selected (body 19) := .ordinary
theorem protected_source : SelectedSource 19 declarations (Selected.protectedMode : Selected 0 true plans 1 9 raw bodies) (body 19) := .protectedMode

/-- An earlier different operation does not change which stored body is used. -/
def prefixedPlans := ClausePlans.cons (operation := 8) (parameter := 1) (binder := 9) (body := raw)
  (.available bodies) (.available bodies) plans
def prefixedSource : Declarations [] prefixedPlans := .cons (.available body) (.available body) declarations

theorem skipped_source : SelectedSource 19 prefixedSource
    (Selected.pass (by decide : 0 ≠ 8) selected) (body 19) := .pass (by decide) selected_source

theorem substituted_source : SelectedSource 19 (declarations.substitution 2 .unit)
    (selected.substitution (name := 2) (value := .unit)) (body 19) := selected_source.substitution

/-- Selection cannot replace the stored body with another annotation of its plan. -/
theorem selected_annotation_fixed (other : Body [] 19 (bodies 19))
    (claimed : SelectedSource 19 declarations selected other) : other = body 19 :=
  claimed.unique selected_source

theorem fresh : actions 19 = none := rfl
theorem absent : 19 ∉ SourceDependencyOwners.owners snapshot.scope := by simp [snapshot, saved, SourceDependencyOwners.owners]
theorem permits : raw.requiredActions.dispose = true → offered.dispose = true := fun impossible => impossible

noncomputable def captureSource : CaptureSource [] actions phases cut source raw.requiredActions :=
  CaptureSource.without_disposal cut source source_valid
    (SourceDependencyCapture.check_capture_iff.mp (by decide)) rfl

noncomputable def context := Context.of_request (recipeLaws []) (fun evidence => evidence)
  cut source raw.requiredActions captureSource permits fresh absent

/-- The original saved delimiter has no code to reinterpret. This works for
either representation chosen by the original retained compiler. -/
theorem recheck_saved {outside : Forest outsideHints} {nextOutside : Forest nextOutsideHints}
    (original : Retained [] saved outside) : ReceiverChange [] actionsNow phasesNow original nextOutside := by
  cases original with
  | operations interfaces => exact .operations (.handler .nil .nil) rfl
  | handler tail => exact .handler rfl .empty

theorem contextual : At (recipeLaws []) (fun evidence => evidence) (body 19) context :=
  .handler .nil (show SourcePlannedRecipeDeclarations.Declarations [] (.nil : ClausePlans .nil []) from .nil)
    (fun permission => recheck_saved (context.resumption permission).val)
    (fun _ => .empty) .resume

/-- Neither a successful target annotation nor a successful capture certificate
is a premise: both follow from the original source and contextual rules. -/
theorem generated : ∃ annotation : Code [] (bodies 19) (.live (owner := 19) saved .nil),
    (SourceScheduledCaptureAnnotations.Capture.site cut selected annotation).Valid [] actions phases ∧
    SourcePlanBounds.ofCode annotation = (body 19).boundAnnotation ∧
    (SourcePlanBounds.ofCode annotation).Admitted ∧
    SourceBoundSnapshots.CapturedBounds snapshot 19 (bodies 19) (.live (owner := 19) saved .nil) :=
  SelectedSource.capture_retaining (recipeLaws []) (fun evidence => evidence) snapshot snapshot_admitted bounded cut selected
    selected_source source captureSource permits rfl fresh absent contextual

theorem allocator_certificate : ∃ certificate : SourceScheduledCaptureAnnotations.Capture [] 19 outer 0 offered
    (some family, some family) plans 1 9 raw saved, certificate.Valid [] actions phases :=
  SelectedSource.capture_certificate (recipeLaws []) (fun evidence => evidence) snapshot snapshot_admitted bounded cut selected
    selected_source source captureSource permits rfl fresh absent contextual

/-- The emitted current-plan bounds cannot silently become absent. -/
theorem nested_bounds_kept : ∃ annotation : Code [] (bodies 19) (.live (owner := 19) saved .nil),
    annotation.Valid [] (actions.insert 19 raw.requiredActions) (OwnerPhaseTransitions.introduce phases 19) ∧
    annotation.boundAt [] 0 false = some none := by
  obtain ⟨annotation, ready, kept, _⟩ := generated
  refine ⟨annotation, ready, ?_⟩
  exact (SourcePlanBounds.ofCode_lookup annotation .here).symm.trans
    (congrArg (fun current => current.lookup .here 0 false) kept)

end Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.bounded
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.snapshot_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.source_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.cut
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.request_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.selected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.selected_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.protected_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.fresh
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.absent
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.permits
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.context
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.recheck_saved
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.contextual
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.allocator_certificate
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.nested_bounds_kept

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.skipped_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.substituted_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CaptureExamples.selected_annotation_fixed
