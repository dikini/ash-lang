import SourceHandlerCoverage
import SourcePlannedSources
import SourceScheduledScopedInvocations
import SourceScheduledClosingCallbacks
import SourceScheduledHandlerRequests

/-! Introduce a newly selected request from structural capture checks.
Disposal requires owner bounds and individual callback admission at closing
positions. No previous request or checked whole closing schedule is assumed. -/
namespace Ash.OneShot.SourceScheduledFreshRequests
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope CaptureGuard)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceScheduledClosingCallbacks (Callbacks)
open SourceDependencyOwners (owners PendingWithin)
open SourceDependencyProjection (project)

/-- Finite coverage supplies an intercepted operation below any caller prefix
through which the effect passes. Its former selection may be a source handler
or a typed builtin. The new handler must offer both protected and ordinary
resumptive capabilities; this theorem introduces no whole-body source premise. -/
theorem request_from_coverage {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    (front : Forest frontHints) (tail : Forest tailHints)
    (covered : SourceHandlerCoverage.check effect table families tailScope = true)
    (found : SourceDependencyCapture.select effect operation tailScope = some selected)
    (typed : SourceHandlerCoverage.BuiltinTyped operation selected)
    (passed : SourceHandlerRequirements.reaches effect frontScope = true) :
    Local outward actions phases world (.request (effect := effect) (operation := operation))
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) tail)) := by
  apply SourceScheduledScopedInvocations.request_from_capability
  exact SourceContextualRequirements.capability_prefix passed
    (SourceHandlerCoverage.selected_capability covered found typed)

/-- Actual source request typing determines its operation signature. Abstract
latent function signatures alone are not a premise of this theorem. -/
theorem builtin_typed_of_source
    (source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.perform (Instantiation.freezeEffect effect) operation operand) output demand requirements checking)
    (signature : operations.erase.erase.ports = ScopedPorts.withCellSignatures users)
    (found : SourceDependencyCapture.select effect operation receiving = some selected) :
    SourceHandlerCoverage.BuiltinTyped operation selected := by
  generalize frozen : Instantiation.freezeEffect effect = requested at source
  cases source with
  | perform known admitted operand formed =>
      have same := ScopedExecution.freeze_effect_injective frozen
      cases same
      have ports := CoherentSourceTypes.port_lookup
        (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known))
      rw [signature] at ports
      exact SourceHandlerCoverage.selected_typed_of_signature ports found

/-- Source typing discharges the former builtin-domain assumption. The actual
operand may still be effectful; lookup and coverage concern its subsequent
request at the stated interpretation scope. -/
theorem request_from_source_coverage {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    (front : Forest frontHints) (tail : Forest tailHints)
    (source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.perform (Instantiation.freezeEffect effect) operation operand) output demand requirements checking)
    (signature : operations.erase.erase.ports = ScopedPorts.withCellSignatures users)
    (covered : SourceHandlerCoverage.check effect table families tailScope = true)
    (found : SourceDependencyCapture.select effect operation tailScope = some selected)
    (passed : SourceHandlerRequirements.reaches effect frontScope = true) :
    Local outward actions phases world (.request (effect := effect) (operation := operation))
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) tail)) :=
  request_from_coverage front tail covered found (builtin_typed_of_source source signature found) passed

namespace CoverageExamples
open SourceDependencyCapture.Examples

/-- The same effect is deliberately reinterpreted under running protection.
The old provider can dispose; the covering provider supplies both resumptive
modes. This is source-request admission, not observational equivalence. -/
theorem protected_same_effect :
    Local [] actions phases [] (.request (effect := effectE) (operation := 0))
      ((Forest.running (.plain .pure .nil)).append
        (.handler (effect := effectE) (table := resumeTable) (families := resumeDependencies) (required := [])
          (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) .nil))) := by
  refine request_from_coverage (selected := .handler (handlerE .nil) .nil
    ⟨true, some [], none⟩ (some disposeFamily, none)) _ _ ?_ ?_ ?_ ?_
  · decide
  · rfl
  · trivial
  · rfl

/-- A complete typed cell interface supports either operation after a source
handler takes over. The retained caller may still contain arbitrary scopes. -/
theorem either_cell_operation {frontHints : Hints frontScope} (front : Forest frontHints)
    (operation : Nat) (valid : operation = 0 ∨ operation = 1)
    (passed : SourceHandlerRequirements.reaches (.cell 4) frontScope = true) :
    Local [] actions phases [4] (.request (effect := .cell 4) (operation := operation))
      (front.append (.handler (effect := .cell 4)
        (table := SourceHandlerCoverage.Examples.cellTable) (families := SourceHandlerCoverage.Examples.cellFamilies)
        (required := []) (.cell (identity := 4) .nil))) :=
  request_from_coverage front (.cell .nil) (by decide) rfl valid passed

/-- Raw dependency lookup accepts operation 2 at a builtin. Source typing
under the declared cell signature rejects it, for every operand and world. -/
theorem invalid_cell_operation_rejected
    (signature : operations.erase.erase.ports = ScopedPorts.withCellSignatures users) :
    ¬ SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.perform (Instantiation.freezeEffect (.cell identity)) 2 operand) output demand requirements checking := by
  intro source
  have impossible := builtin_typed_of_source source signature
    (show SourceDependencyCapture.select (.cell identity) 2 (.cell identity .nil) =
      some (.builtin identity) from by simp [SourceDependencyCapture.select])
  cases impossible with
  | inl impossible | inr impossible => cases impossible

end CoverageExamples

/-- Compile the independent capture guard, structural pending-owner bounds,
and per-callback closing checks into the existing scheduled request rule. -/
theorem request_from_schedule [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (translate : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → certification.accepts outward required plans) {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
    (guarded : CaptureGuard outward scope effect operation)
    (bounded : contract.dispose = true → PendingWithin world (owners captured) captured)
    (scheduled : contract.dispose = true → SourceScheduledChecks.Pending outward actions phases world saved.forClosing (.running waiting)) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) forest := by
  have selected : SourceDependencyCapture.select effect operation (project scope) =
      some (.handler (project captured) (project tail) contract modes) := by
    rw [SourceDependencyProjection.project_select, cut.erase.lookup]
    rfl
  refine .request (SourceDependencyChecks.Local.request_selected selected ?_ ?_ ?_) ?_
  · simpa only [SourceDependencyProjection.project_checkCapture] using
      SourceDependencyCapture.check_capture_iff.mpr guarded
  · intro disposes
    simpa only [SourceDependencySchemes.Retained, SourceDependencyProjection.project_forClosing,
      SourceDependencyProjection.project_idempotent, project] using ((scheduled disposes).erase_with translate).erase
  · intro disposes
    simpa only [SourceDependencySchemes.owners_project] using
      SourcePlannedNeutralChecks.pending_owners_project (bounded disposes)
  · intro actualCaptured actualTail actualSavedHints actualWaitingHints actualContract actualModes actualCut
      actualSaved actualWaiting same disposes
    cases Option.some.inj (cut.erase.lookup.symm.trans actualCut.lookup)
    obtain ⟨rfl, rfl⟩ := cut.erase.unique actualCut.hints
    obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (cut.forest.symm.trans same))
    exact scheduled disposes

/-- The callback interface specializes the policy-independent schedule rule. -/
theorem request_from_callbacks {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
    (guarded : CaptureGuard outward scope effect operation)
    (bounded : contract.dispose = true → PendingWithin world (owners captured) captured)
    (callbacks : contract.dispose = true → Callbacks outward actions phases world saved (.running waiting)) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) forest :=
  request_from_schedule (admission := SourceScheduledChecks.recipePolicy)
    (certification := SourcePlannedChecks.contextualPolicy)
    (fun checked => SourcePlannedRecipeDeclarations.Declarations.erase checked)
    cut guarded bounded (fun disposes => (callbacks disposes).schedule)

/-- These are exactly the existing obligations for a selected disposing
operation. The new rules do not add a blanket restriction on handler effects. -/
theorem disposing_request_iff {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
    (disposes : contract.dispose = true) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) forest ↔
      CaptureGuard outward scope effect operation ∧ PendingWithin world (owners captured) captured ∧
      Callbacks outward actions phases world saved (.running waiting) := by
  constructor
  · intro checked
    have lower := checked.erase.erase
    refine ⟨SourceDependencyCapture.check_capture_iff.mp (SourceDependencySchemes.checked_request lower),
      SourceDependencySchemes.checked_request_owners lower cut.erase.lookup disposes, ?_⟩
    cases checked with
    | request guarded scheduled =>
        exact SourceScheduledClosingCallbacks.callbacks_of_schedule
          (scheduled _ _ _ _ _ _ cut.erase saved waiting cut.forest disposes)
  · rintro ⟨guarded, bounded, callbacks⟩
    exact request_from_callbacks cut guarded (fun _ => bounded) (fun _ => callbacks)

/-- A source handler may newly intercept the request, including one formerly
supplied by a builtin. Its captured source is the actual preceding prefix plus
that handler; the new structural checks are independent of the old selection. -/
theorem installed_request {frontHints : Hints frontScope} {waitingHints : Hints waitingScope}
    (front : Forest frontHints) (waiting : Forest waitingHints)
    (passed : SourceHandlerRequirements.reaches effect frontScope = true)
    (known : lookup operation table = some contract)
    (declared : SourceDependencyCapture.lookupDependencies operation families = some modes)
    (guarded : CaptureGuard outward (frontScope.append (.handler effect table families waitingScope)) effect operation)
    (bounded : contract.dispose = true → PendingWithin world
      (owners (frontScope.append (.handler effect table families .nil)))
      (frontScope.append (.handler effect table families .nil)))
    (callbacks : contract.dispose = true → Callbacks outward actions phases world
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) .nil))
      (.running waiting)) :
    Local outward actions phases world (.request (effect := effect) (operation := operation))
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) waiting)) :=
  request_from_callbacks (SourceScheduledHandlerRequests.cut_prefix front passed (.hit known declared)) guarded bounded callbacks

/-- Installing the selected handler at the end of a captured prefix adds no
closing callback. Reuse the proved equality of actual closing plans, including
all recursively saved branches. -/
theorem callbacks_at_handler {frontHints : Hints frontScope} (front : Forest frontHints)
    {outside : Forest outsideHints} :
    Callbacks outward actions phases world
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) .nil)) outside ↔
    Callbacks outward actions phases world front outside := by
  rw [SourceScheduledClosingCallbacks.callbacks_iff_schedule,
    SourceScheduledClosingCallbacks.callbacks_iff_schedule]
  exact (SourceScheduledRecomposition.predicate_congr
    (SourceHandlerRequests.forClosing_inserted frontScope)
    (SourceScheduledHandlerRequests.hints_forClosing_inserted frontHints .nil)
    (SourceScheduledHandlerRequests.forest_forClosing_inserted front .nil)
    (fun closing => Pending outward actions phases world closing outside)).trans
    (SourceScheduledRecomposition.predicate_congr
      (SourceDependencyProjection.scope_append_nil frontScope)
      (SourcePlannedRecomposition.hints_append_nil frontHints)
      (SourceScheduledRecomposition.forest_append_nil front)
      (fun retained => Pending outward actions phases world retained.forClosing outside))

/-- Prefix annotations suffice for a newly installed disposer. Its selected
handler owns no continuation and contributes no callback, so both obligations
are derived from the original prefix's structural checks. -/
theorem installed_request_from_prefix {frontHints : Hints frontScope} {waitingHints : Hints waitingScope}
    (front : Forest frontHints) (waiting : Forest waitingHints)
    (passed : SourceHandlerRequirements.reaches effect frontScope = true)
    (known : lookup operation table = some contract)
    (declared : SourceDependencyCapture.lookupDependencies operation families = some modes)
    (guarded : CaptureGuard outward (frontScope.append (.handler effect table families waitingScope)) effect operation)
    (bounded : contract.dispose = true → PendingWithin world (owners frontScope) frontScope)
    (callbacks : contract.dispose = true → Callbacks outward actions phases world front (.running waiting)) :
    Local outward actions phases world (.request (effect := effect) (operation := operation))
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) waiting)) := by
  apply installed_request front waiting passed known declared guarded
  · intro disposes
    have original : PendingWithin world (owners frontScope) (frontScope.append .nil) := by
      simpa only [SourceDependencyProjection.scope_append_nil] using bounded disposes
    have inserted := SourceHandlerRequests.pending_owners_inserted
      (effect := effect) (table := table) (families := families) frontScope original
    simpa only [SourceHandlerRequests.owners_inserted, SourceDependencyProjection.scope_append_nil] using inserted
  · intro disposes
    exact (callbacks_at_handler front).mpr (callbacks disposes)

end Ash.OneShot.SourceScheduledFreshRequests

#print axioms Ash.OneShot.SourceScheduledFreshRequests.request_from_callbacks
#print axioms Ash.OneShot.SourceScheduledFreshRequests.disposing_request_iff
#print axioms Ash.OneShot.SourceScheduledFreshRequests.installed_request

#print axioms Ash.OneShot.SourceScheduledFreshRequests.callbacks_at_handler
#print axioms Ash.OneShot.SourceScheduledFreshRequests.installed_request_from_prefix

#print axioms Ash.OneShot.SourceScheduledFreshRequests.request_from_coverage
#print axioms Ash.OneShot.SourceScheduledFreshRequests.builtin_typed_of_source
#print axioms Ash.OneShot.SourceScheduledFreshRequests.request_from_source_coverage
#print axioms Ash.OneShot.SourceScheduledFreshRequests.CoverageExamples.protected_same_effect
#print axioms Ash.OneShot.SourceScheduledFreshRequests.CoverageExamples.either_cell_operation
#print axioms Ash.OneShot.SourceScheduledFreshRequests.CoverageExamples.invalid_cell_operation_rejected

#print axioms Ash.OneShot.SourceScheduledFreshRequests.request_from_schedule
