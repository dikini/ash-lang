import SourceConsumingBoundAnnotations
import SourceScheduledInterfaceCuts

/-! The capture boundary checks the actual exposed interfaces against the
bounds stored for the selected declaration mode. Only permitted continuation
actions need their corresponding interface check. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (ClausePlans)
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)

/-- Finite membership checks authenticate the actual saved/closing interfaces.
Unused action bounds impose no constraint on the other continuation action. -/
def Bounds.check (bounds : Bounds) (rights : Syntax.OneShotRights)
    (resume close : List Requirement) : Bool :=
  (if rights.resume then decide (resume ⊆ bounds.resume) else true) &&
    (if rights.dispose then decide (close ⊆ bounds.close) else true)

theorem Bounds.check_iff (bounds : Bounds) (rights : Syntax.OneShotRights) {resume close : List Requirement} :
    bounds.check rights resume close = true ↔
      (rights.resume = true → resume ⊆ bounds.resume) ∧
      (rights.dispose = true → close ⊆ bounds.close) := by
  cases rights with
  | mk resumes disposes => cases resumes <;> cases disposes <;> simp [Bounds.check]

def ClauseBounds.check {plans : ClausePlans clauses families} (bounds : ClauseBounds plans)
    (operation : Nat) (held : Bool) (rights : Syntax.OneShotRights)
    (resume close : List Requirement) : Bool :=
  match bounds.lookup operation held with
  | none => false
  | some selected => selected.check rights resume close

/-- Check the continuation footprint extracted from the current source at
this exact cut, using the bounds recorded for its selected offered mode. -/
def ClauseBounds.checkSource {plans : ClausePlans clauses families} (bounds : ClauseBounds plans)
    {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (rights : Syntax.OneShotRights) (source : Interfaces world forest)
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail) : Bool :=
  bounds.check operation savedScope.held rights
    (source.atCut cut).1.exposed (source.atCut cut).1.forClosing.exposed

/-- Resource-world extension preserves both acceptance and rejection. The
checker keeps the same declaration bounds and source footprints. -/
theorem ClauseBounds.checkSource_world_weaken {plans : ClausePlans clauses families} (bounds : ClauseBounds plans)
    {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (rights : Syntax.OneShotRights) (source : Interfaces world forest)
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail)
    (larger : world ⊆ nextWorld) :
    bounds.checkSource rights (source.world_weaken larger) cut = bounds.checkSource rights source cut := by
  simp only [ClauseBounds.checkSource, Interfaces.atCut_world_weaken,
    Interfaces.forClosing_world_weaken, Interfaces.exposed_world_weaken]

section
variable [declarations : DeclarationPolicy]

/-- The same deterministic offered-mode lookup is used by declaration
selection and finite capture checking. Original retained checks supply the
internal validity; the checker authenticates replacement-interface bounds. -/
theorem Bounded.schedule [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws declarations admission certification outward)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies)
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing) (after : Interfaces world tail)
    (checked : bounds.check operation savedScope.held code.requiredActions inside.exposed closing.exposed = true)
    (known : actions owner = some code.requiredActions) (available : phases owner = .available)
    (supplied : checkRequirements tailScope required = true)
    (resumeReady : (actions owner).any (fun rights => rights.resume) = true → inside.check resumeOutside = true)
    (closeReady : (actions owner).any (fun rights => rights.dispose) = true → closing.check closeOutside = true)
    (disposal : (actions owner).any (fun rights => rights.dispose) = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.check .nil = true) :
    SourceScheduledChecks.Local outward actions phases world (bodies owner) (.live (owner := owner) saved tail) := by
  obtain ⟨contract, needed, body, found, source, included⟩ := admitted.selected (owner := owner) selected
  have boundsChecked := contract.check_iff code.requiredActions |>.mp
    (show contract.check code.requiredActions inside.exposed closing.exposed = true from by
      simpa only [ClauseBounds.check, found] using checked)
  apply source.schedule laws inside closing after known available
    (SourceContextualRequirements.check_requirements_subset included supplied)
    _ _ resumeReady closeReady disposal tailReady
  · intro permission
    exact boundsChecked.1 (by simpa only [known, Option.any_some] using permission)
  · intro permission
    exact boundsChecked.2 (by simpa only [known, Option.any_some] using permission)

end
/-- Default-policy clause bodies generate the concrete capture certificate
already consumed by the typed allocator. The bound check is tied to the exact
selected declaration and the exact saved/waiting pieces of this cut. -/
theorem Bounded.capture_body_nested {actions : Syntax.UsageTickets}
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (_cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies)
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing) (after : Interfaces world tail)
    (checked : bounds.check operation savedScope.held code.requiredActions inside.exposed closing.exposed = true)
    (supplied : checkRequirements tailScope required = true)
    (resumeReady : code.requiredActions.resume = true → inside.check resumeOutside = true)
    (closeReady : code.requiredActions.dispose = true → closing.check closeOutside = true)
    (disposal : code.requiredActions.dispose = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.check .nil = true) :
    ∃ body : Body world owner (bodies owner), body.Nested ∧
      (body.annotate .hit inside closing .nil after).Valid outward
        (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner) := by
  obtain ⟨contract, needed, body, found, source, included, nested⟩ := admitted.selected_nested (owner := owner) selected
  have boundsChecked := contract.check_iff code.requiredActions |>.mp
    (show contract.check code.requiredActions inside.exposed closing.exposed = true from by
      simpa only [ClauseBounds.check, found] using checked)
  refine ⟨body, nested, ?_⟩
  apply (body.annotate_valid .hit inside closing .nil after).mpr
  apply body.check_from_contract
    (source.at_capture (by simp [Syntax.UsageTickets.insert]) (by simp [OwnerPhaseTransitions.introduce])
      (SourceContextualRequirements.check_requirements_subset included supplied))
  · intro permission
    exact boundsChecked.1 (by simpa [Syntax.UsageTickets.insert] using permission)
  · intro permission
    exact boundsChecked.2 (by simpa [Syntax.UsageTickets.insert] using permission)
  · intro permission
    exact resumeReady (by simpa [Syntax.UsageTickets.insert] using permission)
  · intro permission
    exact closeReady (by simpa [Syntax.UsageTickets.insert] using permission)
  · intro permission
    exact disposal (by simpa [Syntax.UsageTickets.insert] using permission)
  · exact tailReady

theorem Bounded.capture_annotation
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies)
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing) (after : Interfaces world tail)
    (checked : bounds.check operation savedScope.held code.requiredActions inside.exposed closing.exposed = true)
    (supplied : checkRequirements tailScope required = true)
    (resumeReady : code.requiredActions.resume = true → inside.check resumeOutside = true)
    (closeReady : code.requiredActions.dispose = true → closing.check closeOutside = true)
    (disposal : code.requiredActions.dispose = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.check .nil = true) :
    ∃ admission : SourceScheduledCaptureAnnotations.Capture world owner effect operation offered modes
        plans parameter binder code forest, admission.Valid outward actions phases := by
  obtain ⟨body, _, valid⟩ := admitted.capture_body_nested (owner := owner) (actions := actions) (phases := phases) cut selected inside closing after checked supplied
    resumeReady closeReady disposal tailReady
  exact ⟨.site cut selected (body.annotate .hit inside closing .nil after), valid⟩

/-- A single retained source annotation supplies the actual saved, closing
and waiting interfaces. Normal validity is split from its pre-capture check;
closing validity uses the existing finite callback check because disposal
removes source handlers. The bound check still needs preservation at requests. -/
theorem Bounded.capture_from_source
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies)
    (source : Interfaces world forest)
    (original : source.check .nil = true)
    (checked : bounds.checkSource code.requiredActions source cut = true)
    (supplied : checkRequirements tailScope required = true)
    (callbacks : code.requiredActions.dispose = true →
      (source.atCut cut).1.callbacks.check closeOutside = true)
    (disposal : code.requiredActions.dispose = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true) :
    ∃ admission : SourceScheduledCaptureAnnotations.Capture world owner effect operation offered modes
        plans parameter binder code forest, admission.Valid outward actions phases := by
  have parts := Bool.and_eq_true_iff.mp ((source.check_atCut cut).symm.trans original)
  apply admitted.capture_annotation (closeOutside := closeOutside) cut selected
    (source.atCut cut).1 (source.atCut cut).1.forClosing (source.atCut cut).2 checked supplied
    (fun _ => parts.1) _ disposal parts.2
  intro permission
  rw [Interfaces.check_forClosing]
  exact callbacks permission

namespace BoundExamples
open SourceDependencyCapture.Examples (effectE effectF)
open SourceScheduledClauseHandlers.Examples (outerPlans outerFamilies bodies requesting waiting code noActions)

def bounds : ClauseBounds outerPlans :=
  .cons (.available ⟨[(effectF, 0)], []⟩) (.available ⟨[(effectF, 0)], []⟩) .nil

theorem admitted : Bounded bounds Examples.declarations [] := by
  have innerMode : BoundedMode (ScopedExpressions.Code.resume 3 .unit).requiredActions
      (.available ⟨[], []⟩)
      (.available (fun _ => .sequence [] .pure .pure .resume) : Modes []
        (.available SourceScheduledClauseHandlers.Examples.resumeBodies)) [] :=
    .available (.available (fun _ => .sequence (.resume rfl))) (fun _ => .sequence .resume)
  have inner : Bounded (.cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil)
      (.cons (.available (fun _ => .sequence [] .pure .pure .resume))
        (.available (fun _ => .sequence [] .pure .pure .resume)) .nil :
          Declarations [] SourceScheduledClauseHandlers.Examples.innerPlans) [] :=
    .cons innerMode innerMode .nil
  have mode : BoundedMode code.requiredActions (.available ⟨[(effectF, 0)], []⟩)
      (.available Examples.body) [] := .available (.available AdmissionExamples.admitted_body)
        (fun _ => .handler _ inner (Body.Nested.requests (.sequence .resume) _))
  exact .cons mode mode .nil

theorem repeated_operations_allowed :
    bounds.check 0 false ⟨true, false⟩ [(effectF, 0), (effectF, 0)] [(.user 93 [], 0)] = true := rfl

theorem missing_operation_rejected :
    bounds.check 0 false ⟨true, false⟩ [(.user 93 [], 0)] [] = false := rfl

def differentOffers : ClauseBounds outerPlans :=
  .cons (.available ⟨[(effectF, 0)], []⟩) (.available ⟨[], []⟩) .nil

theorem offered_modes_distinct :
    differentOffers.check 0 false ⟨true, false⟩ [(effectF, 0)] [] = true ∧
    differentOffers.check 0 true ⟨true, false⟩ [(effectF, 0)] [] = false := ⟨rfl, rfl⟩

/-- Finite bound authentication and source admission jointly produce the
actual restored schedule; neither is replaced by the other. -/
theorem scheduled :
    SourceScheduledChecks.Local [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (bodies 19) (.live (owner := 19) requesting waiting) :=
  admitted.schedule (SourceScheduledCapabilityAnnotations.recipeLaws [])
    (resumeOutside := ContractExamples.waitingScope) (closeOutside := .nil)
    (SourcePlannedRecipeDeclarations.Selected.ordinary (plans := bodies))
    ContractExamples.retained .nil (.handler .nil .nil) rfl rfl rfl rfl
    (fun _ => rfl) (fun _ => rfl) (by intro impossible; cases impossible) rfl

def source : Interfaces [] (requesting.append waiting) :=
  ContractExamples.retained.append (.handler .nil .nil)

def modes : SourcePlannedCuts.Modes :=
  (SourceDependencyCapture.lookupDependencies 0 outerFamilies).getD (none, none)

theorem cut : SourceScheduledNeutral.Cut effectE 0 ⟨false, some [], some []⟩ modes
    (requesting.append waiting) requesting waiting := .plain (.hit rfl rfl)

/-- The saved F request is recovered from the pre-capture source, checked
against the recorded bound, and interpreted by the F handler in the E clause. -/
theorem captured_from_source :
    ∃ admission : SourceScheduledCaptureAnnotations.Capture [] 19 effectE 0 ⟨false, some [], some []⟩
        modes outerPlans 1 9 code (requesting.append waiting),
      admission.Valid [] noActions OwnerPhaseTransitions.empty := by
  apply admitted.capture_from_source (closeOutside := .nil) cut .ordinary source rfl
  · rfl
  · rfl
  · intro impossible; cases impossible
  · intro impossible; cases impossible

def emptyBounds : ClauseBounds outerPlans :=
  .cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil

theorem missing_bound_rejects_source : emptyBounds.checkSource code.requiredActions source cut = false := rfl

def callbackSource : Interfaces []
    (.cleanup (needs := [effectF]) (.request (effect := effectF) (operation := 0)) waiting) :=
  .cleanup waiting [(effectF, 0)] .request .request (.handler .nil .nil)

/-- The original F handler supplies the callback during normal execution.
Disposal removes that handler, so normal validity cannot replace close checks. -/
theorem normal_check_does_not_supply_closing :
    callbackSource.check .nil = true ∧ callbackSource.forClosing.check .nil = false := ⟨rfl, rfl⟩

end BoundExamples

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounds.check_iff
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ClauseBounds.checkSource_world_weaken
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.schedule

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.capture_annotation
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.capture_from_source

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundExamples.admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundExamples.repeated_operations_allowed
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundExamples.missing_operation_rejected
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundExamples.offered_modes_distinct
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundExamples.scheduled
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundExamples.captured_from_source
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundExamples.missing_bound_rejects_source
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundExamples.normal_check_does_not_supply_closing

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.capture_body_nested
