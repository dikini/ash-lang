import SourceScheduledRetainedInterfaces
import SourceHandlerClosingInsertion
import SourceScheduledCapabilityReconstruction
import SourceCleanupClosingInsertion
import SourceConsumingDirectCapture

/-! Derive callback closing schedules from normal source operation checks and
existing structural closing routes. The callback's operation footprint must be
covered by its declared effect needs. No target callback check is a premise. -/
namespace Ash.OneShot.SourceScheduledCallbackRoutes
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints Requirement checkCapability checkRequirements)
open SourceRetainedPlans (Forest)
open SourceResourceRoutes (Route)
open SourceRecursiveRoutes (Shape Closing)
open SourceHandlerRequirements (reaches capability_prepend capability_append)
open SourceHandlerClosingInsertion (normal_append)
open SourceScheduledCallbackInterfaces (Interfaces Declared)

/-- A valid route excludes local source handlers. It identifies either an
actual builtin capability or a request passed to the shared receiving suffix. -/
theorem route_capability (scope : Scope)
    (routed : Route outward scope.shape.normal effect target) :
    checkCapability scope effect operation = target.isSome ∧
      reaches effect scope = target.isNone := by
  induction scope with
  | nil => cases routed; exact ⟨rfl, rfl⟩
  | handler other table families rest ih =>
      cases routed with
      | handler different next =>
        obtain ⟨capability, passed⟩ := ih next
        exact ⟨(capability_prepend (first := .handler other table families rest)
          (second := rest) (effect := effect) (operation := operation) (layer := .handler other table families)
          (if_neg different)).trans capability, by simpa only [reaches, if_neg different] using passed⟩
  | cell identity rest ih =>
      cases routed with
      | cell same => subst effect; exact ⟨by simp [checkCapability, SourceDependencyCapture.select], by simp [reaches]⟩
      | cellMiss different next =>
        obtain ⟨capability, passed⟩ := ih next
        exact ⟨(capability_prepend (first := .cell identity rest)
          (second := rest) (effect := effect) (operation := operation) (layer := .cell identity)
          (if_neg different)).trans capability, by simpa only [reaches, if_neg different] using passed⟩
  | plain dependencies rest ih | cleanup needs callback rest ih | running rest ih
  | spent owner rest ih =>
      obtain ⟨capability, passed⟩ := ih routed
      constructor
      · calc
          checkCapability _ effect operation = checkCapability rest effect operation := capability_prepend rfl
          _ = _ := capability
      · exact passed
  | live owner saved rest ihSaved ih =>
      obtain ⟨capability, passed⟩ := ih routed
      constructor
      · calc
          checkCapability _ effect operation = checkCapability rest effect operation := capability_prepend rfl
          _ = _ := capability
      · exact passed

/-- Matching source routes preserve the exact capability check for every
operation, including an unavailable operation at the unchanged outside handler. -/
theorem capability_same_routes {first second outside : Scope}
    (before : Route outward first.shape.normal effect target)
    (after : Route outward second.shape.normal effect target) :
    checkCapability (first.append outside) effect operation =
      checkCapability (second.append outside) effect operation := by
  obtain ⟨firstCapability, firstPassed⟩ := route_capability first before (operation := operation)
  obtain ⟨secondCapability, secondPassed⟩ := route_capability second after (operation := operation)
  rw [capability_append, capability_append, firstPassed, secondPassed, firstCapability, secondCapability]

theorem closing_normal (scope : Scope) : scope.forClosing.shape.normal = scope.shape.closing := by
  induction scope <;> simp_all [Scope.forClosing, Scope.shape, Shape.normal, Shape.closing, normal_append]

/-- Coverage connects actual callback operation interfaces to the effect needs
used by the existing route judgment. It grants no continuation permission. -/
inductive Covered : {scope : Scope} → {hints : Hints scope} →
    {forest : Forest hints} → Interfaces forest → Prop where
  | nil : Covered .nil
  | plain : Covered next → Covered (Interfaces.plain (plan := plan) next)
  | handler : Covered next → Covered
      (Interfaces.handler (effect := effect) (table := table) (families := families) (required := required) next)
  | cell : Covered next → Covered (Interfaces.cell (identity := identity) next)
  | cleanup {hints : Hints scope} {rest : Forest hints} {next : Interfaces rest}
      (included : ∀ request ∈ required, request.1 ∈ needs) (tail : Covered next) :
      Covered (Interfaces.cleanup (needs := needs) (plan := plan) rest required footprint next)
  | running : Covered next → Covered (Interfaces.running next)
  | live {hints : Hints scope} {rest : Forest hints} {next : Interfaces rest} :
      Covered saved → Covered next → Covered (Interfaces.live (owner := owner) rest saved next)
  | spent : Covered next → Covered (Interfaces.spent (owner := owner) next)

private def receiving {hints : Hints scope} (_ : Forest hints) : Scope := scope

/-- Check the callback interfaces at their original registration suffixes.
Ordinary pending code has no entry here, so it may use arbitrary continuations. -/
def normalCheck {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces forest) (outside : Scope) : Bool :=
  match interfaces with
  | .nil => true
  | .plain next | .handler next | .cell next | .running next | .spent next => normalCheck next outside
  | .cleanup (scope := restScope) _ required _ next =>
      checkRequirements (.running (restScope.append outside)) required && normalCheck next outside
  | .live (scope := restScope) _ saved next => normalCheck saved (restScope.append outside) && normalCheck next outside

private theorem running_requirements (scope : Scope) :
    checkRequirements (.running scope) required = checkRequirements scope required := by
  simp only [checkRequirements, capability_prepend
    (first := .running scope) (second := scope) (effect := _) (operation := _) rfl]

/-- Closing routes transport all actual callback interfaces together, including
recursively dormant captures. The two prefixes model their normal and closing
receivers; the outside interpretation remains shared. -/
theorem check_from_routes {original surviving outside : Scope} {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces forest) (covered : Covered interfaces)
    (routes : Closing outward scope.shape original.shape.normal surviving.shape.normal)
    (supplied : normalCheck interfaces (original.append outside) = true) :
    interfaces.check (surviving.append outside) = true := by
  induction interfaces generalizing original surviving with
  | nil => rfl
  | plain next ih => cases covered with | plain covered => cases routes with | plain routes => exact ih covered routes supplied
  | handler next ih => cases covered with | handler covered => cases routes with | handler routes => exact ih covered routes supplied
  | cell next ih => cases covered with | cell covered => cases routes with | cell routes => exact ih covered routes supplied
  | running next ih => cases covered with | running covered => cases routes with | plain routes => exact ih covered routes supplied
  | spent next ih => cases covered with | spent covered => cases routes with | spent routes => exact ih covered routes supplied
  | cleanup rest required footprint next ih =>
      cases covered with
      | cleanup included covered =>
        cases routes with
        | cleanup routed routes =>
          obtain ⟨requests, remaining⟩ := Bool.and_eq_true_iff.mp supplied
          apply Bool.and_eq_true_iff.mpr
          refine ⟨?_, ih covered routes remaining⟩
          simp only [running_requirements] at requests ⊢
          apply List.all_eq_true.mpr
          intro request member
          obtain ⟨target, before, after⟩ := routed request.1 (included request member)
          have same := capability_same_routes
            (first := (receiving rest).append original)
            (second := (receiving rest).forClosing.append surviving)
            (outside := outside) (operation := request.2)
            (by simpa only [normal_append, receiving] using before)
            (by simpa only [normal_append, closing_normal, receiving] using after)
          rw [SourceDependencyChecks.scope_append_assoc] at same
          rw [SourceDependencyChecks.scope_append_assoc] at same
          exact same ▸ List.all_eq_true.mp requests request member
  | live rest saved next ihSaved ihRest =>
      cases covered with
      | live coveredSaved coveredRest =>
        cases routes with
        | live inside tail =>
          obtain ⟨savedRequests, remaining⟩ := Bool.and_eq_true_iff.mp supplied
          apply Bool.and_eq_true_iff.mpr
          refine ⟨?_, ihRest coveredRest tail remaining⟩
          have savedReady := ihSaved coveredSaved
            (original := (receiving rest).append original)
            (surviving := (Scope.running (receiving rest).forClosing).append surviving)
            (by simpa only [normal_append, Scope.shape, Shape.normal, closing_normal, receiving] using inside)
            (by simpa only [SourceDependencyChecks.scope_append_assoc, receiving] using savedRequests)
          change saved.check ((Scope.running (receiving rest).forClosing).append (surviving.append outside)) = true
          simpa only [SourceDependencyChecks.scope_append_assoc] using savedReady

/-- A normal source interface and the existing closing guard derive every
closing callback schedule. No successful destination Local or Pending judgment
and no destination operation check is supplied by the caller. -/
theorem compile_from_routes {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (interfaces : Interfaces forest) (declared : Declared world interfaces)
    (covered : Covered interfaces)
    (routes : Closing outward scope.shape [] [])
    (supplied : normalCheck interfaces outsideScope = true) :
    SourceScheduledClosingCallbacks.Callbacks outward actions phases world forest outside := by
  apply interfaces.compile_declared declared
  exact check_from_routes interfaces covered (original := .nil) (surviving := .nil) routes supplied

/-- The existing retained-operation annotation already checks every callback's
normal interface. Its unrelated plain-code checks are not used by this result. -/
theorem normal_from_retained {hints : Hints scope} {forest : Forest hints}
    (interfaces : SourceScheduledRetainedInterfaces.Interfaces world forest)
    (supplied : interfaces.check outside = true) :
    normalCheck interfaces.callbacks outside = true := by
  induction interfaces generalizing outside with
  | nil => rfl
  | plain rest required footprint declared next ih | handler rest next ih =>
      exact ih (Bool.and_eq_true_iff.mp supplied).2
  | cell next ih | running next ih | spent next ih => exact ih supplied
  | cleanup rest required footprint declared next ih =>
      obtain ⟨requests, remaining⟩ := Bool.and_eq_true_iff.mp supplied
      exact Bool.and_eq_true_iff.mpr ⟨requests, ih remaining⟩
  | live rest saved next ihSaved ihRest =>
      obtain ⟨inside, remaining⟩ := Bool.and_eq_true_iff.mp supplied
      exact Bool.and_eq_true_iff.mpr ⟨ihSaved inside, ihRest remaining⟩

/-- Reuse annotation reconstruction after deriving the entire closing schedule.
Only the static inclusion of ordinary declaration recipes is required. -/
theorem closing_annotation
    [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    (legacy : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (interfaces : Interfaces forest) (declared : Declared world interfaces)
    (covered : Covered interfaces)
    (routes : Closing outward scope.shape [] [])
    (supplied : normalCheck interfaces outsideScope = true) :
    ∃ annotation : SourceScheduledCapabilityAnnotations.Retained world forest.forClosing outside,
      annotation.Valid outward actions phases :=
  (SourceScheduledCapabilityAnnotations.annotate_all_with
    (admission := SourceScheduledChecks.recipePolicy)
    (certification := SourcePlannedChecks.contextualPolicy) outward actions legacy).2 _ _ _ _
    (compile_from_routes interfaces declared covered routes supplied).schedule

/-- A selected request now generates its closing annotation from the original
callback interfaces. Capture routing and pending-owner bounds remain independent
primitive checks; no destination source annotation or success proof is supplied. -/
theorem request_annotation
    [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    (legacy : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (interfaces : Interfaces saved) (declared : Declared world interfaces)
    (covered : Covered interfaces)
    (guarded : SourceDependencyCapture.checkCapture outward wholeScope effect operation = true)
    (bounded : contract.dispose = true → SourceDependencyOwners.PendingWithin world
      (SourceDependencyOwners.owners savedScope) savedScope)
    (supplied : contract.dispose = true → normalCheck interfaces (.running waitingScope) = true) :
    ∃ annotation : SourceScheduledCapabilityAnnotations.Code world
      (.request (effect := effect) (operation := operation)) whole,
      annotation.Valid outward actions phases := by
  have generated : contract.dispose = true →
      ∃ annotation : SourceScheduledCapabilityAnnotations.Retained world saved.forClosing (.running waiting),
        annotation.Valid outward actions phases := by
    intro disposes
    exact closing_annotation legacy interfaces declared covered
      (SourceDependencyCapture.disposing_capture guarded cut.erase.lookup disposes).2.1 (supplied disposes)
  exact ⟨.selected cut bounded (fun disposes => Classical.choose (generated disposes)),
    guarded, fun disposes => Classical.choose_spec (generated disposes)⟩

namespace Examples
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture.Examples (effectF resumeTable resumeDependencies)
open SourceCleanupClosingInsertion.Examples

/-- Replace the earlier hand-built closing annotation by source generation.
The callback reads the retained cell; every action/phase map is permitted here
because this callback requests no continuation action. -/
theorem retained_request_generated :
    ∃ annotation : SourceScheduledCapabilityAnnotations.Code [4]
      (.request (effect := disposingEffect) (operation := 0))
      (.cleanup (needs := [callbackEffect])
        (.request (effect := callbackEffect) (operation := 0)) retainedForest),
      annotation.Valid [] actions phases := by
  apply request_annotation (fun checked => checked)
    (.cleanup (.cell (by decide) (.hit rfl rfl)))
    (.cleanup retainedForest [(callbackEffect, 0)] .request (.cell (.handler .nil)))
    (.cleanup .request (.cell (.handler .nil)))
    (.cleanup (by intro request member; cases List.mem_singleton.mp member; exact List.mem_cons_self)
      (.cell (.handler .nil)))
    retained_builtin_accepted (fun _ => .cleanup (.cell (.handler .nil))) (fun _ => rfl)

/-- The original callback can be supplied by a handler even when closing drops
that handler. Omitting the effect from needs makes the route guard vacuous;
the structural coverage rule rejects precisely that missing declaration. -/
def omittedHints : Hints (.cleanup [] (.request effectF 0)
    (.handler effectF resumeTable resumeDependencies .nil)) := .cleanup (.handler [] .nil)
def omitted : Forest omittedHints := .cleanup .request (.handler .nil)
def omittedInterface : Interfaces omitted := .cleanup (.handler .nil) [(effectF, 0)] .request (.handler .nil)

theorem omitted_need_rejected :
    normalCheck omittedInterface .nil = true ∧
      SourceDependencyCapture.checkClosing [] (Scope.cleanup [] (.request effectF 0) (.handler effectF resumeTable resumeDependencies .nil)).shape [] [] = true ∧
      omittedInterface.check .nil = false ∧ ¬ Covered omittedInterface := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro covered
  cases covered with
  | cleanup included tail => exact List.not_mem_nil (included (effectF, 0) List.mem_cons_self)

/-- Plain code may invoke an outside owner: callback generation does not impose
an operation-only restriction on that discarded code. A dormant callback uses
the actual receiving handler, which is outside the disposed forest. -/
def dormantHints : Hints (.live 19
    (.plain (.invoke ⟨37, .resume⟩) (.cleanup [effectF] (.request effectF 0) .nil))
    (.cell 4 .nil)) := .live (.plain (.cleanup .nil)) (.cell .nil)
def dormant : Forest dormantHints := .live (.plain .invoke (.cleanup .request .nil)) (.cell .nil)
def dormantInterface : Interfaces dormant :=
  .live (.cell .nil) (.plain (.cleanup .nil [(effectF, 0)] .request .nil)) (.cell .nil)
def waitingHints : Hints (.handler effectF resumeTable resumeDependencies .nil) := .handler [] .nil
def waiting : Forest waitingHints := .handler .nil

theorem dormant_callbacks_generated :
    ∃ annotation : SourceScheduledCapabilityAnnotations.Retained [4] dormant.forClosing waiting,
      annotation.Valid [effectF] actions phases := by
  apply closing_annotation (fun checked => checked) dormantInterface
    (.live (.plain (.cleanup .request .nil)) (.cell .nil))
    (.live (.plain (.cleanup (by intro request member; cases List.mem_singleton.mp member; exact List.mem_cons_self) .nil)) (.cell .nil))
  · apply SourceDependencyCapture.check_closing_iff.mp
    decide
  · rfl

end Examples

end Ash.OneShot.SourceScheduledCallbackRoutes

#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.route_capability
#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.capability_same_routes
#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.closing_normal
#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.check_from_routes
#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.compile_from_routes

#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.normal_from_retained
#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.closing_annotation
#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.request_annotation

#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.Examples.retained_request_generated
#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.Examples.omitted_need_rejected
#print axioms Ash.OneShot.SourceScheduledCallbackRoutes.Examples.dormant_callbacks_generated

namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy DeclarationLaws)

/-- Connect route-derived callback generation to the existing consuming-clause
capture generator. This interface replaces its checked current request by source
callback evidence and primitive capture/owner checks. The original retained
source still needs its own validation; complete initial admission is separate. -/
theorem Bounded.capture_direct_from_callbacks
    [declarations : DeclarationPolicy]
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required) (direct : annotations.Direct)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies)
    (source : Retained world whole .nil) (retained : source.Valid outward actions phases)
    (interfaces : SourceScheduledCallbackInterfaces.Interfaces saved)
    (declared : SourceScheduledCallbackInterfaces.Declared world interfaces)
    (covered : SourceScheduledCallbackRoutes.Covered interfaces)
    (guarded : SourceDependencyCapture.checkCapture outward wholeScope effect operation = true)
    (bounded : offered.dispose = true → SourceDependencyOwners.PendingWithin world
      (SourceDependencyOwners.owners savedScope) savedScope)
    (normal : offered.dispose = true →
      SourceScheduledCallbackRoutes.normalCheck interfaces (.running waitingScope) = true)
    (permits : code.requiredActions.dispose = true → offered.dispose = true)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none) (absent : owner ∉ SourceDependencyOwners.owners wholeScope) :
    ∃ certificate : SourceScheduledCaptureAnnotations.Capture world owner effect operation offered modes
      plans parameter binder code whole, certificate.Valid outward actions phases := by
  obtain ⟨request, requested⟩ := SourceScheduledCallbackRoutes.request_annotation
    (actions := actions) (phases := phases)
    (fun checked => project (laws.legacyAdmission checked)) cut interfaces declared covered guarded bounded normal
  exact admitted.capture_direct laws project direct cut selected source retained request requested
    permits supplied fresh absent

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.capture_direct_from_callbacks
