import SourceScheduledCleanupInterfaces

/-! Source admission for newly intercepted requests. The original whole callback
interface is split at the actual handler insertion boundary. Original normal
operation checks and the new primitive capture guard derive the new closing
schedule, even when the previous interpretation did not permit disposal. -/
namespace Ash.OneShot.SourceScheduledInterceptAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceScheduledCallbackInterfaces (Interfaces Declared)
open SourceScheduledCallbackRoutes (Covered normalCheck)
open SourceScheduledHandlerSelection (Intercept)
open SourceDependencyOwners (owners PendingWithin)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)

/-- Extract the actual prefix's callback metadata and normal operation evidence.
The receiver includes the original tail; no target closing check is supplied.
Plain code is unrestricted, and dormant callbacks retain their own source data. -/
theorem callbacks_at_prefix {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    (front : Forest frontHints) (tail : Forest tailHints)
    (source : Interfaces (front.append tail)) (declared : Declared world source)
    (covered : Covered source) (ready : normalCheck source outside = true) :
    ∃ prefixSource : Interfaces front, Declared world prefixSource ∧ Covered prefixSource ∧
      normalCheck prefixSource (tailScope.append outside) = true := by
  induction front with
  | nil => exact ⟨.nil, .nil, .nil, rfl⟩
  | plain plan rest ih =>
      cases source with | plain next => cases declared with | plain declared => cases covered with | plain covered =>
        obtain ⟨prefixSource, prefixDeclared, prefixCovered, prefixReady⟩ := ih next declared covered ready
        exact ⟨.plain prefixSource, .plain prefixDeclared, .plain prefixCovered, prefixReady⟩
  | handler rest ih =>
      cases source with | handler next => cases declared with | handler declared => cases covered with | handler covered =>
        obtain ⟨prefixSource, prefixDeclared, prefixCovered, prefixReady⟩ := ih next declared covered ready
        exact ⟨.handler prefixSource, .handler prefixDeclared, .handler prefixCovered, prefixReady⟩
  | cell rest ih =>
      cases source with | cell next => cases declared with | cell declared => cases covered with | cell covered =>
        obtain ⟨prefixSource, prefixDeclared, prefixCovered, prefixReady⟩ := ih next declared covered ready
        exact ⟨.cell prefixSource, .cell prefixDeclared, .cell prefixCovered, prefixReady⟩
  | running rest ih =>
      cases source with | running next => cases declared with | running declared => cases covered with | running covered =>
        obtain ⟨prefixSource, prefixDeclared, prefixCovered, prefixReady⟩ := ih next declared covered ready
        exact ⟨.running prefixSource, .running prefixDeclared, .running prefixCovered, prefixReady⟩
  | spent rest ih =>
      cases source with | spent next => cases declared with | spent declared => cases covered with | spent covered =>
        obtain ⟨prefixSource, prefixDeclared, prefixCovered, prefixReady⟩ := ih next declared covered ready
        exact ⟨.spent prefixSource, .spent prefixDeclared, .spent prefixCovered, prefixReady⟩
  | cleanup callback rest ih =>
      cases source with | cleanup rest required footprint next =>
        cases declared with | cleanup callbackDeclared declared =>
          cases covered with | cleanup included covered =>
            obtain ⟨prefixSource, prefixDeclared, prefixCovered, prefixReady⟩ := ih next declared covered
              (Bool.and_eq_true_iff.mp ready).2
            refine ⟨.cleanup _ required footprint prefixSource, .cleanup callbackDeclared prefixDeclared,
              .cleanup included prefixCovered, Bool.and_eq_true_iff.mpr ⟨?_, prefixReady⟩⟩
            simpa only [SourceDependencyChecks.scope_append_assoc] using (Bool.and_eq_true_iff.mp ready).1
  | live dormant rest ihDormant ihRest =>
      cases source with | live rest saved next =>
        cases declared with | live savedDeclared declared =>
          cases covered with | live savedCovered covered =>
            obtain ⟨prefixSource, prefixDeclared, prefixCovered, prefixReady⟩ := ihRest next declared covered
              (Bool.and_eq_true_iff.mp ready).2
            refine ⟨.live _ saved prefixSource, .live savedDeclared prefixDeclared,
              .live savedCovered prefixCovered, Bool.and_eq_true_iff.mpr ⟨?_, prefixReady⟩⟩
            simpa only [SourceDependencyChecks.scope_append_assoc] using (Bool.and_eq_true_iff.mp ready).1

/-- The inserted selected handler adds no closing code. Its capture guard
therefore derives the old prefix's closing routes and its interference shield.
This reuses the exact finite route theorem rather than assuming route stability. -/
theorem prefix_routes {front tail : Scope}
    (guarded : SourceDependencyCapture.checkCapture outward whole effect operation = true)
    (found : SourceDependencyCapture.select effect operation whole =
      some (.handler (front.append (.handler effect table families .nil)) tail contract modes))
    (disposes : contract.dispose = true) :
    SourceRecursiveRoutes.Closing outward front.shape [] [] ∧
      SourceHandlerInterference.Shielded effect front.shape [] := by
  have routes := (SourceDependencyCapture.disposing_capture guarded found disposes).2.1
  have split := (SourceHandlerClosingInsertion.inserted_closing_iff front (.nil : Scope)).mp routes
  exact ⟨by simpa only [SourceDependencyProjection.scope_append_nil] using split.1, split.2⟩

/-- Fresh interception partitions the original owner inventory exactly, in
order and with multiplicity. The new handler contributes no owner. -/
theorem Intercept.owner_partition
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (intercepted : Intercept effect operation contract modes table families required before after saved waiting) :
    owners beforeScope = owners savedScope ++ owners waitingScope := by
  obtain ⟨_, _, front, passed, rfl, rfl, rfl, rfl, rfl, rfl⟩ := intercepted.prefix
  simp only [SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil]

/-- Derive all newly required closing callbacks from the original whole
source annotation. This is the fresh-request case consumed by the existing
structural adaptation compiler, with no target callback-success input. -/
theorem Intercept.callbacks
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (intercepted : Intercept effect operation contract modes table families required before after saved waiting)
    (source : Interfaces before) (declared : Declared world source) (covered : Covered source)
    (normal : normalCheck source .nil = true)
    (guarded : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
    (disposes : contract.dispose = true) :
    SourceScheduledClosingCallbacks.Callbacks outward actions phases world saved (.running waiting) := by
  obtain ⟨_, _, front, passed, rfl, rfl, rfl, rfl, rfl, rfl⟩ := intercepted.prefix
  obtain ⟨prefixSource, prefixDeclared, prefixCovered, prefixReady⟩ :=
    callbacks_at_prefix front waiting source declared covered normal
  have ready : normalCheck prefixSource (.running waitingScope) = true := by
    rw [← SourceScheduledCleanupInterfaces.normal_running]
    simpa only [SourceDependencyProjection.scope_append_nil] using prefixReady
  exact (SourceScheduledFreshRequests.callbacks_at_handler front).mpr
    (SourceScheduledCallbackRoutes.compile_from_routes prefixSource prefixDeclared prefixCovered
      (prefix_routes guarded intercepted.cut.erase.lookup disposes).1 ready)

/-- Generate a request annotation at an actual new interception from current
callback source evidence. The old request need not have any disposal schedule.
The new guard and pending-owner bound remain independent primitive judgments.
Callback interfaces here use the existing operation-footprint grammar; this
lemma does not narrow the separate general retained-code grammar. -/
theorem Intercept.annotation
    [declarations : DeclarationPolicy]
    (legacy : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (intercepted : Intercept effect operation contract modes table families required before after saved waiting)
    (source : Interfaces before) (declared : Declared world source) (covered : Covered source)
    (normal : contract.dispose = true → normalCheck source .nil = true)
    (guarded : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
    (bounded : contract.dispose = true → PendingWithin world (owners savedScope) savedScope) :
    ∃ annotation : Code world (.request (effect := effect) (operation := operation)) after,
      annotation.Valid outward actions phases := by
  have generated : contract.dispose = true →
      ∃ annotation : Retained world saved.forClosing (.running waiting),
        annotation.Valid outward actions phases := by
    intro disposes
    have captured := Intercept.callbacks intercepted (actions := actions) (phases := phases)
      source declared covered (normal disposes) guarded disposes
    exact (SourceScheduledCapabilityAnnotations.annotate_all_with
      (admission := SourceScheduledChecks.recipePolicy)
      (certification := SourcePlannedChecks.contextualPolicy) outward actions legacy).2 _ _ _ _ captured.schedule
  exact ⟨.selected intercepted.cut bounded (fun permission => Classical.choose (generated permission)),
    guarded, fun permission => Classical.choose_spec (generated permission)⟩

/-- Feed the source-derived fresh branch directly to the established mutual
adaptation proof. Retained selections and recursive continuation transport are
separate branches; this theorem does not assume that they have been generated. -/
theorem Intercept.adaptation
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (intercepted : Intercept effect operation contract modes table families required before after saved waiting)
    (source : Interfaces before) (declared : Declared world source) (covered : Covered source)
    (normal : contract.dispose = true → normalCheck source .nil = true)
    (guarded : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
    (bounded : contract.dispose = true → PendingWithin world (owners savedScope) savedScope) :
    SourceScheduledHandlerAdaptation.Adapt outward actions frame phases world
      (.request (effect := effect) (operation := operation)) before after :=
  .fresh intercepted.cut (SourceDependencyCapture.check_capture_iff.mp guarded) bounded
    (fun disposes => Intercept.callbacks intercepted source declared covered (normal disposes) guarded disposes)

end Ash.OneShot.SourceScheduledInterceptAdmission

#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.callbacks_at_prefix
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.prefix_routes
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Intercept.annotation

#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Intercept.callbacks
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Intercept.adaptation

#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Intercept.owner_partition
