import SourceScheduledSourceRechecking
import SourceScheduledAnnotationPhases

/-! Preserve structural rechecking under permission extension and phase changes
that retain availability for the original source's live owners. The joint proof
reuses exact annotation transport; phase-only APIs specialize that proof. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledPhaseRestriction (AvailableOn owners_closing resumed_owners disposed_owners)
open SourceDependencyOwners (owners)
open SourceDependencyCapture (Scope OwnerSelection)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open OwnerPhaseTransitions (Phases spend)

variable [DeclarationPolicy]

theorem transport_rechecking (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ phases world {dependencies beforeScope afterScope} {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      (plan : Plan dependencies) (before : Forest beforeHints) (source : Code world plan before) (after : Forest afterHints),
      Expression outward actions phases source after → ∀ nextActions next, Syntax.UsageExtension actions nextActions →
      AvailableOn (owners beforeScope) phases next → Expression outward nextActions next source after) ∧
    (∀ phases world {beforeScope outsideScope afterScope nextOutsideScope}
      {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
      {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
      (before : Forest beforeHints) (outside : Forest outsideHints) (source : Retained world before outside)
      (after : Forest afterHints) (nextOutside : Forest nextOutsideHints),
      RetainedChange outward actions phases source after nextOutside → ∀ nextActions next, Syntax.UsageExtension actions nextActions →
      AvailableOn (owners (beforeScope.append outsideScope)) phases next →
      RetainedChange outward nextActions next source after nextOutside) := by
  constructor
  all_goals first
    | (intro phases world dependencies beforeScope afterScope beforeHints afterHints plan before source after changed
       apply Expression.rec
         (motive_1 := fun phases {world _ beforeScope _ _ _} plan before source after _ =>
           ∀ nextActions next, Syntax.UsageExtension actions nextActions → AvailableOn (owners beforeScope) phases next → Expression outward nextActions next source after)
         (motive_2 := fun phases {world beforeScope outsideScope _ _ _ _ _ _} before outside source after nextOutside _ =>
           ∀ nextActions next, Syntax.UsageExtension actions nextActions → AvailableOn (owners (beforeScope.append outsideScope)) phases next →
             RetainedChange outward nextActions next source after nextOutside)
         (t := changed))
    | (intro phases world beforeScope outsideScope afterScope nextOutsideScope beforeHints outsideHints afterHints nextOutsideHints
         before outside source after nextOutside changed
       apply RetainedChange.rec
         (motive_1 := fun phases {world _ beforeScope _ _ _} plan before source after _ =>
           ∀ nextActions next, Syntax.UsageExtension actions nextActions → AvailableOn (owners beforeScope) phases next → Expression outward nextActions next source after)
         (motive_2 := fun phases {world beforeScope outsideScope _ _ _ _ _ _} before outside source after nextOutside _ =>
           ∀ nextActions next, Syntax.UsageExtension actions nextActions → AvailableOn (owners (beforeScope.append outsideScope)) phases next →
             RetainedChange outward nextActions next source after nextOutside)
         (t := changed))
  all_goals intros
  all_goals first
    | exact .same
    | (rename_i supplied nextActions next permissions extension; exact .operations supplied)
    | (rename_i footprint supplied nextActions next permissions extension; exact .reinterface footprint supplied)
    | (rename_i supplied nextActions next permissions extension; exact .capability supplied)
    | (rename_i cut guarded denied nextActions next permissions extension; exact .nonDisposing cut guarded denied)
    | (rename_i intercepted callbacks declared covered normal guarded bounded nextActions next permissions extension
       exact .freshInterfaces intercepted callbacks declared covered normal guarded bounded)
    | (rename_i intercepted normal original guarded bounded closing ih nextActions next permissions extension
       exact .freshRich intercepted normal (fun disposes => normal.valid_transport (original disposes) permissions extension)
         guarded bounded (fun disposes => ih disposes nextActions next permissions extension))
    | (rename_i first second ihFirst ihSecond nextActions next permissions extension
       exact .sequence (ihFirst nextActions next permissions extension) (ihSecond nextActions next permissions extension))
    | (rename_i first second ihFirst ihSecond nextActions next permissions extension
       exact .choice (ihFirst nextActions next permissions extension) (ihSecond nextActions next permissions extension))
    | (rename_i declared bounds supplied body ih nextActions next permissions extension
       exact .handler supplied (ih nextActions next permissions extension))
    | (rename_i body completion ihBody ihCompletion nextActions next permissions extension
       exact .cleanup (ihBody nextActions next permissions extension) (ihCompletion nextActions next permissions extension))
    | (rename_i body ih nextActions next permissions extension
       exact .resource (fun identity fresh => ih identity fresh nextActions next permissions extension))
    | (rename_i interfaces supplied nextActions next permissions extension; exact .operations interfaces supplied)
    | (rename_i source ready previous inserted ih nextActions next permissions extension
       exact .provide (source.valid_transport ready permissions extension)
         (ih nextActions next permissions extension) inserted)
    | (rename_i code tail ihCode ihTail nextActions next permissions extension
       exact .plain (ihCode nextActions next permissions extension) (ihTail nextActions next permissions extension))
    | (rename_i supplied tail ih nextActions next permissions extension; exact .handler supplied (ih nextActions next permissions extension))
    | (rename_i tail ih nextActions next permissions extension; exact .cell (ih nextActions next permissions extension))
    | (rename_i completion tail ihCompletion ihTail nextActions next permissions extension
       exact .cleanup (ihCompletion nextActions next permissions extension) (ihTail nextActions next permissions extension))
    | (rename_i tail ih nextActions next permissions extension; exact .running (ih nextActions next permissions extension))
    | (rename_i tail ih nextActions next permissions extension; exact .spent (ih nextActions next permissions extension))
    | (rename_i before outside source supplied nextActions next permissions extension; exact .install supplied)
    | (rename_i source required footprint declared supplied nextActions next permissions extension
       exact .installCleanup required footprint declared supplied)
    | (rename_i tail ih nextActions next permissions extension; exact .dropPlain (ih nextActions next permissions extension))
    | (rename_i tail ih nextActions next permissions extension; exact .dropHandler (ih nextActions next permissions extension))
    | (rename_i tail ih nextActions next permissions extension; exact .dropSpent (ih nextActions next permissions extension))
    | (rename_i tail ih nextActions next permissions extension; exact .protect (ih nextActions next permissions extension))
    | (rename_i oldCut oldBound afterHints after nextSavedHints nextWaitingHints nextSaved nextWaiting
         nextCut guarded bounded closing ih nextActions next permissions extension
       refine .selected nextCut guarded bounded (fun disposes => ih disposes nextActions next permissions ?_)
       apply extension.weaken
       rw [SourceScheduledPhaseRestriction.owners_append, oldCut.erase.reconstruct_scope,
         SourceScheduledPhaseRestriction.owners_append]
       exact ScopedExpressions.append_subset (owners_closing _) (List.Subset.refl _))
    | (rename_i oldCut nextFrontHints nextTailHints nextFront nextTail nextCut inside before tail ihInside ihBefore ihTail nextActions next permissions extension
       have restored := SourceScheduledCapabilityAnnotations.resumed_phases oldCut extension
       refine .resume nextCut (ihInside nextActions _ permissions restored) (ihBefore nextActions _ permissions ?_) (ihTail nextActions _ permissions ?_)
       · apply restored.weaken
         simp only [SourceScheduledPhaseRestriction.owners_append]
         exact List.subset_append_right _ _
       · apply restored.weaken
         simp only [SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil]
         intro name member
         exact List.mem_append_right _ (List.mem_append_right _ member))
    | (rename_i oldCut nextFrontHints nextTailHints nextFront nextTail nextCut closing before tail ihClosing ihBefore ihTail nextActions next permissions extension
       have restored := SourceScheduledCapabilityAnnotations.disposed_phases oldCut extension
       refine .dispose nextCut (ihClosing nextActions _ permissions restored) (ihBefore nextActions _ permissions ?_) (ihTail nextActions _ permissions ?_)
       · apply restored.weaken
         simp only [SourceScheduledPhaseRestriction.owners_append, owners]
         exact List.subset_append_right _ _
       · apply restored.weaken
         simp only [SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil]
         intro name member
         exact List.mem_append_right _ (List.mem_append_right _ member))
    | (rename_i saved tail ihSaved ihTail nextActions next permissions extension
       first | apply RetainedChange.live | apply RetainedChange.closeLive
       · apply ihSaved nextActions next permissions
         apply extension.weaken
         simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
         exact List.subset_cons_self _ _
       · apply ihTail nextActions next permissions
         apply extension.weaken
         simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
         intro name member
         exact List.mem_cons_of_mem _ (List.mem_append_right _ member))

theorem restrict_rechecking_phases (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ phases world {dependencies beforeScope afterScope} {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      (plan : Plan dependencies) (before : Forest beforeHints) (source : Code world plan before) (after : Forest afterHints),
      Expression outward actions phases source after → ∀ next,
      AvailableOn (owners beforeScope) phases next → Expression outward actions next source after) ∧
    (∀ phases world {beforeScope outsideScope afterScope nextOutsideScope}
      {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
      {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
      (before : Forest beforeHints) (outside : Forest outsideHints) (source : Retained world before outside)
      (after : Forest afterHints) (nextOutside : Forest nextOutsideHints),
      RetainedChange outward actions phases source after nextOutside → ∀ next,
      AvailableOn (owners (beforeScope.append outsideScope)) phases next →
      RetainedChange outward actions next source after nextOutside) := by
  constructor
  · intro phases world dependencies beforeScope afterScope beforeHints afterHints plan before source after changed next extension
    exact (transport_rechecking outward actions).1 _ _ _ _ _ _ changed actions next
      (fun _ _ known => known) extension
  · intro phases world beforeScope outsideScope afterScope nextOutsideScope beforeHints outsideHints afterHints nextOutsideHints
      before outside source after nextOutside changed next extension
    exact (transport_rechecking outward actions).2 _ _ _ _ _ _ _ changed actions next
      (fun _ _ known => known) extension

theorem Expression.restrict_phases
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints} {source : Code world plan before}
    (changed : Expression outward actions phases source after)
    (extension : AvailableOn (owners beforeScope) phases next) : Expression outward actions next source after :=
  (restrict_rechecking_phases outward actions).1 _ _ _ _ _ _ changed next extension

theorem RetainedChange.restrict_phases
    {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
    {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
    {before : Forest beforeHints} {outside : Forest outsideHints}
    {after : Forest afterHints} {nextOutside : Forest nextOutsideHints} {source : Retained world before outside}
    (changed : RetainedChange outward actions phases source after nextOutside)
    (extension : AvailableOn (owners (beforeScope.append outsideScope)) phases next) :
    RetainedChange outward actions next source after nextOutside :=
  (restrict_rechecking_phases outward actions).2 _ _ _ _ _ _ _ changed next extension

theorem Expression.transport
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints} {source : Code world plan before}
    (changed : Expression outward actions phases source after)
    (permissions : Syntax.UsageExtension actions nextActions)
    (extension : AvailableOn (owners beforeScope) phases next) : Expression outward nextActions next source after :=
  (transport_rechecking outward actions).1 _ _ _ _ _ _ changed nextActions next permissions extension

theorem RetainedChange.transport
    {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
    {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
    {before : Forest beforeHints} {outside : Forest outsideHints}
    {after : Forest afterHints} {nextOutside : Forest nextOutsideHints} {source : Retained world before outside}
    (changed : RetainedChange outward actions phases source after nextOutside)
    (permissions : Syntax.UsageExtension actions nextActions)
    (extension : AvailableOn (owners (beforeScope.append outsideScope)) phases next) :
    RetainedChange outward nextActions next source after nextOutside :=
  (transport_rechecking outward actions).2 _ _ _ _ _ _ _ changed nextActions next permissions extension

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.restrict_rechecking_phases
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.restrict_phases
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedChange.restrict_phases

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.transport_rechecking
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.transport
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedChange.transport
