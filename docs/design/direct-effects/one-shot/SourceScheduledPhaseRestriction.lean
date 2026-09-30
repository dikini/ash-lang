import SourceScheduledTransport

/-! Phase changes need preserve availability only for recursively retained live
owners. This is a transport theorem for existing structural checks, not an
additional source-admission premise. Spent history and retired frame metadata
do not make an invocation target reachable. -/
-- Independent owner-set and cut laws are defined in SourceDependencySchemes
-- so lexical and legacy checks share the same phase restriction interface.
namespace Ash.OneShot.SourceScheduledPhaseRestriction
open ScopedExpressions
open SourceDependencyCapture (Scope OwnerSelection OwnerCut)
open SourceDependencyOwners (owners)
open SourceDependencyProjection (project)
open OwnerPhaseTransitions (Phases spend)
open SourceContextualHints (Hints)

/-- The existing dependency checker observes phases only at retained live
owners, including source recursively scheduled by resume and disposal. -/
theorem dependency_restrict
    (source : SourceDependencyChecks.Local outward actions before world dependencies scope)
    (extension : AvailableOn (owners scope) before after) :
    SourceDependencyChecks.Local outward actions after world dependencies scope := by
  refine SourceDependencyChecks.Local.rec
    (motive_1 := fun before world dependencies scope _ => ∀ after, AvailableOn (owners scope) before after →
      SourceDependencyChecks.Local outward actions after world dependencies scope)
    (motive_2 := fun before world forest outside _ => ∀ after, AvailableOn (owners (forest.append outside)) before after →
      SourceDependencyChecks.Pending outward actions after world forest outside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source after extension
  · intros; exact .pure
  · intro scope effect operation phases world guarded scheduled ownerBound ih after extension
    apply SourceDependencyChecks.Local.request guarded _ ownerBound
    intro captured tail contract modes found disposes
    apply ih captured tail contract modes found disposes after
    apply extension.weaken
    rw [owners_append, SourceDependencySchemes.owners_project, SourceDependencySchemes.owners_project,
      selected_scope found, owners_append]
    exact ScopedExpressions.append_subset (owners_closing _) (List.Subset.refl _)
  · intro phases owner scope result world access restored ih after extension
    cases access with
    | checked located known permission available =>
      apply SourceDependencyChecks.Local.resume (.checked located known permission (extension _ (selected_owner located) available))
      apply ih (spend after owner)
      apply extension.spend.weaken
      simpa only [owners_append, SourceDependencySchemes.owners_project, owners, List.append_nil] using resumed_owners located
  · intro phases owner scope result world access scheduled ih after extension
    cases access with
    | checked located known permission available unprotected closes =>
      apply SourceDependencyChecks.Local.dispose (.checked located known permission (extension _ (selected_owner located) available) unprotected closes)
      apply ih (spend after owner)
      apply extension.spend.weaken
      simpa only [owners_append, SourceDependencySchemes.owners_project, owners, List.append_nil] using disposed_owners located
  · intro phases world before next scope first second ihFirst ihSecond after extension
    exact .sequence (ihFirst after extension) (ihSecond after extension)
  · intro phases world first scope second left right ihLeft ihRight after extension
    exact .choice (ihLeft after extension) (ihRight after extension)
  · intro phases world dependencies effect table families scope body ih after extension
    exact .handler (ih after extension)
  · intro phases world dependencies needs callback scope body completion ihBody ihCallback after extension
    exact .cleanup (ihBody after extension) (ihCallback after extension)
  · intro world phases family scope body ih after extension
    exact .resource (fun identity fresh => ih identity fresh after extension)
  · intros; exact .nil
  · intro phases world dependencies rest outside code tail ihCode ihTail after extension
    exact .plain (ihCode after extension) (ihTail after extension)
  · intro phases world rest outside effect table families tail ih after extension
    exact .handler (ih after extension)
  · intro phases world rest outside identity tail ih after extension
    exact .cell (ih after extension)
  · intro phases world dependencies rest outside needs completion tail ihCode ihTail after extension
    exact .cleanup (ihCode after extension) (ihTail after extension)
  · intro phases world rest outside tail ih after extension
    exact .running (ih after extension)
  · intro phases world captured rest outside owner saved tail ihSaved ihTail after extension
    apply SourceDependencyChecks.Pending.live
    · apply ihSaved after
      apply extension.weaken
      simp only [Scope.append, owners, owners_append]
      exact List.subset_cons_self _ _
    · apply ihTail after
      apply extension.weaken
      simp only [Scope.append, owners, owners_append]
      intro name member
      exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
  · intro phases world rest outside owner tail ih after extension
    exact .spent (ih after extension)

private theorem resume_access_restrict
    (source : SourceDependencyCapture.ResumeChecked actions before owner scope result)
    (extension : AvailableOn (owners scope) before after) :
    SourceDependencyCapture.ResumeChecked actions after owner scope result := by
  cases source with
  | checked located known permission available =>
    exact .checked located known permission (extension _ (selected_owner located) available)

private theorem dispose_access_restrict
    (source : SourceDependencyCapture.DisposeChecked outward actions before owner scope result)
    (extension : AvailableOn (owners scope) before after) :
    SourceDependencyCapture.DisposeChecked outward actions after owner scope result := by
  cases source with
  | checked located known permission available unprotected closes =>
    exact .checked located known permission (extension _ (selected_owner located) available) unprotected closes

theorem resume_restrict {hints : Hints scope}
    (source : SourceContextualInvocations.Resume actions before owner hints result)
    (extension : AvailableOn (owners scope) before after) :
    SourceContextualInvocations.Resume actions after owner hints result := by
  cases source with
  | checked found access compatible => exact .checked found (resume_access_restrict access extension) compatible

theorem dispose_restrict {hints : Hints scope}
    (source : SourceContextualInvocations.Dispose outward actions before owner hints result)
    (extension : AvailableOn (owners scope) before after) :
    SourceContextualInvocations.Dispose outward actions after owner hints result := by
  cases source with
  | checked found access compatible => exact .checked found (dispose_access_restrict access extension) compatible

/-- Phase restriction retains actual plans, including dormant source and
cleanup schedules recursively exposed by a continuation invocation. -/
theorem local_restrict [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy] {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope}
    {forest : SourceRetainedPlans.Forest hints}
    (source : SourceScheduledChecks.Local outward actions before world plan forest)
    (extension : AvailableOn (owners scope) before after) :
    SourceScheduledChecks.Local outward actions after world plan forest := by
  refine SourceScheduledChecks.Local.rec
    (motive_1 := fun before world _ scope _ plan forest _ => ∀ after, AvailableOn (owners scope) before after →
      SourceScheduledChecks.Local outward actions after world plan forest)
    (motive_2 := fun before world scope outside _ _ forest outsideForest _ => ∀ after,
      AvailableOn (owners (scope.append outside)) before after →
      SourceScheduledChecks.Pending outward actions after world forest outsideForest)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := source) after extension
  · intros; exact .pure
  · intros
    rename_i guard scheduled ih after extension
    apply SourceScheduledChecks.Local.request
    · exact dependency_restrict guard (by simpa only [SourceDependencySchemes.owners_project] using extension)
    · intro captured tail saved waiting contract modes cut savedPlans waitingPlans same disposes
      apply ih captured tail saved waiting contract modes cut savedPlans waitingPlans same disposes after
      apply extension.weaken
      rw [owners_append, cut.reconstruct_scope, owners_append]
      exact ScopedExpressions.append_subset (owners_closing _) (List.Subset.refl _)
  · intros
    rename_i found access same restored ih after extension
    apply SourceScheduledChecks.Local.resume found (resume_restrict access extension) same
    apply ih (spend after _)
    apply extension.spend.weaken
    simpa only [OwnerSelection.resumed, owners_append, owners, List.append_nil] using
      resumed_owners (SourceContextualInvocationHints.selected_cut found)
  · intros
    rename_i found access same scheduled ih after extension
    apply SourceScheduledChecks.Local.dispose found (dispose_restrict access extension) same
    apply ih (spend after _)
    apply extension.spend.weaken
    simpa only [OwnerSelection.disposed, owners_append, owners, List.append_nil] using
      disposed_owners (SourceContextualInvocationHints.selected_cut found)
  · intros
    rename_i first second ihFirst ihSecond after extension
    exact .sequence (ihFirst after extension) (ihSecond after extension)
  · intros
    rename_i first second ihFirst ihSecond after extension
    exact .choice (ihFirst after extension) (ihSecond after extension)
  · intros
    rename_i recipes declarations supplied body ih after extension
    exact .handler recipes declarations supplied (ih after extension)
  · intros
    rename_i body completion ihBody ihCompletion after extension
    exact .cleanup (ihBody after extension) (ihCompletion after extension)
  · intros
    rename_i body ih after extension
    exact .resource (fun identity fresh => ih identity fresh after extension)
  · intros; exact .nil
  · intros
    rename_i code tail ihCode ihTail after extension
    exact .plain (ihCode after extension) (ihTail after extension)
  · intros
    rename_i supplied tail ih after extension
    exact .handler supplied (ih after extension)
  · intros
    rename_i tail ih after extension
    exact .cell (ih after extension)
  · intros
    rename_i completion tail ihCode ihTail after extension
    exact .cleanup (ihCode after extension) (ihTail after extension)
  · intros
    rename_i tail ih after extension
    exact .running (ih after extension)
  · intros
    rename_i saved tail ihSaved ihTail after extension
    apply SourceScheduledChecks.Pending.live
    · apply ihSaved after
      apply extension.weaken
      simp only [Scope.append, owners, owners_append]
      exact List.subset_cons_self _ _
    · apply ihTail after
      apply extension.weaken
      simp only [Scope.append, owners, owners_append]
      intro name member
      exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
  · intros
    rename_i tail ih after extension
    exact .spent (ih after extension)

end Ash.OneShot.SourceScheduledPhaseRestriction


#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.dependency_restrict

#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.resume_restrict
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.dispose_restrict
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.local_restrict

namespace Ash.OneShot.SourceScheduledFrames

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open SourceDependencyOwners (owners)
open SourceScheduledPhaseRestriction (AvailableOn owners_append local_restrict)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Ordinary frames do not introduce a live continuation owner. -/
theorem Frame.owner_scope
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (scope : SourceDependencyCapture.Scope) : owners (layer scope) = owners scope := by
  cases frame <;> rfl

/-- Restrict phase information without changing any source or retained plan. -/
theorem Frame.phase_restrict {hints : Hints receivingScope} {receiving : Forest hints}
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions before world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (extension : AvailableOn (owners receivingScope) before after) :
    Frame (evidence := evidence) operations policy contracts tables families required outward actions after world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation checked =>
      exact .plain context scope inputAnnotation outputAnnotation (local_restrict checked extension)
  | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
      exact .handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes
  | cell scope noEscape annotation interface => exact .cell scope noEscape annotation interface
  | armed scope callback annotation interface checked =>
      exact .armed scope callback annotation interface (local_restrict checked extension)
  | running scope callback saved annotation interface => exact .running scope callback saved annotation interface
  | closing scope interface => exact .closing scope interface
  | retiring known interface => exact .retiring known interface

/-- Typed pending computations use phase information only at owners in their
actual retained forest and receiving suffix, including dormant captures. -/
theorem Segment.phase_restrict {hints : Hints dependencyScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward before world
      stack input output demand requirements records forest outside incoming outgoing)
    (extension : AvailableOn (owners (dependencyScope.append outsideScope)) before after) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward after world
      stack input output demand requirements records forest outside incoming outgoing := by
  induction source generalizing after with
  | nil bound => exact .nil bound
  | push head tail bound ih =>
      refine .push (head.phase_restrict ?_) (ih ?_) bound <;>
        simpa only [SourceScheduledPhaseRestriction.owners_append, head.owner_scope] using extension
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      apply Segment.live known actionKnown inputAnnotation answerAnnotation scope held
      · apply ihSaved
        apply extension.weaken
        simp only [SourceScheduledPhaseRestriction.owners_append, SourceDependencyOwners.owners, List.cons_append, List.append_assoc]
        exact List.subset_cons_self _ _
      · exact savedBound
      · apply ihTail
        apply extension.weaken
        simp only [SourceScheduledPhaseRestriction.owners_append, SourceDependencyOwners.owners, List.cons_append, List.append_assoc]
        intro name member
        exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
      · exact resume
      · exact close
      · exact bound
  | spent known annotation scope tail bound ih =>
      exact .spent known annotation scope (ih extension) bound

end Ash.OneShot.SourceScheduledFrames

#print axioms Ash.OneShot.SourceScheduledFrames.Frame.owner_scope
#print axioms Ash.OneShot.SourceScheduledFrames.Frame.phase_restrict
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.phase_restrict
