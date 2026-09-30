import SourceAnnotatedRuntimeBoundaries
import SourceScheduledPhaseRestriction

/-! Retirement preserves annotated saved computations. The existing finite-owner
phase restriction and ownership trace supply the scheduling and consumption
proofs; the annotations and rich source choices remain unchanged. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeTyping

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
  | plain context hint closed scope inputAnnotation outputAnnotation checked =>
      exact .plain context hint closed scope inputAnnotation outputAnnotation (local_restrict checked extension)
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

end Ash.OneShot.SourceAnnotatedRuntimeTyping

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Frame.owner_scope
#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Frame.phase_restrict
#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.phase_restrict

namespace Ash.OneShot.SourceAnnotatedRuntimeRetirement

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)
open OwnerPhaseTransitions (available spendAll Trace)
open SourceAnnotatedRuntimeReturns (value_pending value_configuration value_configuration_atPlan)

/-- Retiring a ticket changes availability without invalidating the retained
stack's source checks. No check on the successor is assumed. -/
theorem retire_snapshot [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope (.unit hint) (.push (.retiring owner) tail) snapshot.plan snapshot.forest output demand row evidence) :
    ∃ remaining, ∃ next : SourceBoundSnapshots.Snapshot world,
      demand = owner :: remaining ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        scope (.unit hint) tail next.plan next.forest output remaining row evidence ∧
      SourceBoundSnapshots.Exited .running snapshot next ∧
      Trace (available (ownedTickets (.push (.retiring owner) tail.erase))) [owner] (available (ownedTickets tail.erase)) := by
  rcases snapshot with ⟨rootDependencies, rootPlan, rootBounds, receiving, hints, wholeForest, queuedMetadata⟩
  dsimp only at state ⊢
  obtain ⟨input, incoming, requirements, records, disposals, summary, ⟨ticket, scopeTyped⟩, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state.state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | retiring known interface => cases matched with
      | running matched => cases queuedMetadata with
      | running remainingBounds =>
        obtain ⟨firstRow, tailRow, firstCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
        have ready := OwnerPhaseTransitions.trace_available (RecursiveRequirements.checked_trace firstCheck) owner List.mem_cons_self
        have firstEmpty : firstRow = [] := by
          have evaluated := RecursiveRequirements.checked_complete firstCheck
          simpa only [Requirements.prepend, RecursiveClosing.evaluate_retire, if_pos ready, Option.some.injEq] using evaluated.symm
        subst firstRow
        have phases := OwnerPhaseTransitions.spend_available_cons (List.nodup_cons.mp unique).1
        have next := tailCheck
        simp only [spendAll, SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase, ownedTickets, phases] at next
        have restricted := rest.phase_restrict (after := available (ownedTickets tail.erase)) (by
          intro name member _
          have live : name ∈ tail.erase.erase.liveTickets := by
            simpa only [SourceScheduledPhaseRestriction.owners_append, SourceDependencyOwners.owners,
              List.append_nil, SourceDependencyOwners.realized_owners rest.erase.source.source.matches.realizes] using member
          exact if_pos (recursive_live_tickets_owned tail.erase live))
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        refine ⟨_, SourceBoundSnapshots.Snapshot.value remainingBounds, rfl, ?_, .running rootBounds remainingBounds, .cons ready ?_⟩
        · exact value_configuration_atPlan summary trivial scopeTyped restricted closing templatesAfter matched
            (List.nodup_cons.mp unique).2 (by simpa only [same, List.nil_append] using next) accepted
        · simpa only [ownedTickets, phases] using (Trace.nil (before := available (ownedTickets tail.erase)))

theorem retire [SourceScheduledChecks.DeclarationProjection admission certification]
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.unit hint) (.push (.retiring owner) tail) wholeForest output demand row evidence) :
    ∃ remaining, demand = owner :: remaining ∧
      (∃ rest : SourceScheduledSavedPlans.Saved,
        SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
          scope (.unit hint) tail rest.forest output remaining row evidence) ∧
      Trace (available (ownedTickets (.push (.retiring owner) tail.erase))) [owner] (available (ownedTickets tail.erase)) := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, wholeForest, SourceBoundSnapshots.Retained.absent wholeForest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          scope (.unit hint) (.push (.retiring owner) tail) snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting
      obtain ⟨remaining, next, consumed, typed, _, trace⟩ := retire_snapshot snapshot indexed
      exact ⟨remaining, consumed, ⟨⟨_, _, next.forest⟩, typed.state⟩, trace⟩

end Ash.OneShot.SourceAnnotatedRuntimeRetirement

#print axioms Ash.OneShot.SourceAnnotatedRuntimeRetirement.retire

#print axioms Ash.OneShot.SourceAnnotatedRuntimeRetirement.retire_snapshot
