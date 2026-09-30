import SourceAnnotatedStoredBoundaries
import SourceAnnotatedRuntimeRetirement
import SourceScheduledPhaseRestriction

/-! Retirement preserves annotated saved computations. The existing finite-owner
phase restriction and ownership trace supply the scheduling and consumption
proofs; the annotations and rich source choices remain unchanged. -/
namespace Ash.OneShot.SourceAnnotatedStoredTyping

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open SourceDependencyOwners (owners)
open SourceScheduledPhaseRestriction (AvailableOn owners_append local_restrict)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

theorem Frame.owner_scope
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing packet)
    (scope : SourceDependencyCapture.Scope) : owners (layer scope) = owners scope := by
  exact frame.forget.owner_scope scope

theorem Frame.phase_restrict {hints : Hints receivingScope} {receiving : Forest hints}
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions before world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing packet)
    (extension : AvailableOn (owners receivingScope) before after) :
    Frame (evidence := evidence) operations policy contracts tables families required outward actions after world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing packet :=
  ⟨frame.forget.phase_restrict extension, frame.packetSource⟩

theorem Segment.phase_restrict {hints : Hints dependencyScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward before world
      stack input output demand requirements records forest outside incoming outgoing stored)
    (extension : AvailableOn (owners (dependencyScope.append outsideScope)) before after) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward after world
      stack input output demand requirements records forest outside incoming outgoing stored := by
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

end Ash.OneShot.SourceAnnotatedStoredTyping

namespace Ash.OneShot.SourceAnnotatedStoredRetirement

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)
open OwnerPhaseTransitions (available spendAll Trace)
open SourceAnnotatedStoredReturns (value_pending)
open SourceAnnotatedStoredResumption (value_configuration_atPackets)

/-- Retiring a ticket changes availability without invalidating the retained
stack's source checks. No check on the successor is assumed. -/
theorem retire_snapshot [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.unit hint) (.push (.retiring owner) tail) snapshot.plan snapshot.forest output demand row (.push .retiring stored) evidence) :
    ∃ remaining, ∃ next : SourceBoundSnapshots.Snapshot world,
      demand = owner :: remaining ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        scope (.unit hint) tail next.plan next.forest output remaining row stored evidence ∧
      SourceBoundSnapshots.Exited .running snapshot next ∧
      Trace (available (ownedTickets (.push (.retiring owner) tail.erase))) [owner] (available (ownedTickets tail.erase)) := by
  rcases snapshot with ⟨rootDependencies, rootPlan, rootBounds, receiving, hints, wholeForest, queuedMetadata⟩
  dsimp only at state ⊢
  obtain ⟨input, incoming, requirements, records, disposals, summary, ⟨ticket, scopeTyped⟩, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => rcases head with ⟨head, packetSource⟩; cases head with
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
              List.append_nil, SourceDependencyOwners.realized_owners rest.forget.erase.source.source.matches.realizes] using member
          exact if_pos (recursive_live_tickets_owned tail.erase live))
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        refine ⟨_, SourceBoundSnapshots.Snapshot.value remainingBounds, rfl, ?_, .running rootBounds remainingBounds, .cons ready ?_⟩
        · exact value_configuration_atPackets summary trivial scopeTyped restricted closing templatesAfter matched
            (List.nodup_cons.mp unique).2 (by simpa only [same, List.nil_append] using next) accepted
        · simpa only [ownedTickets, phases] using (Trace.nil (before := available (ownedTickets tail.erase)))

end Ash.OneShot.SourceAnnotatedStoredRetirement

#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Frame.owner_scope
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Frame.phase_restrict
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.phase_restrict
#print axioms Ash.OneShot.SourceAnnotatedStoredRetirement.retire_snapshot
