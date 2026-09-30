import SourceConsumingCleanupAdmission
import SourceScheduledCaptureRetention
import SourceScheduledStructuralClosing

/-! Build capture contexts from original source and structural closing.
The closing field is fixed to the runtime snapshot's canonical projection,
not chosen from unrelated valid annotations of the same closing forest. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy DeclarationLaws)
open SourceScheduledSourceRechecking (Closing)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceDependencyOwners (owners)
open OwnerPhaseTransitions (spend introduce)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Reuse closing annotations already validated at the original request.
Their equality to the normal source's canonical metadata is checked separately.
Fresh-owner insertion and receiver transport are the existing capture proofs. -/
theorem Context.capture_canonical
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (inside : Retained world saved waiting) (after : Retained world waiting .nil)
    (ready : inside.Valid outward actions phases)
    (originalClosing : rights.dispose = true →
      ∃ annotation : Retained world saved.forClosing (.running waiting),
        annotation.Valid outward actions phases ∧ ofCapability annotation = (ofCapability inside).forClosing)
    (disposal : rights.dispose = true → savedScope.held = false ∧
      SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.Valid outward actions phases)
    (fresh : actions owner = none) (absent : owner ∉ owners (savedScope.append waitingScope)) :
    ∃ context : Context world owner outward (actions.insert owner rights) (introduce phases owner)
        (.live (owner := owner) saved waiting) .nil saved waiting,
      (∀ permission, ofCapability (context.resumption permission).val = ofCapability inside) ∧
      (∀ permission, ofCapability (context.closing permission).val = (ofCapability inside).forClosing) ∧
      ofCapability context.after = ofCapability after := by
  have originalValid (permission : rights.dispose = true) :
      ∃ annotation : Retained world saved.forClosing (.running waiting), annotation.Valid outward actions phases := by
    obtain ⟨annotation, valid, _⟩ := originalClosing permission
    exact ⟨annotation, valid⟩
  have closingAbsent : owner ∉ owners (savedScope.forClosing.append (.running waitingScope)) := by
    intro member
    apply absent
    simp only [SourceScheduledPhaseRestriction.owners_append, owners] at member ⊢
    exact (ScopedExpressions.append_subset (SourceScheduledPhaseRestriction.owners_closing savedScope)
      (List.Subset.refl (owners waitingScope))) member
  have generated (permission : ((actions.insert owner rights) owner).any (fun rights => rights.dispose) = true) :
      ∃ annotation : Retained world saved.forClosing (.running (.spent (owner := owner) waiting)),
        annotation.Valid outward (actions.insert owner rights) (spend (introduce phases owner) owner) ∧
        ofCapability annotation = (ofCapability inside).forClosing := by
    have allowed : rights.dispose = true := by simpa [Syntax.UsageTickets.insert] using permission
    obtain ⟨original, valid, originalKept⟩ := originalClosing allowed
    obtain ⟨annotation, checked, kept⟩ := original.expand_receiver_retaining laws project
      (original.valid_spent_fresh_owner valid fresh closingAbsent) (.running (.history .refl))
    exact ⟨annotation, checked, kept.trans originalKept⟩
  let base := Context.capture laws project inside after (fun _ => ready) originalValid disposal tailReady fresh absent
  let context : Context world owner outward (actions.insert owner rights) (introduce phases owner)
      (.live (owner := owner) saved waiting) .nil saved waiting :=
    { base with closing := fun permission => ⟨Classical.choose (generated permission), (Classical.choose_spec (generated permission)).1⟩ }
  refine ⟨context, ?_, ?_, rfl⟩
  · intro permission
    exact Context.capture_resumption_bounds laws project inside after (fun _ => ready)
      originalValid disposal tailReady fresh absent permission
  · intro permission
    exact (Classical.choose_spec (generated permission)).2

/-- Structural closing of the original source supplies the fresh context's
canonical disposal metadata. Existing fresh-owner and receiver transport proofs
provide validity; no target annotation or successful target check is assumed. -/
theorem Context.capture_structural
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (inside : Retained world saved waiting) (after : Retained world waiting .nil)
    (ready : inside.Valid outward actions phases)
    (closing : rights.dispose = true → Closing outward actions phases inside (.running waiting))
    (disposal : rights.dispose = true → savedScope.held = false ∧
      SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.Valid outward actions phases)
    (fresh : actions owner = none) (absent : owner ∉ owners (savedScope.append waitingScope)) :
    ∃ context : Context world owner outward (actions.insert owner rights) (introduce phases owner)
        (.live (owner := owner) saved waiting) .nil saved waiting,
      (∀ permission, ofCapability (context.resumption permission).val = ofCapability inside) ∧
      (∀ permission, ofCapability (context.closing permission).val = (ofCapability inside).forClosing) ∧
      ofCapability context.after = ofCapability after := by
  exact Context.capture_canonical laws project inside after ready
    (fun permission => (closing permission).compile_retaining laws project ready)
    disposal tailReady fresh absent

omit admission certification [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- Canonical contextual closing is precisely the existing runtime disposal
snapshot, including the spent owner and protected waiting tail. This is a data
correspondence lemma; execution and ownership reuse the established allocator. -/
theorem Context.discarded_of_closing
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (context : Context world owner outward actions phases
      (.live (owner := owner) saved waiting) .nil saved waiting)
    (savedBounds : SourceBoundSnapshots.Retained world saved)
    (permission : (actions owner).any (fun rights => rights.dispose) = true)
    (kept : ofCapability (context.closing permission).val = savedBounds.forClosing)
    {plan : SourceDeclarationPlans.Plan dependencies} (current : SourcePlanBounds.Annotation world plan) :
    SourceBoundSnapshots.Discarded owner
      ⟨_, plan, current, _, _, .live (owner := owner) saved waiting,
        .live savedBounds (ofCapability context.after)⟩
      (SourceBoundSnapshots.Snapshot.value
        ((ofCapability (context.closing permission).val).append
          (.running (.spent (owner := owner) (ofCapability context.after))))) := by
  rw [kept]
  exact .cut current .nil savedBounds (ofCapability context.after)

/-- Capture and subsequent contextual disposal share the original source
snapshot. Both snapshot admission results follow from the existing runtime
relations, while Closing generates the valid canonical closing annotation. -/
theorem Context.capture_structural_snapshot
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (inside : Retained world saved waiting) (after : Retained world waiting .nil)
    (ready : inside.Valid outward actions phases)
    (closing : rights.dispose = true → Closing outward actions phases inside (.running waiting))
    (disposal : rights.dispose = true → savedScope.held = false ∧
      SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.Valid outward actions phases)
    (fresh : actions owner = none) (absent : owner ∉ owners (savedScope.append waitingScope))
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotReady : snapshot.Admitted)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes snapshot.forest saved waiting)
    (aligned : HEq ((ofCapability inside).append (ofCapability after)) snapshot.pending)
    {plan : SourceDeclarationPlans.Plan dependencies} (current : SourcePlanBounds.Annotation world plan)
    (currentReady : current.Admitted) :
    ∃ context : Context world owner outward (actions.insert owner rights) (introduce phases owner)
        (.live (owner := owner) saved waiting) .nil saved waiting,
      let captured : SourceBoundSnapshots.Snapshot world :=
        ⟨_, plan, current, _, _, .live (owner := owner) saved waiting,
          .live (ofCapability inside) (ofCapability context.after)⟩
      SourceBoundSnapshots.Captured owner snapshot captured ∧ captured.Admitted ∧
      (∀ permission, ofCapability (context.resumption permission).val = ofCapability inside) ∧
      ∀ permission,
        let closed := SourceBoundSnapshots.Snapshot.value
          ((ofCapability (context.closing permission).val).append
            (.running (.spent (owner := owner) (ofCapability context.after))))
        SourceBoundSnapshots.Discarded owner captured closed ∧ closed.Admitted := by
  obtain ⟨context, resumeKept, closeKept, tailKept⟩ :=
    Context.capture_structural laws project inside after ready closing disposal tailReady fresh absent
  have original : HEq ((ofCapability inside).append (ofCapability context.after)) snapshot.pending :=
    (heq_of_eq (congrArg (fun tail => (ofCapability inside).append tail) tailKept)).trans aligned
  have moved := SourceScheduledCapabilityAnnotations.capture_snapshot_from_parts (owner := owner)
    snapshot cut (ofCapability inside) (ofCapability context.after) original current
  have admitted := moved.admitted snapshotReady currentReady
  refine ⟨context, moved, admitted, resumeKept, ?_⟩
  intro permission
  have disposed := context.discarded_of_closing (ofCapability inside) permission (closeKept permission) current
  exact ⟨disposed, disposed.admitted admitted⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.capture_canonical
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.capture_structural
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.discarded_of_closing

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.capture_structural_snapshot
