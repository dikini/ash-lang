import SourceScheduledHandlerInterfaceAdmission

/-! Generate consuming source by checking saved operation interfaces at the
consuming leaves. Intermediate handler contexts need not validate dormant saved
code. Waiting annotations remain arbitrary and retain their exact metadata. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledNeutral (OwnerCut)
open SourceBoundSnapshots.Retained (ofCapability)
open OwnerPhaseTransitions (spend)

variable [DeclarationPolicy]

/-- One structural traversal constructs the annotation and its correspondence.
The operation-bound transport at each consuming leaf is the existing interface
lemma. Saved/closing source may have permission-dependent interfaces; the waiting
source is kept verbatim. No intermediate receiver-change premise is required. -/
theorem Body.generate_leaf_interfaces {plan : Plan dependencies} (body : Body world owner plan)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : OwnerCut owner whole front saved waiting)
    (before : Interfaces world front)
    (bounds : ContinuationBounds world owner actions saved waiting)
    (inside : (actions owner).any (fun rights => rights.resume) = true → Interfaces world saved)
    (closing : (actions owner).any (fun rights => rights.dispose) = true → Interfaces world saved.forClosing)
    (after : Retained world waiting .nil)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope before)
    (resumeBound : ∀ permission, (inside permission).exposed ⊆ resumeRequired)
    (closeBound : ∀ permission, (closing permission).exposed ⊆ closeRequired)
    (resumeReady : ∀ permission, (inside permission).check resumeOutside = true)
    (closeReady : ∀ permission, (closing permission).check closeOutside = true)
    (disposal : (actions owner).any (fun rights => rights.dispose) = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.Valid outward actions (spend phases owner))
    (resumeKept : ∀ permission, SourceBoundSnapshots.Retained.absent saved = bounds.resumption permission)
    (closeKept : ∀ permission, SourceBoundSnapshots.Retained.absent saved.forClosing = bounds.closing permission)
    (waitingKept : ofCapability after = bounds.after) :
    ∃ annotation : Code world plan whole,
      annotation.Valid outward actions phases ∧ Generated actions bounds body annotation := by
  induction body generalizing wholeScope frontScope with
  | resume =>
      refine ⟨.resume cut (.operations (inside checked.1)) (.operations before) after, ?_, ?_⟩
      · exact ⟨checked.1, checked.2.1,
          (inside checked.1).check_from_bound (resumeReady checked.1) (resumeBound checked.1) checked.2.2.1,
          checked.2.2.2, tailReady⟩
      · exact .resume checked.1 (resumeKept checked.1) waitingKept
  | dispose =>
      refine ⟨.dispose cut (.operations (closing checked.1)) (.operations before) after, ?_, ?_⟩
      · exact ⟨checked.1, checked.2.1, (disposal checked.1).1, (disposal checked.1).2,
          (closing checked.1).check_from_bound (closeReady checked.1) (closeBound checked.1) checked.2.2.1,
          checked.2.2.2, tailReady⟩
      · exact .dispose checked.1 (closeKept checked.1) waitingKept
  | sequence required footprint declared rest ih =>
      obtain ⟨code, valid, generated⟩ := ih cut before bounds inside closing after checked.2
        resumeBound closeBound resumeReady closeReady disposal tailReady resumeKept closeKept waitingKept
      exact ⟨.sequence (.operations required footprint declared) code, ⟨checked.1, valid⟩, .sequence generated⟩
  | choice first second ihFirst ihSecond =>
      obtain ⟨left, leftValid, leftGenerated⟩ := ihFirst cut before bounds inside closing after checked.1
        resumeBound closeBound resumeReady closeReady disposal tailReady resumeKept closeKept waitingKept
      obtain ⟨right, rightValid, rightGenerated⟩ := ihSecond cut before bounds inside closing after checked.2
        resumeBound closeBound resumeReady closeReady disposal tailReady resumeKept closeKept waitingKept
      exact ⟨.choice left right, ⟨leftValid, rightValid⟩, .choice leftGenerated rightGenerated⟩
  | handler clauseBounds admitted body ih =>
      obtain ⟨code, valid, generated⟩ := ih (.handler cut) (.handler front before) bounds inside closing after checked.2
        resumeBound closeBound resumeReady closeReady disposal tailReady resumeKept closeKept waitingKept
      exact ⟨.handler admitted code (some clauseBounds), ⟨checked.1, valid⟩, .handler generated⟩
  | cleanup required footprint declared body ih =>
      obtain ⟨code, valid, generated⟩ := ih (.cleanup cut) (.cleanup front required footprint declared before)
        bounds inside closing after checked.1 resumeBound closeBound resumeReady closeReady
        disposal tailReady resumeKept closeKept waitingKept
      exact ⟨.cleanup code (.operations required footprint declared), ⟨valid, checked.2⟩, .cleanup generated⟩
  | resource body ih =>
      have each := fun identity fresh => ih identity fresh (.cell cut)
        (.cell (before.world_weaken (List.subset_append_left _ _)))
        (bounds.world_weaken (List.subset_append_left _ _))
        (fun permission => (inside permission).world_weaken (List.subset_append_left _ _))
        (fun permission => (closing permission).world_weaken (List.subset_append_left _ _))
        (after.world_weaken (List.subset_append_left _ _)) (checked identity fresh)
        (fun permission => by simpa only [Interfaces.exposed_world_weaken] using resumeBound permission)
        (fun permission => by simpa only [Interfaces.exposed_world_weaken] using closeBound permission)
        (fun permission => by simpa only [Interfaces.check_world_weaken] using resumeReady permission)
        (fun permission => by simpa only [Interfaces.check_world_weaken] using closeReady permission)
        disposal (after.world_weaken_valid (List.subset_append_left _ _) tailReady)
        (fun permission => by
          dsimp only [ContinuationBounds.world_weaken]
          rw [← resumeKept permission, SourceBoundSnapshots.Retained.absent_world_weaken])
        (fun permission => by
          dsimp only [ContinuationBounds.world_weaken]
          rw [← closeKept permission, SourceBoundSnapshots.Retained.absent_world_weaken])
        (by rw [after.ofCapability_world_weaken, waitingKept]; rfl)
      refine ⟨.resource (fun identity fresh => Classical.choose (each identity fresh)), ?_, .resource ?_⟩
      · exact fun identity fresh => (Classical.choose_spec (each identity fresh)).1
      · exact fun identity fresh => (Classical.choose_spec (each identity fresh)).2

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.generate_leaf_interfaces

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceConsumingClauseAnnotations (Body Admitted Generated)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)

variable [declarations : DeclarationPolicy]

/-- Original-source views and the existing local contract suffice; this does
not require constructing a valid Context at every intermediate handler. -/
theorem Context.OperationSources.generate_leaf_source
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {context : Context world owner outward actions phases whole front saved waiting}
    (source : context.OperationSources) {body : Body world owner plan}
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    (resumeBound : ∀ permission, (source.resumption permission).exposed ⊆ resumeRequired)
    (closeBound : ∀ permission, (source.closing permission).exposed ⊆ closeRequired) :
    ∃ annotation : Code world plan whole,
      annotation.Valid outward actions phases ∧ Generated actions context.continuationBounds body annotation :=
  body.generate_leaf_interfaces context.cut context.before context.continuationBounds
    source.resumption source.closing context.after checked resumeBound closeBound
    (fun permission => (source.resumeSource permission).valid_iff.mp (context.resumption permission).property)
    (fun permission => (source.closeSource permission).valid_iff.mp (context.closing permission).property)
    context.disposal context.tailReady
    (fun permission => (source.resumeSource permission).bounds.symm)
    (fun permission => (source.closeSource permission).bounds.symm) rfl

/-- Initial structural admission derives the consuming-leaf checks. The actual
saved and closing views are checked only against their declared bounds; no
future At derivation, target validity or receiver-change witness is supplied. -/
theorem Context.OperationSources.initial_source
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {context : Context world owner outward actions phases (.live (owner := owner) saved waiting) .nil saved waiting}
    (source : context.OperationSources) {body : Body world owner plan}
    (admitted : Admitted rights resumeRequired closeRequired body required)
    (known : actions owner = some rights) (available : phases owner = .available)
    (supplied : checkRequirements waitingScope required = true)
    (resumeBound : ∀ permission, (source.resumption permission).exposed ⊆ resumeRequired)
    (closeBound : ∀ permission, (source.closing permission).exposed ⊆ closeRequired) :
    ∃ annotation : Code world plan (.live (owner := owner) saved waiting),
      annotation.Valid outward actions phases ∧ Generated actions context.continuationBounds body annotation := by
  apply source.generate_leaf_source (resumeRequired := resumeRequired) (closeRequired := closeRequired)
  · have checked := admitted.at_capture (captured := savedScope) known available supplied
    have before : context.before = .nil := by cases context.before; rfl
    simpa only [before] using checked
  · exact resumeBound
  · exact closeBound

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.generate_leaf_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.initial_source
