import SourceConsumingReceiverMetadata
import SourceConsumingStructuralCleanupExamples
import SourceScheduledRetainedRecompositionExamples

/-! Separate physical receiver agreement from retained metadata agreement.
A concrete old-generation result can satisfy validity/current bounds while
losing saved bounds. Receiver-only rechecking fixes those data independently. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceScheduledSourceRechecking (ReceiverChange RetainedChange)
open SourceScheduledSourceRechecking
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceBoundSnapshots.Retained (ofCapability)

def actions : Syntax.UsageTickets := fun owner => if owner = 19 then some ⟨true, false⟩ else none
def phases := OwnerPhaseTransitions.available [19]
def saved := RecompositionExamples.suffix

def rich : Retained [] saved (.spent (owner := 19) .nil) :=
  .plain (RecompositionExamples.annotated (.spent (owner := 19) .nil)) (.operations .nil)
def erasedInterfaces : Interfaces [] saved :=
  .plain .nil [] (.handler .pure rfl) (.handler .nil .pure) .nil
def erased : Retained [] saved (.spent (owner := 19) .nil) := .operations erasedInterfaces

theorem rich_valid : rich.Valid [] actions (OwnerPhaseTransitions.spend phases 19) :=
  ⟨RecompositionExamples.annotated_valid _, rfl⟩
theorem erased_valid : erased.Valid [] actions (OwnerPhaseTransitions.spend phases 19) := rfl

def context (inside : Retained [] saved (.spent (owner := 19) .nil))
    (ready : inside.Valid [] actions (OwnerPhaseTransitions.spend phases 19)) :
    Context [] 19 [] actions phases (.live (owner := 19) saved .nil) .nil saved .nil where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨inside, ready⟩
  closing := fun impossible => False.elim (Bool.noConfusion impossible)
  disposal := fun impossible => False.elim (Bool.noConfusion impossible)
  after := .operations .nil
  tailReady := rfl

def richContext := context rich rich_valid
def erasedContext := context erased erased_valid

/-- The rich source admits resumption directly; replacing it by the erased
context is no longer a permitted same-receiver conversion. -/
theorem admitted_at_rich : At (recipeLaws []) (fun evidence => evidence)
    (Body.resume : Body [] 19 (Plan.invoke (key := ⟨19, .resume⟩))) richContext :=
  .resume

/-- Equal physical stacks and caller interfaces do not imply metadata equality. -/
theorem same_receiver_changes_bounds : ¬ erasedContext.BoundsAgree richContext := by
  intro agreement
  have impossible := agreement.resumption (by rfl)
  cases impossible

def oldWitness : Code [] (Plan.invoke (key := ⟨19, .resume⟩)) (.live (owner := 19) saved .nil) :=
  .resume richContext.cut erased (.operations .nil) (.operations .nil)

theorem old_witness_valid : oldWitness.Valid [] actions phases := ⟨rfl, rfl, erased_valid, rfl, rfl⟩

/-- This is a counterexample to strengthening the old result type implicitly,
not a claim about which witness a classical existential actually chooses. -/
theorem current_bounds_do_not_fix_saved_bounds :
    ∃ annotation : Code [] (Plan.invoke (key := ⟨19, .resume⟩)) (.live (owner := 19) saved .nil),
      annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation =
        (Body.resume : Body [] 19 (Plan.invoke (key := ⟨19, .resume⟩))).boundAnnotation ∧
      annotation.boundAt [.saved, .body] 0 false ≠ (richContext.resumption (by rfl)).val.boundAt [.body] 0 false :=
  ⟨oldWitness, old_witness_valid, rfl, by decide⟩

/-- General rechecking can discard and recreate an identical physical forest.
Its metadata-provenance contract deliberately permits the resulting absence. -/
theorem general_rechecking_can_erase : RetainedChange [] actions phases
    RecompositionExamples.suffixSource saved .nil :=
  .dropPlain (.operations erasedInterfaces rfl)

theorem erased_metadata_differs :
    SourceBoundSnapshots.Retained.absent saved ≠ ofCapability RecompositionExamples.suffixSource := by
  intro same
  cases same

/-- The receiver-only judgment admits a real cleanup insertion around an
outside-owner resumption and preserves the original context's complete bounds. -/
theorem outside_owner_rechecked :
    ∃ next : Context [4] 19 [] StructuralExamples.actions StructuralExamples.phases
        (.cleanup (needs := [.cell 4]) StructuralExamples.callback StructuralExamples.whole)
        (.cleanup (needs := [.cell 4]) StructuralExamples.callback .nil)
        StructuralExamples.saved StructuralExamples.waiting,
      next.before = Interfaces.cleanup .nil [(.cell 4, 0)] .request .request StructuralExamples.context.before ∧
      StructuralExamples.context.BoundsAgree next := by
  refine ⟨StructuralExamples.context.cleanupSource (recipeLaws []) (fun evidence => evidence)
    .request .request [.cell 4] StructuralExamples.resumption_rechecked
    (fun impossible => False.elim (Bool.noConfusion impossible)), rfl, ?_⟩
  exact Context.cleanupSource_bounds (recipeLaws []) (fun evidence => evidence) StructuralExamples.context
    .request .request [.cell 4] StructuralExamples.resumption_rechecked
    (fun impossible => False.elim (Bool.noConfusion impossible))

/-- Installing a real interpretation around the caller keeps nonempty saved
handler metadata; this is the positive counterpart of the erased witness above. -/
theorem bounded_handler_rechecked :
    ∃ next : Context [] 19 [] actions phases
        (.handler (effect := .user 81 []) (table := []) (families := []) (required := [])
          (.live (owner := 19) saved .nil))
        (.handler (effect := .user 81 []) (table := []) (families := []) (required := []) .nil) saved .nil,
      richContext.BoundsAgree next ∧
      ofCapability (next.resumption (by rfl)).val ≠ SourceBoundSnapshots.Retained.absent saved := by
  let next := richContext.handler (recipeLaws []) (fun evidence => evidence) (.user 81 []) [] [] []
    (fun _ => ReceiverChange.plain (.handler rfl (.operations rfl)) .empty)
    (fun impossible => False.elim (Bool.noConfusion impossible))
  have agreement : richContext.BoundsAgree next := Context.handler_bounds
    (recipeLaws []) (fun evidence => evidence) richContext (.user 81 []) [] [] []
    (fun _ => ReceiverChange.plain (.handler rfl (.operations rfl)) .empty)
    (fun impossible => False.elim (Bool.noConfusion impossible))
  refine ⟨next, agreement, ?_⟩
  intro erased
  have impossible := (agreement.resumption (by rfl)).symm.trans erased
  cases impossible

end Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.rich_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.erased_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.admitted_at_rich
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.same_receiver_changes_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.old_witness_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.current_bounds_do_not_fix_saved_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.general_rechecking_can_erase
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.erased_metadata_differs
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.outside_owner_rechecked

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverMetadataExamples.bounded_handler_rechecked
