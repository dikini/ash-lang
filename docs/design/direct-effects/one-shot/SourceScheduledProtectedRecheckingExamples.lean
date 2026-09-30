import SourceScheduledProtectedRechecking
import SourceScheduledStructuralClosing

/-! A callback can use an outer handler's protected mode even when that
handler offers no ordinary mode. This is source/receiver rechecking evidence;
it does not authorize exchanging interpretations or omit capture route checks. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples
open SourceDeclarationPlans (Plan)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceDependencyCapture (Scope)
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies)

def contract : ProtectionContracts.ClauseContract := ⟨false, none, some []⟩
def modes : SourcePlannedCuts.Modes := (none, some (fun _ => .pure))
def table := [(0, contract)]
def families := [(0, modes)]
def before : Forest (Hints.handler (effect := effectE) (table := resumeTable)
    (families := resumeDependencies) [] .nil) := .handler .nil
def after : Forest (Hints.handler (effect := effectE) (table := table)
    (families := families) [] .nil) := .handler .nil
def request := Plan.request (effect := effectE) (operation := 0)
def original : Code [] request (.running before) := .operations [(effectE, 0)] .request .request
def actions : Syntax.UsageTickets := fun _ => none
def phases := OwnerPhaseTransitions.empty

theorem original_valid : original.Valid [] actions phases := rfl

theorem protected_guard : SourceDependencyCapture.checkCapture []
    (.running (.handler effectE table families .nil)) effectE 0 = true := rfl

theorem ordinary_rejected : SourceDependencyCapture.checkCapture []
    (.handler effectE table families .nil) effectE 0 = false := rfl

/-- The uniform operation interface correctly rejects the absent ordinary
mode. The local protected-mode rule does not weaken that reusable interface. -/
theorem uniform_capability_rejected : ¬ SourceContextualClauses.RequestCapability effectE 0
    (.running (.handler effectE table families .nil)) := by
  intro capability
  have checked := SourceContextualRequirements.check_capability_iff.mpr capability
  change false = true at checked
  cases checked

theorem rechecked : Expression [] actions phases original (.running after) :=
  .crosses_cleanup_from_contract .nil rfl (.hit rfl rfl) rfl rfl rfl

theorem generated : ∃ annotation : Code [] request (.running after),
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode original :=
  rechecked.compile_retaining (recipeLaws []) (fun checked => checked) original_valid

def normal : Retained [] (Forest.cleanup (needs := [effectE]) request .nil) before :=
  .cleanup original (.operations .nil)

theorem normal_valid : normal.Valid [] actions phases := ⟨original_valid, rfl⟩

/-- The arbitrary-prefix lemma covers the second running marker introduced
by disposal. The callback keeps its actual request and original source bounds. -/
theorem closing : Closing [] actions phases normal (.running after) :=
  .cleanup (.crosses_cleanup_from_contract (Forest.running .nil) rfl (.hit rfl rfl) rfl rfl rfl) .empty

theorem generated_closing :
    ∃ annotation : Retained [] (Forest.cleanup (needs := [effectE]) request .nil).forClosing (.running after),
      annotation.Valid [] actions phases ∧ SourceBoundSnapshots.Retained.ofCapability annotation =
        (SourceBoundSnapshots.Retained.ofCapability normal).forClosing :=
  closing.compile_retaining (recipeLaws []) (fun checked => checked) normal_valid

/-- A protected row without its matching source-body family is insufficient. -/
theorem missing_protected_body_rejected : SourceDependencyCapture.checkCapture []
    (.running (.handler effectE table [(0, (none, none))] .nil)) effectE 0 = false := rfl

/-- Crossing a running callback never admits a disposing interpretation. -/
theorem disposing_handler_rejected : SourceDependencyCapture.checkCapture []
    (.running (.handler effectE [(0, ⟨true, some [], some []⟩)] families .nil)) effectE 0 = false := rfl

end Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.protected_guard
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.ordinary_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.uniform_capability_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.normal_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.closing
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.generated_closing
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.missing_protected_body_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ProtectedRequestExamples.disposing_handler_rejected
