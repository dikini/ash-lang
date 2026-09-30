import SourceScheduledSurvivingRequirements
import SourceScheduledSourceRecheckingExamples

/-! Finite admission of saved ordinary source, callbacks and dormant source
at a surviving interpretation boundary. Cells retained by closing discharge
local requirements; actual removed user interpretations are rejected. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (Retained recipeLaws)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceDependencyCapture.Examples (resumeTable resumeDependencies)

private def effect : Instance := .user 93 []
private def shadow : Instance := .user 94 []
def request := Plan.request (effect := effect) (operation := 0)
def cellRequest := Plan.request (effect := .cell 7) (operation := 0)
def saved := Forest.plain request (.cleanup (needs := [.cell 7]) cellRequest
  (.live (owner := 19) (.plain request .nil) .nil))
def interfaces : Interfaces [7] saved :=
  .plain _ [(effect, 0)] .request .request
    (.cleanup _ [(.cell 7, 0)] .request .request
      (.live _ (.plain _ [(effect, 0)] .request .request .nil) .nil))

def closing := Forest.handler (effect := shadow) (table := resumeTable)
  (families := resumeDependencies) (required := []) (.cell (identity := 7) .nil)
def outside := Forest.handler (effect := effect) (table := resumeTable)
  (families := resumeDependencies) (required := []) .nil

def source : Retained [7] saved (closing.append outside) := .operations interfaces

theorem original_valid : source.Valid [] actions phases := rfl

theorem exposed_requests : interfaces.exposed = [(effect, 0), (.cell 7, 0), (effect, 0)] := rfl

/-- Closing retains cell 7. Only the two external occurrences of E reach the
surviving handler; the cell requirement is not imposed on that outside. -/
theorem surviving_requests : SourceHandlerRequirements.outwardRequirements
    (Scope.handler shadow resumeTable resumeDependencies (.cell 7 .nil)).forClosing
    interfaces.exposed = [(effect, 0), (effect, 0)] := rfl

theorem outside_does_not_supply_cell : checkRequirements
    (.handler effect resumeTable resumeDependencies .nil) [(.cell 7, 0)] = false := rfl

theorem admitted : ReceiverChange [] actions phases source (closing.forClosing.append (.running outside)) :=
  .surviving_operations closing outside interfaces original_valid rfl

theorem generated : ∃ annotation : Retained [7] saved (closing.forClosing.append (.running outside)),
    annotation.Valid [] actions phases ∧
    SourceBoundSnapshots.Retained.ofCapability annotation = SourceBoundSnapshots.Retained.ofCapability source :=
  admitted.compile_retaining (recipeLaws []) (fun evidence => evidence) original_valid

/-- A stronger finite outside contract covers the entire exposed interface.
It suffices for all closing prefixes, including arbitrary dormant branches. -/
def suppliedOutside := Forest.cell (identity := 7) outside

theorem all_closing_prefixes {hints : Hints scope} (prefixForest : Forest hints) :
    ReceiverChange [] actions phases source (prefixForest.forClosing.append (.running suppliedOutside)) := by
  apply ReceiverChange.operations interfaces
  exact interfaces.check_any_closing (original_valid (actions := actions) (phases := phases))
    (required := [(effect, 0), (.cell 7, 0)])
    (by
      rw [exposed_requests]
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> simp) rfl scope

/-- If E belongs to the discarded handler prefix, the normal source still
passes, but its factored admission check at the surviving outside fails. -/
def lostClosing := Forest.handler (effect := effect) (table := resumeTable)
  (families := resumeDependencies) (required := []) (.cell (identity := 7) .nil)
def lostSource : Retained [7] saved lostClosing := .operations interfaces

theorem lost_original_valid : lostSource.Valid [] actions phases := rfl

theorem lost_boundary_rejected : checkRequirements .nil
    (SourceHandlerRequirements.outwardRequirements
      (Scope.handler effect resumeTable resumeDependencies (.cell 7 .nil)).forClosing interfaces.exposed) = false := rfl

theorem lost_interface_rejected : interfaces.check
    ((Scope.handler effect resumeTable resumeDependencies (.cell 7 .nil)).forClosing.append (.running .nil)) ≠ true := by
  intro accepted
  have impossible := (interfaces.check_closing_receiver_iff
    (lost_original_valid (actions := fun _ => none) (phases := OwnerPhaseTransitions.empty))).mp accepted
  change false = true at impossible
  cases impossible

end Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.exposed_requests
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.surviving_requests
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.outside_does_not_supply_cell
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.admitted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.all_closing_prefixes
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.lost_original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.lost_boundary_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.SurvivingRequirementsExamples.lost_interface_rejected
