import SourceScheduledSourceRechecking
import SourceScheduledAdmissionFactorsExamples

/-! Compilation constructs one annotated target even when one original factor
fails. Only the independently established factor is transported; no complete
source-validity premise can be supplied in these examples. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples
open SourceDependencyCapture.Examples (resumeTable resumeDependencies)

def supplied := Forest.handler (effect := .user 99 []) (table := resumeTable)
  (families := resumeDependencies) (required := []) .nil

def noActions : Syntax.UsageTickets := fun _ => none
def emptyPhases := OwnerPhaseTransitions.empty

theorem request_change : Expression [] noActions emptyPhases unsupported supplied :=
  .reinterface .request rfl

/-- The old interpretation check fails, so full original Valid is unavailable. -/
theorem request_original_rejected : ¬ unsupported.Valid [] noActions emptyPhases :=
  unsupported_rejected

theorem request_generated_control :
    ∃ annotation : Code [] (.request (effect := .user 99 []) (operation := 0)) supplied,
      annotation.ContinuationChecks noActions emptyPhases ∧
      SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode unsupported := by
  obtain ⟨annotation, _, control, bounds⟩ :=
    request_change.compile_factors_retaining (recipeLaws []) (fun checked => checked)
  exact ⟨annotation, control no_control_obligation, bounds⟩

def deniedActions : Syntax.UsageTickets := fun owner =>
  if owner = 11 then some ⟨true, false⟩ else none

def branchSource := Code.choice source source

theorem branch_change : Expression [] deniedActions phases branchSource receiver :=
  .choice .same .same

theorem branch_original_rejected : ¬ branchSource.Valid [] deniedActions phases := by
  intro ready
  have checked := (branchSource.valid_iff_factors.mp ready).2
  exact missing_nested_permission checked.1

/-- The same compiler constructs a target whose interpretation factor is known,
although the original recursive owner-permission factor fails. -/
theorem branch_generated_interpretations :
    ∃ annotation : Code [] (.choice (.invoke (key := ⟨11, .resume⟩)) (.invoke (key := ⟨11, .resume⟩))) receiver,
      annotation.InterpretationChecks [] ∧
      SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode branchSource := by
  obtain ⟨annotation, effects, _, bounds⟩ :=
    branch_change.compile_factors_retaining (recipeLaws []) (fun checked => checked)
  exact ⟨annotation, effects ⟨interpretations, interpretations⟩, bounds⟩

def resourceSource : Code [] (.resource (fun _ => Plan.pure)) .nil :=
  .resource (fun _ _ => .operations [] .pure .pure)

theorem resource_change : Expression [] noActions emptyPhases resourceSource (.running .nil) :=
  .resource (fun _ _ => .operations rfl)

/-- A single family of output annotations carries BOTH implications; they are
not separate existential choices for effects and control. -/
theorem resource_generated :
    ∃ annotation : Code [] (.resource (fun _ => Plan.pure)) (.running .nil),
      annotation.InterpretationChecks [] ∧ annotation.ContinuationChecks noActions emptyPhases ∧
      SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode resourceSource := by
  obtain ⟨annotation, effects, control, bounds⟩ :=
    resource_change.compile_factors_retaining (recipeLaws []) (fun checked => checked)
  exact ⟨annotation, effects (fun _ _ => rfl), control (fun _ _ => True.intro), bounds⟩

def discarded : Retained [] (.plain (.request (effect := .user 99 []) (operation := 0)) .nil) .nil :=
  .plain unsupported (.operations .nil)

theorem discard_change : RetainedChange [] noActions emptyPhases discarded .nil .nil :=
  .dropPlain .same

theorem discarded_original_rejected : ¬ discarded.Valid [] noActions emptyPhases := by
  intro checked
  exact unsupported_rejected checked.1

/-- Dropping a frame is intentionally not reflective: erased invalid code need
not remain valid. The compiler still constructs its target without that premise. -/
theorem discarded_generated : ∃ annotation : Retained [] .nil .nil,
    annotation.Valid [] noActions emptyPhases ∧
    RetainedBounds discarded (SourceBoundSnapshots.Retained.ofCapability annotation) := by
  obtain ⟨annotation, _, _, bounds⟩ :=
    discard_change.compile_factors_retaining (recipeLaws []) (fun checked => checked)
  refine ⟨annotation, ?_, bounds⟩
  rw [retained_nil_eq annotation]
  rfl

end Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.request_change
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.request_original_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.request_generated_control
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.branch_change
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.branch_original_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.branch_generated_interpretations
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.resource_change
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.resource_generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.discard_change
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.discarded_original_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.FactorCompilationExamples.discarded_generated
