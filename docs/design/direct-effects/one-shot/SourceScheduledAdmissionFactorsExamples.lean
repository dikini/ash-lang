import SourceScheduledAdmissionFactors

/-! Independent rejection of missing interpretations and missing/consumed owner
rights. Recursive invocation checks follow the actual saved source, rather than
an operation footprint that would exclude continuation use. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)

def actions : Syntax.UsageTickets := fun owner =>
  if owner = 11 ∨ owner = 22 then some ⟨true, false⟩ else none
def phases := OwnerPhaseTransitions.available [11, 22]
def tail := Forest.live (owner := 22) .nil .nil
def saved := Forest.plain (Plan.invoke (key := ⟨22, .resume⟩)) .nil
def receiver := Forest.live (owner := 11) saved tail

def nested : Code [] (.invoke (key := ⟨22, .resume⟩)) (.spent (owner := 11) tail) :=
  .resume (.spent .hit) (.operations .nil) (.spent (.operations .nil)) (.operations .nil)

def source : Code [] (.invoke (key := ⟨11, .resume⟩)) receiver :=
  .resume .hit (.plain nested (.operations .nil)) (.operations .nil)
    (.live (.operations .nil) (.operations .nil))

theorem interpretations : source.InterpretationChecks [] := by
  simp [source, nested, Code.InterpretationChecks, Retained.InterpretationChecks,
    SourceScheduledRetainedInterfaces.Interfaces.check]

theorem continuations : source.ContinuationChecks actions phases := by
  simp [source, nested, Code.ContinuationChecks, Retained.ContinuationChecks,
    actions, phases, OwnerPhaseTransitions.available, OwnerPhaseTransitions.spend]

/-- Both successive owners are checked, including the nested restored source. -/
theorem compiled : SourceScheduledChecks.Local [] actions phases []
    (.invoke (key := ⟨11, .resume⟩)) receiver :=
  source.compile_factors (recipeLaws []) interpretations continuations

/-- Available effect interpretations do not grant the second owner permission. -/
theorem missing_nested_permission :
    ¬ source.ContinuationChecks (fun owner => if owner = 11 then some ⟨true, false⟩ else none) phases := by
  simp [source, nested, Code.ContinuationChecks, Retained.ContinuationChecks,
    phases, OwnerPhaseTransitions.available, OwnerPhaseTransitions.spend]

/-- A consumed outside owner is rejected inside the recursively restored body. -/
theorem consumed_nested_owner :
    ¬ source.ContinuationChecks actions (OwnerPhaseTransitions.spend phases 22) := by
  simp [source, nested, Code.ContinuationChecks, Retained.ContinuationChecks,
    actions, phases, OwnerPhaseTransitions.available, OwnerPhaseTransitions.spend]

/-- The current owner cannot be consumed again even when all effect checks pass. -/
theorem consumed_current_owner :
    ¬ source.ContinuationChecks actions (OwnerPhaseTransitions.spend phases 11) := by
  simp [source, nested, Code.ContinuationChecks, Retained.ContinuationChecks,
    actions, phases, OwnerPhaseTransitions.available, OwnerPhaseTransitions.spend]

private def missingEffect : Instance := .user 99 []
def unsupported : Code [] (.request (effect := missingEffect) (operation := 0)) .nil :=
  .operations [(missingEffect, 0)] .request .request

theorem no_control_obligation : unsupported.ContinuationChecks anyActions anyPhases := True.intro

theorem missing_interpretation : ¬ unsupported.InterpretationChecks [] := by
  change ¬ false = true
  decide

theorem unsupported_rejected : ¬ unsupported.Valid [] anyActions anyPhases := by
  intro ready
  exact missing_interpretation (unsupported.valid_iff_factors.mp ready).1

/-- Separate checking remains possible for a retained dormant source tree. -/
def retained : Retained [] (.plain (.invoke (key := ⟨11, .resume⟩)) .nil) receiver :=
  .plain source (.operations .nil)

theorem compiled_retained : SourceScheduledChecks.Pending [] actions phases []
    (.plain (.invoke (key := ⟨11, .resume⟩)) .nil) receiver :=
  retained.compile_factors (recipeLaws []) ⟨interpretations, rfl⟩ ⟨continuations, True.intro⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.interpretations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.continuations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.compiled
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.missing_nested_permission
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.consumed_nested_owner
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.consumed_current_owner
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.no_control_obligation
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.missing_interpretation
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.unsupported_rejected
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.AdmissionFactorsExamples.compiled_retained
