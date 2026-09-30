import SourceScheduledSourceJoin
import SourceScheduledRetainedRecompositionExamples
import SourceScheduledAdmissionFactorsExamples

/-! One source-only join retains rich callback/dormant metadata and preserves
failure of either input check. Construction never waits for those checks. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceScheduledSourceRechecking.RecompositionExamples

/-- The actual join exists before any permission or interpretation is supplied. -/
def joined := frontSource.joinSource suffixSource

theorem exact_metadata : ofCapability joined =
    (ofCapability frontSource).append (ofCapability suffixSource) :=
  frontSource.joinSource_bounds suffixSource

theorem valid : joined.Valid [] actions phases :=
  (frontSource.joinSource_valid suffixSource).mpr ⟨front_valid, suffix_valid⟩

theorem interpretation_equivalence : joined.InterpretationChecks outward ↔
    frontSource.InterpretationChecks outward ∧ suffixSource.InterpretationChecks outward :=
  frontSource.joinSource_interpretations suffixSource

theorem continuation_equivalence : joined.ContinuationChecks permissions states ↔
    frontSource.ContinuationChecks permissions states ∧ suffixSource.ContinuationChecks permissions states :=
  frontSource.joinSource_continuations suffixSource

/-- A compact prefix leaves the suffix's explicit handler metadata intact. -/
theorem compact_prefix_metadata : ofCapability (operationSource.joinSource suffixSource) =
    (ofCapability operationSource).append (ofCapability suffixSource) :=
  operationSource.joinSource_bounds suffixSource

private def purePrefix := Forest.plain Plan.pure .nil
private def pureInterfaces : SourceScheduledRetainedInterfaces.Interfaces [] purePrefix :=
  .plain .nil [] .pure .pure .nil

def ownerPrefix : Retained [] purePrefix
    ((Forest.plain (Plan.invoke (key := ⟨11, .resume⟩)) .nil).append AdmissionFactorsExamples.receiver) :=
  .operations pureInterfaces

def ownerJoin := ownerPrefix.joinSource AdmissionFactorsExamples.retained

/-- The same joined annotation checks both nested owner uses. -/
theorem owner_join_valid : ownerJoin.Valid [] AdmissionFactorsExamples.actions AdmissionFactorsExamples.phases := by
  apply (ownerPrefix.joinSource_valid AdmissionFactorsExamples.retained).mpr
  constructor
  · rfl
  · exact AdmissionFactorsExamples.retained.valid_iff_factors.mpr
      ⟨⟨AdmissionFactorsExamples.interpretations, rfl⟩, ⟨AdmissionFactorsExamples.continuations, True.intro⟩⟩

/-- Joining cannot manufacture permission for an invocation in the suffix. -/
theorem missing_nested_permission : ¬ ownerJoin.ContinuationChecks
    (fun owner => if owner = 11 then some ⟨true, false⟩ else none) AdmissionFactorsExamples.phases := by
  intro checked
  have tailChecked := (ownerPrefix.joinSource_continuations AdmissionFactorsExamples.retained).mp checked
  exact AdmissionFactorsExamples.missing_nested_permission tailChecked.2.1

/-- Joining cannot reset an already consumed owner in a recursive saved body. -/
theorem consumed_nested_owner : ¬ ownerJoin.ContinuationChecks AdmissionFactorsExamples.actions
    (OwnerPhaseTransitions.spend AdmissionFactorsExamples.phases 22) := by
  intro checked
  have tailChecked := (ownerPrefix.joinSource_continuations AdmissionFactorsExamples.retained).mp checked
  exact AdmissionFactorsExamples.consumed_nested_owner tailChecked.2.1

private def unsupportedEffect : Instance := .user 99 []
def unsupportedTail : Retained [] (.plain (.request (effect := unsupportedEffect) (operation := 0)) .nil) .nil :=
  .plain (.operations [(unsupportedEffect, 0)] .request .request) (.operations .nil)
def unsupportedPrefix : Retained [] purePrefix
    ((Forest.plain (.request (effect := unsupportedEffect) (operation := 0)) .nil).append .nil) :=
  .operations pureInterfaces
def unsupportedJoin := unsupportedPrefix.joinSource unsupportedTail

/-- The annotation is constructible even when its interpretation check fails. -/
theorem unsupported_interpretation : ¬ unsupportedJoin.InterpretationChecks [] := by
  intro checked
  have tailChecked := (unsupportedPrefix.joinSource_interpretations unsupportedTail).mp checked
  have impossible := tailChecked.2.1
  change false = true at impossible
  cases impossible

end Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples.exact_metadata
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples.valid
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples.interpretation_equivalence
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples.continuation_equivalence
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples.compact_prefix_metadata
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples.owner_join_valid
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples.missing_nested_permission
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples.consumed_nested_owner
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.SourceJoinExamples.unsupported_interpretation
