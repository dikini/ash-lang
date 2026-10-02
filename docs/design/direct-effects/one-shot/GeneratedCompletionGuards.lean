import CoreCallableGeneratedCleanupCompletion
namespace Ash.OneShot.CoreCallableGeneratedCleanupCompletion.Guards
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation ScopedExpressions ScopedExecution
open CoreCallableGeneralHistory CoreCallableGeneratedChronology CoreRequestFrames

theorem direct_handler_not_append
    (past : GeneralHandlerPast graph owners site environment data)
    (header : CoreEffectFrames.BoundaryRel graph owners heap
      (.handlerBoundary site environment data.activation) (.handler data))
    (tail : GeneralHistory graph heap physical target) :
    ¬ HEq (GeneralHistory.handler past header tail)
      ((GeneralHistory.handler past header .nil).append tail) := by
  intro same
  have equal := eq_of_heq same
  cases equal

theorem direct_live_not_empty_append
    (past : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data)
    (header : OwnerHeader graph owners heap handler owner occurrence data)
    (saved : GeneralHistory graph heap captured capturedTarget)
    (outside : GeneralHistory graph heap physical target) :
    ¬ HEq (GeneralHistory.live (result := result) past header saved outside)
      ((GeneralHistory.nil (graph := graph) (heap := heap)).append
        (.live (result := result) past header saved outside)) := by
  intro same
  have equal := eq_of_heq same
  cases equal

noncomputable def handler_front_structural_split
    (past : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data)
    (header : OwnerHeader graph owners heap handler owner occurrence data)
    (saved : GeneralHistory graph heap captured capturedTarget)
    (outside : GeneralHistory graph heap physical target)
    (installation : GeneralHandlerPast graph frontOwners site environment frontData)
    (boundary : CoreEffectFrames.BoundaryRel graph frontOwners heap
      (.handlerBoundary site environment frontData.activation) (.handler frontData)) :
    ResumeSplit past header saved outside result
      (.handler installation boundary (.live (result := result) past header saved outside)) (.handler installation boundary .nil) :=
  .handler installation boundary _ _ .here

noncomputable def append_handler_head
    (past : GeneralHandlerPast graph owners site environment data)
    (header : CoreEffectFrames.BoundaryRel graph owners heap
      (.handlerBoundary site environment data.activation) (.handler data))
    (outside : GeneralHistory graph heap physical target) :
    HandlerHead past header ((GeneralHistory.handler past header .nil).append outside)
      ((GeneralHistory.nil (graph := graph) (heap := heap)).append outside) :=
  .append _ _ _ (.here .nil)

/-- A matching spent frame blocks the same physical search even if an older
live receipt exists farther out; structural splitting cannot bypass PassFront. -/
theorem spent_blocks_older_live (handler owner occurrence ticket olderOccurrence olderTicket : Nat)
    (captured : List CoreMachine.Frame) :
    CoreMachine.findOwner handler owner
      [.clauseBoundary handler owner occurrence ticket none,
       .clauseBoundary handler owner olderOccurrence olderTicket (some captured)] =
      .error (.consumedOwner handler owner) := by
  simp [CoreMachine.findOwner]

theorem matching_spent_front_rejected
    (past : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data)
    (header : OwnerHeader graph owners heap handler owner occurrence data)
    (outside : GeneralHistory graph heap physical target) :
    ¬ PassFront handler owner (.spent past header outside) :=
  matching_spent_blocks past header outside

#print axioms direct_handler_not_append
#print axioms direct_live_not_empty_append
#print axioms handler_front_structural_split
#print axioms append_handler_head
#print axioms spent_blocks_older_live
#print axioms matching_spent_front_rejected
#check CaptureData.clauseAt
#check CaptureData.closed
#check ResumeSplit.physical
#check ResumeSplit.lexical
#check ResumeSplit.stamps
#check HandlerHead.physical
#check HandlerHead.lexical
#check SpentHead.physical
#check SpentHead.lexical
#check FinishInput.head
#check Activation.inactive
#check Completed.from_actual_start
#check_failure ResumeSplit.equivalence
#check_failure HandlerHead.equivalence
#check_failure SpentHead.equivalence
#check_failure PassFront.matchingSpent
#check_failure Completed.chosenResult
end Ash.OneShot.CoreCallableGeneratedCleanupCompletion.Guards
