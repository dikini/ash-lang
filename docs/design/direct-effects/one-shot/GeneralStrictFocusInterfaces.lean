import CoreCallableStrictFocusConsumers
namespace Ash.OneShot.GeneralStrictFocusInterfaces
open CoreSyntax CoreMachine CoreValueRelation CoreStrictStack CoreTranslationFuel
open ScopedExpressions ScopedExecution CoreCallableGeneratedChronology
open CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers

/-- The middle is actual named execution; literal retains the episode's
original installation index, and right transition consumes that SAME receipt. -/
theorem literal_then_right {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : Middle pastRun ready current count created discharged)
    (literal : LiteralInput current)
    (returned : ReturnedReady ready (pastRun.receipt ready) (literal_result literal).after) :
    CoreAllocationHistory.Steps graph (count+2) original.state (right_after returned).state ∧
    CoreUnwindRelation.Trace original.point.machine (right_after returned).point.machine created discharged := by
  have middle := Middle.covered run (Operation.literal literal)
  have completed := complete_episode middle returned
  simpa using completed

theorem literal_preserves_physical_installation (literal : LiteralInput current) :
    (literal_result literal).after.physical = current.physical ∧
    (literal_result literal).after.lexical = current.lexical ∧
    HEq (literal_result literal).after.history current.history := ⟨rfl,rfl,HEq.rfl⟩

theorem restores_saved_map_and_scope {kind : PairApplication} {original current : Endpoint graph}
    {ready : EntryReady kind original} {receipt : EntryReceipt ready} (returned : ReturnedReady ready receipt current) :
    (right_after returned).owners = original.owners ∧
    (right_after returned).focus.scope = ready.plain.scope ∧
    (right_after returned).physical = kind.rightFrame returned.value :: original.physical :=
  ⟨rfl,returned.sameScope,rfl⟩

theorem returned_entry_control_excluded {kind : PairApplication} {current : Endpoint graph}
    (ready : EntryReady kind current) (actual : current.state.control = .returned value) : False := by
  have impossible := ready.control
  rw [actual] at impossible
  cases impossible

theorem value_entry_child_excluded {kind : PairApplication} {current : Endpoint graph}
    (ready : EntryReady kind current) (value : ready.leftCode.IsValue) : False := ready.notValue value

theorem value_saved_right_excluded {kind : PairApplication} {original current : Endpoint graph}
    {ready : EntryReady kind original} {receipt : EntryReceipt ready}
    (returned : ReturnedReady ready receipt current) (value : ready.rightCode.IsValue) : False := returned.notValue value

#print axioms literal_then_right
#print axioms literal_preserves_physical_installation
#print axioms restores_saved_map_and_scope
#print axioms returned_entry_control_excluded
#print axioms value_entry_child_excluded
#print axioms value_saved_right_excluded
end Ash.OneShot.GeneralStrictFocusInterfaces
