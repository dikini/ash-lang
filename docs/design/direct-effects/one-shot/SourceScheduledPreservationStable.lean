import SourceScheduledPreservationState

/-! Preservation for transitions with determined successor metadata. The
operational relation carries no source, ownership or successor-admission premise;
the common invariant supplies these through the established transition endpoints. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyFrames (unwindStore)

namespace Stable

inductive Step (operations : SourcePlannedTyping.Operations) : Snapshot operations → Snapshot operations → Prop where
  | computation {snapshot : Snapshot operations} (ready : RecursiveExpressions.Ready before.expression)
      (step : RawStep before after [] []) :
      Step operations {snapshot with run := ⟨⟨.eval before, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval after, issued, completed⟩, actions⟩}
  | plug {snapshot : Snapshot operations} (closed : ClosedValue value) :
      Step operations {snapshot with run := ⟨⟨.eval ⟨value, runtimeScope, .push (.plain plain) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨plain.context.plug value, plain.scope, tail⟩, issued, completed⟩, actions⟩}
  | start_normal_cleanup {snapshot : Snapshot operations} (closed : ClosedValue value) :
      Step operations {snapshot with run := ⟨⟨.eval ⟨value, runtimeScope, .push (.armed action) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩, issued, completed⟩, actions⟩}
  | finish_normal_cleanup {snapshot : Snapshot operations}  :
      Step operations {snapshot with run := ⟨⟨.eval ⟨.unit, runtimeScope, .push (.running action value closed) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨value, action.scope, tail⟩, issued, .cleanup action.identity :: completed⟩, actions⟩}
  | leave_handler {snapshot : Snapshot operations} (closed : ClosedValue value) :
      Step operations {snapshot with run := ⟨⟨.eval ⟨value, runtimeScope, .push (.handler handler) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨value, handler.scope, tail⟩, issued, completed⟩, actions⟩}
  | leave_clause {snapshot : Snapshot operations} (closed : ClosedValue value) :
      Step operations {snapshot with run := ⟨⟨.eval ⟨value, runtimeScope, .spent owner answer caller tail⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨value, caller, tail⟩, issued, completed⟩, actions⟩}
  | close_value {snapshot : Snapshot operations} (closed : ClosedValue value) :
      Step operations {snapshot with run := ⟨⟨.eval ⟨value, runtimeScope, .push (.closing identity caller) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨.unit, caller, tail⟩, issued, .close identity :: completed⟩, actions⟩}
  | finish_close_unit {snapshot : Snapshot operations}  :
      Step operations {snapshot with run := ⟨⟨.eval ⟨.unit, runtimeScope, .push (.closing identity caller) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨.unit, caller, tail⟩, issued, .close identity :: completed⟩, actions⟩}
  | retire_value {snapshot : Snapshot operations} (closed : ClosedValue value) :
      Step operations {snapshot with run := ⟨⟨.eval ⟨value, runtimeScope, .push (.retiring owner) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with resumes := RecursiveTransport.removeOwner owner snapshot.resumes, disposals := RecursiveTransport.removeOwner owner snapshot.disposals, annotatedStore := RecursiveTransport.removeOwner owner snapshot.annotatedStore, run := ⟨⟨.eval ⟨value, runtimeScope, tail⟩, issued, .ticket owner :: completed⟩, actions⟩}
  | retire {snapshot : Snapshot operations}  :
      Step operations {snapshot with run := ⟨⟨.eval ⟨.unit, runtimeScope, .push (.retiring owner) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with resumes := RecursiveTransport.removeOwner owner snapshot.resumes, disposals := RecursiveTransport.removeOwner owner snapshot.disposals, annotatedStore := RecursiveTransport.removeOwner owner snapshot.annotatedStore, run := ⟨⟨.eval ⟨.unit, runtimeScope, tail⟩, issued, .ticket owner :: completed⟩, actions⟩}
  | read_cell {snapshot : Snapshot operations} (builtin : operations.erase.erase.ports (.cell identity) 0 = some (.reference identity, .integer))
      (selected : CellUpdate identity payload payload beforeStack afterStack) :
      Step operations {snapshot with run := ⟨⟨.eval ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), runtimeScope, beforeStack⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨.integer payload, runtimeScope, afterStack⟩, issued, completed⟩, actions⟩}
  | write_cell {snapshot : Snapshot operations} (builtin : operations.erase.erase.ports (.cell identity) 1 = some (.product (.reference identity) .integer, .unit))
      (selected : CellUpdate identity old new beforeStack afterStack) :
      Step operations {snapshot with run := ⟨⟨.eval ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer new)), runtimeScope, beforeStack⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨.unit, runtimeScope, afterStack⟩, issued, completed⟩, actions⟩}
  | start_unwind_cleanup {snapshot : Snapshot operations}  :
      Step operations {snapshot with run := ⟨⟨.unwind runtimeScope (.push (.armed action) tail), issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨.app action.action .unit, .none, .push (.unwinding action) tail⟩, issued, completed⟩, actions⟩}
  | finish_unwind_cleanup {snapshot : Snapshot operations}  :
      Step operations {snapshot with run := ⟨⟨.eval ⟨.unit, runtimeScope, .push (.unwinding action) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.unwind action.scope tail, issued, .cleanup action.identity :: completed⟩, actions⟩}
  | finish_unwind_close {snapshot : Snapshot operations}  :
      Step operations {snapshot with run := ⟨⟨.unwind runtimeScope (.push (.closing identity caller) tail), issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨.unit, caller, tail⟩, issued, .close identity :: completed⟩, actions⟩}
  | leave_resource {snapshot : Snapshot operations} (closed : ClosedValue value) :
      Step operations {snapshot with run := ⟨⟨.eval ⟨value, runtimeScope, .push (.cell identity payload caller answer) tail⟩, issued, completed⟩, actions⟩}
        {snapshot with run := ⟨⟨.eval ⟨value, caller, tail⟩, issued, .resource identity :: completed⟩, actions⟩}
  | advance {snapshot : Snapshot operations} (step : LexicalUnwind.Advance beforeStack afterStack discharged) :
      Step operations {snapshot with run := ⟨⟨.unwind runtimeScope beforeStack, issued, completed⟩, actions⟩}
        {snapshot with resumes := unwindStore beforeStack snapshot.resumes, disposals := unwindStore beforeStack snapshot.disposals, annotatedStore := unwindStore beforeStack snapshot.annotatedStore, run := ⟨⟨.unwind runtimeScope afterStack, issued, discharged ++ completed⟩, actions⟩}

private theorem no_allocation_event
    (state : Valid policy outward ambient budget ports emptyRows output outputRows before)
    (transition : LexicalUnwind.Transition before.run.execution.machine next [] discharged) :
    LexicalUnwind.Event before.run.execution
      ⟨next, before.run.execution.issued, discharged ++ before.run.execution.completed⟩ := by
  simpa only [List.append_nil] using
    (LexicalUnwind.Event.step (before := before.run.execution) transition
      (by simpa only [List.append_nil, LexicalUnwind.RunState.erase] using state.ledger.2))

/-- Every stable operational step preserves the complete common state and is
an event of the existing lexical machine. -/
theorem Step.preserve
    (step : Step operations before after)
    (state : Valid policy outward ambient budget ports emptyRows output outputRows before) :
    LexicalUnwind.Event before.run.execution after.run.execution ∧
      Valid policy outward ambient budget ports emptyRows output outputRows after := by
  cases step with
  | computation ready step =>
      exact state.computation ready step
  | plug closed =>
      exact state.plug closed
  | start_normal_cleanup closed =>
      exact state.start_normal_cleanup closed
  | finish_normal_cleanup  =>
      exact state.finish_normal_cleanup
  | leave_handler closed =>
      exact state.leave_handler closed
  | leave_clause closed =>
      exact state.leave_clause closed
  | close_value closed =>
      exact state.close_value closed
  | finish_close_unit  =>
      exact state.finish_close_unit.2
  | retire_value closed =>
      exact state.retire_value closed
  | retire  =>
      exact state.retire.2
  | read_cell builtin selected =>
      refine ⟨?_, state.read_cell builtin selected⟩
      simpa only [List.nil_append] using
        no_allocation_event state (.evaluate (.readCell _ _ _ _ _ selected) trivial)
  | write_cell builtin selected =>
      refine ⟨?_, state.write_cell builtin selected⟩
      simpa only [List.nil_append] using
        no_allocation_event state (.evaluate (.writeCell _ _ _ _ _ _ selected) trivial)
  | start_unwind_cleanup  =>
      exact state.start_unwind_cleanup
  | finish_unwind_cleanup  =>
      exact state.finish_unwind_cleanup
  | finish_unwind_close  =>
      exact state.finish_unwind_close
  | leave_resource closed =>
      exact state.leave_resource closed
  | advance step =>
      refine ⟨?_, state.advance step⟩
      exact no_allocation_event state (.advance step)

end Stable
end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Stable.Step.preserve
