import CoreCallableComposedRuntimeCompletion
import ComposedResourceRuntimeCallProbes
namespace Ash.OneShot.ComposedResourceRuntimeCompletionProbes
open ScopedExpressions ScopedExecution CoreMachine
open CoreCallableComposedRuntimeCompletion CoreCallableComposedRuntimeCalls.Original
open CoreCallableComposedResourceOrigins CoreCallableComposedResourceOrigins.Probes
open CoreCallableComposedCapturedHandle CoreCallableComposedRuntimeBindings ComposedResourceRuntimeOriginProbes
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The original executed graph, opening and constructor transcript continues
through the same checked call and normal resource release. -/
theorem connected_original_completion :
    ∃ resource : Opened,
    ∃ staticReader : ReaderPath resource,
    ∃ readerReceipt : PLift (Current staticReader.path selection.s8.nextActivation (by simp)),
    ∃ handleReceipt : PLift (CapturedHandle staticReader.path selection.s8.nextActivation (by simp)),
    ∃ staticHigher : HigherPath resource,
    ∃ higherReceipt : PLift (Current staticHigher.path selection.s8.nextActivation (by simp)),
    ∃ checked : CheckedCall staticReader readerReceipt.down handleReceipt.down staticHigher higherReceipt.down,
      produce_graph_prefix CoreCallableCompositionalResourceRoot.graph originalPath
        Original.api Original.policy Original.declarations [] [] [] .none [] = .ok originalGraphPrefix ∧
      produce_opened originalPrefix Original.annotation Original.body Original.initialRecipe Original.bodyRecipe [] [] = .ok resource ∧
      produce_current staticReader.path selection.s8.nextActivation (by simp) = some readerReceipt ∧
      capture_handle staticReader.path selection.s8.nextActivation (by simp) = .ok handleReceipt ∧
      produce_current staticHigher.path selection.s8.nextActivation (by simp) = some higherReceipt ∧
      check_call staticReader readerReceipt.down handleReceipt.down staticHigher higherReceipt.down = .ok checked ∧
      finish_checked staticReader readerReceipt.down handleReceipt.down staticHigher higherReceipt.down =
        .ok ⟨checked,complete checked⟩ ∧
      (complete checked).retained = checked ∧
      (complete checked).calls = checked_call_actual checked ∧
      staticHigher.stored = higherTree ∧
      CoreAllocationHistory.Steps G 35 (CoreMachine.initial G) e35.state ∧
      CoreMachine.next G e35.state = .done (.integer 17) := by
  obtain ⟨resource,staticReader,readerReceipt,handleReceipt,staticHigher,higherReceipt,checked,
    graphAccepted,openedAccepted,readerAccepted,handleAccepted,higherAccepted,accepted,
    _outer,_inner,_domain,_steps,_target,_environment,_reply⟩ :=
    ComposedResourceRuntimeCallProbes.connected_original_read
  refine ⟨resource,staticReader,readerReceipt,handleReceipt,staticHigher,higherReceipt,checked,
    graphAccepted,openedAccepted,readerAccepted,handleAccepted,higherAccepted,accepted,?_,rfl,rfl,
    higher_storage_domain staticHigher,initial_to_done,final_done⟩
  unfold finish_checked
  rw [accepted]
  rfl

theorem exact_full_observations : e35.state.observations =
    [.entered 22,.entered 0,.entered 21,.entered 3,.entered 1,.entered 2,.acquired 21 0,
     .entered 20,.entered 6,.entered 19,.entered 10,.entered 18,.entered 13,.entered 11,
     .entered 12,.entered 9,.entered 7,.entered 8,.entered 5,.entered 4,.read 0 0,
     .entered 17,.entered 14,.entered 15,.released 0] := full_observations

theorem release_matching : CoreUnwindRelation.Trace e29.point.machine e35.point.machine [] [.resource 0] := remaining_target

theorem final_issuance_unchanged : e35.state.nextActivation = 1 ∧
    CoreAllocationHistory.acquiredKeys e35.state.observations = [0] ∧
    CoreAllocationHistory.History e35.state := final_ledger

theorem empty_final_history : CoreGeneralStack.GeneralSegment G e35.state.heap [] .nil := e35.history.related

theorem intermediate_reply_is_not_final : e35.state.control ≠ e29.state.control := final_not_read_reply

theorem saved_continuation_is_not_callee : e30.state.control = .evaluate 17 callerEnvironment ∧
    e30.state.control ≠ .evaluate 17 readerBodyEnvironment := saved_caller

theorem whole_initial_matching : ∃ created discharged,
    CoreUnwindRelation.Trace (.eval selection.p0.target) e35.point.machine created
      (.resource 0 :: discharged) := initial_target_done

#print axioms connected_original_completion
#print axioms exact_full_observations
#print axioms release_matching
#print axioms final_issuance_unchanged
#print axioms empty_final_history
#print axioms intermediate_reply_is_not_final
#print axioms saved_continuation_is_not_callee
#print axioms whole_initial_matching
end Ash.OneShot.ComposedResourceRuntimeCompletionProbes
