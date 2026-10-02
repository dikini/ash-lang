import CoreCallableComposedRuntimeCalls
namespace Ash.OneShot.ComposedResourceRuntimeCallProbes
open ScopedExpressions ScopedExecution CoreSyntax CoreMachine CoreValueRelation
open CoreCallableComposedRuntimeCalls CoreCallableComposedRuntimeCalls.Original
open CoreCallableComposedRuntimeBindings ComposedResourceRuntimeOriginProbes CoreCallableGeneratedChronology
open CoreCallableComposedResourceOrigins CoreCallableComposedCapturedHandle
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- One executed original transcript supplies both constructor families used
by the actual beta inputs, followed by the same original call/read endpoint. -/
theorem connected_original_read :
    ∃ resource : CoreCallableComposedResourceOrigins.Probes.Opened,
    ∃ staticReader : CoreCallableComposedResourceOrigins.Probes.ReaderPath resource,
    ∃ readerReceipt : PLift (Current staticReader.path selection.s8.nextActivation (by simp)),
    ∃ handleReceipt : PLift (CapturedHandle staticReader.path selection.s8.nextActivation (by simp)),
    ∃ staticHigher : CoreCallableComposedResourceOrigins.Probes.HigherPath resource,
    ∃ higherReceipt : PLift (Current staticHigher.path selection.s8.nextActivation (by simp)),
    ∃ checked : CheckedCall staticReader readerReceipt.down handleReceipt.down staticHigher higherReceipt.down,
      produce_graph_prefix CoreCallableCompositionalResourceRoot.graph
        CoreCallableComposedResourceOrigins.Probes.originalPath
        CoreCallableComposedResourceOrigins.Probes.Original.api
        CoreCallableComposedResourceOrigins.Probes.Original.policy
        CoreCallableComposedResourceOrigins.Probes.Original.declarations [] [] [] .none [] =
        .ok CoreCallableComposedResourceOrigins.Probes.originalGraphPrefix ∧
      produce_opened CoreCallableComposedResourceOrigins.Probes.originalPrefix
        CoreCallableComposedResourceOrigins.Probes.Original.annotation
        CoreCallableComposedResourceOrigins.Probes.Original.body
        CoreCallableComposedResourceOrigins.Probes.Original.initialRecipe
        CoreCallableComposedResourceOrigins.Probes.Original.bodyRecipe [] [] = .ok resource ∧
      produce_current staticReader.path selection.s8.nextActivation (by simp) = some readerReceipt ∧
      capture_handle staticReader.path selection.s8.nextActivation (by simp) = .ok handleReceipt ∧
      produce_current staticHigher.path selection.s8.nextActivation (by simp) = some higherReceipt ∧
      check_call staticReader readerReceipt.down handleReceipt.down staticHigher higherReceipt.down = .ok checked ∧
      (beta_result checked.outer).after = e21 ∧ (beta_result checked.inner).after = e26 ∧
      staticHigher.stored.value 0 = .function [] (.function [0,0] (.storage []) (.storage [])) (.storage []) ∧
      CoreAllocationHistory.Steps G 29 (CoreMachine.initial G) e29.state ∧
      CoreUnwindRelation.Trace e15.point.machine e29.point.machine [] [] ∧
      e26.state.control = .evaluate 5 readerBodyEnvironment ∧
      e29.state.control = .returned (.integer 0) := by
  obtain ⟨resource,staticReader,readerReceipt,handleReceipt,_oldJoined,
    graphAccepted,openedAccepted,readerAccepted,handleAccepted,_pairedAccepted,_steps,_lookup⟩ := original_runtime_join
  obtain ⟨staticHigher,_⟩ := CoreCallableComposedResourceOrigins.Probes.connected_higher resource
  obtain ⟨higherReceipt,higherAccepted⟩ := CoreCallableComposedResourceOrigins.Probes.higher_current_all_fresh staticHigher selection.s8.nextActivation
  obtain ⟨checked,accepted⟩ := check_call_executed staticReader readerReceipt.down handleReceipt.down staticHigher higherReceipt.down
  exact ⟨resource,staticReader,readerReceipt,handleReceipt,staticHigher,higherReceipt,checked,
    graphAccepted,openedAccepted,readerAccepted,handleAccepted,higherAccepted,accepted,
    (checked_beta_endpoints checked).1,(checked_beta_endpoints checked).2,
    retained_lower_domain staticHigher,initial_to_read,call_target_trace,second_beta_environment,read_result.1⟩

theorem exact_ready_higher_prefix : CoreAllocationHistory.Steps G 15 (CoreMachine.initial G) e15.state := initial_to_higher

noncomputable def named_suffix : CoreCallableInitialChronology.OperationSegment e15 e28 13 [] [] := calls_segment

theorem correct_saved_callee_environment : e26.state.control =
    .evaluate 5 (.binding 10 .unit (.binding 9 (.handle 0) (.resource 3 0 (.binding 7 (.integer 17) .empty)))) :=
  second_beta_environment

theorem wrong_caller_environment_rejected :
    e26.state.control ≠ .evaluate 5 selectedHigher.environment := by
  rw [second_beta_environment]
  intro impossible
  exact callee_saved_environment_differs (CoreMachine.Control.evaluate.inj impossible).2

theorem full_reader_argument_metadata : selectedHigher.plain.input =
    .function (.function .unit .integer [.cell 0] [0,0]) .integer [.cell 0] [] := rfl

theorem read_reply_positive : CoreMachine.next G e28.state = .stepped e29.state ∧
    CoreUnwindRelation.Positive e28.point.machine e29.point.machine [] [] := read_actual

theorem actual_read_observation : e29.state.observations = e28.state.observations ++ [.read 0 0] := read_observation

theorem retained_current_history : CoreGeneralStack.GeneralSegment G e29.state.heap e29.physical e29.lexical := read_history

theorem original_activation_ledger : selection.s8.nextActivation = 0 ∧ e29.state.nextActivation = 1 ∧
    CoreAllocationHistory.History e29.state := original_owner_ledger

/-- A nearest erased-domain shadow cannot satisfy the original higher slot's
entire reader function domain. Older rich storage slots remain in the map. -/
theorem shadowed_reader_domain_rejected :
    CoreCallableCompositionalResourceStorage.check CoreCallableComposedResourceOrigins.Probes.Original.api 3 []
      ((13,higherTree)::(12,.storage [])::CoreCallableComposedResourceOrigins.Probes.higherStorage)
      (.app (.variable 13) (.variable 12)) (.app .variable .variable) = none := by
  simp [CoreCallableCompositionalResourceStorage.check,CoreCallableCompositionalResourceStorage.lookup,
    CoreCallableCompositionalResourceStorage.Tree.valid,CoreCallableCompositionalResourceStorage.Atom.valid,
    higherTree,CoreCallableComposedResourceOrigins.Probes.readerResult]

theorem same_initial_target_matching : ∃ created discharged,
    CoreUnwindRelation.Trace (.eval selection.p0.target) e29.point.machine created discharged := initial_target_trace

#print axioms same_initial_target_matching

#print axioms connected_original_read
#print axioms exact_ready_higher_prefix
#print axioms named_suffix
#print axioms correct_saved_callee_environment
#print axioms wrong_caller_environment_rejected
#print axioms full_reader_argument_metadata
#print axioms read_reply_positive
#print axioms actual_read_observation
#print axioms retained_current_history
#print axioms original_activation_ledger
#print axioms shadowed_reader_domain_rejected
end Ash.OneShot.ComposedResourceRuntimeCallProbes
