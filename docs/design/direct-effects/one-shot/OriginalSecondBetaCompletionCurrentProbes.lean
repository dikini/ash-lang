import CoreCallableOriginalReadCompletionCurrent
import OriginalBetaCurrentProviderProbes
namespace Ash.OneShot.OriginalSecondBetaCompletionCurrentProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableOriginalCallableCurrent.Original CoreCallableOriginalHigherCurrent.Original
open CoreCallableOriginalBetaCurrent.Original CoreCallableOriginalSecondBetaCurrent.Original
open CoreCallableOriginalReadCompletionCurrent.Original
open CoreCallableComposedRuntimeCalls.Original CoreCallableComposedRuntimeCompletion
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- One no-input SAME original Program/current/runtime witness through 35 edges. -/
theorem original_initial_to_normal_completion : Nonempty InstalledCompletion := installed_completion

theorem original_graph_unchanged : CoreSyntax.checkShape G = .ok () ∧
    CoreTranslation.translate G = .ok CoreCallableCompositionalResourceRoot.rootCode :=
  CompositionalInitialAdmissionProbes.exact_graph

theorem both_original_families (produced : InstalledCompletion) :
    produced.second.first.beta.selected.family = produced.second.first.higher.origin.family ∧
    produced.second.beta.selected.family = produced.second.first.higher.installed.origin.family :=
  ⟨produced.second.first.beta.chosen,produced.second.beta.chosen⟩

theorem full_reader_private_points (produced : InstalledCompletion) (lexical : CoreCallableReceiverRefinement.LexicalBounds)
    (call : CoreCallableReceiverRefinement.CallBounds [0]) :
    HEq (produced.second.first.higher.installed.origin.family.plans lexical call)
      (CoreCallablePlanSubstitution.plan reader.closedBody
        (produced.second.first.higher.installed.origin.first.plans
          (CoreCallableCapturedLambdaConstructor.restored lexical 7 (.integer 17)) call) 7 (.integer 17)) ∧
    HEq (produced.second.first.higher.installed.origin.family.rows lexical call)
      (produced.second.first.higher.installed.origin.first.rows
        (CoreCallableCapturedLambdaConstructor.restored lexical 7 (.integer 17)) call) :=
  ⟨produced.second.first.higher.installed.origin.pointPlans lexical call,
    produced.second.first.higher.installed.origin.pointRows lexical call⟩

theorem actual_unit_support : readerCall.world = [0] ∧ readerCall.receiver = [0] ∧ readerCall.argument = [] :=
  ⟨rfl,rfl,rfl⟩

theorem composed_current_root_transport (produced : InstalledCompletion) :
    CoreCallableRootRefinement.RootTransport CoreCallableOriginalResourceCurrent.Original.root produced.second.beta.nextRoot :=
  produced.second.first.beta.rootTransport.compose produced.second.beta.rootTransport

theorem captured_and_saved_environments (produced : InstalledCompletion) :
    e26.state.control = .evaluate 5 readerBodyEnvironment ∧
    readerBodyEnvironment = .binding 10 .unit ComposedResourceRuntimeOriginProbes.selection.acquiredEnvironment ∧
    readerBodyEnvironment ≠ selectedHigher.environment ∧
    e30.state.control = .evaluate 17 callerEnvironment :=
  ⟨produced.second.beta.callee,rfl,callee_saved_environment_differs,saved_caller.1⟩

theorem original_closing_receipts :
    CoreValueRelation.EnvCloses G [] [] readerBodyEnvironment
      (.perform (.cell (.bound 3)) 0 (.variable 9)) (.perform (.cell (.activation 0)) 0 (.resourceRef (.activation 0))) ∧
    CoreValueRelation.EnvCloses G [] [] callerEnvironment
      (.branch (.boolean true) (.variable 7) (.variable 7)) branchCode :=
  ⟨second_beta_closing,branch_closing⟩

theorem current_second_beta (produced : InstalledCompletion) :
    CoreCallableRichBetaCore.Current e25 produced.second.application.site ∧
    CoreCallableRichBetaCore.Current e26 produced.second.beta.next :=
  ⟨produced.second.application.adminRelated,produced.second.beta.related⟩

theorem current_read_and_saved_caller (produced : InstalledCompletion) :
    CoreCallableRichBetaCore.Current e29 produced.completion.readBind.read ∧
    CoreCallableRichBetaCore.Current e30 produced.completion.readBind.branch :=
  ⟨produced.completion.readBind.readRelated,produced.completion.readBind.branchRelated⟩

theorem current_chosen_and_final (produced : InstalledCompletion) :
    CoreCallableRichBetaCore.Current e33 produced.completion.chosen ∧
    CoreCallableRichBetaCore.Current e35 produced.completion.finalSite ∧ produced.completion.finalSite.bound = [] :=
  ⟨produced.completion.chosenRelated,produced.completion.finalRelated,produced.completion.finalBound⟩

theorem original35_actual (produced : InstalledCompletion) :
    CoreAllocationHistory.Steps G 35 (CoreMachine.initial G) e35.state := produced.completion.actual

theorem positive_second_beta (produced : InstalledCompletion) :
    CoreMachine.next G e25.state = .stepped e26.state ∧
    CoreCallableGeneratedChronology.Matching G e25 e26 [] [] :=
  ⟨produced.second.beta.actual,produced.second.beta.matching⟩

theorem positive_read_bind_choice_release :
    CoreUnwindRelation.Positive e28.point.machine e29.point.machine [] [] ∧
    CoreUnwindRelation.Positive e29.point.machine e30.point.machine [] [] ∧
    CoreUnwindRelation.Positive e32.point.machine e33.point.machine [] [] ∧
    CoreUnwindRelation.Positive e34.point.machine e35.point.machine [] [.resource 0] :=
  ⟨read_actual.2,bind_actual.2,selection_actual.2,release_actual.2⟩

theorem ranked_second_administration :
    CoreCallableGeneratedChronology.Matching G e21 e22 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e22 e23 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e23 e24 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e24 e25 [] [] :=
  ⟨(CoreCallableGeneratedChronology.Operation.actual (.entry innerEntry)).2,
    (CoreCallableGeneratedChronology.Operation.actual (.literal innerFunction)).2,
    (CoreCallableGeneratedChronology.Operation.actual (.swap innerSwap)).2,
    (CoreCallableGeneratedChronology.Operation.actual (.literal innerArgument)).2⟩

theorem ranked_read_branch_outer_administration :
    CoreCallableGeneratedChronology.Matching G e26 e27 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e27 e28 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e30 e31 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e31 e32 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e33 e34 [] [] :=
  ⟨(CoreCallableGeneratedChronology.Operation.actual (.entry requestEntry)).2,
    (CoreCallableGeneratedChronology.Operation.actual (.literal requestOperand)).2,
    branch_entry_actual.2,boolean_actual.2,outer_actual.2⟩

theorem request_current_administration (produced : InstalledCompletion) :
    CoreCallableRichBetaCore.Current e27 produced.second.beta.next ∧
    CoreCallableRichBetaCore.Current e28 produced.second.beta.next := ⟨⟨rfl⟩,⟨rfl⟩⟩

theorem branch_outer_current_administration (produced : InstalledCompletion) :
    CoreCallableRichBetaCore.Current e31 produced.completion.readBind.branch ∧
    CoreCallableRichBetaCore.Current e32 produced.completion.readBind.branch ∧
    CoreCallableRichBetaCore.Current e34 produced.completion.chosen := ⟨⟨rfl⟩,⟨rfl⟩,⟨rfl⟩⟩

theorem exact_read_observation : e29.state.observations = e28.state.observations ++ [.read 0 0] := read_observation

theorem exact_final_observations : e35.state.observations =
    [.entered 22,.entered 0,.entered 21,.entered 3,.entered 1,.entered 2,.acquired 21 0,
     .entered 20,.entered 6,.entered 19,.entered 10,.entered 18,.entered 13,.entered 11,
     .entered 12,.entered 9,.entered 7,.entered 8,.entered 5,.entered 4,.read 0 0,
     .entered 17,.entered 14,.entered 15,.released 0] := full_observations

theorem final_observation : CoreMachine.next G e35.state = .done (.integer 17) := final_done

theorem final_ownership (produced : InstalledCompletion) :
    e35.state.nextActivation = 1 ∧ CoreAllocationHistory.acquiredKeys e35.state.observations = [0] ∧
    CoreAllocationHistory.History e35.state ∧ e35.state.frames = [] ∧ e35.lexical = .nil := by
  have history := CoreAllocationHistory.initial_steps_history G produced.completion.actual
  exact ⟨rfl,history,history,rfl,rfl⟩

theorem historical_world_empty_receiver : CoreCallableContractExecution.actualReceiver [0] SourceDependencyCapture.Scope.nil [] = [] := rfl

theorem original_scalar_erasure_rejected (produced : InstalledCompletion) :
    produced.second.first.higher.path.stored.value 0 ≠
      CallableContracts.Contract.function [] (.storage []) (.storage []) :=
  OriginalBetaCurrentProviderProbes.scalar_domain_erasure_rejected produced.second.first

theorem wrong_saved_caller_rejected : e30.state.control ≠ .evaluate 17 readerBodyEnvironment := saved_caller.2

theorem final_not_cell_read_reply : e35.state.control ≠ e29.state.control := final_not_read_reply

theorem exact_second_private_successor (produced : InstalledCompletion) :
    produced.second.beta.next.dependencies = produced.second.beta.selected.family.dependencies [] readerCall ∧
    produced.second.beta.next.sourceDemand = produced.second.beta.selected.family.demand ∧
    HEq produced.second.beta.next.requirements produced.second.beta.selected.family.requirements ∧
    HEq produced.second.beta.next.plan produced.second.beta.selected.nextPlan ∧
    HEq produced.second.beta.next.rows produced.second.beta.selected.nextRows :=
  ⟨produced.second.beta.exactDependencies,produced.second.beta.exactDemand,
    produced.second.beta.exactRequirements,produced.second.beta.exactPlan,produced.second.beta.exactRows⟩

theorem integer_source_dependencies {plan : SourceDeclarationPlans.Plan dependencies}
    {rows : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Rows (SourcePlanSignatures.signature plan)}
    (source : CoreCallableContractAdmission.Source globals outward world allowed scope environment
      (.integer value) .integer demand requirements plan rows) : dependencies = .pure := by
  cases source
  rfl

theorem current_literal_rows (produced : InstalledCompletion) :
    produced.completion.readBind.read.dependencies = .pure ∧
    produced.completion.finalSite.dependencies = .pure :=
  ⟨integer_source_dependencies produced.completion.readBind.read.current.source,
    integer_source_dependencies produced.completion.finalSite.current.source⟩

#print axioms exact_second_private_successor
#print axioms current_literal_rows
#print axioms original_initial_to_normal_completion
#print axioms original_graph_unchanged
#print axioms both_original_families
#print axioms full_reader_private_points
#print axioms actual_unit_support
#print axioms composed_current_root_transport
#print axioms captured_and_saved_environments
#print axioms original_closing_receipts
#print axioms current_second_beta
#print axioms current_read_and_saved_caller
#print axioms current_chosen_and_final
#print axioms original35_actual
#print axioms positive_second_beta
#print axioms positive_read_bind_choice_release
#print axioms ranked_second_administration
#print axioms ranked_read_branch_outer_administration
#print axioms request_current_administration
#print axioms branch_outer_current_administration
#print axioms exact_read_observation
#print axioms exact_final_observations
#print axioms final_observation
#print axioms final_ownership
#print axioms historical_world_empty_receiver
#print axioms original_scalar_erasure_rejected
#print axioms wrong_saved_caller_rejected
#print axioms final_not_cell_read_reply
end Ash.OneShot.OriginalSecondBetaCompletionCurrentProbes
