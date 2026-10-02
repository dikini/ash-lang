import CoreCallableOriginalCallableCurrent
namespace Ash.OneShot.OriginalCurrentProviderProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableOriginalCallableCurrent.Original
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy := SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The one SAME original graph witness joins executed admission, actual
acquisition/reader installation, full constructor families and CURRENT Site. -/
theorem original_initial_to_current : Nonempty Installed := installed_current

theorem original_graph_unchanged : CoreSyntax.checkShape CoreCallableCompositionalResourceRoot.graph = .ok () ∧
    CoreTranslation.translate CoreCallableCompositionalResourceRoot.graph = .ok CoreCallableCompositionalResourceRoot.rootCode :=
  CompositionalInitialAdmissionProbes.exact_graph

theorem current_actual_target (produced : Installed) :
    (CoreCallableComposedRuntimeCurrent.current reader).point.machine =
      .eval ⟨reader.p12.target.expression,.none,CoreCallableOriginalResourceCurrent.Original.cellStack⟩ :=
  produced.related.machine

theorem complete_private_points (produced : Installed) (lexical : CoreCallableReceiverRefinement.LexicalBounds)
    (call : CoreCallableReceiverRefinement.CallBounds [0]) :
    HEq (produced.origin.family.plans lexical call)
      (CoreCallablePlanSubstitution.plan reader.closedBody
        (produced.origin.first.plans (CoreCallableCapturedLambdaConstructor.restored lexical 7 (.integer 17)) call)
        7 (.integer 17)) ∧
    HEq (produced.origin.family.rows lexical call)
      (produced.origin.first.rows (CoreCallableCapturedLambdaConstructor.restored lexical 7 (.integer 17)) call) :=
  ⟨produced.origin.pointPlans lexical call,produced.origin.pointRows lexical call⟩

theorem full_lower_receipt (produced : Installed) :
    CallableContracts.Derives CoreCallableComposedResourceOrigins.Probes.Original.declarations
      (CoreCallableReturnStorageProducer.environment []) [0] .none
      (Code.lambda 10 reader.closedBody) (produced.selected.stored.value 0) := produced.origin.lowerClosed

theorem computed_runtime_environment : reader.installedEnvironment =
    .binding 12 (.closure 10 5 (.binding 9 (.handle 0) (.resource 3 0 (.binding 7 (.integer 17) .empty))))
      (.binding 9 (.handle 0) (.resource 3 0 (.binding 7 (.integer 17) .empty))) :=
  ComposedResourceRuntimeOriginProbes.exact_installed_environment

/-- A full-contract regression, not a language rejection from an erased port. -/
theorem request_row_erasure_rejected : readerContract ≠ Contract.function .unit .integer [] []
    SourceDeclarationPlans.Plan.pure Rows.pure := by
  intro impossible
  have requests := (Contract.function.inj impossible).2.2.1
  cases requests

#print axioms original_initial_to_current
#print axioms original_graph_unchanged
#print axioms current_actual_target
#print axioms complete_private_points
#print axioms full_lower_receipt
#print axioms computed_runtime_environment
#print axioms request_row_erasure_rejected
end Ash.OneShot.OriginalCurrentProviderProbes
