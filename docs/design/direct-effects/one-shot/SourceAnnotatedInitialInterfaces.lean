import SourceAnnotatedEventProgress
import SourceScheduledCapabilityAnnotations
import SourceAnnotatedStoredExecution

/-! Initial source programs derive scheduling from structural code annotations
with independently checked continuation capabilities. Closed operation
interfaces remain a specialization. Runtime assembly and universal finite safety
are reused; general declaration, completion and support admission stay separate. -/
namespace Ash.OneShot.SourceAnnotatedInitialInterfaces
open SourcePlanSignatures (signature)
open SourceAnnotatedSources (Expression)
open SourceAnnotatedExecution (Run)
open SourceScheduledSourceInterfaces (Declared)
open SourceRequestFootprints (Footprint)

/-- Construct the packet-aware initial invariant from independent structural
checks. No runtime invariant, stored continuation, or target-state check is an
input. Bounds refer to the same capability annotation used for scheduling. -/
theorem initial_atPackets_from_annotation
    [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification [])
    {plan : SourceDeclarationPlans.Plan dependencies}
    (source : SourceAnnotatedSources.Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (SourcePlanSignatures.signature plan))
    (annotation : SourceScheduledCapabilityAnnotations.Code [] plan .nil)
    (validated : annotation.Valid [] (fun _ => none) (OwnerPhaseTransitions.available []))
    (bounds : (SourcePlanBounds.ofCode annotation).Admitted)
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (agreement : operations.erase.erase.ports = DeclarationResults.signature declarations) :
    let snapshot := SourceBoundSnapshots.Snapshot.initial annotation
    demand = [] ∧ snapshot.Admitted ∧
      (SourceConsumingStoredBounds.StackBounds.nil (families := families)).Admitted [] required ∧
      SourceAnnotatedExecution.AtPackets operations declarations policy (fun _ => none) (fun _ => none)
        tables families required (fun _ => none)
        ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ snapshot.plan snapshot.forest output [] [] resultBound .nil evidence := by
  obtain ⟨empty, run⟩ := SourceAnnotatedExecution.initial_atPlan
    source (annotation.compile_with laws validated) admitted result agreement
  exact ⟨empty, ⟨bounds, .nil⟩, .nil, run.empty_packets⟩


/-- General scheduling annotations can include recursive continuation uses.
Their structural validation derives scheduling, while the remaining rich source,
completion and signature premises keep their existing independent roles. -/
theorem initial_run_from_annotation {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (annotation : SourceScheduledCapabilityAnnotations.Code [] plan .nil)
    (validated : annotation.Valid [] (fun _ => none) (OwnerPhaseTransitions.available []))
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (agreement : operations.erase.erase.ports = DeclarationResults.signature declarations) :
    demand = [] ∧ Run operations declarations policy (fun _ => none) (fun _ => none) tables families required (fun _ => none)
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ .nil output [] [] resultBound :=
  SourceAnnotatedExecution.initial_run source (annotation.compile validated) admitted result agreement

/-- The source's actual checking signature connects declaration annotations and
the finite operation interface to the same initial runtime derivation. -/
theorem initial_run {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (declared : Declared [] (signature plan))
    (interface : Footprint (signature plan) [])
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (agreement : operations.erase.erase.ports = DeclarationResults.signature declarations) :
    demand = [] ∧ Run operations declarations policy (fun _ => none) (fun _ => none) tables families required (fun _ => none)
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ .nil output [] [] resultBound :=
  initial_run_from_annotation source (.operations [] interface declared) rfl admitted result agreement

/-- Universal finite execution is reused unchanged with general initial source
scheduling annotations. No intermediate or final invariant is an input. -/
theorem finite_progress_from_annotation {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (annotation : SourceScheduledCapabilityAnnotations.Code [] plan .nil)
    (validated : annotation.Valid [] (fun _ => none) (OwnerPhaseTransitions.available []))
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (agreement : operations.erase.erase.ports = DeclarationResults.signature declarations)
    (trace : SourceAnnotatedExecutionEvents.Steps operations.erase.erase.ports output.erase.erase.port count
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ after) :
    (after.execution.configuration.expression.erase.IsValue ∧ after.execution.configuration.stack = .nil) ∨
    ∃ next, SourceAnnotatedExecutionEvents.Step operations.erase.erase.ports output.erase.erase.port after next := by
  have run := (initial_run_from_annotation (tables := fun _ => []) (families := fun _ => []) (required := fun _ => [])
    source annotation validated admitted result agreement).2
  exact SourceAnnotatedExecutionEvents.finite_progress trace run

theorem terminal_accounting_from_annotation {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (annotation : SourceScheduledCapabilityAnnotations.Code [] plan .nil)
    (validated : annotation.Valid [] (fun _ => none) (OwnerPhaseTransitions.available []))
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (agreement : operations.erase.erase.ports = DeclarationResults.signature declarations)
    (trace : SourceAnnotatedExecutionEvents.Steps operations.erase.erase.ports output.erase.erase.port count
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ after)
    (terminal : ScopedPortProgress.Terminal after.execution.configuration.erase) :
    after.execution.issued.Perm after.execution.completed ∧ after.execution.completed.Nodup := by
  have run := (initial_run_from_annotation (tables := fun _ => []) (families := fun _ => []) (required := fun _ => [])
    source annotation validated admitted result agreement).2
  exact SourceAnnotatedExecutionEvents.terminal_accounting trace run terminal

/-- Any supplied finite trace from this source interface ends terminally or can
continue. Only the initial structural annotations and finite checks are inputs;
there is no initial, intermediate or final Run premise. -/
theorem finite_progress {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (declared : Declared [] (signature plan))
    (interface : Footprint (signature plan) [])
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (agreement : operations.erase.erase.ports = DeclarationResults.signature declarations)
    (trace : SourceAnnotatedExecutionEvents.Steps operations.erase.erase.ports output.erase.erase.port count
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ after) :
    (after.execution.configuration.expression.erase.IsValue ∧ after.execution.configuration.stack = .nil) ∨
    ∃ next, SourceAnnotatedExecutionEvents.Step operations.erase.erase.ports output.erase.erase.port after next :=
  finite_progress_from_annotation source (.operations [] interface declared) rfl admitted result agreement trace

/-- The same source-derived initial state supplies exact-once owner discharge
at every terminal endpoint of any supplied trace. -/
theorem terminal_accounting {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (declared : Declared [] (signature plan))
    (interface : Footprint (signature plan) [])
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (agreement : operations.erase.erase.ports = DeclarationResults.signature declarations)
    (trace : SourceAnnotatedExecutionEvents.Steps operations.erase.erase.ports output.erase.erase.port count
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ after)
    (terminal : ScopedPortProgress.Terminal after.execution.configuration.erase) :
    after.execution.issued.Perm after.execution.completed ∧ after.execution.completed.Nodup :=
  terminal_accounting_from_annotation source (.operations [] interface declared) rfl admitted result agreement trace terminal

end Ash.OneShot.SourceAnnotatedInitialInterfaces

#print axioms Ash.OneShot.SourceAnnotatedInitialInterfaces.initial_run
#print axioms Ash.OneShot.SourceAnnotatedInitialInterfaces.initial_run_from_annotation
#print axioms Ash.OneShot.SourceAnnotatedInitialInterfaces.finite_progress_from_annotation
#print axioms Ash.OneShot.SourceAnnotatedInitialInterfaces.terminal_accounting_from_annotation
#print axioms Ash.OneShot.SourceAnnotatedInitialInterfaces.finite_progress
#print axioms Ash.OneShot.SourceAnnotatedInitialInterfaces.terminal_accounting

#print axioms Ash.OneShot.SourceAnnotatedInitialInterfaces.initial_atPackets_from_annotation
