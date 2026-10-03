import CoreCallableRichAdmittedEventConsumers
import CoreCallableOriginalResourceCurrent
import ComposedResourceRuntimeOriginProbes

namespace Ash.OneShot.RichAdmittedEventInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableGeneratedChronology CoreCallableRichAdmittedCurrentOrigins
open CoreCallableRichAdmittedEventConsumers
open SourcePlannedChecks (DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]

/-- The existing private substitution Plan/Rows remain literal full outputs,
not merely public port projections. -/
theorem beta_private_indices (event : BetaEvent input site current) :
    HEq event.preserved.next.plan event.preserved.selected.nextPlan ∧
    HEq event.preserved.next.rows event.preserved.selected.nextRows ∧
    event.preserved.next.sourceDemand = event.preserved.selected.family.demand ∧
    HEq event.preserved.next.requirements event.preserved.selected.family.requirements :=
  ⟨event.preserved.exactPlan,event.preserved.exactRows,
    event.preserved.exactDemand,event.preserved.exactRequirements⟩

/-- Event bookkeeping is inherited exactly; it creates or completes no owner. -/
theorem beta_bookkeeping (event : BetaEvent input site current) :
    event.after.run.issued = current.run.issued ∧
    event.after.run.completed = current.run.completed ∧
    event.after.eventCount = current.eventCount + 1 :=
  ⟨event.issued,event.completed,event.count⟩

/-- Positive beta cannot be represented by a zero target-event increment. -/
theorem beta_not_zero_events (event : BetaEvent input site current) :
    event.after.eventCount ≠ current.eventCount := by
  have count := event.count
  omega

/-- Nonallocating beta cannot insert an extra issued owner, even if that owner
would independently be fresh. This is an exact computed-ledger negative. -/
theorem beta_no_extra_owner (event : BetaEvent input site current) (owner : Owner) :
    event.after.run.issued ≠ current.run.issued ++ [owner] := by
  intro same
  have lengths := congrArg List.length (event.issued.symm.trans same)
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega

/-- A genuinely current terminal receipt can use the actual M4 raw-trace
accounting theorem. Empty physical history is never used to derive this guard
or replace its rich GeneralHistory. -/
theorem current_terminal_accounting (current : Current program endpoint site)
    (terminal : current.run.machine = .eval ⟨value,scope,.nil⟩) :
    current.run.issued.Perm current.run.completed ∧ current.run.completed.Nodup :=
  current.past.terminal_accounting ⟨List.Perm.refl [],List.nodup_nil⟩ terminal

/-- Reuse the existing resource graph, executed static input and accepted rich
Program. This is an instance of the general adapter, not another fixture or
resource admission factory. -/
noncomputable def original_resource_seed
    (program : CoreCallableInitialAdmission.Program
      CoreCallableOriginalResourceCurrent.Original.globals (fun _ => none) []
      CoreCallableCompositionalResourceRoot.rootCode) :
    Current program
      (CoreCallableInitialChronology.initial_endpoint ComposedResourceRuntimeOriginProbes.initialInput)
      program.site :=
  initial_from_input program ComposedResourceRuntimeOriginProbes.initialInput

end
local instance : DeclarationPolicy := SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- The already executed original checker supplies the SAME accepted Program;
its resource-capable graph gate supplies the original static input. -/
theorem accepted_original_resource_seed :
    ∃ program : CoreCallableInitialAdmission.Program
      CoreCallableOriginalResourceCurrent.Original.globals (fun _ => none) []
      CoreCallableCompositionalResourceRoot.rootCode,
      CompositionalInitialAdmissionProbes.rootCheck = .ok program ∧
      Nonempty (Current program
        (CoreCallableInitialChronology.initial_endpoint ComposedResourceRuntimeOriginProbes.initialInput)
        program.site) := by
  obtain ⟨program,accepted,_⟩ := CoreCallableOriginalResourceCurrent.Original.original_program
  exact ⟨program,accepted,⟨original_resource_seed program⟩⟩

#print axioms beta_private_indices
#print axioms beta_bookkeeping
#print axioms beta_not_zero_events
#print axioms beta_no_extra_owner
#print axioms current_terminal_accounting
#print axioms original_resource_seed
#print axioms accepted_original_resource_seed
end Ash.OneShot.RichAdmittedEventInterfaces
