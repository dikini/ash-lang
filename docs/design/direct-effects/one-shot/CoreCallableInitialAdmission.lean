import CoreCallableRestoredResume
import ScopedPortProgress

/-! Initial admission for the rich common-contract source. Static source and
authentication construct the actual empty-stack Site. Its port projection
supplies the existing initial joint invariant and first-step progress theorem;
no legacy port-bounded Auth or desired successor is required. First-step joint
progress does not assert rich whole-state preservation or M4 finite prefixes. -/

namespace Ash.OneShot.CoreCallableInitialAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies RowAnnotation)
open RecursiveRequirements (Requirements Checked)
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission (Globals Source Authenticated Supported)
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableContractExecution (Site actualReceiver lowerOperations lowerEnvironment)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)

section
variable [DeclarationPolicy]

/-- All facets describe the same closed initial syntax and literal private plan.
One-shot usage is ordinary finite static evidence, not a future execution.
Initial resource support is empty; resources introduced inside the program are
checked by its existing source, code and accounting constructors. -/
structure Program (globals : Globals) (actions : Syntax.UsageTickets)
    (budget : Footprint) (expression : Code) where
  result : Contract
  dependencies : Dependencies
  plan : Plan dependencies
  rows : Rows (signature plan)
  demand : List Nat
  requirements : Requirements demand
  source : Source globals [] [] [] .none Environment.empty
    expression result demand requirements plan rows
  authenticated : Authenticated globals.registry [] source ([] : LexicalBounds) []
  support : SourceSupport.Bounds ScopedPorts.Support.empty expression.dependencies []
  usage : Uses globals.policy .none .available expression .available
  certificate : SourceAdmission.Code [] actions budget
    (OwnerPhaseTransitions.available []) [] [] rows Context.nil
  certificateChecked : InstallationSupport.CodeChecked [] [] certificate
  rootDemand : List Nat
  root : Requirements rootDemand
  accounting : Accounting.Run [] [] rows Context.nil root
  annotated : Requirements rootDemand
  annotation : RowAnnotation root annotated
  row : Footprint
  checked : Checked [] [] (OwnerPhaseTransitions.available [])
    (annotateDisposals annotated) row
  bounded : row ⊆ budget

/-- The rich initial invariant is constructed from static evidence. The nil
pending, retained and retained-checking proofs are the existing constructors. -/
def Program.site (program : Program globals actions budget expression) :
    Site globals [] [] [] actions (OwnerPhaseTransitions.available []) budget [] []
      expression .none .nil program.result program.result Context.nil program.root :=
  { sourceDemand := program.demand
    requirements := program.requirements
    dependencies := program.dependencies
    plan := program.plan
    rows := program.rows
    bound := []
    current :=
      { source := program.source
        support := program.support
        issued := List.Subset.refl _
        authentication := ⟨[], rfl, program.authenticated⟩
        receiverIssued := by simp [actualReceiver, SourceDependencyCapture.Scope.visibleResources] }
    received := List.Subset.refl _
    certificate := program.certificate
    certificateChecked := program.certificateChecked
    pending := .nil
    retained := .nil
    retainedChecked := .nil
    accounting := program.accounting
    annotated := program.annotated
    row := program.row
    annotation := program.annotation
    checked := program.checked
    bounded := program.bounded }

/-- Empty initial support follows from the same support derivation stored in
the constructed Site; it is not inferred from a resource-free public port. -/
theorem Program.initial_resources (program : Program globals actions budget expression) :
    Syntax.resourceDependencies expression.dependencies = [] :=
  List.eq_nil_iff_forall_not_mem.mpr (fun _ member => by
    simpa only [Program.site, List.not_mem_nil] using
      program.site.current.support.resources member)

/-- Initial port typing is a projection of the actual rich current source.
It preserves the global table and public contract; it does not construct the
refuted legacy authentication at that port. -/
theorem Program.initial_ports (program : Program globals actions budget expression) :
    ScopedPorts.Typed (lowerOperations globals).ports [] ScopedPorts.TypeEnv.empty
      .none [] expression program.result.port := by
  have typed := SourceTemplates.expression_ports
    (CoreCallableContractExecution.Source.lower program.site.current.source)
    ScopedPorts.EffectScope.none
  exact typed

/-- The actual rich initial Site supplies the current facets of the existing
joint invariant. This weaker projection does not replace the rich Site. -/
theorem Program.initial_joint (program : Program globals actions budget expression) :
    ScopedPortJoint.Valid (lowerOperations globals).ports globals.policy (fun _ => none) []
      ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ program.result.port [] :=
  ScopedPortJoint.initial_configuration_valid program.initial_ports program.usage
    program.initial_resources

/-- Existing initial progress consumes the current rich source's projection.
The equality states the actual builtin ABI, without changing any operation
contract. It yields an actual first step and the established joint guarantees;
rich successor preservation and M4 availability remain separate obligations. -/
theorem Program.initial_progress (program : Program globals actions budget expression)
    (builtins : (lowerOperations globals).ports = ScopedPorts.withCellSignatures users) :
    expression.IsValue ∨ ∃ registry after,
      NamedAccessStep [] ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ after ∧
      ScopedPortJoint.Valid (lowerOperations globals).ports globals.policy registry []
        after program.result.port [] := by
  have typed := program.initial_ports
  rw [builtins] at typed
  simpa only [builtins] using
    (ScopedPortProgress.initial_progress typed program.usage program.initial_resources)

end
end Ash.OneShot.CoreCallableInitialAdmission

#print axioms Ash.OneShot.CoreCallableInitialAdmission.Program.site
#print axioms Ash.OneShot.CoreCallableInitialAdmission.Program.initial_resources
#print axioms Ash.OneShot.CoreCallableInitialAdmission.Program.initial_ports
#print axioms Ash.OneShot.CoreCallableInitialAdmission.Program.initial_joint
#print axioms Ash.OneShot.CoreCallableInitialAdmission.Program.initial_progress
