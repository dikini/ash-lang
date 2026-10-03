import CoreCallableInitialAdmission
import CoreCallableRichBetaCore
import CoreCallableStaticProducer
import SourceScheduledM4Execution

namespace Ash.OneShot.CoreCallableRichAdmittedCurrentOrigins
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreCallableGeneratedChronology CoreCallableInitialChronology
open CoreCallableContractAdmission (Globals)
open CoreCallableContractExecution (Site)
open CoreCallableInitialAdmission (Program)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation (RawTrace)
open SourcePlannedChecks (DeclarationPolicy)

section
variable [DeclarationPolicy]

/-- Current causal authority retains the accepted static Program and full rich
Site. Historical event bookkeeping is separate from physical/lexical history.
This receipt does not assert the legacy M4 complete-state invariant. -/
structure Current (program : Program initialGlobals initialActions initialBudget originalCode)
    (endpoint : Endpoint graph)
    (site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root) where
  input : InitialInput graph originalCode
  related : CoreCallableRichBetaCore.Current endpoint site
  run : LexicalUnwind.RunState
  machine : run.machine = endpoint.point.machine
  eventCount : Nat
  past : RawTrace ⟨.eval ⟨originalCode,.none,.nil⟩,[],[]⟩ eventCount run
  ledger : Ledger run.erase

omit [DeclarationPolicy] in
/-- Literal translation is obtained from the existing successful graph gate.
Empty static instantiation is proved structurally; no source identity is inferred
from agreement of the graph gate's proof with the accepted Program's proof. -/
theorem graph_input
    (gate : CoreCallableStaticProducer.GraphResult graph graph.root [] Instantiation.Environment.empty
      entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver) :
    InitialInput graph code := by
  have literal : gate.raw = code := by
    have unchanged := gate.raw.instantiation_identity Instantiation.Environment.empty
      (by intro name member; rfl)
    exact unchanged.symm.trans gate.literalCode
  exact ⟨gate.shape,by simpa only [literal] using gate.translated⟩

/-- Any accepted rich Program with SAME current executed shape/translation
outputs has an initial receipt. Admission is already supplied by Program; no
second constructor grammar or source/authentication gate is required. -/
noncomputable def initial_from_input
    (program : Program globals actions budget code)
    (input : InitialInput graph code) :
    Current program (initial_endpoint input) program.site := {
  input := input
  related := ⟨rfl⟩
  run := ⟨.eval ⟨code,.none,.nil⟩,[],[]⟩
  machine := rfl
  eventCount := 0
  past := .refl
  ledger := ⟨List.Perm.refl [],List.nodup_nil⟩ }

/-- The original GraphResult interface delegates to the minimal static-input
seed. Its exact Program indices and public interface remain unchanged. -/
noncomputable def initial
    (program : Program globals actions budget code)
    (gate : CoreCallableStaticProducer.GraphResult graph graph.root [] Instantiation.Environment.empty
      entries policy outward owners world allowed scope bindings code program.result program.demand program.requirements program.plan program.rows lexical receiver) :
    Current program (initial_endpoint (graph_input gate)) program.site :=
  initial_from_input program (graph_input gate)

theorem initial_bookkeeping
    (program : Program globals actions budget code)
    (gate : CoreCallableStaticProducer.GraphResult graph graph.root [] Instantiation.Environment.empty
      entries policy outward owners world allowed scope bindings code program.result program.demand program.requirements program.plan program.rows lexical receiver) :
    (initial program gate).run.issued = [] ∧ (initial program gate).run.completed = [] ∧
      (initial program gate).eventCount = 0 := ⟨rfl,rfl,rfl⟩

/-- The accepted Program's original joint projection remains available. It is
separate from the richer current Site and never asserted to be legacy M4 Valid. -/
theorem Current.initial_joint
    {program : Program initialGlobals initialActions initialBudget originalCode}
    (_current : Current program endpoint site) :
    ScopedPortJoint.Valid (CoreCallableContractExecution.lowerOperations initialGlobals).ports
      initialGlobals.policy (fun _ => none) []
      ⟨⟨⟨originalCode,.none,.nil⟩,[],[]⟩,[]⟩ program.result.port [] :=
  program.initial_joint

/-- Historical freshness for a nonallocating edge comes from the current
ledger, not from a ticket occurrence bound. -/
theorem Current.nonallocating_fresh (current : Current program endpoint site) :
    (current.run.issued ++ []).Nodup := by
  simpa only [List.append_nil,LexicalUnwind.RunState.erase] using current.ledger.2

end
#print axioms graph_input
#print axioms initial
#print axioms initial_bookkeeping
#print axioms Current.initial_joint
#print axioms Current.nonallocating_fresh
#print axioms initial_from_input
end Ash.OneShot.CoreCallableRichAdmittedCurrentOrigins
