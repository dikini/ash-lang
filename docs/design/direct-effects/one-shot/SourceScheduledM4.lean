import SourceScheduledM4Availability
import SourceScheduledM4Reachability
import SourceScheduledPreservationExample

/-! M4's checked boundary for the current one-shot snapshot.

Current-state availability is exhaustive, and M3 preservation turns its request
into an actual lexical event with a valid successor.  Fuel-bounded execution
records only raw lexical events while reconstructing endpoint validity at every
step.  The older request-indexed reachability interface remains available for
clients that need explicit realization witnesses.
-/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Value)
open Reachability
open InitialAdmission

abbrev Reachable := Reachability.ValidSnapshot

theorem reachable_endpoint_valid
    {operations : Operations} {policy : Syntax.TicketPolicy} {outward : List Instance}
    {ambient : List Nat} {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)} {output : Value}
    {outputRows : ValueRows output}
    {initial final : Reachable operations policy outward ambient budget ports emptyRows output outputRows}
    (trace : Trace operations policy outward ambient budget ports emptyRows output outputRows initial final) :
    Valid policy outward ambient budget ports emptyRows output outputRows final.snapshot :=
  trace.endpoint_valid

theorem applicable_step
    {operations : Operations} {policy : Syntax.TicketPolicy} {outward : List Instance}
    {ambient : List Nat} {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)} {output : Value}
    {outputRows : ValueRows output}
    {before : Reachable operations policy outward ambient budget ports emptyRows output outputRows}
    (request : Request before.snapshot) :
    ∃ after : Reachable operations policy outward ambient budget ports emptyRows output outputRows,
      LexicalUnwind.Event before.snapshot.run.execution after.snapshot.run.execution ∧
      Realizes request after.snapshot ∧
      Trace operations policy outward ambient budget ports emptyRows output outputRows before after := by
  exact Trace.preserving_step .refl request

theorem terminal_accounting_reachable
    {operations : Operations} {policy : Syntax.TicketPolicy} {outward : List Instance}
    {ambient : List Nat} {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)} {output : Value}
    {outputRows : ValueRows output}
    {snapshot : Snapshot operations}
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (terminal : Terminal snapshot) :
    snapshot.run.execution.issued.Perm snapshot.run.execution.completed ∧
      snapshot.run.execution.completed.Nodup ∧
      ScopedTyping.resourceWorld snapshot.run.execution.issued ⊆ snapshot.world ∧
      snapshot.run.execution.machine.stack.erase.owners = [] :=
  terminal_accounting valid terminal

/-- Initial admission supplies the complete M4 starting invariant; no runtime
premise beyond the admitted program is required for bounded execution. -/
theorem InitialAdmission.Program.finite_prefix
    (program : Program operations policy ports [] [] expression)
    (tables : CallableProtectionFrames.Tables)
    (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required)
    (fuel : Nat) :
    ∃ count final,
      RawTrace (initialRun expression).execution count final.run.execution ∧
      Valid policy [] [] [] ports emptyRows program.result program.resultRows final ∧
      count ≤ fuel ∧ (count = fuel ∨ Terminal final) := by
  let state := program.closed_initial_state tables families required
  simpa [state] using Preservation.finite_prefix program.builtinSignatures
    (valid_ofState state) fuel

namespace Examples

open InitialAdmission.HandledExample

/-- The admitted handled-operation fixture therefore has a bounded raw prefix
for every fuel, including its handler installation, capture and discard path. -/
theorem handled_discard_finite_prefix (fuel : Nat) :
    ∃ count final,
      RawTrace (initialRun expression).execution count final.run.execution ∧
      Valid policy [] [] [] ports emptyRows .unit .unit final ∧
      count ≤ fuel ∧ (count = fuel ∨ Terminal final) :=
  Preservation.InitialAdmission.Program.finite_prefix program
    (fun _ => []) (fun _ => .nil) (fun _ => []) fuel

end Examples

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.reachable_endpoint_valid
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.applicable_step
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.terminal_accounting_reachable
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InitialAdmission.Program.finite_prefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Examples.handled_discard_finite_prefix
