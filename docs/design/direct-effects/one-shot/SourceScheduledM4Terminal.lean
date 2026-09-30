import SourceScheduledPreservation

/-! Terminal ownership facts for the preserved one-shot snapshot.

The terminal shape is deliberately the executable machine shape already used by
Core: an evaluated value with an empty control stack.  The ledger then reduces
to the exactly-once relation between issued and completed owners.  This file
does not assert that the contract or annotation maps are empty; those maps are
historical metadata and may retain consumed entries.
-/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Value)

/-- A terminal snapshot is an evaluated value with no remaining control
    frames.  The runtime scope is retained because it is part of the Core
    configuration, even though an empty stack makes it operationally inert. -/
def Terminal (snapshot : Snapshot operations) : Prop :=
  ∃ value scope,
    value.IsValue ∧
      snapshot.run.execution.machine = .eval ⟨value, scope, .nil⟩

/-- The terminal machine contains no live, pending, or retained stack owner. -/
theorem Terminal.no_pending_owners
    (terminal : Terminal snapshot) :
    snapshot.run.execution.machine.stack.erase.owners = [] := by
  obtain ⟨value, scope, _isValue, machine⟩ := terminal
  simp [machine, LexicalUnwind.Machine.stack, Stack.erase, Control.owners]

/-- The lifetime ledger at a terminal snapshot discharges every issued owner.
    This is a permutation because owner order is operationally immaterial. -/
theorem terminal_issued_completed
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (terminal : Terminal snapshot) :
    snapshot.run.execution.issued.Perm snapshot.run.execution.completed := by
  obtain ⟨value, scope, _isValue, machine⟩ := terminal
  have state := Valid.unpack valid
  have balance := state.ledger.1
  change snapshot.run.execution.issued.Perm
    (snapshot.run.execution.machine.stack.erase.owners ++ snapshot.run.execution.completed) at balance
  rw [machine] at balance
  simpa [LexicalUnwind.RunState.erase, LexicalUnwind.Machine.stack, Stack.erase,
    Control.owners] using balance

/-- Terminal completion is one-shot: no owner appears twice in the completed
    history. -/
theorem terminal_completed_nodup
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (_terminal : Terminal snapshot) :
    snapshot.run.execution.completed.Nodup := by
  have state := Valid.unpack valid
  exact ledger_no_double_completion state.ledger

/-- The terminal owner and resource facts carried by the common invariant. -/
theorem terminal_accounting
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (terminal : Terminal snapshot) :
    snapshot.run.execution.issued.Perm snapshot.run.execution.completed ∧
      snapshot.run.execution.completed.Nodup ∧
      ScopedTyping.resourceWorld snapshot.run.execution.issued ⊆ snapshot.world ∧
      snapshot.run.execution.machine.stack.erase.owners = [] := by
  have state := Valid.unpack valid
  exact ⟨terminal_issued_completed valid terminal,
    ledger_no_double_completion state.ledger,
    state.issuedResources,
    terminal.no_pending_owners⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Terminal.no_pending_owners
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.terminal_issued_completed
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.terminal_completed_nodup
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.terminal_accounting
