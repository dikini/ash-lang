import SourceScheduledM4Terminal
import SourceScheduledPreservation

/-! Raw finite execution facts for M4.  Trace nodes contain only lexical events;
validity belongs to the separate source-preserving construction. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation
open ScopedExpressions ScopedExecution ProtectionContracts

inductive RawTrace (initial : LexicalUnwind.RunState) : Nat → LexicalUnwind.RunState → Prop where
  | refl : RawTrace initial 0 initial
  | step {count before after} (pre : RawTrace initial count before)
      (event : LexicalUnwind.Event before after) : RawTrace initial (count + 1) after

theorem RawTrace.preserves_ledger
    (trace : RawTrace initial count final) (ledger : Ledger initial.erase) :
    Ledger final.erase := by
  induction trace with
  | refl => exact ledger
  | step pre event ih => exact LexicalUnwind.event_preserves_ledger event ih

theorem RawTrace.ownership
    (trace : RawTrace initial count final) (ledger : Ledger initial.erase) :
    Ledger final.erase ∧ final.completed.Nodup ∧
      (∀ owner, owner ∈ final.machine.stack.erase.owners → owner ∉ final.completed) := by
  have next := trace.preserves_ledger ledger
  exact ⟨next, ledger_no_double_completion next,
    fun owner live => ledger_no_live_completed_alias next live⟩

theorem RawTrace.terminal_accounting
    (trace : RawTrace initial count final) (ledger : Ledger initial.erase)
    (terminal : final.machine = .eval ⟨value, scope, .nil⟩) :
    final.issued.Perm final.completed ∧ final.completed.Nodup := by
  have next := trace.preserves_ledger ledger
  constructor
  · have balance := next.1
    change final.issued.Perm (final.machine.stack.erase.owners ++ final.completed) at balance
    rw [terminal] at balance
    simpa [LexicalUnwind.Machine.stack, Stack.erase, Control.owners] using balance
  · exact ledger_no_double_completion next

theorem RawTrace.prepend
    (event : LexicalUnwind.Event initial after)
    (trace : RawTrace after count final) : RawTrace initial (count + 1) final := by
  induction trace with
  | refl => exact .step .refl event
  | @step n before next pre nextEvent ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using RawTrace.step ih nextEvent

/-- Fuel-bounded execution from any availability theorem.  Each nonterminal
iteration selects an M3 request, so validity is reconstructed by preservation;
the raw trace itself contains only lexical events. -/
theorem finite_prefix_with
    {operations : SourcePlannedTyping.Operations}
    {ports : OperationRows operations}
    {initial : Snapshot operations}
    (available : ∀ snapshot : Snapshot operations,
      Valid policy outward ambient budget ports emptyRows output outputRows snapshot →
      Terminal snapshot ∨ Nonempty (Request snapshot))
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows initial)
    (fuel : Nat) :
    ∃ count final,
      RawTrace initial.run.execution count final.run.execution ∧
      Valid policy outward ambient budget ports emptyRows output outputRows final ∧
      count ≤ fuel ∧ (count = fuel ∨ Terminal final) := by
  induction fuel generalizing initial with
  | zero => exact ⟨0, initial, .refl, valid, Nat.le_refl 0, .inl rfl⟩
  | succ fuel ih =>
      rcases available initial valid with terminal | request
      · exact ⟨0, initial, .refl, valid, Nat.zero_le _, .inr terminal⟩
      · obtain ⟨request⟩ := request
        obtain ⟨after, event, realizes, nextValid⟩ := preservation valid request
        obtain ⟨count, final, trace, finalValid, bound, exhausted | terminal⟩ := ih nextValid
        · exact ⟨count + 1, final, trace.prepend event, finalValid,
            by omega, .inl (by omega)⟩
        · exact ⟨count + 1, final, trace.prepend event, finalValid,
            by omega, .inr terminal⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.RawTrace.preserves_ledger
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.RawTrace.ownership
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.RawTrace.terminal_accounting
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.RawTrace.prepend
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.finite_prefix_with
