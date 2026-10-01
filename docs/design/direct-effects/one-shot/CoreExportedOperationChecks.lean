import CoreExportedOperationMetadata
import ScopedPortSteps

/-! Connected finite declaration construction from the SAME generated metadata.
Resource binder 0 is instantiated by an arbitrary runtime identity; cell ports
retain the reference argument and integer payload. The current builtin overlay
agrees on the exported cell and all user instances, without asserting equality
on unrelated cells. This is a declaration input consumer, not general source
admission or Rust compiler soundness. -/
namespace Ash.OneShot.CoreExportedOperationChecks
open Instantiation CoreOperationSignatures

 def environment (identity : Nat) : Instantiation.Environment := Environment.empty.bind 0 identity
 def table (identity : Nat) : Table := [
   ⟨.cell identity, 0, .reference identity, .integer⟩,
   ⟨.cell identity, 1, .product (.reference identity) .integer, .unit⟩,
   ⟨.user 0 [], 0, .boolean, .unit⟩]

 theorem built (identity : Nat) :
     build (environment identity) CoreExportedOperationMetadata.entries = .ok (table identity) := by
   simp [build, environment, Environment.bind,
     CoreExportedOperationMetadata.entries, table, resolveEntry, realizeEffect, realizeName,
     declarationPort, emptySupport, CoreTypeSupport.decorate, realizeType, ScopedPorts.eraseType,
     checkConflicts, checkPair, List.mapM_cons, List.mapM_nil, Except.bind, Except.pure,
     Except.mapError, Pure.pure, Bind.bind]

 theorem entries_realized (identity : Nat) :
     ListRealizes (EntryRealizes (environment identity)) CoreExportedOperationMetadata.entries
       (table identity) ∧ Compatible (table identity) := build_sound (built identity)

 theorem accepted_lookup (identity : Nat) :
     lookup (table identity) requested operation = some ports ↔
       ∃ raw, raw ∈ CoreExportedOperationMetadata.entries ∧ ∃ resolved,
         EntryRealizes (environment identity) raw resolved ∧ resolved.effect = requested ∧
         resolved.operation = operation ∧ (resolved.input, resolved.output) = ports :=
   accepted_lookup_iff (built identity)

 theorem cell_read (identity : Nat) :
     lookup (table identity) (.cell identity) 0 = some (.reference identity, .integer) := by
   simp [table, lookup]

 theorem cell_write (identity : Nat) :
     lookup (table identity) (.cell identity) 1 =
       some (.product (.reference identity) .integer, .unit) := by
   simp [table, lookup]

 theorem user_request (identity : Nat) :
     lookup (table identity) (.user 0 []) 0 = some (.boolean, .unit) := by
   simp [table, lookup]

 def signature (identity : Nat) : ScopedPorts.Signature :=
   ScopedPorts.withCellSignatures (lookup (table identity))

 theorem cell_signature_agrees (identity operation : Nat) :
     lookup (table identity) (.cell identity) operation = signature identity (.cell identity) operation := by
   cases operation with
   | zero => exact cell_read identity
   | succ operation => cases operation with
     | zero => exact cell_write identity
     | succ operation => simp [table, lookup, signature, ScopedPorts.withCellSignatures]

 theorem user_signature_agrees (identity family operation : Nat) (arguments : List TypeArgument) :
     lookup (table identity) (.user family arguments) operation =
       signature identity (.user family arguments) operation := rfl

 theorem exported_domain_agrees (identity : Nat)
     (covered : requested = .cell identity ∨ ∃ family arguments, requested = .user family arguments) :
     lookup (table identity) requested operation = signature identity requested operation := by
   rcases covered with rfl | ⟨family, arguments, rfl⟩
   · exact cell_signature_agrees identity operation
   · exact user_signature_agrees identity family operation arguments

 theorem absent_operation (identity operation : Nat) :
     lookup (table identity) (.cell identity) (operation + 2) = none := by
   simp [table, lookup]

 theorem unrelated_cell_absent (identity other operation : Nat) (different : other ≠ identity) :
     lookup (table identity) (.cell other) operation = none := by
   simp [table, lookup, Ne.symm different]

 /-- Every successful lookup is consumed by the current builtin overlay at
 the same ports. Unrelated cells do not obtain a fabricated table entry. -/
 theorem known_ports_agree (identity : Nat)
     (known : lookup (table identity) requested operation = some ports) :
     signature identity requested operation = some ports := by
   cases requested with
   | cell other =>
     by_cases same : other = identity
     · subst other
       rw [← cell_signature_agrees identity operation]
       exact known
     · have absent := unrelated_cell_absent identity other operation same
       rw [absent] at known
       cases known
   | user family arguments => exact known

 theorem entry_ports_agree (identity : Nat)
     (present : raw ∈ CoreExportedOperationMetadata.entries)
     (realized : EntryRealizes (environment identity) raw resolved) :
     signature identity resolved.effect resolved.operation = some (resolved.input, resolved.output) := by
   apply known_ports_agree identity
   exact (accepted_lookup identity).mpr ⟨raw, present, resolved, realized, rfl, rfl, rfl⟩

 theorem missing_resource_rejected
     (missing : env 0 = none) :
     build env CoreExportedOperationMetadata.entries = .error (.unresolvedResource 0) := by
   simp [build, CoreExportedOperationMetadata.entries, resolveEntry, realizeEffect, realizeName, missing,
     List.mapM_cons, Except.bind, Bind.bind]

 def conflictingRead : RawEntry := {CoreExportedOperationMetadata.entries[0] with output := .boolean}

 theorem conflicting_read_rejected (identity : Nat) :
     build (environment identity) (CoreExportedOperationMetadata.entries ++ [conflictingRead]) =
       .error (.conflictingPorts (.cell identity) 0) := by
   simp [build, environment, Environment.bind, conflictingRead,
     CoreExportedOperationMetadata.entries, resolveEntry, realizeEffect, realizeName,
     declarationPort, emptySupport, CoreTypeSupport.decorate, realizeType, ScopedPorts.eraseType,
     checkConflicts, checkPair, List.mapM_cons, List.mapM_nil, Except.bind, Except.pure,
     Except.mapError, Pure.pure, Bind.bind]

#print axioms built
#print axioms entries_realized
#print axioms accepted_lookup
#print axioms cell_read
#print axioms cell_write
#print axioms user_request
#print axioms cell_signature_agrees
#print axioms user_signature_agrees
#print axioms exported_domain_agrees
#print axioms absent_operation
#print axioms unrelated_cell_absent
#print axioms known_ports_agree
#print axioms entry_ports_agree
#print axioms missing_resource_rejected
#print axioms conflicting_read_rejected
end Ash.OneShot.CoreExportedOperationChecks
