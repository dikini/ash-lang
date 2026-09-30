import CoreOperationSignatures
import SourceScheduledBuiltinSignatures
import CoreInitialExample

/-! Builtin compatibility for finite supplied declaration tables. Every cell
entry is validated before lookup; user instances are retained unchanged. The
partial enrichment below constructs only primitive/product/reference values.
Functional ports need authentic dependency/plan evidence, which remains open
for the wider C2 fragment; no pure functional plan is fabricated here.

The finite table supplies no signature outside its domain and is not an
authenticated Rust registry or complete source-admission certificate. -/
namespace Ash.OneShot.CoreBuiltinSignatures
open CoreOperationSignatures

inductive Error where
  | malformedCell : ResolvedEntry → Error
  | conflictingPorts : CoreOperationSignatures.Error → Error
  | functionalPort : ScopedPorts.Port → Error
  deriving DecidableEq, Repr

/-- Actual cell declaration ports, including the reference identity in the
ordinary operand. User-instance declarations are left unrestricted. -/
def CellShape (entry : ResolvedEntry) : Prop :=
  match entry.effect with
  | .user _ _ => True
  | .cell identity =>
      (entry.operation = 0 ∧ entry.input = .reference identity ∧ entry.output = .integer) ∨
      (entry.operation = 1 ∧ entry.input = .product (.reference identity) .integer ∧ entry.output = .unit)

instance (entry : ResolvedEntry) : Decidable (CellShape entry) := by
  unfold CellShape
  cases entry.effect <;> infer_instance

def checkEntry (entry : ResolvedEntry) : Except Error Unit :=
  if CellShape entry then .ok () else .error (.malformedCell entry)

def validateBuiltin : Table → Except Error Unit
  | [] => .ok ()
  | entry :: rest => do
      checkEntry entry
      validateBuiltin rest

/-- Return the same complete table after validation; malformed declarations
reject rather than disappear behind a fallback or an earlier duplicate. -/
def checkBuiltin (table : Table) : Except Error Table := do
  validateBuiltin table
  pure table

def TableCellShape (table : Table) : Prop := ∀ entry, entry ∈ table → CellShape entry

def PortCompatible (signature : ScopedPorts.Signature) : Prop :=
  ∀ identity operation input output,
    signature (.cell identity) operation = some (input, output) →
      (operation = 0 ∧ input = .reference identity ∧ output = .integer) ∨
      (operation = 1 ∧ input = .product (.reference identity) .integer ∧ output = .unit)

private theorem bind_ok {α β : Type} (a : Except Error α)
    (f : α → Except Error β) (value : β) (success : a.bind f = .ok value) :
    ∃ item, a = .ok item ∧ f item = .ok value := by
  cases h : a with
  | error e => simp [h, Except.bind] at success
  | ok item => exact ⟨item, rfl, by simpa [h, Except.bind] using success⟩

theorem checkEntry_iff : checkEntry entry = .ok () ↔ CellShape entry := by
  unfold checkEntry
  split <;> simp_all

theorem validateBuiltin_iff : validateBuiltin table = .ok () ↔ TableCellShape table := by
  induction table with
  | nil => simp [validateBuiltin, TableCellShape]
  | cons entry rest ih =>
      constructor
      · intro success
        obtain ⟨checked, first, tail⟩ := bind_ok _ _ _ success
        cases checked
        intro current member
        rcases List.mem_cons.mp member with rfl | later
        · exact checkEntry_iff.mp first
        · exact ih.mp tail current later
      · intro shape
        have first := checkEntry_iff.mpr (shape entry List.mem_cons_self)
        have tail := ih.mpr (fun current member => shape current (List.mem_cons_of_mem _ member))
        simp only [validateBuiltin, first, tail]
        rfl

theorem checkBuiltin_sound (success : checkBuiltin table = .ok checked) :
    checked = table ∧ TableCellShape table := by
  obtain ⟨unitResult, first, result⟩ := bind_ok _ _ _ success
  cases unitResult
  have same : table = checked := by simpa [Pure.pure, Except.pure] using result
  exact ⟨same.symm, validateBuiltin_iff.mp first⟩

theorem table_port_compatible (shape : TableCellShape table) : PortCompatible (lookup table) := by
  intro identity operation input output known
  obtain ⟨entry, member, effect, operationEq, ports⟩ := lookup_sound known
  have checked := shape entry member
  unfold CellShape at checked
  rw [effect] at checked
  have inputEq : entry.input = input := congrArg Prod.fst ports
  have outputEq : entry.output = output := congrArg Prod.snd ports
  simpa [operationEq, inputEq, outputEq] using checked

/-- Generic compatibility follows from checking all declarations, not just the
first occurrence of a key. -/
theorem checked_table_compatible (success : checkBuiltin table = .ok checked) :
    checked = table ∧ PortCompatible (lookup checked) := by
  obtain ⟨rfl, shape⟩ := checkBuiltin_sound success
  exact ⟨rfl, table_port_compatible shape⟩

/-- This helper has no clause for callable enrichment: function dependencies,
footprints and plans cannot be inferred from a declaration port. -/
def enrichPort : ScopedPorts.Port → Except Error SourcePlannedTyping.Value
  | .unit => .ok .unit
  | .boolean => .ok .boolean
  | .integer => .ok .integer
  | .reference identity => .ok (.reference identity)
  | .product left right => do
      pure (.pair (← enrichPort left) (← enrichPort right))
  | port@(.function _ _ _) => .error (.functionalPort port)

def PrimitivePort : ScopedPorts.Port → Bool
  | .unit | .boolean | .integer | .reference _ => true
  | .product left right => PrimitivePort left && PrimitivePort right
  | .function _ _ _ => false

def erasedPort (value : SourcePlannedTyping.Value) : ScopedPorts.Port := value.erase.erase.port

theorem enrichPort_sound (success : enrichPort port = .ok value) :
    erasedPort value = port ∧ PrimitivePort port = true := by
  induction port generalizing value with
  | unit => simp [enrichPort] at success; cases success; exact ⟨rfl, rfl⟩
  | boolean => simp [enrichPort] at success; cases success; exact ⟨rfl, rfl⟩
  | integer => simp [enrichPort] at success; cases success; exact ⟨rfl, rfl⟩
  | reference identity => simp [enrichPort] at success; cases success; exact ⟨rfl, rfl⟩
  | function input output requests => simp [enrichPort] at success
  | product left right ihLeft ihRight =>
      obtain ⟨a, first, rest⟩ := bind_ok _ _ _ success
      obtain ⟨b, second, result⟩ := bind_ok _ _ _ rest
      have same : SourcePlannedTyping.Value.pair a b = value := by
        simpa [Pure.pure, Except.pure] using result
      subst value
      have left := ihLeft first
      have right := ihRight second
      constructor
      · change ScopedPorts.Port.product (erasedPort a) (erasedPort b) = _
        rw [left.1, right.1]
      · simp [PrimitivePort, left.2, right.2]

theorem enrichPort_complete (supported : PrimitivePort port = true) :
    ∃ value, enrichPort port = .ok value := by
  induction port with
  | unit => exact ⟨.unit, rfl⟩
  | boolean => exact ⟨.boolean, rfl⟩
  | integer => exact ⟨.integer, rfl⟩
  | reference identity => exact ⟨.reference identity, rfl⟩
  | function input output requests => simp [PrimitivePort] at supported
  | product left right ihLeft ihRight =>
      have parts : PrimitivePort left = true ∧ PrimitivePort right = true := by
        simpa [PrimitivePort] using supported
      obtain ⟨a, first⟩ := ihLeft parts.1
      obtain ⟨b, second⟩ := ihRight parts.2
      exact ⟨.pair a b, by simp only [enrichPort, first, second]; rfl⟩

structure EnrichedEntry where
  effect : Instance
  operation : Nat
  input : SourcePlannedTyping.Value
  output : SourcePlannedTyping.Value

abbrev EnrichedTable := List EnrichedEntry

def enrichEntry (entry : ResolvedEntry) : Except Error EnrichedEntry := do
  let input ← enrichPort entry.input
  let output ← enrichPort entry.output
  pure ⟨entry.effect, entry.operation, input, output⟩

def enrichTable : Table → Except Error EnrichedTable
  | [] => .ok []
  | first :: rest => do
      pure ((← enrichEntry first) :: (← enrichTable rest))

/-- Public partial enrichment checks original conflict and builtin obligations
before constructing enriched values. It neither drops nor replaces entries. -/
def enrichChecked (table : Table) : Except Error EnrichedTable := do
  (checkConflicts table).mapError Error.conflictingPorts
  validateBuiltin table
  enrichTable table

def operations : EnrichedTable → SourcePlannedTyping.Operations
  | [], _, _ => none
  | entry :: rest, effect, operation =>
      if entry.effect = effect ∧ entry.operation = operation then some (entry.input, entry.output)
      else operations rest effect operation

def eraseEntry (entry : EnrichedEntry) : ResolvedEntry :=
  ⟨entry.effect, entry.operation, erasedPort entry.input, erasedPort entry.output⟩

/-- The complete ordered list is retained by enrichment, including duplicates;
this relation checks keys and both operation-port erasures entry by entry. -/
def EntryErases (entry : ResolvedEntry) (rich : EnrichedEntry) : Prop := eraseEntry rich = entry

theorem enrichEntry_sound (success : enrichEntry entry = .ok rich) : EntryErases entry rich := by
  obtain ⟨input, first, rest⟩ := bind_ok _ _ _ success
  obtain ⟨output, second, result⟩ := bind_ok _ _ _ rest
  have same : EnrichedEntry.mk entry.effect entry.operation input output = rich := by
    simpa [Pure.pure, Except.pure] using result
  subst rich
  unfold EntryErases eraseEntry
  rw [(enrichPort_sound first).1, (enrichPort_sound second).1]

theorem enrichTable_sound (success : enrichTable table = .ok rich) :
    Instantiation.ListRealizes EntryErases table rich := by
  induction table generalizing rich with
  | nil => simp [enrichTable] at success; cases success; exact .nil
  | cons first rest ih =>
      obtain ⟨head, firstSuccess, remaining⟩ := bind_ok _ _ _ success
      obtain ⟨tail, tailSuccess, result⟩ := bind_ok _ _ _ remaining
      have same : head :: tail = rich := by simpa [Pure.pure, Except.pure] using result
      subst rich
      exact .cons (enrichEntry_sound firstSuccess) (ih tailSuccess)

private theorem mapError_ok {α ε : Type} (a : Except ε α) (f : ε → Error) (value : α)
    (success : a.mapError f = .ok value) : a = .ok value := by
  cases a with
  | error e => simp [Except.mapError] at success
  | ok item => simpa [Except.mapError] using success

/-- Public enrichment retains both consistency and builtin checks, rather than
assuming arbitrary supplied tables were consistent before enrichment. -/
theorem enrichChecked_sound (success : enrichChecked table = .ok rich) :
    CoreOperationSignatures.Compatible table ∧ TableCellShape table ∧
      Instantiation.ListRealizes EntryErases table rich := by
  obtain ⟨conflicts, first, rest⟩ := bind_ok _ _ _ success
  cases conflicts
  obtain ⟨builtins, second, remaining⟩ := bind_ok _ _ _ rest
  cases builtins
  exact ⟨checkConflicts_sound (mapError_ok _ _ _ first), validateBuiltin_iff.mp second,
    enrichTable_sound remaining⟩

private theorem erasure_from_entries (related : Instantiation.ListRealizes EntryErases table rich) :
    (operations rich).erase.erase.ports = lookup table := by
  induction related with
  | nil => rfl
  | @cons entry rich table rest head tail ih =>
      unfold EntryErases at head
      subst entry
      funext effect operation
      by_cases matching : rich.effect = effect ∧ rich.operation = operation
      · simp [operations, lookup, eraseEntry, erasedPort, matching, SourcePlannedTyping.Operations.erase,
          SourceDependencyAnnotations.Operations.erase, CoherentSourceTypes.Operations.ports]
      · simpa [operations, lookup, eraseEntry, matching, SourcePlannedTyping.Operations.erase,
          SourceDependencyAnnotations.Operations.erase, CoherentSourceTypes.Operations.ports]
          using congrFun (congrFun ih effect) operation

/-- No declared key is lost or fabricated while primitive enrichment is erased.
The accepted table's conflict certificate is retained in the public result. -/
theorem enrichChecked_erasure (success : enrichChecked table = .ok rich) :
    CoreOperationSignatures.Compatible table ∧ (operations rich).erase.erase.ports = lookup table := by
  have accepted := enrichChecked_sound success
  exact ⟨accepted.1, erasure_from_entries accepted.2.2⟩

/-- The checked finite operations satisfy the existing builtin-cell boundary.
Undefined keys, including unlisted activations, stay undefined. -/
theorem enrichChecked_builtin_compatible (success : enrichChecked table = .ok rich) :
    SourceScheduledBuiltinSignatures.Compatible (operations rich) := by
  have accepted := enrichChecked_sound success
  unfold SourceScheduledBuiltinSignatures.Compatible
  rw [erasure_from_entries accepted.2.2]
  exact table_port_compatible accepted.2.1

namespace InitialExample

local notation "initialOperations" =>
  Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.operations

/-- One selected activation plus the initial example's exact user operation.
This finite domain does not stand for all cell activation identities. -/
def table (identity : Nat) : Table := [
  ⟨.cell identity, 0, .reference identity, .integer⟩,
  ⟨.cell identity, 1, .product (.reference identity) .integer, .unit⟩,
  ⟨.user 0 [], 0, .boolean, .unit⟩]

def rich (identity : Nat) : EnrichedTable := [
  ⟨.cell identity, 0, .reference identity, .integer⟩,
  ⟨.cell identity, 1, .pair (.reference identity) .integer, .unit⟩,
  ⟨.user 0 [], 0, .boolean, .unit⟩]

theorem checked (identity : Nat) : enrichChecked (table identity) = .ok (rich identity) := by
  simp [enrichChecked, table, rich, checkConflicts, checkPair, validateBuiltin, checkEntry,
    CellShape, enrichTable, enrichEntry, enrichPort, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

def Domain (identity : Nat) (effect : Instance) (operation : Nat) : Prop :=
  (effect = .cell identity ∧ (operation = 0 ∨ operation = 1)) ∨
    (effect = .user 0 [] ∧ operation = 0)

instance (identity : Nat) (effect : Instance) (operation : Nat) :
    Decidable (Domain identity effect operation) := by
  unfold Domain
  infer_instance

def restricted (identity : Nat) : SourcePlannedTyping.Operations :=
  fun effect operation => if Domain identity effect operation then initialOperations effect operation else none

theorem agrees_on_domain (domain : Domain identity effect operation) :
    operations (rich identity) effect operation = initialOperations effect operation := by
  rcases domain with ⟨rfl, read | write⟩ | ⟨rfl, rfl⟩
  · subst operation
    simp [operations, rich,
      Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.operations]
  · subst operation
    simp [operations, rich,
      Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.operations]
  · simp [operations, rich,
      Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.operations]

theorem absent_outside (outside : ¬ Domain identity effect operation) :
    operations (rich identity) effect operation = none := by
  have noRead : ¬ (Instance.cell identity = effect ∧ 0 = operation) := by
    intro h
    exact outside (.inl ⟨h.1.symm, .inl h.2.symm⟩)
  have noWrite : ¬ (Instance.cell identity = effect ∧ 1 = operation) := by
    intro h
    exact outside (.inl ⟨h.1.symm, .inr h.2.symm⟩)
  have noUser : ¬ (Instance.user 0 [] = effect ∧ 0 = operation) := by
    intro h
    exact outside (.inr ⟨h.1.symm, h.2.symm⟩)
  simp [operations, rich, noRead, noWrite, noUser]

/-- Equality is to the initial example restricted to this finite domain,
without extending the table to its infinite builtin activation family. -/
theorem operations_eq_restriction (identity : Nat) : operations (rich identity) = restricted identity := by
  funext effect operation
  by_cases domain : Domain identity effect operation
  · simpa [restricted, domain] using agrees_on_domain domain
  · simpa [restricted, domain] using absent_outside domain

theorem builtin_compatible (identity : Nat) :
    SourceScheduledBuiltinSignatures.Compatible (operations (rich identity)) :=
  enrichChecked_builtin_compatible (checked identity)

theorem erased_ports (identity : Nat) :
    (operations (rich identity)).erase.erase.ports = lookup (table identity) :=
  (enrichChecked_erasure (checked identity)).2

end InitialExample

namespace Examples

example : checkBuiltin [⟨.cell 7, 0, .reference 7, .integer⟩,
    ⟨.cell 7, 1, .product (.reference 7) .integer, .unit⟩] = .ok [
      ⟨.cell 7, 0, .reference 7, .integer⟩,
      ⟨.cell 7, 1, .product (.reference 7) .integer, .unit⟩] := rfl

example : checkBuiltin [⟨.cell 7, 0, .unit, .integer⟩] =
    .error (.malformedCell ⟨.cell 7, 0, .unit, .integer⟩) := rfl

example : checkBuiltin [⟨.cell 7, 0, .reference 8, .integer⟩] =
    .error (.malformedCell ⟨.cell 7, 0, .reference 8, .integer⟩) := rfl

example : checkBuiltin [⟨.cell 7, 1, .integer, .unit⟩] =
    .error (.malformedCell ⟨.cell 7, 1, .integer, .unit⟩) := rfl

example : checkBuiltin [⟨.cell 7, 2, .unit, .unit⟩] =
    .error (.malformedCell ⟨.cell 7, 2, .unit, .unit⟩) := rfl

/-- A malformed later duplicate is still checked; it cannot hide behind read. -/
example : checkBuiltin [⟨.cell 7, 0, .reference 7, .integer⟩,
    ⟨.cell 7, 0, .unit, .integer⟩] = .error (.malformedCell ⟨.cell 7, 0, .unit, .integer⟩) := rfl

/-- Builtin validation retains functional user declarations unchanged. The
separate partial enrichment then reports its missing callable evidence. -/
example : checkBuiltin [⟨.user 5 [.apply (.nominal 9) (.resource 7)], 3,
    .function .unit .integer [.user 6 []], .boolean⟩] = .ok [
      ⟨.user 5 [.apply (.nominal 9) (.resource 7)], 3,
        .function .unit .integer [.user 6 []], .boolean⟩] := rfl

example : enrichChecked [⟨.user 5 [], 3, .function .unit .integer [.user 6 []], .boolean⟩] =
    .error (.functionalPort (.function .unit .integer [.user 6 []])) := rfl

example : enrichChecked [⟨.user 5 [], 3, .unit, .boolean⟩,
    ⟨.user 5 [], 3, .integer, .boolean⟩] =
    .error (.conflictingPorts (.conflictingPorts (.user 5 []) 3)) := rfl

example : enrichChecked [⟨.user 5 [], 3, .unit, .boolean⟩,
    ⟨.user 5 [], 3, .unit, .boolean⟩] = .ok [
      ⟨.user 5 [], 3, .unit, .boolean⟩, ⟨.user 5 [], 3, .unit, .boolean⟩] := rfl

example : operations (InitialExample.rich 7) (.cell 8) 0 = none := rfl

example : operations (InitialExample.rich 7) (.cell 7) 0 = some (.reference 7, .integer) := rfl

example : operations (InitialExample.rich 7) (.cell 7) 1 = some (.pair (.reference 7) .integer, .unit) := rfl

end Examples

#print axioms validateBuiltin_iff
#print axioms checked_table_compatible
#print axioms enrichPort_sound
#print axioms enrichPort_complete
#print axioms enrichChecked_sound
#print axioms enrichChecked_erasure
#print axioms enrichChecked_builtin_compatible
#print axioms InitialExample.checked
#print axioms InitialExample.operations_eq_restriction
#print axioms InitialExample.builtin_compatible
end Ash.OneShot.CoreBuiltinSignatures
