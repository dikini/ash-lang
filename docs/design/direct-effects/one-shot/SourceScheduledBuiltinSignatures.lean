import SourceScheduledInstallationMachine

/-! The immutable operation environment agrees with the two builtin cell
operations whenever it defines a cell operation.  Undefined operations remain
allowed, so a source with no cell operations still satisfies the boundary. -/

namespace Ash.OneShot.SourceScheduledBuiltinSignatures

open ScopedExpressions SourcePlannedTyping

def Compatible (operations : Operations) : Prop :=
  ∀ identity operation input output,
    operations.erase.erase.ports (.cell identity) operation = some (input, output) →
      (operation = 0 ∧ input = .reference identity ∧ output = .integer) ∨
      (operation = 1 ∧ input = .product (.reference identity) .integer ∧ output = .unit)

theorem Compatible.read (compatible : Compatible operations)
    (known : operations.erase.erase.ports (.cell identity) 0 = some (input, output)) :
    input = .reference identity ∧ output = .integer := by
  rcases compatible identity 0 input output known with read | write
  · exact ⟨read.2.1, read.2.2⟩
  · cases write.1

theorem Compatible.write (compatible : Compatible operations)
    (known : operations.erase.erase.ports (.cell identity) 1 = some (input, output)) :
    input = .product (.reference identity) .integer ∧ output = .unit := by
  rcases compatible identity 1 input output known with read | write
  · cases read.1
  · exact ⟨write.2.1, write.2.2⟩

theorem empty : Compatible (fun _ _ => none) := by
  intro identity operation input output known
  cases known

def canonical : Operations
  | .cell identity, 0 => some (.reference identity, .integer)
  | .cell identity, 1 => some (.pair (.reference identity) .integer, .unit)
  | _, _ => none

theorem canonical_compatible : Compatible canonical := by
  intro identity operation input output known
  cases operation with
  | zero =>
      simp [canonical, Operations.erase, SourceDependencyAnnotations.Operations.erase,
        CoherentSourceTypes.Operations.ports] at known
      exact Or.inl ⟨rfl, known.1.symm, known.2.symm⟩
  | succ operation => cases operation with
    | zero =>
        simp [canonical, Operations.erase, SourceDependencyAnnotations.Operations.erase,
          CoherentSourceTypes.Operations.ports] at known
        exact Or.inr ⟨rfl, known.1.symm, known.2.symm⟩
    | succ operation => simp [canonical, Operations.erase,
        SourceDependencyAnnotations.Operations.erase, CoherentSourceTypes.Operations.ports] at known

theorem rejects_operation_two
    (operations : Operations)
    (defined : operations.erase.erase.ports (.cell identity) 2 = some (input, output)) :
    ¬ Compatible operations := by
  intro compatible
  rcases compatible identity 2 input output defined with read | write <;> omega

theorem rejects_wrong_read
    (operations : Operations)
    (defined : operations.erase.erase.ports (.cell identity) 0 = some (.unit, output)) :
    ¬ Compatible operations := by
  intro compatible
  have read := compatible.read defined
  cases read.1

end Ash.OneShot.SourceScheduledBuiltinSignatures

#print axioms Ash.OneShot.SourceScheduledBuiltinSignatures.empty
#print axioms Ash.OneShot.SourceScheduledBuiltinSignatures.canonical_compatible
#print axioms Ash.OneShot.SourceScheduledBuiltinSignatures.rejects_operation_two
#print axioms Ash.OneShot.SourceScheduledBuiltinSignatures.rejects_wrong_read
