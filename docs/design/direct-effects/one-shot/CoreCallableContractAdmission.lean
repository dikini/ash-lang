import CoreCallableSupportedSubstitution

/-! Callable source admission and receiver-aware authenticated substitution.
The imported proof layers preserve exact deterministic plans and complete rows. -/
namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourcePlannedChecks (DeclarationPolicy)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
section
variable [DeclarationPolicy]
/-- Request inversion uses the same fixed operation table for input and result. -/
theorem IndexedSource.request_contract
    (source : IndexedSource registry outward owners world allowed scope environment
      (.perform (Instantiation.freezeEffect effect) operation value) output demand requirements plan rows) :
    ∃ input, registry.operations effect operation = some (input, output) := by
  generalize equation : Code.perform (Instantiation.freezeEffect effect) operation value = code at source
  cases source <;> try { cases equation }
  case perform =>
    rename_i actual operationActual input valueActual deps operandPlan operandRows admitted known formed operandReq operand
    simp only [Code.perform.injEq] at equation
    obtain ⟨sameEffect, sameOperation, sameValue⟩ := equation
    have same : effect = actual := Instantiation.effect_realization_unique
      (Instantiation.frozen_effect_realizes Instantiation.Environment.empty effect)
      (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty actual)
    subst actual
    subst operationActual
    exact ⟨input, known⟩


abbrev Source.request_contract := @IndexedSource.request_contract

/-- Operand authentication and result contract come from one exact global key. -/
theorem IndexedSource.request_operand
    (source : IndexedSource registry outward owners world allowed scope environment
      (.perform (Instantiation.freezeEffect effect) operation value) output demand requirements plan rows) :
    ∃ (input : Contract) (operandDemand : List Nat) (operandReq : Requirements operandDemand)
      (operandDependencies : Dependencies) (operandPlan : Plan operandDependencies) (operandRows : Rows (signature operandPlan)),
      registry.operations effect operation = some (input, output) ∧
      IndexedSource registry outward owners world allowed scope environment value input operandDemand operandReq operandPlan operandRows := by
  generalize equation : Code.perform (Instantiation.freezeEffect effect) operation value = code at source
  cases source <;> try { cases equation }
  case perform =>
    rename_i actual operationActual input valueActual deps operandPlan operandRows admitted known formed operandReq operand
    simp only [Code.perform.injEq] at equation
    obtain ⟨sameEffect, sameOperation, sameValue⟩ := equation
    have same : effect = actual := Instantiation.effect_realization_unique
      (Instantiation.frozen_effect_realizes Instantiation.Environment.empty effect)
      (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty actual)
    subst actual
    subst operationActual
    subst valueActual
    exact ⟨input, _, operandReq, deps, operandPlan, operandRows, known, operand⟩


abbrev Source.request_operand := @IndexedSource.request_operand


#print axioms IndexedSource.request_contract
#print axioms IndexedSource.request_operand
end
end Ash.OneShot.CoreCallableContractAdmission
