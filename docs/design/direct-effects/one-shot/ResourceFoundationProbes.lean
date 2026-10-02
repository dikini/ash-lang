import CoreCallableRichResourceFoundation
namespace Ash.OneShot.ResourceFoundationProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableStorageRecipes

/-- A concrete retaining lambda is excluded at the original receiver boundary. -/
theorem retaining_lambda_rejected
    {declarations : Instantiation.DeclarationRegistry} {world : List Nat}
    {ticket : CallableContracts.Ticket}
    (bindings : CoreCallableReturnStorageProducer.Bindings) (inst : Instantiation.Environment)
    (binder formal identity : Nat) (recipe : Recipe) (originalBound : List Nat)
    (outside : identity ∉ originalBound) :
    opening bindings inst binder identity (.lambda formal (.resourceRef (.bound binder)))
      recipe originalBound ≠ some result := by
  apply retaining_opening_rejected (declarations := declarations) (world := world) (ticket := ticket)
    (show (Code.instantiate _ _).IsValue from by simp [Code.instantiate, Code.IsValue]) ?_ outside
  simp [Code.instantiate, Instantiation.ResourceName.instantiate, Instantiation.Environment.bind,
    Code.dependencies, Syntax.resourceDependencies, Syntax.without]

/-- Acquisition uses the separate resource namespace even for equal binder names. -/
theorem ordinary_formal_not_shadowed (inst : Instantiation.Environment) (formal identity : Nat) :
    Code.instantiate (inst.bind formal identity) (.variable formal) = .variable formal := rfl

#print axioms retaining_lambda_rejected
#print axioms ordinary_formal_not_shadowed
#check CoreCallableContractAdmission.IndexedSource.resource
#check CoreCallableContractAdmission.Hereditary.resource
#check CoreCallableRichResourceFoundation.formal_resource_foundation
end Ash.OneShot.ResourceFoundationProbes
