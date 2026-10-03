import CoreCallableContractSource
namespace Ash.OneShot.CoreCallableContractOperandDomain
open CoreCallableContractSource (Contract)
/-- Full scalar operation domains carry no resource dependencies. -/
def domainSupport (argument : Contract) (receiver : List Nat) : List Nat :=
  match argument with | .unit | .boolean | .integer => [] | _ => receiver
theorem domainSupport_received : domainSupport argument receiver ⊆ receiver := by
  cases argument <;> simp [domainSupport]
#print axioms domainSupport_received
end Ash.OneShot.CoreCallableContractOperandDomain
