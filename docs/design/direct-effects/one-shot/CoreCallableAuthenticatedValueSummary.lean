import CoreCallableAuthenticatedCompletion
namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (Registry Owners)
open CoreCallableReceiverRefinement (LexicalBounds)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [evidence : DeclarationPolicy]
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
theorem Authenticated.value_summary
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment value contract demand requirements plan rows)
      lexical receiver) (isValue : value.IsValue) :
    Authenticated registry outward (source.value_summary isValue) lexical receiver := by
  cases checked with
  | checked current hereditary =>
    apply Authenticated.checked current
    cases hereditary with
    | unit => exact .unit
    | boolean => exact .boolean
    | integer => exact .integer
    | reference => exact .reference (issued := by assumption)
    | purePair left right | pair left right =>
      exact .purePair (left.value_summary isValue.1) (right.value_summary isValue.2)
    | lambda refinement bodyOutward latentBound publicCertified formed known body =>
      exact .lambda (bodySource := by assumption) refinement bodyOutward latentBound publicCertified formed known body
    | receiverLambda bodyOutward latentBound publicCertified formed known body refinement =>
      exact .receiverLambda bodyOutward latentBound publicCertified formed known body refinement
    | «variable» | app | bind | branch | perform | resume | discard | handler | handlerDomain | cleanup | resource => exact False.elim isValue
termination_by sizeOf value
end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.value_summary
