import CoreCallableSourceSubstitution
namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (Registry Owners)
open CoreCallableReceiverRefinement (CallBounds LexicalBounds)
open SourcePlannedChecks (Certified DeclarationPolicy)
section
variable [evidence : DeclarationPolicy]
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
 theorem Authenticated.value_world_weaken
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment value contract demand requirements plan rows)
      lexical receiver)
    (isValue : value.IsValue) (larger : world ⊆ nextWorld) :
    Authenticated registry outward (source.world_weaken larger) lexical receiver := by
  cases checked with
  | checked current hereditary =>
    apply Authenticated.checked current
    cases hereditary with
    | unit => exact Hereditary.unit
    | boolean => exact Hereditary.boolean
    | integer => exact Hereditary.integer
    | reference =>
      rename_i identity issued
      exact Hereditary.reference (issued := larger issued)
    | purePair left right =>
      exact Hereditary.purePair (left.value_world_weaken isValue.1 larger) (right.value_world_weaken isValue.2 larger)
    | pair left right =>
      exact Hereditary.pair (left.value_world_weaken isValue.1 larger) (right.value_world_weaken isValue.2 larger)
    | lambda refinement bodyOutward latentBound publicCertified formed known body =>
      rename_i bodySource
      exact Hereditary.lambda (bodySource := bodySource.world_weaken larger) refinement bodyOutward latentBound
        (certified_world publicCertified larger) (ScopedPorts.in_world_mono formed larger) known
        (fun nextLexical call known received => body nextLexical (call.rebase larger) known received)
    | receiverLambda bodyOutward latentBound publicCertified formed known body refinement =>
      exact Hereditary.receiverLambda bodyOutward latentBound
        (certified_world publicCertified larger) (ScopedPorts.in_world_mono formed larger) known
        (fun nextLexical call known received => body nextLexical (call.rebase larger) known received)
        (fun nextLexical call known received => refinement nextLexical (call.rebase larger) known received)
    | «variable» | app | bind | branch | perform | resume | discard | handler | handlerDomain | cleanup | resource => cases isValue
termination_by sizeOf value
end
end Ash.OneShot.CoreCallableContractAdmission

#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.value_world_weaken
