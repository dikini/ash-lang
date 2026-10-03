import CoreCallableAuthenticatedValueWorld
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
private theorem authenticated_closed_receiver
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment value contract demand requirements plan rows)
      lexical receiver)
    (closed : ClosedValue value)
    (received : ScopedPorts.Support.evaluate nextLexical.environment value.dependencies ⊆ nextReceiver) :
    Authenticated registry outward source nextLexical nextReceiver := by
  cases checked with
  | checked current hereditary =>
    apply Authenticated.checked (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr received)
    cases hereditary with
    | unit => exact Hereditary.unit
    | boolean => exact Hereditary.boolean
    | integer => exact Hereditary.integer
    | reference =>
      rename_i identity issued
      exact Hereditary.reference (issued := issued)
    | purePair left right | pair left right =>
      have resources := List.append_eq_nil_iff.mp closed.2.1
      have supports := List.append_subset.mp (by simpa only [Code.dependencies, ScopedPorts.Support.evaluate, List.flatMap_append] using received)
      first | apply Hereditary.purePair | apply Hereditary.pair
      · apply authenticated_closed_receiver left ?_ supports.1
        exact ⟨closed.1.1, resources.1, fun dep member => closed.2.2 dep (List.mem_append_left _ member)⟩
      · apply authenticated_closed_receiver right ?_ supports.2
        exact ⟨closed.1.2, resources.2, fun dep member => closed.2.2 dep (List.mem_append_right _ member)⟩
    | lambda refinement bodyOutward latentBound publicCertified formed known body =>
      rename_i bodySource
      exact Hereditary.lambda (bodySource := bodySource) refinement bodyOutward latentBound publicCertified formed
        (fun name member => False.elim (ScopedTyping.closedValue_no_variable closed member)) body
    | receiverLambda bodyOutward latentBound publicCertified formed known body refinement =>
      exact Hereditary.receiverLambda bodyOutward latentBound publicCertified formed
        (fun name member => False.elim (ScopedTyping.closedValue_no_variable closed member)) body refinement
    | «variable» | app | bind | branch | perform | resume | discard | handler | handlerDomain | cleanup | resource => exact False.elim closed.1
termination_by sizeOf value
theorem Authenticated.value_reauthenticate
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment value contract [] (.request [] []) .pure Rows.pure)
      lexical receiver)
    (closed : ClosedValue value)
    (received : ScopedPorts.Support.evaluate nextLexical.environment value.dependencies ⊆ nextReceiver) :
    Authenticated registry outward source nextLexical nextReceiver :=
  authenticated_closed_receiver checked closed received
end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.value_reauthenticate
