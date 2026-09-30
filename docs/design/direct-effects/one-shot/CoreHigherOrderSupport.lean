import CoreCallableSupport
import CoreTypeSupport

/-! Exact D4 obstruction for the request-allowance refinement used by
CoreCallableSupport, exposed by core-cleanup-passed-pure-closure.ash.
The fixture's Invoke.run has no resource argument and accepts a declared pure
Unit→Unit callable retaining a live cell; current Rust CLI evidence is Unit.

The theorems concern unchanged retained lambda code and unchanged operation
ports under the current Source/Auth rules. They do not exclude all translations,
a separately proved capture-erasing normalization, or a revised independent
retention interface. No full Program is constructed here. -/
namespace Ash.OneShot.CoreHigherOrderSupport
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value Environment)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreCallableSupport
open RecursiveRequirements (Requirements)
open SourcePlanSignatures (signature)

variable {operations : Operations} {policy : Syntax.TicketPolicy} {contracts : Contracts}
  {ports : OperationRows operations} {world : List Nat} {allowed : List Instance}
  {scope : Execution.Scope} {environment : Environment}
  {owners : ContractRows contracts} {environmentRows : EnvironmentRows environment}

/-- The selected closure makes no request but its original code still retains
this cell in the lambda dependency list. -/
theorem retained_cell_dependency (identity : Nat) :
    identity ∈ Syntax.resourceDependencies (closure identity).dependencies := by
  simp [closure, body, Code.dependencies, Syntax.without, Syntax.resourceDependencies]

/-- An unchanged declared pure function port cannot hide an added request
allowance, even when the body footprint remains empty. -/
theorem exact_pure_port_requests
    (same : (Value.function .unit .unit requests latent bodySignature).erase.erase.port =
      ScopedPorts.Port.function .unit .unit []) : requests = [] := by
  simpa [Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port] using same

/-- Keeping the operation's exact pure input port and the original retained
lambda makes the existing capture guard unavailable. -/
theorem allowance_strategy_obstruction (identity : Nat)
    (same : (Value.function .unit .unit requests latent bodySignature).erase.erase.port =
      ScopedPorts.Port.function .unit .unit []) :
    ¬ LambdaPortCaptureSupport.captures environment 2 (body identity) .unit .unit requests := by
  have requestsEmpty := exact_pure_port_requests same
  subst requests
  exact empty_allowance_does_not_supply_capture_guard identity

/-- The cell allowance that repairs the old guard changes the declaration's
exact function request row; resource-free user keys cannot account for it. -/
theorem added_cell_changes_pure_port (identity : Nat) :
    (Value.function .unit .unit [.cell identity] [] (signature bodyPlan)).erase.erase.port ≠
      ScopedPorts.Port.function .unit .unit [] := by
  simp [Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port]

/-- This current Auth invariant independently exposes the same precise boundary:
a retaining syntactic lambda cannot be authenticated at a resource-free port.
It makes no claim about changed code, independent-retention revisions or every
possible Core translation. -/
theorem retained_code_resource_free_auth_obstruction
    {source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (closure identity) value demand requirements checking}
    (resourceFree : value.erase.erase.port.resources = []) :
    ¬ Auth operations policy ports owners environmentRows source valueRows rows := by
  intro authenticated
  have supported := authenticated.value_support (by simp [closure, Code.IsValue])
  have present := supported (retained_cell_dependency identity)
  rw [resourceFree] at present
  cases present

/-- Source construction itself can preserve the exact empty request row. Its
separate Auth lambda capture premise is the component that fails. -/
def pureValue : Value := .function .unit .unit [] [] (signature bodyPlan)

theorem pure_closure_source (issued : identity ∈ world) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (closure identity) pureValue [] empty .pure := by
  unfold closure pureValue empty
  refine SourcePlannedSources.Expression.lambda ?_ bodyOutward ?_ ?_
  · exact .bind (.reference issued) .unit
  · intro resource member
    simp [Value.erase, SourceDependencyAnnotations.Value.erase,
      CoherentSourceTypes.Value.port, ScopedPorts.Port.resources] at member
  · intro request member
    cases member

theorem pure_source_not_authenticated (issued : identity ∈ world) :
    ¬ Auth operations policy ports owners environmentRows
      (pure_closure_source (operations := operations) (policy := policy) (contracts := contracts)
        (allowed := allowed) (scope := scope) (environment := environment) issued)
      (.function .unit .unit (.sequence .pure .pure)) .pure := by
  apply retained_code_resource_free_auth_obstruction
  rfl

/-- The operation key itself contains no cell activation or resource argument.
Adding resources to its function input is not an exact-signature-preserving step. -/
def invokeEffect : Instance := .user 0 []

theorem invoke_key_resource_free : invokeEffect.resources = [] := rfl

def exactOperationPort : ScopedPorts.Port × ScopedPorts.Port :=
  (.function .unit .unit [], .unit)

def refinedOperationPort (identity : Nat) : ScopedPorts.Port × ScopedPorts.Port :=
  (.function .unit .unit [.cell identity], .unit)

theorem operation_port_strategy_mismatch (identity : Nat) :
    refinedOperationPort identity ≠ exactOperationPort := by
  simp [refinedOperationPort, exactOperationPort]

/-- The unchanged resource-free user operation can have a Source derivation
with this retained lambda operand. Auth.perform additionally needs its operand's
Auth derivation, excluded above at this unchanged pure operation input. -/
theorem request_source (known : operations invokeEffect 0 = some (pureValue, .unit))
    (admitted : invokeEffect ∈ allowed) (issued : identity ∈ world) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.perform (Instantiation.freezeEffect invokeEffect) 0 (closure identity)) .unit []
      (.emitAfter empty [] [⟨invokeEffect, 0, false⟩])
      (.sequence .pure (.request (effect := invokeEffect) (operation := 0))) := by
  apply SourcePlannedSources.Expression.perform known admitted (pure_closure_source issued)
  intro resource member
  cases member

/-- The existing independent type decoration keeps the pure exact row while
recording retained support separately. This data alone does not revise Auth. -/
example : CoreTypeSupport.decorate (.function .unit .unit [])
    (.function .unit .unit [.bound 3]) =
      .ok (.function .unit .unit [] [.bound 3]) := rfl

#print axioms retained_cell_dependency
#print axioms allowance_strategy_obstruction
#print axioms retained_code_resource_free_auth_obstruction
#print axioms pure_closure_source
#print axioms pure_source_not_authenticated
#print axioms operation_port_strategy_mismatch
#print axioms request_source
end Ash.OneShot.CoreHigherOrderSupport
