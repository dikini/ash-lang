import CoreCallableFiniteResourceTemplate
set_option maxRecDepth 10000
namespace Ash.OneShot.CoreCallableFiniteResourceConsumers
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableReceiverRefinement CoreCallableStorageRecipes
open CoreCallableFiniteResourceTemplate
local instance : SourcePlannedChecks.DeclarationPolicy := SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- SAME finite body over the full original ordinary environment. -/
def fullBody (original : CoreCallableStaticProducer.Bindings) :
    Body ((7,.slot 0) :: contextTemplate original 1)
      (.bind 9 (.resourceRef (.bound 3))
        (.bind 5 (.perform (.cell (.bound 3)) 0 (.variable 9)) (.variable 7))) (.slot 0) :=
  .bind (.reference (.bound 3)) (.bind (.read (.variable .head)) (.variable (.tail (.tail .head))))

private theorem full_accepted {lexical : LexicalBounds} (input : Contract) (original : CoreCallableStaticProducer.Bindings)
    (formed : ScopedPorts.InWorld world input.port) (received : support ⊆ receiver) (issued : receiver ⊆ world) :
    resourceCheck (fullBody original) CoreCallableFiniteCellRegistry.original ((7,input)::original) 3 world [] allowed
      (lexical.extend 7 support) receiver = true := by
  have aligned := contextTemplate_aligned ((7,input)::original) 0
  have closed := contextTemplate_closed ((7,input)::original) 0
  simp only [contextTemplate] at aligned closed
  simp [resourceCheck,openingCheck,fullBody,Body.check,LocalRef.check,ContractPattern.check,
    ContractPattern.closed,closed,aligned,slotContract,CoreCallableFiniteCellRegistry.original,
    CoreCallableFiniteCellRegistry.CellApi.check,allowedName,nameCheck,CoreCallableGraphAnnotationChecks.subsetB,
    CoreCallableGraphAnnotationChecks.knownB,LexicalBounds.lookup,LexicalBounds.extend,Code.dependencies,
    ScopedPorts.Support.evaluate,LexicalBounds.environment,Syntax.without,effectAtoms,Instantiation.Effect.resources]
  exact ⟨⟨formed,received⟩,issued⟩

/-- The full returned slot is taken from a produced SAME paired argument.
The new cell registry is explicit; this does not transport old Admission. -/
theorem paired_compositional_source
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {annotationBody : CoreCallableStaticProducer.Annotation entries owners richBindings bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
    {current : CoreCallablePairedOrigin.Admission root annotationBody storageBindings lexical records storageBody storageBodyResult
      policy declarations outward call.world allowed scope call.receiver originalBound}
    {annotation : CoreCallableStaticProducer.Annotation entries owners richBindings value input valueDemand valueReq valuePlan valueRows}
    (argument : ArgumentReceipt call current annotation actualInst argumentRecipe) (payload : Int) :
    ResourceResult CoreCallableFiniteCellRegistry.original entries policy outward owners call.world allowed scope
      ((7,input)::richBindings) 3 payload (fullBody richBindings) (lexical.extend 7 call.argument) call.receiver := by
  have formed : ScopedPorts.InWorld call.world input.port := ScopedPorts.typed_result_in_world
    ((argument.rich.source.value_allowed argument.closed.1 allowed .none).erase)
  exact check_resource (fullBody richBindings) payload (full_accepted input richBindings formed call.argumentReceived call.receivingIssued)

/-- Lower storage construction for the SAME compositional body and actual map.
The request's scalar result is supplied by the existing builtin declaration
signature, not by a storage recipe or a future derivation annotation. -/
theorem paired_compositional_storage
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {annotationBody : CoreCallableStaticProducer.Annotation entries owners richBindings bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
    {current : CoreCallablePairedOrigin.Admission root annotationBody storageBindings lexical records storageBody storageBodyResult
      policy declarations outward call.world allowed scope call.receiver originalBound}
    {annotation : CoreCallableStaticProducer.Annotation entries owners richBindings value input valueDemand valueReq valuePlan valueRows}
    (argument : ArgumentReceipt call current annotation actualInst argumentRecipe)
    (identity : Nat) (fresh : identity ∉ call.world) :
    CallableContracts.Derives declarations
      (CoreCallableReturnStorageProducer.environment (CoreCallableReturnStorageProducer.extend storageBindings 7 argument.stored))
      (call.world ++ [identity]) .none
      ((Code.bind 9 (.resourceRef (.bound 3))
        (.bind 5 (.perform (.cell (.bound 3)) 0 (.variable 9)) (.variable 7))).instantiate
          (Instantiation.Environment.empty.bind 3 identity)) argument.stored ∧
    argument.stored.storageOf ⊆ call.receiver ∧ identity ∉ argument.stored.storageOf := by
  have formal := formal_opening_receipt argument Instantiation.Environment.empty 3 7 identity fresh
  refine ⟨?_,formal.2.1,formal.2.2⟩
  have reference : CallableContracts.Derives declarations
      (CoreCallableReturnStorageProducer.environment (CoreCallableReturnStorageProducer.extend storageBindings 7 argument.stored))
      (call.world ++ [identity]) .none (.resourceRef (.activation identity)) (.storage [identity]) :=
    .leaf trivial rfl (.cons (.resource (by simp)) .nil)
  have read : CallableContracts.Derives declarations
      ((CoreCallableReturnStorageProducer.environment (CoreCallableReturnStorageProducer.extend storageBindings 7 argument.stored)).extend 9 (.storage [identity]))
      (call.world ++ [identity]) .none (.perform (.cell (.activation identity)) 0 (.variable 9)) (.storage []) :=
    .perform (requested := .cell identity) (operation := 0) (input := .reference identity) (output := .integer) (operandContract := .storage [identity])
      (.variable (by simp [CallableContracts.Environment.extend])) rfl rfl
  have returned : CallableContracts.Derives declarations
      (((CoreCallableReturnStorageProducer.environment (CoreCallableReturnStorageProducer.extend storageBindings 7 argument.stored)).extend 9 (.storage [identity])).extend 5 (.storage []))
      (call.world ++ [identity]) .none (.variable 7) argument.stored :=
    .variable (by simp [CallableContracts.Environment.extend,CoreCallableReturnStorageProducer.environment,
      CoreCallableReturnStorageProducer.extend,CoreCallableReturnStorageProducer.lookup])
  simpa [Code.instantiate,Instantiation.Effect.instantiate,Instantiation.ResourceName.instantiate,Instantiation.Environment.bind] using
    (CallableContracts.Derives.bind reference (.bind read returned))

#print axioms paired_compositional_source
#print axioms paired_compositional_storage
end Ash.OneShot.CoreCallableFiniteResourceConsumers
