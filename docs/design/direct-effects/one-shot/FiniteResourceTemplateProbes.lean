import CoreCallableFiniteResourceTemplate
import ResourceFoundationProbes
import CoreTranslation
set_option maxRecDepth 10000
namespace Ash.OneShot.FiniteResourceTemplateProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableFiniteResourceTemplate
open CoreCallableFiniteCellRegistry

def original (contract : Contract) : CoreCallableStaticProducer.Bindings := [(7,contract),(9,.unit)]
def context : CoreCallableFiniteResourceTemplate.Context := [(7,.slot 0),(9,.slot 1)]
/-- Exact translated wrapper: ordinary handle 9 shadows the prior ordinary 9;
request reads that new handle, then returns original full slot 0 at name 7. -/
def body : Body context
    (.bind 9 (.resourceRef (.bound 3))
      (.bind 5 (.perform (.cell (.bound 3)) 0 (.variable 9)) (.variable 7))) (.slot 0) :=
  .bind (.reference (.bound 3))
    (.bind (.read (.variable .head)) (.variable (.tail (.tail .head))))

theorem accepted_composition (contract : Contract)
    (formed : CoreCallableGraphAnnotationChecks.subsetB contract.port.resources world = true) :
    resourceCheck body CoreCallableFiniteCellRegistry.original (original contract) 3 world [] allowed [(7,[])] [] = true := by
  have ports := CoreCallableGraphAnnotationChecks.subsetB_sound formed
  simp [resourceCheck,openingCheck,body,Body.check,LocalRef.check,ContractPattern.check,
    ContractPattern.closed,contextClosed,aligned,context,original,slotContract,CoreCallableFiniteCellRegistry.original,
    CellApi.check,allowedName,nameCheck,CoreCallableGraphAnnotationChecks.subsetB,
    CoreCallableGraphAnnotationChecks.knownB,LexicalBounds.lookup,Code.dependencies,
    ScopedPorts.Support.evaluate,LexicalBounds.environment,Syntax.without,effectAtoms,Instantiation.Effect.resources]
  exact ports

theorem accepted_with_receiver (contract : Contract)
    (formed : CoreCallableGraphAnnotationChecks.subsetB contract.port.resources world = true)
    (received : CoreCallableGraphAnnotationChecks.subsetB support receiver = true)
    (issued : CoreCallableGraphAnnotationChecks.subsetB receiver world = true) :
    resourceCheck body CoreCallableFiniteCellRegistry.original (original contract) 3 world [] allowed [(7,support)] receiver = true := by
  have ports := CoreCallableGraphAnnotationChecks.subsetB_sound formed
  have retained := CoreCallableGraphAnnotationChecks.subsetB_sound received
  have receiverIssued := CoreCallableGraphAnnotationChecks.subsetB_sound issued
  simp [resourceCheck,openingCheck,body,Body.check,LocalRef.check,ContractPattern.check,
    ContractPattern.closed,contextClosed,aligned,context,original,slotContract,CoreCallableFiniteCellRegistry.original,
    CellApi.check,allowedName,nameCheck,CoreCallableGraphAnnotationChecks.subsetB,
    CoreCallableGraphAnnotationChecks.knownB,LexicalBounds.lookup,Code.dependencies,
    ScopedPorts.Support.evaluate,LexicalBounds.environment,Syntax.without,effectAtoms,Instantiation.Effect.resources]
  exact ⟨⟨ports,retained⟩,receiverIssued⟩

theorem arbitrary_full_return (contract : Contract)
    (formed : CoreCallableGraphAnnotationChecks.subsetB contract.port.resources world = true) (payload : Int) :
    ResourceResult CoreCallableFiniteCellRegistry.original [] (fun _ => ⟨true,true⟩)
      outward owners world allowed scope (original contract) 3 payload body [(7,[])] [] :=
  check_resource body payload (accepted_composition contract formed)

theorem full_slot_preserved (contract : Contract) :
    (ContractPattern.slot 0).value (original contract) identity = contract := rfl

theorem identity_dependent_private_plan : body.dependencies 20 ≠ body.dependencies 21 := by
  intro same
  simp [body,Body.dependencies,nameValue] at same

def firstRequest : SourceDeclarationPlans.Plan dependencies → Option Instance
  | .request (effect := effect) => some effect
  | .sequence left right => (firstRequest left).or (firstRequest right)
  | _ => none

def resourceMemberEffect (plan : SourceDeclarationPlans.Plan dependencies) (identity : Nat) : Option Instance :=
  match plan with
  | .sequence _ (.resource family) => firstRequest (family identity)
  | _ => none

theorem computed_private_member (identity : Nat) : resourceMemberEffect body.resourcePlan identity = some (.cell identity) := rfl

theorem private_family_not_constant : resourceMemberEffect body.resourcePlan 20 ≠ resourceMemberEffect body.resourcePlan 21 := by decide

theorem shadowed_old_handle_rejected :
    (LocalRef.tail (bound := 9) (value := .reference (.bound 3))
      (LocalRef.head (name := 9) (pattern := .slot 1) (rest := []))).check = false := rfl

theorem numeric_resource_namespace :
    nameCheck 9 [] (.bound 9) = true ∧
    (.variable (.head (name := 9) (pattern := .reference (.bound 9)) (rest := [])) :
      Body [(9,.reference (.bound 9))] (.variable 9) (.reference (.bound 9))).check [] 9 [] [] = true := by decide

theorem fresh_reference_return_rejected :
    openingCheck (.reference (.bound 3) : Body [] (.resourceRef (.bound 3)) (.reference (.bound 3)))
      CoreCallableFiniteCellRegistry.original [] 3 [] [] [] [] = false := by simp [openingCheck,ContractPattern.closed]

theorem baseline_fixed_entries_cannot_supply_fresh_read :
    CoreCallableStaticProducer.operations [(.cell 0,0,.reference 0,.integer)] (.cell 7) 0 = none := rfl

theorem actual_api_supplies_fresh_read :
    (registry (some CoreCallableFiniteCellRegistry.original) [] (fun _ => ⟨true,true⟩)).operations (.cell 7) 0 =
      some (.reference 7,.integer) := read_known (by simp [CellApi.check,CoreCallableFiniteCellRegistry.original])

theorem renamed_api_is_not_original :
    (⟨3,readDeclaration 3,writeDeclaration 3,CoreExportedOperationMetadata.sourceManifest⟩ : CellApi).check = false := rfl

/-- Actual raw graph translation supplies this exact ordinary wrapper. The
result type is retained as graph data; this theorem does not assert validation. -/
def templateGraph (resultType : CoreSyntax.ValueType) : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 0) .integer,
  CoreTranslation.Examples.node 1 (.variable 9) (.reference (.bound 3)),
  CoreTranslation.Examples.node 2 (.request (.cell (.bound 3)) 0 1) .integer,
  CoreTranslation.Examples.node 3 (.variable 7) resultType,
  CoreTranslation.Examples.node 4 (.bind ⟨5,.integer⟩ 2 3) resultType,
  CoreTranslation.Examples.node 5 (.resource 3 ⟨9,.reference (.bound 3)⟩ 0 4) resultType],5⟩

theorem actual_graph_wrapper (resultType : CoreSyntax.ValueType)
    (shaped : CoreSyntax.checkShape (templateGraph resultType) = .ok ()) :
    CoreTranslation.translate (templateGraph resultType) = .ok
      (.resource 3 (.integer 0) (.bind 9 (.resourceRef (.bound 3))
        (.bind 5 (.perform (.cell (.bound 3)) 0 (.variable 9)) (.variable 7)))) := by
  simp only [CoreTranslation.translate,shaped]
  rfl

#print axioms accepted_composition
#print axioms accepted_with_receiver
#print axioms arbitrary_full_return
#print axioms full_slot_preserved
#print axioms identity_dependent_private_plan
#print axioms computed_private_member
#print axioms private_family_not_constant
#print axioms shadowed_old_handle_rejected
#print axioms numeric_resource_namespace
#print axioms fresh_reference_return_rejected
#print axioms baseline_fixed_entries_cannot_supply_fresh_read
#print axioms actual_api_supplies_fresh_read
#print axioms renamed_api_is_not_original
#print axioms actual_graph_wrapper
#print axioms ResourceFoundationProbes.retaining_lambda_rejected
#check CoreTranslation.resource_equation
end Ash.OneShot.FiniteResourceTemplateProbes
