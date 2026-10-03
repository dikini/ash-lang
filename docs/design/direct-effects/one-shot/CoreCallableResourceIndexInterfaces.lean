import CoreCallableResourceIndexData
import CoreCallableFiniteCellRegistry

/-! Upstream resource indices retain full opaque contracts and checking data.
This interface does not import producer or resource source proof modules. -/
namespace Ash.OneShot.CoreCallableResourceIndexInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableStaticProducer (Bindings RecipeTag)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows

#check CoreCallableFiniteResourceTemplate.nameValue
#check CoreCallableFiniteResourceTemplate.nameCheck
#check CoreCallableFiniteResourceTemplate.ContractPattern
#check CoreCallableFiniteResourceTemplate.slotContract
#check CoreCallableFiniteResourceTemplate.ContractPattern.value
#check CoreCallableFiniteResourceTemplate.ContractPattern.check
#check CoreCallableFiniteResourceTemplate.ContractPattern.closed
#check CoreCallableFiniteResourceTemplate.Context
#check CoreCallableFiniteResourceTemplate.bindings
#check CoreCallableFiniteResourceTemplate.contextClosed
#check CoreCallableFiniteResourceTemplate.aligned
#check CoreCallableFiniteResourceTemplate.contextTemplate
#check CoreCallableFiniteResourceTemplate.LocalRef
#check CoreCallableFiniteResourceTemplate.LocalRef.check
#check CoreCallableFiniteResourceTemplate.LocalRef.realize
#check CoreCallableFiniteResourceTemplate.Body
#check CoreCallableFiniteResourceTemplate.allowedName
#check CoreCallableFiniteResourceTemplate.Body.check
#check CoreCallableFiniteResourceTemplate.Body.dependencies
#check CoreCallableFiniteResourceTemplate.Body.plan
#check CoreCallableFiniteResourceTemplate.Body.rows
#check CoreCallableFiniteResourceTemplate.Body.requirements
#check CoreCallableFiniteResourceTemplate.outsideName
#check CoreCallableFiniteResourceTemplate.Body.outsideRequirements
#check CoreCallableFiniteResourceTemplate.Body.resourcePlan
#check CoreCallableFiniteResourceTemplate.Body.resourceRows
#check CoreCallableCompositionalResourceBody.EffectName
#check CoreCallableCompositionalResourceBody.EffectName.value
#check CoreCallableCompositionalResourceBody.EffectName.check
#check CoreCallableCompositionalResourceBody.EffectName.outside
#check CoreCallableCompositionalResourceBody.RequestName
#check CoreCallableCompositionalResourceBody.RequestName.value
#check CoreCallableCompositionalResourceBody.Checking
#check CoreCallableCompositionalResourceBody.Checking.dependencies
#check CoreCallableCompositionalResourceBody.Checking.plan
#check CoreCallableCompositionalResourceBody.Checking.rows
#check CoreCallableCompositionalResourceBody.oldRecipe
#check CoreCallableCompositionalResourceBody.Checking.recipe
#check CoreCallableCompositionalResourceBody.Checking.check
#check CoreCallableCompositionalResourceBody.Need
#check CoreCallableCompositionalResourceBody.Need.requirements
#check CoreCallableCompositionalResourceBody.oldSummary
#check CoreCallableCompositionalResourceBody.Need.summary
#check CoreCallableCompositionalResourceBody.Pattern
#check CoreCallableCompositionalResourceBody.Pattern.value
#check CoreCallableCompositionalResourceBody.Context
#check CoreCallableCompositionalResourceBody.bindings
#check CoreCallableCompositionalResourceBody.Ref
#check CoreCallableCompositionalResourceBody.Ref.check
#check CoreCallableCompositionalResourceBody.Ref.realize
#check CoreCallableCompositionalResourceBody.FunctionSlot
#check CoreCallableCompositionalResourceBody.closedRequests
#check CoreCallableCompositionalResourceBody.Body
#check CoreCallableCompositionalResourceBody.lookup
#check CoreCallableCompositionalResourceBody.oldLookup
#check CoreCallableCompositionalResourceBody.sameOld
#check CoreCallableCompositionalResourceBody.embeddingCheck
#check CoreCallableCompositionalResourceBody.Pattern.check
#check CoreCallableCompositionalResourceBody.Checking.isClosed
#check CoreCallableCompositionalResourceBody.Pattern.isClosed
#check CoreCallableCompositionalResourceBody.EffectName.canonical
#check CoreCallableCompositionalResourceBody.effectsSubset
#check CoreCallableCompositionalResourceBody.Body.check
#check CoreCallableCompositionalResourceBody.CheckingValue
#check CoreCallableCompositionalResourceBody.Checking.value
#check CoreCallableCompositionalResourceBody.sequenceValue
#check CoreCallableCompositionalResourceBody.choiceValue
#check CoreCallableCompositionalResourceBody.functionValue
#check CoreCallableCompositionalResourceBody.Need.valid
#check CoreCallableCompositionalResourceBody.outsideRequests
#check CoreCallableCompositionalResourceBody.Need.outsideRequirements
#check CoreCallableCompositionalResourceBody.oldContext
#check CoreCallableCompositionalResourceBody.aligned
#check CoreCallableCompositionalResourceBody.Checking.closed
#check CoreCallableCompositionalResourceBody.FunctionSlot.head
#check CoreCallableCompositionalResourceBody.Body.slotCallable
#check CoreCallableFiniteCellRegistry.operations
#check CoreCallableFiniteCellRegistry.registry
#check CoreCallableFiniteCellRegistry.checked_source_identity

 theorem full_contract (contract : Contract) (original : Bindings) (identity : Nat) :
    (CoreCallableCompositionalResourceBody.Pattern.closed contract).value original identity =
      contract := rfl

 theorem full_checking {dependencies : Dependencies} (plan : Plan dependencies)
    (rows : Rows (signature plan)) (recipe : RecipeTag plan) (identity : Nat) :
    (CoreCallableCompositionalResourceBody.Checking.closed plan rows recipe).value identity =
      ⟨dependencies,plan,rows⟩ := rfl

 theorem full_recipe {dependencies : Dependencies} (plan : Plan dependencies)
    (rows : Rows (signature plan)) (recipe : RecipeTag plan) (identity : Nat) :
    (CoreCallableCompositionalResourceBody.Checking.closed plan rows recipe).recipe identity =
      recipe := rfl

 theorem selected_cell_declaration (api : CoreCallableFiniteCellRegistry.CellApi)
    (accepted : api.check = true) (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) (identity : Nat) :
    (CoreCallableFiniteCellRegistry.registry (some api) entries policy).operations
      (.cell identity) 0 = some (.reference identity,.integer) :=
  CoreCallableFiniteCellRegistry.read_known accepted

#print axioms full_contract
#print axioms full_checking
#print axioms full_recipe
#print axioms selected_cell_declaration
end Ash.OneShot.CoreCallableResourceIndexInterfaces
