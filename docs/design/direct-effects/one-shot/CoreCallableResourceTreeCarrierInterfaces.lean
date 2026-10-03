import CoreCallableStaticTreeCarrier
import CoreCallableCompositionalResourceBody

/-! Public interfaces retain the original complete dependent tree and computed
resource derivations. This module has no producer/checker ancestor. -/
namespace Ash.OneShot.CoreCallableResourceTreeCarrierInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableStaticProducer (StaticTree Bindings)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

#check CoreCallableStaticProducer.StaticTree
#check CoreCallableStaticProducer.StaticTree.unit
#check CoreCallableStaticProducer.StaticTree.boolean
#check CoreCallableStaticProducer.StaticTree.integer
#check CoreCallableStaticProducer.StaticTree.reference
#check CoreCallableStaticProducer.StaticTree.variable
#check CoreCallableStaticProducer.StaticTree.pair
#check CoreCallableStaticProducer.StaticTree.bind
#check CoreCallableStaticProducer.StaticTree.app
#check CoreCallableStaticProducer.StaticTree.resume
#check CoreCallableStaticProducer.StaticTree.discard
#check CoreCallableStaticProducer.StaticTree.cleanup
#check CoreCallableStaticProducer.StaticTree.perform
#check CoreCallableStaticProducer.StaticTree.branch
#check CoreCallableStaticProducer.StaticTree.lambda
#check CoreCallableStaticProducer.StaticTree.resource
#check CoreCallableStaticProducer.StaticTree.receiverLambda
#check CoreCallableStaticProducer.StaticTree.authenticate_world
#check CoreCallableStaticProducer.StaticTree.outward
#check CoreCallableFiniteResourceTemplate.Derived
#check CoreCallableFiniteResourceTemplate.Body.derive
#check CoreCallableFiniteResourceTemplate.Opening
#check CoreCallableFiniteResourceTemplate.check_opening
#check CoreCallableFiniteResourceTemplate.ResourceResult
#check CoreCallableFiniteResourceTemplate.check_resource
#check CoreCallableCompositionalResourceBody.Derived
#check CoreCallableCompositionalResourceBody.Body.derive
#check CoreCallableCompositionalResourceBody.Basic
#check CoreCallableCompositionalResourceBody.StaticTree.rebase_basic
#check CoreCallableCompositionalResourceBody.FunctionSlot
#check CoreCallableCompositionalResourceBody.FunctionSlot.exact
#check CoreCallableCompositionalResourceBody.Checking
#check CoreCallableCompositionalResourceBody.Checking.plan
#check CoreCallableCompositionalResourceBody.Checking.rows
#check CoreCallableCompositionalResourceBody.Need.hides

 theorem full_authentication
    {source : IndexedSource actualRegistry outward owners world allowed scope valueEnvironment
      code contract demand requirements plan rows}
    (tree : StaticTree actualRegistry outward source) (larger : world ⊆ later)
    {lexical : LexicalBounds} {receiver : List Nat}
    (known : CoreCallableContractAdmission.LexicalBounds.Known lexical code.dependencies)
    (bounds : SourceSupport.Bounds lexical.environment code.dependencies receiver) :
    Authenticated actualRegistry outward (source.world_weaken larger) lexical receiver :=
  tree.authenticate_world larger known bounds

 theorem full_outward
    {source : IndexedSource actualRegistry outward owners world allowed scope valueEnvironment
      code contract demand requirements plan rows}
    (tree : StaticTree actualRegistry outward source) (normal : scope = .none) :
    ∃ row, RecursiveOutward.Outward requirements row := tree.outward normal

 theorem template_derived_tree
    (body : CoreCallableFiniteResourceTemplate.Body context code pattern)
    (api : CoreCallableFiniteCellRegistry.CellApi)
    (apiValid : api.check = true) (accepted : body.check original binder world residual = true) :
    StaticTree (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward
      (body.derive (entries := entries) (policy := policy) (outward := outward)
        (owners := owners) (scope := scope) (identity := identity) apiValid accepted).source :=
  (body.derive (entries := entries) (policy := policy) (outward := outward)
    (owners := owners) (scope := scope) (identity := identity) apiValid accepted).tree

 theorem compositional_derived_tree
    (body : CoreCallableCompositionalResourceBody.Body original context code pattern checking needs)
    (api : CoreCallableFiniteCellRegistry.CellApi)
    (apiValid : api.check = true) (accepted : body.check original binder world residual allowed = true) :
    StaticTree (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward
      (body.derive (entries := entries) (policy := policy) (outward := outward)
        (owners := owners) (scope := scope) (identity := identity) apiValid accepted).source :=
  (body.derive (entries := entries) (policy := policy) (outward := outward)
    (owners := owners) (scope := scope) (identity := identity) apiValid accepted).tree

#print axioms full_authentication
#print axioms full_outward
#print axioms template_derived_tree
#print axioms compositional_derived_tree
end Ash.OneShot.CoreCallableResourceTreeCarrierInterfaces
