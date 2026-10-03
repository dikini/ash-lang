import CoreCallableCompositionalResourceOpening

/-! Generic interfaces for computed resource tree provenance. The finite checker
still supplies the same full indices; no annotation grammar is added here. -/
namespace Ash.OneShot.CoreCallableResourceTreeInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableCompositionalResourceBody
open CoreCallableCompositionalResourceOpening
open CoreCallableStaticProducer (StaticTree)
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Future-world authentication follows from the SAME successful resource
checker output and actual lexical support, with literal private data retained. -/
theorem checked_authenticate_world
    {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows}
    {body : Body original context code pattern checking needs}
    {receipt : PLift (Result api entries policy outward owners world residual allowed scope
      original binder annotation body lexical receiver)}
    (accepted : check_compositional annotation body api policy outward world residual allowed
      scope binder lexical receiver = .ok receipt)
    (larger : world ⊆ later) (nextLexical : LexicalBounds) (nextReceiver : List Nat)
    (known : LexicalBounds.Known nextLexical (Code.resource binder initial code).dependencies)
    (bounds : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds
      nextLexical.environment (Code.resource binder initial code).dependencies nextReceiver) :
    Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward
      (receipt.down.source.world_weaken larger) nextLexical nextReceiver :=
  (check_compositional_tree accepted).authenticate_world larger known bounds

/-- Outward interpretation comes from the computed tree at empty execution
scope, retaining the original initializer and exact hidden body requirements. -/
theorem checked_outward
    {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows}
    {body : Body original context code pattern checking needs}
    {receipt : PLift (Result api entries policy outward owners world residual allowed scope
      original binder annotation body lexical receiver)}
    (accepted : check_compositional annotation body api policy outward world residual allowed
      scope binder lexical receiver = .ok receipt)
    (normal : scope = .none) :
    ∃ row, RecursiveOutward.Outward (.sequence initialReq needs.outsideRequirements) row :=
  (check_compositional_tree accepted).outward normal

#check @StaticTree.resource
#check @CoreCallableFiniteRegistryBridge.transfer_tree
#check @check_opening_tree
#check @check_compositional_tree
#print axioms checked_authenticate_world
#print axioms checked_outward
#print axioms CoreCallableStaticProducer.StaticTree.authenticate_world
#print axioms CoreCallableStaticProducer.StaticTree.outward
#print axioms CoreCallableFiniteRegistryBridge.transfer_tree
#print axioms CoreCallableCompositionalResourceOpening.check_compositional_tree
end Ash.OneShot.CoreCallableResourceTreeInterfaces
