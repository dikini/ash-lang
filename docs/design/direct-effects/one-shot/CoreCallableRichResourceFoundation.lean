import CoreCallableStorageRecipes
import CoreCallableRestoredChecking

/-! Resource foundation for the existing rich fragment. The formal-return
consumer takes an already produced paired argument; it does not enlarge the
finite annotation grammar or assume source/authentication for its resource body. -/
namespace Ash.OneShot.CoreCallableRichResourceFoundation
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract sequenceRows)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableStorageRecipes
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

def formalPlan : Plan (.sequence .pure (.resource (fun _ => .pure))) :=
  .sequence .pure (.resource (fun _ => .pure))
def formalRows : Rows (signature formalPlan) := sequenceRows Rows.pure (Rows.resource (fun _ => Rows.pure))

/-- This finite full-contract receipt produces every fresh rich opening of
SAME formal-return template, plus its independent original-map storage receipt.
The resource binder never shadows the ordinary formal, even when names coincide. -/
theorem formal_resource_foundation
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
    {current : CoreCallablePairedOrigin.Admission root body bindings lexical records storageBody storageBodyResult
      policy declarations outward call.world allowed scope call.receiver originalBound}
    {annotation : CoreCallableStaticProducer.Annotation entries owners richBindings value input
      valueDemand valueReq valuePlan valueRows}
    (argument : ArgumentReceipt call current annotation actualInst argumentRecipe)
    (inst : Instantiation.Environment) (binder formal : Nat) (payload : Int) :
    ∃ source : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward owners
        call.world allowed .none (CoreCallableStaticProducer.environment ((formal,input) :: richBindings))
        (.resource binder (.integer payload) (.variable formal)) input []
        (.sequence (.request [] []) (.request [] [])) formalPlan formalRows,
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward source
        (lexical.extend formal call.argument) call.receiver ∧
      CallableContracts.Derives declarations
        (CoreCallableReturnStorageProducer.environment
          (CoreCallableReturnStorageProducer.extend bindings formal argument.stored))
        call.world .none (.resource binder (.integer payload) (.variable formal)) argument.stored ∧
      (∀ identity, identity ∉ call.world →
        CallableContracts.Derives declarations
          (CoreCallableReturnStorageProducer.environment
            (CoreCallableReturnStorageProducer.extend bindings formal argument.stored))
          (call.world ++ [identity]) .none
          ((Code.variable formal).instantiate (inst.bind binder identity)) argument.stored ∧
        argument.stored.storageOf ⊆ call.receiver ∧ identity ∉ argument.stored.storageOf) ∧
      (∀ identity, contract (CoreCallableReturnStorageProducer.extend bindings formal argument.stored)
          (inst.bind binder identity) (.slot formal) = some argument.stored) := by
  have formed : ScopedPorts.InWorld call.world input.port :=
    ScopedPorts.typed_result_in_world
      ((argument.rich.source.value_allowed argument.closed.1 allowed .none).erase)
  have known : CoreCallableStaticProducer.environment ((formal,input) :: richBindings) formal = some input := by
    simp [CoreCallableStaticProducer.environment, CoreCallableContractSource.Environment.extend]
  let opened := fun identity (_fresh : identity ∉ call.world) =>
    (IndexedSource.variable (registry := CoreCallableStaticProducer.registry entries policy)
      (outward := outward) (owners := owners) (allowed := .cell identity :: []) (scope := .none)
      known (ScopedPorts.in_world_mono formed
        (by intro id member; exact List.mem_append_left [identity] member)))
  have hidden : ∀ identity, identity ∉ call.world →
      ResourceRequirements.Hides identity (Requirements.request [] []) (.request [] []) :=
    fun _ _ => .request
  let source := IndexedSource.resource (allowed := allowed) (binder := binder) (code := .variable formal)
    (IndexedSource.integer (value := payload)) (fun identity fresh => by
      simpa only [Code.instantiate] using opened identity fresh)
    formed (List.nil_subset _) (List.nil_subset _) hidden
  have bodyAuth : ∀ identity (fresh : identity ∉ call.world),
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward
        (opened identity fresh) (lexical.extend formal call.argument) (identity :: call.receiver) := by
    intro identity fresh
    refine .checked ?_ (.variable (known := known) (formed := ScopedPorts.in_world_mono formed
      (by intro id member; exact List.mem_append_left [identity] member)) ⟨call.argument, by simp [LexicalBounds.lookup, LexicalBounds.extend]⟩)
    apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
    simpa [Code.dependencies, ScopedPorts.Support.evaluate, LexicalBounds.environment_extend,
      ScopedPorts.Support.extend] using
      (show call.argument ⊆ identity :: call.receiver from
        fun id member => List.mem_cons_of_mem _ (call.argumentReceived member))
  have auth : Authenticated (CoreCallableStaticProducer.registry entries policy) outward source
      (lexical.extend formal call.argument) call.receiver := by
    refine .checked ?_ (Hereditary.resource (bodySource := fun identity fresh => by
      simpa only [Code.instantiate] using opened identity fresh) (formed := formed)
      (effectsBound := List.nil_subset _) (admitted := List.nil_subset _) (hidden := hidden)
      (.checked (by constructor) .integer) bodyAuth)
    apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
    simpa [Code.dependencies, ScopedPorts.Support.evaluate, LexicalBounds.environment_extend,
      ScopedPorts.Support.extend] using call.argumentReceived
  have initialAccepted : check (CoreCallableReturnStorageProducer.extend bindings formal argument.stored)
      inst (.integer payload) (.node (some (.storage [])) []) = some (.storage []) := by
    simp [check, specialize, specializeList, contract, bound,
      CoreCallableReturnStorageProducer.check, CoreCallableReturnStorageProducer.captureCheck,
      Code.dependencies]
  exact ⟨source, auth, formal_resource_storage argument initialAccepted,
    fun identity fresh => formal_opening_receipt argument inst binder formal identity fresh,
    fun identity => formal_slot_specialization bindings formal argument.stored (inst.bind binder identity)⟩

#print axioms formal_resource_foundation
end Ash.OneShot.CoreCallableRichResourceFoundation
