import CoreCallablePairedOrigin

namespace Ash.OneShot.CoreCallableStorageRecipes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableReceiverRefinement (CallBounds LexicalBounds)
open CoreCallableContractSource (Contract)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission

local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Finite capture instructions refer to the actual paired binding storage,
not public ports. Resource binders use the SAME opening environment as Code. -/
inductive BoundAtom where
  | activation : Nat → BoundAtom
  | resourceBinder : Nat → BoundAtom
  | slot : Nat → BoundAtom
  deriving Repr

def atom (bindings : CoreCallableReturnStorageProducer.Bindings) (inst : Instantiation.Environment) : BoundAtom → Option (List Nat)
  | .activation identity => some [identity]
  | .resourceBinder binder => (inst binder).map fun identity => [identity]
  | .slot name => (CoreCallableReturnStorageProducer.lookup bindings name).map CallableContracts.Contract.storageOf

def bound (bindings : CoreCallableReturnStorageProducer.Bindings) (inst : Instantiation.Environment) : List BoundAtom → Option (List Nat)
  | [] => some []
  | head :: tail => do
      let first ← atom bindings inst head
      let rest ← bound bindings inst tail
      return first ++ rest

/-- A slot preserves the exact actual storage domain/result tree. -/
inductive ContractTemplate where
  | slot : Nat → ContractTemplate
  | storage : List BoundAtom → ContractTemplate
  | pair : ContractTemplate → ContractTemplate → ContractTemplate
  | function : List BoundAtom → ContractTemplate → ContractTemplate → ContractTemplate
  deriving Repr

def contract (bindings : CoreCallableReturnStorageProducer.Bindings) (inst : Instantiation.Environment) : ContractTemplate → Option CallableContracts.Contract
  | .slot name => CoreCallableReturnStorageProducer.lookup bindings name
  | .storage atoms => (bound bindings inst atoms).map .storage
  | .pair left right => do return .pair (← contract bindings inst left) (← contract bindings inst right)
  | .function captures input output => do
      return .function (← bound bindings inst captures) (← contract bindings inst input) (← contract bindings inst output)

/-- Structural annotation recipes carry no Source/Auth/Derives judgments. -/
inductive Recipe where
  | node : Option ContractTemplate → List Recipe → Recipe
  deriving Repr

mutual
def specialize (bindings : CoreCallableReturnStorageProducer.Bindings) (inst : Instantiation.Environment) : Recipe → Option CoreCallableReturnStorageProducer.Annotation
  | .node none children => do return .node none (← specializeList bindings inst children)
  | .node (some template) children => do return .node (some (← contract bindings inst template)) (← specializeList bindings inst children)
termination_by recipe => sizeOf recipe
decreasing_by all_goals simp_wf; all_goals omega

def specializeList (bindings : CoreCallableReturnStorageProducer.Bindings) (inst : Instantiation.Environment) : List Recipe → Option (List CoreCallableReturnStorageProducer.Annotation)
  | [] => some []
  | head :: tail => do return (← specialize bindings inst head) :: (← specializeList bindings inst tail)
termination_by recipes => sizeOf recipes
decreasing_by all_goals simp_wf; all_goals omega
end

def check (bindings : CoreCallableReturnStorageProducer.Bindings) (inst : Instantiation.Environment)
    (code : Code) (recipe : Recipe) : Option CallableContracts.Contract := do
  let annotation ← specialize bindings inst recipe
  CoreCallableReturnStorageProducer.check bindings code annotation

theorem check_sound (accepted : check bindings inst code recipe = some result) :
    CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment bindings) world ticket code result := by
  cases specialized : specialize bindings inst recipe with
  | none => simp [check, specialized] at accepted
  | some annotation =>
      simp [check, specialized] at accepted
      exact CoreCallableReturnStorageProducer.check_sound accepted


/-- Every identity opens the SAME literal Code at its actual binder. No
representative family member or alternate body is checked. -/
def opening (bindings : CoreCallableReturnStorageProducer.Bindings) (inst : Instantiation.Environment)
    (binder identity : Nat) (code : Code) (recipe : Recipe) (originalBound : List Nat) : Option CallableContracts.Contract := do
  let opened := inst.bind binder identity
  let result ← check bindings opened (code.instantiate opened) recipe
  if result.storageOf ⊆ originalBound then some result else none

theorem opening_sound (accepted : opening bindings inst binder identity code recipe originalBound = some result) :
    CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment bindings) (world ++ [identity]) ticket
      (code.instantiate (inst.bind binder identity)) result ∧ result.storageOf ⊆ originalBound := by
  cases checked : check bindings (inst.bind binder identity) (code.instantiate (inst.bind binder identity)) recipe with
  | none => simp [opening, checked] at accepted
  | some actual =>
      simp [opening, checked] at accepted
      rcases accepted with ⟨bounded, rfl⟩
      exact ⟨check_sound checked, bounded⟩


/-- An actual paired argument is checker OUTPUT. Old CallBounds supplies only
world/resource inclusions, not this full storage contract or value origin. -/
structure ArgumentReceipt
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
    (call : CallBounds creationWorld)
    (current : CoreCallablePairedOrigin.Admission root body bindings lexical records storageBody storageBodyResult
      policy declarations outward call.world allowed scope call.receiver originalBound)
    (argument : CoreCallableStaticProducer.Annotation entries owners richBindings value input valueDemand valueReq valuePlan valueRows)
    (inst : Instantiation.Environment) (recipe : Recipe) where
  rich : CoreCallableStaticProducer.Result entries policy outward owners call.world allowed scope richBindings
    value input valueDemand valueReq valuePlan valueRows lexical call.receiver
  richAccepted : CoreCallableStaticProducer.check argument policy outward call.world allowed scope lexical call.receiver = .ok rich
  stored : CallableContracts.Contract
  storageAccepted : check bindings inst value recipe = some stored
  storageDerived : CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment bindings) call.world .none value stored
  argumentBounded : stored.storageOf ⊆ call.argument
  closed : ClosedValue value

def pair_argument
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
    (call : CallBounds creationWorld)
    (current : CoreCallablePairedOrigin.Admission root body bindings lexical records storageBody storageBodyResult
      policy declarations outward call.world allowed scope call.receiver originalBound)
    (argument : CoreCallableStaticProducer.Annotation entries owners richBindings value input valueDemand valueReq valuePlan valueRows)
    (inst : Instantiation.Environment) (recipe : Recipe) (closed : ClosedValue value) :
    Except CoreCallablePairedOrigin.Error (ArgumentReceipt call current argument inst recipe) := do
  match richAccepted : CoreCallableStaticProducer.check argument policy outward call.world allowed scope lexical call.receiver with
  | .error error => .error (.rich error)
  | .ok rich =>
      match accepted : check bindings inst value recipe with
      | none => .error .storageInitializer
      | some stored =>
          if bounded : decide (stored.storageOf ⊆ call.argument) = true then
            return ⟨rich, richAccepted, stored, accepted, check_sound accepted, of_decide_eq_true bounded, closed⟩
          else .error .storageReceiver


/-- Generic full-contract formal return. It applies to arbitrary actual
higher-order domains/results, not a fixed callable signature or example. -/
theorem formal_opening
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
    {current : CoreCallablePairedOrigin.Admission root body bindings lexical records storageBody storageBodyResult
      policy declarations outward call.world allowed scope call.receiver originalBound}
    (argument : ArgumentReceipt call current annotation actualInst argumentRecipe)
    (inst : Instantiation.Environment) (binder formal identity : Nat) :
    opening (CoreCallableReturnStorageProducer.extend bindings formal argument.stored) inst binder identity
      (.variable formal) (.node none []) call.receiver = some argument.stored := by
  have bounded := argument.argumentBounded.trans call.argumentReceived
  simp [opening, check, specialize, specializeList, CoreCallableReturnStorageProducer.check,
    CoreCallableReturnStorageProducer.lookup, CoreCallableReturnStorageProducer.extend, Code.instantiate, bounded]


theorem ArgumentReceipt.fresh_excluded
    (argument : ArgumentReceipt call current annotation actualInst argumentRecipe)
    (fresh : identity ∉ call.world) : identity ∉ argument.stored.storageOf :=
  fun retained => fresh ((argument.argumentBounded.trans (call.argumentReceived.trans call.receivingIssued)) retained)

/-- The full actual contract and exact opened expression are retained for every
fresh identity; richer private plan/row families are not rewritten here. -/
theorem formal_opening_receipt
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
    {current : CoreCallablePairedOrigin.Admission root body bindings lexical records storageBody storageBodyResult
      policy declarations outward call.world allowed scope call.receiver originalBound}
    (argument : ArgumentReceipt call current annotation actualInst argumentRecipe)
    (inst : Instantiation.Environment) (binder formal identity : Nat) (fresh : identity ∉ call.world) :
    CallableContracts.Derives declarations
      (CoreCallableReturnStorageProducer.environment (CoreCallableReturnStorageProducer.extend bindings formal argument.stored))
      (call.world ++ [identity]) .none ((Code.variable formal).instantiate (inst.bind binder identity)) argument.stored ∧
      argument.stored.storageOf ⊆ call.receiver ∧ identity ∉ argument.stored.storageOf := by
  have accepted := formal_opening argument inst binder formal identity
  obtain ⟨derived, bounded⟩ := opening_sound (declarations := declarations) (world := call.world) (ticket := .none) accepted
  exact ⟨derived, bounded, argument.fresh_excluded fresh⟩

/-- A generic storage resource derivation for returning the actual formal.
Initializer evidence is a check on the SAME initializer, not a future body. -/
theorem formal_resource_storage
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
    {current : CoreCallablePairedOrigin.Admission root body bindings lexical records storageBody storageBodyResult
      policy declarations outward call.world allowed scope call.receiver originalBound}
    (argument : ArgumentReceipt call current annotation actualInst argumentRecipe)
    (initializerAccepted : check (CoreCallableReturnStorageProducer.extend bindings formal argument.stored)
      inst initializer initializerRecipe = some initializerContract) :
    CallableContracts.Derives declarations
      (CoreCallableReturnStorageProducer.environment (CoreCallableReturnStorageProducer.extend bindings formal argument.stored))
      call.world .none (.resource binder initializer (.variable formal)) argument.stored := by
  have initial := check_sound (declarations := declarations) (world := call.world) (ticket := .none) initializerAccepted
  refine .resource initial ?_ ?_ (argument.argumentBounded.trans (call.argumentReceived.trans call.receivingIssued))
  · simpa [Code.ResourceClosed, Code.freeNames] using CallableContracts.resource_closed initial
  · intro identity fresh
    exact (formal_opening_receipt argument Instantiation.Environment.empty binder formal identity fresh).1

/-- Fresh capture instructions retain the actual acquired identity. -/
theorem bound_fresh_atom
    {inst : Instantiation.Environment}
    (rest : bound bindings (inst.bind binder identity) atoms = some resources) :
    bound bindings (inst.bind binder identity) (.resourceBinder binder :: atoms) = some (identity :: resources) := by
  simp [bound, atom, Instantiation.Environment.bind, rest]

/-- No retaining value crosses an original receiver which excludes the fresh
identity, irrespective of its public callable port. -/
theorem retaining_opening_rejected
    {declarations : Instantiation.DeclarationRegistry} {world : List Nat} {ticket : CallableContracts.Ticket}
    (isValue : (code.instantiate (inst.bind binder identity)).IsValue)
    (retained : identity ∈ Syntax.resourceDependencies (code.instantiate (inst.bind binder identity)).dependencies)
    (outside : identity ∉ originalBound) :
    opening bindings inst binder identity code recipe originalBound ≠ some result := by
  intro accepted
  obtain ⟨derived, bounded⟩ := opening_sound (declarations := declarations) (world := world) (ticket := ticket) accepted
  exact outside (bounded (CallableContracts.value_support derived isValue retained))

/-- Slot specialization is structural and universal in the complete actual
contract, including callable capture/domain/result trees. -/
theorem formal_slot_specialization (bindings : CoreCallableReturnStorageProducer.Bindings)
    (formal : Nat) (actual : CallableContracts.Contract) (inst : Instantiation.Environment) :
    contract (CoreCallableReturnStorageProducer.extend bindings formal actual) inst (.slot formal) = some actual := by
  simp [contract, CoreCallableReturnStorageProducer.lookup, CoreCallableReturnStorageProducer.extend]

#print axioms check_sound
#print axioms opening_sound
#print axioms pair_argument
#print axioms formal_opening
#print axioms ArgumentReceipt.fresh_excluded
#print axioms formal_opening_receipt
#print axioms formal_resource_storage
#print axioms bound_fresh_atom
#print axioms retaining_opening_rejected
#print axioms formal_slot_specialization
end Ash.OneShot.CoreCallableStorageRecipes
