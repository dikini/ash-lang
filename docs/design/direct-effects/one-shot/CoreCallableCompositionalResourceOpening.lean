import CoreCallableFiniteRegistryBridge
import CoreCallableCompositionalResourceBody
namespace Ash.OneShot.CoreCallableCompositionalResourceOpening
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract sequenceRows)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableCompositionalResourceBody
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy


def allowedNames (binder : Nat) (residual : List Instance) : List EffectName :=
  .cell (.bound binder) :: residual.map EffectName.closed

def openingCheck (original : CoreCallableStaticProducer.Bindings) (body : Body original context code pattern checking needs)
    (api : CoreCallableFiniteCellRegistry.CellApi)
    (binder : Nat) (world : List Nat) (residual : List Instance) (lexical : LexicalBounds) (receiver : List Nat) : Bool :=
  api.check && body.check original binder world residual (allowedNames binder residual) &&
  aligned original context && pattern.isClosed && pattern.check original binder world &&
  CoreCallableGraphAnnotationChecks.knownB lexical code.dependencies &&
  CoreCallableGraphAnnotationChecks.subsetB (ScopedPorts.Support.evaluate lexical.environment code.dependencies) receiver &&
  CoreCallableGraphAnnotationChecks.subsetB receiver world

structure Opening (api : CoreCallableFiniteCellRegistry.CellApi) (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (residual : List Instance) (scope : Execution.Scope)
    (original : CoreCallableStaticProducer.Bindings) (binder : Nat)
    (body : Body original context code pattern checking needs) (lexical : LexicalBounds) (receiver : List Nat) where
  source : ∀ identity, identity ∉ world → IndexedSource
    (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
    (world ++ [identity]) (.cell identity :: residual) scope
    (CoreCallableStaticProducer.environment original)
    (code.instantiate (Instantiation.Environment.empty.bind binder identity))
    (pattern.value original 0) [] (needs.requirements identity) (checking.plan identity) (checking.rows identity)
  auth : ∀ identity (fresh : identity ∉ world), Authenticated
    (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward (source identity fresh) lexical (identity :: receiver)
  formed : ScopedPorts.InWorld world (pattern.value original 0).port
  hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity
    (needs.requirements identity) needs.outsideRequirements
  receiverIssued : receiver ⊆ world

theorem check_opening (body : Body original context code pattern checking needs)
    (accepted : openingCheck original body api binder world residual lexical receiver = true) :
    Opening api entries policy outward owners world residual scope original binder body lexical receiver := by
  obtain ⟨⟨⟨⟨⟨⟨⟨a,b⟩,h⟩,d⟩,e⟩,f⟩,g⟩,r⟩ := (by simpa only [openingCheck,Bool.and_eq_true] using accepted)
  have known := CoreCallableGraphAnnotationChecks.knownB_sound f
  have bounds := SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound g)
  have env : ∀ identity, bindings original identity context = original := fun _ => aligned_original h
  have output : ∀ identity, pattern.value original identity = pattern.value original 0 := fun _ => pattern.constant d
  let derived := fun identity => body.derive (entries := entries) (policy := policy) (outward := outward) (owners := owners)
    (scope := scope) (identity := identity) a b
  have allowed : ∀ identity, (allowedNames binder residual).map (EffectName.value identity) = .cell identity :: residual := by
    intro identity
    simp [allowedNames,EffectName.value,CoreCallableFiniteResourceTemplate.nameValue,List.map_map,Function.comp_def]
  refine ⟨fun identity _ => by simpa only [env identity,output identity,allowed identity] using (derived identity).source,?_,
    pattern.formed_closed e d,fun _ fresh => needs.hides (body.needs_valid b) fresh,CoreCallableGraphAnnotationChecks.subsetB_sound r⟩
  intro identity fresh
  simpa only [env identity,output identity,allowed identity] using
    (derived identity).tree.authenticate_world (List.Subset.refl _)
      (CoreCallableFiniteResourceTemplate.opening_known known) (CoreCallableFiniteResourceTemplate.opening_bounds bounds)

/-- The successful finite opening check computes a tree for each SAME opened
source, retaining all identity-indexed checking data. -/
theorem check_opening_tree (body : Body original context code pattern checking needs)
    (accepted : openingCheck original body api binder world residual lexical receiver = true)
    (identity : Nat) (fresh : identity ∉ world) :
    CoreCallableStaticProducer.StaticTree
      (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward
      ((check_opening (entries := entries) (policy := policy) (outward := outward)
        (owners := owners) (scope := scope) body accepted).source identity fresh) := by
  obtain ⟨⟨⟨⟨⟨⟨⟨a,b⟩,h⟩,d⟩,_e⟩,_f⟩,_g⟩,_r⟩ :=
    (by simpa only [openingCheck,Bool.and_eq_true] using accepted)
  have env : bindings original identity context = original := aligned_original h
  have output : pattern.value original identity = pattern.value original 0 := pattern.constant d
  have allowed : (allowedNames binder residual).map (EffectName.value identity) =
      .cell identity :: residual := by
    simp [allowedNames,EffectName.value,CoreCallableFiniteResourceTemplate.nameValue,
      List.map_map,Function.comp_def]
  simpa only [env,output,allowed] using
    (body.derive (entries := entries) (policy := policy) (outward := outward)
      (owners := owners) (scope := scope) (identity := identity) a b).tree

def resourceCheck (original : CoreCallableStaticProducer.Bindings) (body : Body original context code pattern checking needs)
    (api : CoreCallableFiniteCellRegistry.CellApi)
    (binder : Nat) (world : List Nat) (residual allowed : List Instance) (lexical : LexicalBounds) (receiver : List Nat) : Bool :=
  openingCheck original body api binder world residual lexical receiver &&
  CoreCallableGraphAnnotationChecks.subsetB (residual.flatMap Instance.resources) world &&
  CoreCallableGraphAnnotationChecks.subsetB residual allowed

/-- Initializer metadata is an exact index, not replaced by a pure prefix. -/
def combinedPlan (_body : Body original context code pattern checking needs) (initialPlan : Plan initialDependencies) :
    Plan (.sequence initialDependencies (.resource (fun identity => checking.dependencies identity))) :=
  .sequence initialPlan (.resource (fun identity => checking.plan identity))
def combinedRows (body : Body original context code pattern checking needs) (initialRows : Rows (signature initialPlan)) :
    Rows (signature (combinedPlan body initialPlan)) :=
  sequenceRows initialRows (Rows.resource (fun identity => checking.rows identity))

/-- All fields are produced after actual current checks. The original
initializer Code/demand/requirements/private Plan/full Rows remain indices. -/
structure Result (api : CoreCallableFiniteCellRegistry.CellApi)
    (entries : CoreCallableStaticProducer.OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (residual allowed : List Instance) (scope : Execution.Scope)
    (original : CoreCallableStaticProducer.Bindings) (binder : Nat)
    (annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows)
    (body : Body original context code pattern checking needs) (lexical : LexicalBounds) (receiver : List Nat) : Prop where
  initializer : CoreCallableFiniteRegistryBridge.Rechecked api entries policy outward owners world allowed scope
    original initial .integer initialDemand initialReq initialPlan initialRows lexical receiver
  source : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
    world allowed scope (CoreCallableStaticProducer.environment original)
    (.resource binder initial code) (pattern.value original 0) (initialDemand ++ [])
    (.sequence initialReq needs.outsideRequirements) (combinedPlan body initialPlan) (combinedRows body initialRows)
  authenticated : Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward source lexical receiver
  opening : Opening api entries policy outward owners world residual scope original binder body lexical receiver

private theorem produce
    (annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows)
    (initial : CoreCallableFiniteRegistryBridge.Rechecked api entries policy outward owners world allowed scope
      original initial .integer initialDemand initialReq initialPlan initialRows lexical receiver)
    (body : Body original context code pattern checking needs)
    (accepted : resourceCheck original body api binder world residual allowed lexical receiver = true) :
    Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver := by
  obtain ⟨initialSource,_tree,initialAuth,_issued⟩ := initial
  obtain ⟨⟨opened,effects⟩,admitted⟩ :
      (openingCheck original body api binder world residual lexical receiver = true ∧
      CoreCallableGraphAnnotationChecks.subsetB (residual.flatMap Instance.resources) world = true) ∧
      CoreCallableGraphAnnotationChecks.subsetB residual allowed = true := by
    simpa [resourceCheck] using accepted
  let opening := check_opening (entries := entries) (policy := policy) (outward := outward)
    (owners := owners) (scope := scope) body opened
  let source := IndexedSource.resource (binder := binder) initialSource opening.source opening.formed
    (CoreCallableGraphAnnotationChecks.subsetB_sound effects)
    (CoreCallableGraphAnnotationChecks.subsetB_sound admitted) opening.hidden
  have bodyBound : ScopedPorts.Support.evaluate lexical.environment code.dependencies ⊆ receiver := by
    have guards := opened
    simp only [openingCheck,Bool.and_eq_true] at guards
    exact CoreCallableGraphAnnotationChecks.subsetB_sound guards.1.2
  have support : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds lexical.environment
      (Code.resource binder initial code).dependencies receiver := by
    apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
    have initBound := SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp initialAuth.current_support
    simpa [Code.dependencies,ScopedPorts.Support.evaluate,List.flatMap_append] using
      List.append_subset.mpr ⟨initBound,bodyBound⟩
  exact ⟨⟨initialSource,_tree,initialAuth,_issued⟩,source,
    .checked support (Hereditary.resource (bodySource := opening.source) (formed := opening.formed)
      (effectsBound := CoreCallableGraphAnnotationChecks.subsetB_sound effects)
      (admitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted)
      (hidden := opening.hidden) initialAuth opening.auth),opening⟩

inductive Error where
  | initializer : CoreCallableFiniteRegistryBridge.Error → Error
  | resourceBody
  deriving Repr

/-- Executes original finite Annotation→recheck itself. No caller-created
Source/Auth/Rechecked or value-only ArgumentReceipt is an input. -/
def check_compositional
    (annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows)
    (body : Body original context code pattern checking needs) (api : CoreCallableFiniteCellRegistry.CellApi)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat)
    (residual allowed : List Instance) (scope : Execution.Scope) (binder : Nat)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (PLift (Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver)) := do
  match CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope lexical receiver with
  | .error error => .error (.initializer error)
  | .ok receipt =>
      if accepted : resourceCheck original body api binder world residual allowed lexical receiver = true then
        .ok ⟨produce annotation receipt.down body accepted⟩
      else .error .resourceBody

theorem check_success
    {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows}
    {receipt : PLift (Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver)}
    (_accepted : check_compositional annotation body api policy outward world residual allowed scope binder lexical receiver = .ok receipt) :
    Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver := receipt.down

theorem initializer_error_propagated
    {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows}
    (rejected : CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope lexical receiver = .error error) :
    check_compositional annotation body api policy outward world residual allowed scope binder lexical receiver = .error (.initializer error) := by
  simp [check_compositional,rejected]

/-- Successful output retains the exact executed original initializer gate. -/
theorem check_inputs
    {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows}
    {receipt : PLift (Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver)}
    (accepted : check_compositional annotation body api policy outward world residual allowed scope binder lexical receiver = .ok receipt) :
    (∃ initialReceipt, CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope lexical receiver = .ok initialReceipt) ∧
    resourceCheck original body api binder world residual allowed lexical receiver = true := by
  cases checked : CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope lexical receiver with
  | error error => simp [check_compositional,checked] at accepted
  | ok initialReceipt =>
      refine ⟨⟨initialReceipt,rfl⟩,?_⟩
      by_cases valid : resourceCheck original body api binder world residual allowed lexical receiver = true
      · exact valid
      · simp [check_compositional,checked,valid] at accepted

/-- SAME successful checker receipt, full initializer and all fresh opened
bodies produce resource provenance; no source family is a checker input. -/
theorem check_compositional_tree
    {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows}
    {receipt : PLift (Result api entries policy outward owners world residual allowed scope
      original binder annotation body lexical receiver)}
    (accepted : check_compositional annotation body api policy outward world residual allowed
      scope binder lexical receiver = .ok receipt) :
    CoreCallableStaticProducer.StaticTree
      (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward
      receipt.down.source := by
  obtain ⟨⟨initialReceipt,initialAccepted⟩,resourceAccepted⟩ := check_inputs accepted
  obtain ⟨initialSource,initialTree,_initialAuth,_issued⟩ :=
    CoreCallableFiniteRegistryBridge.recheck_success initialAccepted
  obtain ⟨⟨opened,effects⟩,admitted⟩ :
      (openingCheck original body api binder world residual lexical receiver = true ∧
      CoreCallableGraphAnnotationChecks.subsetB (residual.flatMap Instance.resources) world = true) ∧
      CoreCallableGraphAnnotationChecks.subsetB residual allowed = true := by
    simpa [resourceCheck] using resourceAccepted
  let opening := check_opening (entries := entries) (policy := policy) (outward := outward)
    (owners := owners) (scope := scope) body opened
  exact CoreCallableStaticProducer.StaticTree.resource
    (formed := opening.formed)
    (effectsBound := CoreCallableGraphAnnotationChecks.subsetB_sound effects)
    (admitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted)
    (hidden := opening.hidden) initialTree
    (check_opening_tree body opened)

#print axioms check_opening_tree
#print axioms check_compositional_tree

#print axioms check_opening
#print axioms check_success
#print axioms check_inputs
#print axioms initializer_error_propagated
end Ash.OneShot.CoreCallableCompositionalResourceOpening
