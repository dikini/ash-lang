import CoreCallableFiniteRegistryBridge
import CoreCallableFiniteResourceTemplate
namespace Ash.OneShot.CoreCallableGeneralResourceInitializer
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract sequenceRows)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableFiniteResourceTemplate
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Initializer metadata is an exact index, not replaced by a pure prefix. -/
def combinedPlan (body : Body context code pattern) (initialPlan : Plan initialDependencies) :
    Plan (.sequence initialDependencies (.resource (fun identity => body.dependencies identity))) :=
  .sequence initialPlan (.resource (fun identity => body.plan identity))
def combinedRows (body : Body context code pattern) (initialRows : Rows (signature initialPlan)) :
    Rows (signature (combinedPlan body initialPlan)) :=
  sequenceRows initialRows (Rows.resource (fun identity => body.rows identity))

/-- All fields are produced after actual current checks. The original
initializer Code/demand/requirements/private Plan/full Rows remain indices. -/
structure Result (api : CoreCallableFiniteCellRegistry.CellApi)
    (entries : CoreCallableStaticProducer.OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (residual allowed : List Instance) (scope : Execution.Scope)
    (original : CoreCallableStaticProducer.Bindings) (binder : Nat)
    (annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows)
    (body : Body context code pattern) (lexical : LexicalBounds) (receiver : List Nat) : Prop where
  initializer : CoreCallableFiniteRegistryBridge.Rechecked api entries policy outward owners world allowed scope
    original initial .integer initialDemand initialReq initialPlan initialRows lexical receiver
  source : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
    world allowed scope (CoreCallableStaticProducer.environment original)
    (.resource binder initial code) (pattern.value original 0) (initialDemand ++ [])
    (.sequence initialReq body.outsideRequirements) (combinedPlan body initialPlan) (combinedRows body initialRows)
  authenticated : Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward source lexical receiver
  opening : Opening api entries policy outward owners world residual scope original binder body lexical receiver

private theorem produce
    (annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows)
    (initial : CoreCallableFiniteRegistryBridge.Rechecked api entries policy outward owners world allowed scope
      original initial .integer initialDemand initialReq initialPlan initialRows lexical receiver)
    (body : Body context code pattern)
    (accepted : resourceCheck body api original binder world residual allowed lexical receiver = true) :
    Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver := by
  obtain ⟨initialSource,_tree,initialAuth,_issued⟩ := initial
  obtain ⟨⟨opened,effects⟩,admitted⟩ :
      (openingCheck body api original binder world residual lexical receiver = true ∧
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
def check
    (annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows)
    (body : Body context code pattern) (api : CoreCallableFiniteCellRegistry.CellApi)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat)
    (residual allowed : List Instance) (scope : Execution.Scope) (binder : Nat)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (PLift (Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver)) := do
  match CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope lexical receiver with
  | .error error => .error (.initializer error)
  | .ok receipt =>
      if accepted : resourceCheck body api original binder world residual allowed lexical receiver = true then
        .ok ⟨produce annotation receipt.down body accepted⟩
      else .error .resourceBody

theorem check_success
    {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows}
    {receipt : PLift (Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver)}
    (_accepted : check annotation body api policy outward world residual allowed scope binder lexical receiver = .ok receipt) :
    Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver := receipt.down

theorem initializer_error_propagated
    {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows}
    (rejected : CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope lexical receiver = .error error) :
    check annotation body api policy outward world residual allowed scope binder lexical receiver = .error (.initializer error) := by
  simp [check,rejected]

/-- Successful output retains the exact executed original initializer gate. -/
theorem check_inputs
    {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer
      initialDemand initialReq initialPlan initialRows}
    {receipt : PLift (Result api entries policy outward owners world residual allowed scope original binder annotation body lexical receiver)}
    (accepted : check annotation body api policy outward world residual allowed scope binder lexical receiver = .ok receipt) :
    (∃ initialReceipt, CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope lexical receiver = .ok initialReceipt) ∧
    resourceCheck body api original binder world residual allowed lexical receiver = true := by
  cases checked : CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope lexical receiver with
  | error error => simp [check,checked] at accepted
  | ok initialReceipt =>
      refine ⟨⟨initialReceipt,rfl⟩,?_⟩
      by_cases valid : resourceCheck body api original binder world residual allowed lexical receiver = true
      · exact valid
      · simp [check,checked,valid] at accepted

/-- The unchanged integer-only ResourceResult remains the literal specialization. -/
theorem literal_specialization
    (result : Result api entries policy outward owners world residual allowed scope original binder
      (CoreCallableStaticProducer.Annotation.integer payload) body lexical receiver) :
    ResourceResult api entries policy outward owners world allowed scope original binder payload body lexical receiver :=
  ⟨result.source,result.authenticated⟩

#print axioms check_success
#print axioms check_inputs
#print axioms initializer_error_propagated
#print axioms literal_specialization
end Ash.OneShot.CoreCallableGeneralResourceInitializer
