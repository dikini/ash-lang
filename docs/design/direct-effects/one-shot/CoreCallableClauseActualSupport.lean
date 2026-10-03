import CoreCallableDeliveredOperandSupport
import CoreCallableFiniteHandlerRegistryCoverage
namespace Ash.OneShot.CoreCallableClauseActualSupport
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (Registry Owners OwnerContract)
open CoreCallableContractAdmission CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourcePlanSignatures (signature modeSignatures clauseSignatures)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

/-- A finite output assignment contains one support list per original clause. -/
inductive FormalSupports : Clauses → Type where
  | nil : FormalSupports .nil
  | cons (support : List Nat) (tail : FormalSupports clauses) :
      FormalSupports (.cons operation parameter binder body clauses)

def whole (clauses : Clauses) (receiver : List Nat) : FormalSupports clauses :=
  match clauses with
  | .nil => .nil
  | .cons _ _ _ _ rest => .cons receiver (whole rest receiver)

/-- Selection uses the exact operation key. The registry checker also requires
complete unique clause keys, so no second formal receives a selected delivery. -/
def selected (clauses : Clauses) (operation : Nat) (support receiver : List Nat) : FormalSupports clauses :=
  match clauses with
  | .nil => .nil
  | .cons key _ _ _ rest => .cons (if key = operation then support else receiver) (selected rest operation support receiver)

theorem selected_head : selected (.cons operation parameter binder body clauses) operation support receiver =
    .cons support (selected clauses operation support receiver) := by simp [selected]

theorem unselected_head (different : key ≠ operation) :
    selected (.cons key parameter binder body clauses) operation support receiver =
      .cons receiver (selected clauses operation support receiver) := by simp [selected,different]

/-- The nearest formal's full assigned support is exactly the resume operand
bound obligation; outer entries and owner tickets cannot erase it. -/
theorem formal_resume_bound_iff {lexical : LexicalBounds} :
    SourceSupport.Bounds (lexical.extend parameter support).environment (Code.resume binder (.variable parameter)).dependencies bound ↔
      support ⊆ bound := by
  simp [SourceSupport.bounds_iff,Code.dependencies,ScopedPorts.Support.evaluate,
    LexicalBounds.environment_extend,ScopedPorts.Support.extend]

inductive DeclarationAuthenticationAt (registry : Registry) (outward : List Instance) :
    {owners : Owners} → {world : List Nat} → {environment : Environment} → {allowed : List Instance} →
    {requested : Instance} → {answer : Contract} → {clauses : Clauses} → {table : List (Nat × ClauseContract)} →
    {families : ClauseDependencies} → {plans : ClausePlans clauses families} → {rows : ClauseRows (clauseSignatures plans)} →
    SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows →
    LexicalBounds → List Nat → FormalSupports clauses → Prop where
  | nil : DeclarationAuthenticationAt registry outward SourceDeclarations.nil lexical receiver .nil
  | cons
      {environment : Environment}
      {ordinarySource : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body false dispose ordinaryRow ordinaryPlan ordinaryRows}
      {protectedSource : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body true dispose protectedRow protectedPlan protectedRows}
      {restSource : SourceDeclarations registry outward owners world environment allowed requested answer clauses table restPlan restRows}
      (known : registry.operations requested operation = some (argument, input))
      (bodyBound : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds
        (lexical.extend parameter formalSupport).environment body.dependencies supportBound)
      (formalReceived : formalSupport ⊆ receiver)
      (storedReceived : supportBound ⊆ receiver)
      (ordinary : OfferAuthentication registry outward ordinarySource (lexical.extend parameter formalSupport) receiver)
      (protectedMode : OfferAuthentication registry outward protectedSource (lexical.extend parameter formalSupport) receiver)
      (rest : DeclarationAuthenticationAt registry outward restSource lexical receiver tail) :
      DeclarationAuthenticationAt registry outward (SourceDeclarations.cons (parameter := parameter) (body := body)
        supportBound known ordinarySource protectedSource restSource) lexical receiver (.cons formalSupport tail)

section Whole
variable {registry : Registry} {outward : List Instance} {owners : Owners} {world : List Nat}
  {environment : Environment} {allowed : List Instance} {requested : Instance} {answer : Contract}
  {clauses : Clauses} {table : List (Nat × ClauseContract)} {families : ClauseDependencies}
  {plans : ClausePlans clauses families} {rows : ClauseRows (clauseSignatures plans)}
  {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows}

/-- The original whole-receiver judgment is exactly the specialization. -/
theorem whole_forward
    (original : DeclarationAuthentication registry outward source lexical receiver) :
    DeclarationAuthenticationAt registry outward source lexical receiver (whole clauses receiver) := by
  induction measure : sizeOf clauses using Nat.strongRecOn generalizing clauses table families plans rows with
  | ind measure ih =>
      cases original with
      | nil => exact .nil
      | cons known bounded stored ordinary protectedMode tail =>
          have tailAt := ih _ (by simp_all; omega) tail rfl
          exact .cons known bounded (List.Subset.refl _) stored ordinary protectedMode tailAt

theorem whole_backward
    (precise : DeclarationAuthenticationAt registry outward source lexical receiver (whole clauses receiver)) :
    DeclarationAuthentication registry outward source lexical receiver := by
  generalize same : whole clauses receiver = assignment at precise
  induction precise with
  | nil => exact .nil
  | cons known bounded formalReceived stored ordinary protectedMode rest ih =>
      simp only [whole] at same
      cases same
      exact .cons known bounded stored ordinary protectedMode (ih rfl)

theorem whole_iff :
    DeclarationAuthenticationAt registry outward source lexical receiver (whole clauses receiver) ↔
      DeclarationAuthentication registry outward source lexical receiver := ⟨whole_backward,whole_forward⟩

end Whole

structure ReceiptAt (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Declarations entries requested answer bindings clauses) (lexical : LexicalBounds) (receiver : List Nat)
    (assignment : FormalSupports clauses) : Type where
  source : SourceDeclarations (registry entries policy) outward owners world (environment bindings) allowed requested answer
    clauses data.table data.plans data.rows
  authenticated : DeclarationAuthenticationAt (registry entries policy) outward source lexical receiver assignment
  modes : SourceTemplates.ClauseModes clauses data.table
  capabilities : ClausesUse policy clauses
  recipes : ClauseDeclarations outward clauses data.families []

private def checkAt (data : Declarations entries requested answer bindings clauses)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (lexical : LexicalBounds) (receiver : List Nat) (assignment : FormalSupports clauses) :
    Except Error (ReceiptAt entries policy outward owners world allowed data lexical receiver assignment) :=
  match data, assignment with
  | .nil, .nil => .ok ⟨.nil,.nil,.nil,.nil,.nil⟩
  | .cons (operation := operation) (parameter := parameter) (binder := binder) (code := code) (argument := argument) (input := input) reference body supportBound ordinary protectedMode resumeEffects closeEffects rest, .cons formalSupport tailSupports => do
    if located : reference.check = true then
      if _useValid : currentUse policy (.ticket binder (policy binder)) .available code = some .consumed then
      if supported : body.supported = true then
        if permission : (policy binder).resume = true then
          if required : code.requiredActions.resume = true then
            if noDispose : code.requiredActions.dispose = false then
              if formalReceived : CoreCallableGraphAnnotationChecks.subsetB formalSupport receiver = true then
                if stored : CoreCallableGraphAnnotationChecks.subsetB supportBound receiver = true then
                  if bounded : CoreCallableGraphAnnotationChecks.subsetB
                      (ScopedPorts.Support.evaluate (lexical.extend parameter formalSupport).environment code.dependencies) supportBound = true then
                    let _checked ← body.check entries policy outward owners world allowed (lexical.extend parameter formalSupport) receiver
                    let a ← checkMode body ordinary entries policy outward owners world allowed resumeEffects closeEffects false false (lexical.extend parameter formalSupport) receiver
                    let b ← checkMode body protectedMode entries policy outward owners world allowed resumeEffects closeEffects true false (lexical.extend parameter formalSupport) receiver
                    let tail ← checkAt rest policy outward owners world allowed lexical receiver tailSupports
                    let known := reference.sound located
                    let source := SourceDeclarations.cons supportBound known a.source b.source tail.source
                    let ordinaryRecipe : DeclarationModes outward code.requiredActions [] (modeFamily body ordinary) := by
                      cases ordinary with
                      | none => exact .unavailable
                      | some row => exact .available (.existing (body.recipe supported required).erase)
                    let protectedRecipe : DeclarationModes outward code.requiredActions [] (modeFamily body protectedMode) := by
                      cases protectedMode with
                      | none => exact .unavailable
                      | some row => exact .available (.existing (body.recipe supported required).erase)
                    .ok ⟨source,
                      .cons known (SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound bounded))
                        (CoreCallableGraphAnnotationChecks.subsetB_sound formalReceived)
                        (CoreCallableGraphAnnotationChecks.subsetB_sound stored) a.authenticated b.authenticated tail.authenticated,
                      .cons (by intro impossible; rw [noDispose] at impossible; cases impossible) tail.modes,
                      .cons (body.use supported permission) tail.capabilities,
                      by simpa [Declarations.families] using (ClauseDeclarations.cons ordinaryRecipe protectedRecipe tail.recipes)⟩
                  else .error .support
                else .error .support
              else .error .support
            else .error .capability
          else .error .capability
        else .error .capability
      else .error (.unsupported "clause template")
      else .error .capability
    else .error .operationShadowing

structure ReceivingReceipt (api : CoreCallableFiniteCellRegistry.CellApi) (entries : OperationEntries)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Declarations entries requested answer bindings clauses) (lexical : LexicalBounds) (receiver : List Nat)
    (assignment : FormalSupports clauses) (operation : Nat) (held : Bool) : Type where
  checked : ReceiptAt entries policy outward owners world allowed data lexical receiver assignment
  coverage : CoreCallableFiniteHandlerRegistryCoverage.CoverageReceipt api entries policy requested clauses
  selectedContract : ClauseContract
  selectedRow : Footprint
  selectedFound : ProtectionContracts.lookup operation data.table = some selectedContract
  selectedAvailable : selectedContract.row held = some selectedRow

/-- This public route computes assignment from the same delivered operand. The
existing complete target registry coverage and selected availability are executed. -/
def checkDeliveredDeclarations
    {reference : OperationRef entries requested operation argument input}
    {annotation : Annotation entries owners richBindings code argument demand requirements plan rows}
    (delivered : CoreCallableDeliveredOperandSupport.DeliveredSupport storageDeclarations reference annotation storageBindings inst recipe
      graph machineOwners heap value policy outward world allowed lexical receiver)
    (api : CoreCallableFiniteCellRegistry.CellApi) (held : Bool)
    (data : Declarations entries requested answer bindings clauses) :
    Except CoreCallableStaticProducer.Error (ReceivingReceipt api entries policy outward owners world allowed data lexical receiver
      (selected clauses operation (CoreCallableDeliveredOperandSupport.actualSupport code delivered.stored) receiver) operation held) := do
  let coverage ← match CoreCallableFiniteHandlerRegistryCoverage.check api entries policy requested clauses with
    | .error _ => .error .operationShadowing
    | .ok receipt => .ok receipt
  if _covered : clauseKeysCheck entries requested clauses = true then
    match found : ProtectionContracts.lookup operation data.table with
    | none => .error .operationShadowing
    | some contract =>
      match available : contract.row held with
      | none => .error .capability
      | some row =>
        let checked ← checkAt data policy outward owners world allowed lexical receiver
          (selected clauses operation (CoreCallableDeliveredOperandSupport.actualSupport code delivered.stored) receiver)
        .ok ⟨checked,coverage.down,contract,row,found,available⟩
  else .error .operationShadowing

/-- Target lookup keeps the same complete original argument/result record.
It follows from the executed coverage compatibility, never port equality. -/
theorem delivered_target_record
    {reference : OperationRef entries requested operation argument input}
    {annotation : Annotation entries owners richBindings code argument demand requirements plan rows}
    (delivered : CoreCallableDeliveredOperandSupport.DeliveredSupport storageDeclarations reference annotation storageBindings inst recipe
      graph machineOwners heap value policy outward world allowed lexical receiver)
    (coverage : CoreCallableFiniteHandlerRegistryCoverage.CoverageReceipt api entries policy requested clauses) :
    (CoreCallableFiniteCellRegistry.registry (some api) entries policy).operations requested operation = some (argument,input) :=
  CoreCallableFiniteRegistryCompatibility.selected_lookup_preserved coverage.compatibility delivered.known

#print axioms selected_head
#print axioms unselected_head
#print axioms formal_resume_bound_iff
#print axioms whole_forward
#print axioms whole_backward
#print axioms whole_iff
#print axioms checkDeliveredDeclarations
#print axioms delivered_target_record
end Ash.OneShot.CoreCallableClauseActualSupport
