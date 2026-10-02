import CoreCallableCompositionalResourceStorage
import CoreCallableCapturedLambdaConstructor

namespace Ash.OneShot.CoreCallableComposedResourceOrigins
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Original finite initializer data selects a causal bind prior. There is no
annotation for the enclosing resource and no desired storage output. -/
inductive Prefix (entries : CoreCallableStaticProducer.OperationEntries)
    (owners : CoreCallableContractRegistries.Owners) (root : Code) :
    Code → CoreCallableStaticProducer.Bindings → Type where
  | here : Prefix entries owners root root []
  | bind
      (previous : Prefix entries owners root (.bind parameter initial body) bindings)
      (annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial input demand requirements plan rows)
      (recipe : CoreCallableStorageRecipes.Recipe) :
      Prefix entries owners root body ((parameter,input)::bindings)

/-- Every edge retains the exact executed finite checks and actual whole maps. -/
inductive Executed (api : CoreCallableFiniteCellRegistry.CellApi) (policy : Syntax.TicketPolicy)
    (declarations : Instantiation.DeclarationRegistry) (outward : List Instance)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) (receiver : List Nat) :
    {entries : CoreCallableStaticProducer.OperationEntries} → {owners : CoreCallableContractRegistries.Owners} →
    {root code : Code} → {bindings : CoreCallableStaticProducer.Bindings} →
    Prefix entries owners root code bindings → CoreCallableReturnStorageProducer.Bindings →
    LexicalBounds → List CoreCallableReturnStorageProducer.BindingAnnotation → Prop where
  | here : Executed api policy declarations outward world allowed scope receiver .here [] [] []
  | bind
      {path : Prefix entries owners root (.bind parameter initial body) bindings}
      {annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial input demand requirements plan rows}
      (previous : Executed api policy declarations outward world allowed scope receiver path storage lexical records)
      (richAccepted : CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope lexical receiver = .ok rich)
      (specialized : CoreCallableStorageRecipes.specialize storage Instantiation.Environment.empty recipe = some storedAnnotation)
      (storageAccepted : CoreCallableReturnStorageProducer.check storage initial storedAnnotation = some stored)
      (bounded : stored.storageOf ⊆ receiver) :
      Executed api policy declarations outward world allowed scope receiver
        (.bind (parameter := parameter) (body := body) path annotation recipe)
        (CoreCallableReturnStorageProducer.extend storage parameter stored)
        (lexical.extend parameter receiver)
        ({name := parameter, initializer := initial, annotation := storedAnnotation,
          expected := stored, resources := receiver}::records)

 theorem Executed.origins
    (executed : Executed api policy declarations outward world allowed scope receiver
      (path : Prefix entries owners root code bindings) storage lexical records) :
    CoreCallablePairedOrigin.Origins (CoreCallableFiniteCellRegistry.registry (some api) entries policy)
      declarations outward owners world allowed scope receiver root code bindings storage lexical records := by
  induction executed with
  | here => exact .initial
  | bind previous richAccepted specialized storageAccepted bounded ih =>
      obtain ⟨source,_,auth,_⟩ := CoreCallableFiniteRegistryBridge.recheck_success richAccepted
      exact .bind ih source auth (CoreCallableReturnStorageProducer.check_sound storageAccepted) bounded

structure CheckedOriginalPrefix
    (path : Prefix entries owners root code bindings)
    (api : CoreCallableFiniteCellRegistry.CellApi) (policy : Syntax.TicketPolicy)
    (declarations : Instantiation.DeclarationRegistry) (outward : List Instance)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) (receiver : List Nat) where
  storage : CoreCallableReturnStorageProducer.Bindings
  lexical : LexicalBounds
  records : List CoreCallableReturnStorageProducer.BindingAnnotation
  executed : Executed api policy declarations outward world allowed scope receiver path storage lexical records

inductive Error where
  | original : CoreCallableFiniteRegistryBridge.Error → Error
  | specialization | storage | bound

def produce_prefix
    (path : Prefix entries owners root code bindings)
    (api : CoreCallableFiniteCellRegistry.CellApi) (policy : Syntax.TicketPolicy)
    (declarations : Instantiation.DeclarationRegistry) (outward : List Instance)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) (receiver : List Nat) :
    Except Error (CheckedOriginalPrefix path api policy declarations outward world allowed scope receiver) :=
  match path with
  | .here => .ok ⟨[],[],[],.here⟩
  | .bind previous annotation recipe => do
      let before ← produce_prefix previous api policy declarations outward world allowed scope receiver
      match accepted : CoreCallableFiniteRegistryBridge.recheck annotation api policy outward world allowed scope before.lexical receiver with
      | .error error => .error (.original error)
      | .ok _rich =>
        match specialized : CoreCallableStorageRecipes.specialize before.storage Instantiation.Environment.empty recipe with
        | none => .error .specialization
        | some storedAnnotation =>
          match checked : CoreCallableReturnStorageProducer.check before.storage _ storedAnnotation with
          | none => .error .storage
          | some stored =>
            if bounded : decide (stored.storageOf ⊆ receiver) = true then
              .ok ⟨_,_,_,.bind before.executed accepted specialized checked (of_decide_eq_true bounded)⟩
            else .error .bound

 theorem CheckedOriginalPrefix.origins
    {path : Prefix entries owners root code bindings}
    (receipt : CheckedOriginalPrefix path api policy declarations outward world allowed scope receiver) :
    CoreCallablePairedOrigin.Origins (CoreCallableFiniteCellRegistry.registry (some api) entries policy)
      declarations outward owners world allowed scope receiver root code bindings receipt.storage receipt.lexical receipt.records :=
  receipt.executed.origins

/-- Original graph shape/translation are executed beside the finite prefix.
Raw graph type admission and a general Program are separate obligations. -/
structure CheckedGraphPrefix (graph : CoreSyntax.Graph)
    (path : Prefix entries owners root code bindings)
    (api : CoreCallableFiniteCellRegistry.CellApi) (policy : Syntax.TicketPolicy)
    (declarations : Instantiation.DeclarationRegistry) (outward : List Instance)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) (receiver : List Nat) where
  original : CheckedOriginalPrefix path api policy declarations outward world allowed scope receiver
  shape : CoreSyntax.checkShape graph = .ok ()
  translated : CoreTranslation.translate graph = .ok root

inductive GraphError where
  | shape : CoreSyntax.Error → GraphError
  | translation : CoreSyntax.Error → GraphError
  | code
  | original : Error → GraphError

def produce_graph_prefix (graph : CoreSyntax.Graph)
    (path : Prefix entries owners root code bindings)
    (api : CoreCallableFiniteCellRegistry.CellApi) (policy : Syntax.TicketPolicy)
    (declarations : Instantiation.DeclarationRegistry) (outward : List Instance)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) (receiver : List Nat) :
    Except GraphError (CheckedGraphPrefix graph path api policy declarations outward world allowed scope receiver) := do
  match shaped : CoreSyntax.checkShape graph with
  | .error error => .error (.shape error)
  | .ok _ =>
    match translated : CoreTranslation.translate graph with
    | .error error => .error (.translation error)
    | .ok actual =>
      if same : CoreCallableChecks.codeEq actual root = true then
        let original ← (produce_prefix path api policy declarations outward world allowed scope receiver).mapError GraphError.original
        .ok ⟨original,by simpa using shaped,by simpa only [CoreCallableChecks.codeEq_sound actual root same] using translated⟩
      else .error .code

/-- The joint receipt is attached to the executed original root prior. -/
structure ResourceOpened
    (prior : CheckedOriginalPrefix (path : Prefix entries owners root (.resource binder initial code) bindings)
      api policy declarations outward world allowed scope receiver)
    (annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows)
    (body : CoreCallableCompositionalResourceBody.Body bindings context code pattern checking needs)
    (initialRecipe : CoreCallableStorageRecipes.Recipe)
    (bodyRecipe : CoreCallableCompositionalResourceStorage.Recipe) (residual : List Instance) (bound : List Nat) where
  combined : CoreCallableCompositionalResourceStorage.Combined prior.origins annotation body initialRecipe bodyRecipe residual bound
  accepted : CoreCallableCompositionalResourceStorage.check_composed prior.origins annotation body initialRecipe bodyRecipe residual bound = .ok combined

def produce_opened
    (prior : CheckedOriginalPrefix (path : Prefix entries owners root (.resource binder initial code) bindings)
      api policy declarations outward world allowed scope receiver)
    (annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows)
    (body : CoreCallableCompositionalResourceBody.Body bindings context code pattern checking needs)
    (initialRecipe : CoreCallableStorageRecipes.Recipe)
    (bodyRecipe : CoreCallableCompositionalResourceStorage.Recipe) (residual : List Instance) (bound : List Nat) :
    Except CoreCallableCompositionalResourceStorage.Error (ResourceOpened prior annotation body initialRecipe bodyRecipe residual bound) :=
  match accepted : CoreCallableCompositionalResourceStorage.check_composed prior.origins annotation body initialRecipe bodyRecipe residual bound with
  | .error error => .error error
  | .ok combined => .ok ⟨combined,accepted⟩

 theorem produce_opened_accepted
    {prior : CheckedOriginalPrefix (originalPath : Prefix entries owners root (.resource binder initial code) bindings)
      api policy declarations outward world allowed scope receiver}
    {annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows}
    {body : CoreCallableCompositionalResourceBody.Body bindings context code pattern checking needs}
    {combined : CoreCallableCompositionalResourceStorage.Combined prior.origins annotation body initialRecipe bodyRecipe residual bound}
    (accepted : CoreCallableCompositionalResourceStorage.check_composed prior.origins annotation body initialRecipe bodyRecipe residual bound = .ok combined) :
    ∃ opened, produce_opened prior annotation body initialRecipe bodyRecipe residual bound = .ok opened := by
  unfold produce_opened
  split
  · rename_i failed
    rw [failed] at accepted
    contradiction
  · exact ⟨_,rfl⟩

/-- The composed resource edge retains the exact graph transcript and prefix. -/
structure GraphOpened
    (checked : CheckedGraphPrefix graph (path : Prefix entries owners root (.resource binder initial code) bindings)
      api policy declarations outward world allowed scope receiver)
    (annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows)
    (body : CoreCallableCompositionalResourceBody.Body bindings context code pattern checking needs)
    (initialRecipe : CoreCallableStorageRecipes.Recipe)
    (bodyRecipe : CoreCallableCompositionalResourceStorage.Recipe) (residual : List Instance) (bound : List Nat) where
  resource : ResourceOpened checked.original annotation body initialRecipe bodyRecipe residual bound
  accepted : produce_opened checked.original annotation body initialRecipe bodyRecipe residual bound = .ok resource

def produce_graph_opened
    (checked : CheckedGraphPrefix graph (path : Prefix entries owners root (.resource binder initial code) bindings)
      api policy declarations outward world allowed scope receiver)
    (annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows)
    (body : CoreCallableCompositionalResourceBody.Body bindings context code pattern checking needs)
    (initialRecipe : CoreCallableStorageRecipes.Recipe)
    (bodyRecipe : CoreCallableCompositionalResourceStorage.Recipe) (residual : List Instance) (bound : List Nat) :
    Except CoreCallableCompositionalResourceStorage.Error (GraphOpened checked annotation body initialRecipe bodyRecipe residual bound) :=
  match accepted : produce_opened checked.original annotation body initialRecipe bodyRecipe residual bound with
  | .error error => .error error
  | .ok resource => .ok ⟨resource,accepted⟩

 theorem produce_graph_opened_success
    {checked : CheckedGraphPrefix graph (path : Prefix entries owners root (.resource binder initial code) bindings)
      api policy declarations outward world allowed scope receiver}
    {annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows}
    {body : CoreCallableCompositionalResourceBody.Body bindings context code pattern checking needs}
    {resource : ResourceOpened checked.original annotation body initialRecipe bodyRecipe residual bound}
    (accepted : produce_opened checked.original annotation body initialRecipe bodyRecipe residual bound = .ok resource) :
    ∃ output, produce_graph_opened checked annotation body initialRecipe bodyRecipe residual bound = .ok output := by
  unfold produce_graph_opened
  split
  · rename_i failed
    rw [failed] at accepted
    contradiction
  · exact ⟨_,rfl⟩

/-- These paths retain the computational Body metadata and the matching
produced symbolic storage constructor chain, rather than invert erased proofs. -/
inductive OpenedBind
    {prior : CheckedOriginalPrefix (originalPath : Prefix entries owners root (.resource binder initial code) bindings)
      api policy declarations outward world allowed scope receiver}
    {annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows}
    {body : CoreCallableCompositionalResourceBody.Body bindings context code pattern checking needs}
    (opened : ResourceOpened prior annotation body initialRecipe bodyRecipe residual bound) :
    {context : CoreCallableCompositionalResourceBody.Context} → {code : Code} →
    {pattern : CoreCallableCompositionalResourceBody.Pattern} →
    {checking : CoreCallableCompositionalResourceBody.Checking} → {needs : CoreCallableCompositionalResourceBody.Need} →
    {storage : CoreCallableCompositionalResourceStorage.Bindings} → {stored : CoreCallableCompositionalResourceStorage.Tree} →
    CoreCallableCompositionalResourceBody.Body bindings context code pattern checking needs →
    CoreCallableCompositionalResourceStorage.Produced api binder world storage code stored →
    CoreCallableCompositionalResourceStorage.Recipe → List Nat → Prop where
  | here : OpenedBind opened body opened.combined.opening.produced bodyRecipe []
  | bind
      {first : CoreCallableCompositionalResourceBody.Body bindings childContext childInitial input checkingA needsA}
      {second : CoreCallableCompositionalResourceBody.Body bindings ((parameter,input)::childContext) tail output checkingB needsB}
      {whole : CoreCallableCompositionalResourceStorage.Produced api binder world storage (.bind parameter childInitial tail) stored}
      {firstLower : CoreCallableCompositionalResourceStorage.Produced api binder world storage childInitial storedInput}
      {secondLower : CoreCallableCompositionalResourceStorage.Produced api binder world ((parameter,storedInput)::storage) tail storedOutput}
      (previous : OpenedBind opened (.bind first second) whole (.bind firstRecipe secondRecipe) names)
      (firstAccepted : CoreCallableCompositionalResourceStorage.check api binder world storage childInitial firstRecipe = some ⟨storedInput,firstLower⟩)
      (secondAccepted : CoreCallableCompositionalResourceStorage.check api binder world ((parameter,storedInput)::storage) tail secondRecipe = some ⟨storedOutput,secondLower⟩) :
      OpenedBind opened second secondLower secondRecipe (parameter::names)
  | initializer
      {first : CoreCallableCompositionalResourceBody.Body bindings childContext childInitial input checkingA needsA}
      {second : CoreCallableCompositionalResourceBody.Body bindings ((parameter,input)::childContext) tail output checkingB needsB}
      {whole : CoreCallableCompositionalResourceStorage.Produced api binder world storage (.bind parameter childInitial tail) stored}
      {firstLower : CoreCallableCompositionalResourceStorage.Produced api binder world storage childInitial storedInput}
      (previous : OpenedBind opened (.bind first second) whole (.bind firstRecipe secondRecipe) names)
      (firstAccepted : CoreCallableCompositionalResourceStorage.check api binder world storage childInitial firstRecipe = some ⟨storedInput,firstLower⟩) :
      OpenedBind opened first firstLower firstRecipe names

 theorem OpenedBind.accepted
    {prior : CheckedOriginalPrefix (originalPath : Prefix entries owners root (.resource binder initial code) bindings)
      api policy declarations outward world allowed scope receiver}
    {annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows}
    {body : CoreCallableCompositionalResourceBody.Body bindings rootContext code rootPattern rootChecking rootNeeds}
    {opened : ResourceOpened prior annotation body initialRecipe bodyRecipe residual bound}
    {current : CoreCallableCompositionalResourceBody.Body bindings context currentCode pattern checking needs}
    {produced : CoreCallableCompositionalResourceStorage.Produced api binder world storage currentCode stored}
    (path : OpenedBind opened current produced recipe names) :
    CoreCallableCompositionalResourceStorage.check api binder world storage currentCode recipe = some ⟨stored,produced⟩ := by
  induction path with
  | here => exact opened.combined.opening.accepted
  | bind previous firstAccepted secondAccepted ih => exact secondAccepted
  | initializer previous firstAccepted ih => exact firstAccepted

abbrev bind_checked := @OpenedBind.bind
abbrev initializer_checked := @OpenedBind.initializer

section Bind
variable {prior : CheckedOriginalPrefix (originalPath : Prefix entries owners root (.resource binder initial code) bindings)
  api policy declarations outward world allowed scope receiver}
variable {annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows}
variable {body : CoreCallableCompositionalResourceBody.Body bindings rootContext code rootPattern rootChecking rootNeeds}
variable {opened : ResourceOpened prior annotation body initialRecipe bodyRecipe residual bound}
variable {first : CoreCallableCompositionalResourceBody.Body bindings context initialCode input checkingA needsA}
variable {second : CoreCallableCompositionalResourceBody.Body bindings ((parameter,input)::context) tail output checkingB needsB}
variable {whole : CoreCallableCompositionalResourceStorage.Produced api binder world storage (.bind parameter initialCode tail) stored}

structure BindOutput
    (previous : OpenedBind opened (.bind first second) whole (.bind firstRecipe secondRecipe) names) where
  inputStored : CoreCallableCompositionalResourceStorage.Tree
  stored : CoreCallableCompositionalResourceStorage.Tree
  initialProduced : CoreCallableCompositionalResourceStorage.Produced api binder world storage initialCode inputStored
  tailProduced : CoreCallableCompositionalResourceStorage.Produced api binder world ((parameter,inputStored)::storage) tail stored
  initialAccepted : CoreCallableCompositionalResourceStorage.check api binder world storage initialCode firstRecipe = some ⟨inputStored,initialProduced⟩
  tailAccepted : CoreCallableCompositionalResourceStorage.check api binder world ((parameter,inputStored)::storage) tail secondRecipe = some ⟨stored,tailProduced⟩
  selected : OpenedBind opened first initialProduced firstRecipe names
  continuation : OpenedBind opened second tailProduced secondRecipe (parameter::names)

def produce_bind
    (previous : OpenedBind opened (.bind first second) whole (.bind firstRecipe secondRecipe) names) :
    Option (BindOutput previous) :=
  match initialAccepted : CoreCallableCompositionalResourceStorage.check api binder world storage initialCode firstRecipe with
  | none => none
  | some ⟨inputStored,initialProduced⟩ =>
    match tailAccepted : CoreCallableCompositionalResourceStorage.check api binder world ((parameter,inputStored)::storage) tail secondRecipe with
    | none => none
    | some ⟨stored,tailProduced⟩ => some ⟨inputStored,stored,initialProduced,tailProduced,initialAccepted,tailAccepted,
        (by exact OpenedBind.initializer (opened := opened) (first := first) (second := second) (names := names) previous initialAccepted),
        (by exact OpenedBind.bind (opened := opened) (first := first) (second := second) (names := names) previous initialAccepted tailAccepted)⟩
 theorem produce_bind_success
    (previous : OpenedBind opened (.bind first second) whole (.bind firstRecipe secondRecipe) names) :
    ∃ output, produce_bind previous = some output := by
  have accepted := previous.accepted
  unfold produce_bind
  split
  · rename_i failed
    simp only [CoreCallableCompositionalResourceStorage.check] at accepted
    rw [failed] at accepted
    dsimp at accepted
    contradiction
  · rename_i inputStored initialProduced initialAccepted
    split
    · rename_i failed
      simp only [CoreCallableCompositionalResourceStorage.check] at accepted
      rw [initialAccepted] at accepted
      dsimp at accepted
      rw [failed] at accepted
      dsimp at accepted
      contradiction
    · exact ⟨_,rfl⟩

end Bind

/-- Full ordered lexical shadowing follows the retained actual bind names. -/
def lexicalAfter (original : LexicalBounds) (receiver : List Nat) : List Nat → LexicalBounds
  | [] => original
  | name::names => (lexicalAfter original receiver names).extend name receiver

section Current
variable {prior : CheckedOriginalPrefix (originalPath : Prefix entries owners root (.resource binder initial code) bindings)
  api policy declarations outward world allowed scope receiver}
variable {annotation : CoreCallableStaticProducer.Annotation entries owners bindings initial .integer initialDemand initialReq initialPlan initialRows}
variable {body : CoreCallableCompositionalResourceBody.Body bindings context code pattern checking needs}
variable {opened : ResourceOpened prior annotation body initialRecipe bodyRecipe residual bound}
variable {current : CoreCallableCompositionalResourceBody.Body bindings currentContext currentCode currentPattern currentChecking currentNeeds}
variable {produced : CoreCallableCompositionalResourceStorage.Produced api binder world currentStorage currentCode currentStored}

structure Current
    (path : OpenedBind opened current produced recipe names) (identity : Nat) (fresh : identity ∉ world) : Prop where
  source : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
    (world ++ [identity]) (.cell identity::residual) scope
    (CoreCallableStaticProducer.environment (CoreCallableCompositionalResourceBody.bindings bindings identity currentContext))
    (currentCode.instantiate (Instantiation.Environment.empty.bind binder identity))
    (currentPattern.value bindings identity) [] (currentNeeds.requirements identity)
    (currentChecking.plan identity) (currentChecking.rows identity)
  authenticated : Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward source
    (lexicalAfter prior.lexical (identity::receiver) names) (identity::receiver)
  storage : CallableContracts.Derives declarations
    (CoreCallableReturnStorageProducer.environment (CoreCallableCompositionalResourceStorage.realize identity currentStorage))
    (world ++ [identity]) .none (currentCode.instantiate (Instantiation.Environment.empty.bind binder identity))
    (currentStored.value identity)

/-- Current checks are executed on the selected original child and exact full
maps. No Source/Auth, future family or desired lower result is an input. -/
def produce_current
    (path : OpenedBind opened current produced recipe names) (identity : Nat) (fresh : identity ∉ world) :
    Option (PLift (Current path identity fresh)) :=
  if valid : api.check = true then
    if checked : current.check bindings binder world residual
        (CoreCallableCompositionalResourceOpening.allowedNames binder residual) = true then
      let lexical := lexicalAfter prior.lexical (identity::receiver) names
      let actual := currentCode.instantiate (Instantiation.Environment.empty.bind binder identity)
      if known : CoreCallableGraphAnnotationChecks.knownB lexical actual.dependencies = true then
        if bounded : CoreCallableGraphAnnotationChecks.subsetB (ScopedPorts.Support.evaluate lexical.environment actual.dependencies) (identity::receiver) = true then
          let derived := current.derive (entries := entries) (policy := policy) (outward := outward) (owners := owners)
            (scope := scope) (identity := identity) valid checked
          have sameAllowed : (CoreCallableCompositionalResourceOpening.allowedNames binder residual).map
              (CoreCallableCompositionalResourceBody.EffectName.value identity) = .cell identity::residual := by
            simp [CoreCallableCompositionalResourceOpening.allowedNames,CoreCallableCompositionalResourceBody.EffectName.value,
              CoreCallableFiniteResourceTemplate.nameValue,List.map_map,Function.comp_def]
          some ⟨{
            source := by simpa only [sameAllowed] using derived.source
            authenticated := by
              simpa only [sameAllowed] using derived.tree.authenticate_world
                (List.Subset.refl _) (CoreCallableGraphAnnotationChecks.knownB_sound known)
                (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
                  (CoreCallableGraphAnnotationChecks.subsetB_sound bounded))
            storage := produced.derive }⟩
        else none
      else none
    else none
  else none

 theorem produce_current_success
    (path : OpenedBind opened current produced recipe names) (identity : Nat) (fresh : identity ∉ world)
    (apiValid : api.check = true)
    (bodyChecked : current.check bindings binder world residual (CoreCallableCompositionalResourceOpening.allowedNames binder residual) = true)
    (known : CoreCallableGraphAnnotationChecks.knownB (lexicalAfter prior.lexical (identity::receiver) names)
      (currentCode.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies = true)
    (bounded : CoreCallableGraphAnnotationChecks.subsetB
      (ScopedPorts.Support.evaluate (lexicalAfter prior.lexical (identity::receiver) names).environment
        (currentCode.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies)
      (identity::receiver) = true) :
    ∃ receipt, produce_current path identity fresh = some receipt := by
  unfold produce_current
  simp only [apiValid,bodyChecked,known,bounded]
  exact ⟨_,rfl⟩

end Current

#print axioms Executed.origins
#print axioms CheckedOriginalPrefix.origins
#print axioms produce_prefix
#print axioms produce_graph_prefix
#print axioms produce_opened
#print axioms produce_opened_accepted
#print axioms produce_graph_opened
#print axioms produce_graph_opened_success
#print axioms OpenedBind.accepted
#print axioms produce_bind
#print axioms produce_bind_success
#print axioms produce_current
#print axioms produce_current_success
end Ash.OneShot.CoreCallableComposedResourceOrigins
