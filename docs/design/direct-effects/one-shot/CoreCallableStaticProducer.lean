import CoreCallableStaticTreeCarrier
import CoreCallableStaticRegistryBackend

/-! Finite constructor annotations retain their exact full contracts and literal
plans. Their fields are syntax and structural tags, never Source/Auth proofs.
The checker constructs those judgments as outputs. Unsupported source forms
remain explicit full-fragment obligations. -/
namespace Ash.OneShot.CoreCallableStaticProducer
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractAdmission
open CoreCallableContractRegistries (Owners OwnerContract)

/-- Typed constructor data fix literal source indices. Lookup paths and recipe
instructions are finite data; successful checking will produce the judgments.
Unimplemented constructors have a named failure and remain acceptance items. -/
inductive Annotation (entries : OperationEntries) (owners : Owners) : Bindings → Code → Contract →
    (demand : List Nat) → RecursiveRequirements.Requirements demand →
    {dependencies : Dependencies} → (plan : Plan dependencies) → Rows (signature plan) → Type where
  | unit : Annotation entries owners bindings .unit .unit [] (.request [] []) .pure Rows.pure
  | boolean (value : Bool) : Annotation entries owners bindings (.boolean value) .boolean [] (.request [] []) .pure Rows.pure
  | integer (value : Int) : Annotation entries owners bindings (.integer value) .integer [] (.request [] []) .pure Rows.pure
  | reference (identity : Nat) : Annotation entries owners bindings (.resourceRef (.activation identity)) (.reference identity)
      [] (.request [] []) .pure Rows.pure
  | variable (reference : BindingRef bindings name contract) :
      Annotation entries owners bindings (.variable name) contract [] (.request [] []) .pure Rows.pure
  | pair (first : Annotation entries owners bindings a left firstDemand firstReq firstPlan firstRows)
      (second : Annotation entries owners bindings b right secondDemand secondReq secondPlan secondRows) :
      Annotation entries owners bindings (.pair a b) (.pair left right) (firstDemand ++ secondDemand)
        (.sequence firstReq secondReq) (.sequence firstPlan secondPlan) (sequenceRows firstRows secondRows)
  | bind (initializer : Annotation entries owners bindings a input firstDemand firstReq firstPlan firstRows)
      (body : Annotation entries owners ((parameter,input) :: bindings) b output secondDemand secondReq secondPlan secondRows) :
      Annotation entries owners bindings (.bind parameter a b) output (firstDemand ++ secondDemand)
        (.sequence firstReq secondReq) (.sequence firstPlan secondPlan) (sequenceRows firstRows secondRows)
  | app (function : Annotation entries owners bindings f (.function input output requests latent publicPlan publicRows)
        functionDemand functionReq functionPlan functionRows)
      (argument : Annotation entries owners bindings a input argumentDemand argumentReq argumentPlan argumentRows)
      (recipe : RecipeTag publicPlan) :
      Annotation entries owners bindings (.app f a) output (functionDemand ++ argumentDemand)
        (.emitAfter (.sequence functionReq argumentReq) [] latent)
        (.sequence functionPlan (.sequence argumentPlan publicPlan))
        (sequenceRows functionRows (sequenceRows argumentRows publicRows))
  | perform (reference : OperationRef entries effect operation input output)
      (operand : Annotation entries owners bindings value input operandDemand operandReq operandPlan operandRows) :
      Annotation entries owners bindings (.perform (Instantiation.freezeEffect effect) operation value) output
        operandDemand (.emitAfter operandReq [] [⟨effect,operation,false⟩])
        (.sequence operandPlan (.request (effect := effect) (operation := operation))) (sequenceRows operandRows Rows.request)
  | resume (reference : OwnerRef owners owner ownerContract)
      (operand : Annotation entries owners bindings value ownerContract.input operandDemand operandReq operandPlan operandRows) :
      Annotation entries owners bindings (.resume binder value) ownerContract.answer
        (operandDemand ++ owner :: ownerContract.resumeDemand)
        (.sequence operandReq (.invoke ⟨owner, .resume⟩ ownerContract.resumeDemand []))
        (.sequence operandPlan (.invoke (key := ⟨owner, .resume⟩))) (sequenceRows operandRows Rows.invoke)
  | discard (reference : OwnerRef owners owner ownerContract) :
      Annotation entries owners bindings (.discard binder) .unit (owner :: ownerContract.closeDemand)
        (.invoke ⟨owner, .dispose⟩ ownerContract.closeDemand []) (.invoke (key := ⟨owner, .dispose⟩)) Rows.invoke
  | cleanup (callback : Annotation entries owners bindings action
        (.function .unit .unit requests latent publicPlan publicRows)
        callbackDemand callbackReq callbackActualPlan callbackActualRows)
      (body : Annotation entries owners bindings code output bodyDemand bodyReq bodyPlan bodyRows)
      (recipe : RecipeTag publicPlan) :
      Annotation entries owners bindings (.cleanup action code) output (callbackDemand ++ bodyDemand)
        (.emitAfter (.sequence callbackReq bodyReq) [] (qualify true latent))
        (.sequence callbackActualPlan (.cleanup (needs := requests) publicPlan bodyPlan))
        (by simpa only [signature] using (Rows.sequence callbackActualRows (Rows.cleanup (needs := requests) latent publicRows bodyRows)))
  | branch (condition : Annotation entries owners bindings test .boolean conditionDemand conditionReq conditionPlan conditionRows)
      (yes : Annotation entries owners bindings a output yesDemand yesReq yesPlan yesRows)
      (no : Annotation entries owners bindings b output noDemand noReq noPlan noRows)
      (same : DemandPermutation yesDemand noDemand) :
      Annotation entries owners bindings (.branch test a b) output (conditionDemand ++ yesDemand)
        (.sequence conditionReq (.choice yesReq noReq same.sound))
        (.sequence conditionPlan (.choice yesPlan noPlan)) (sequenceRows conditionRows (choiceRows yesRows noRows))
  | lambda (body : Annotation entries owners ((parameter,input) :: bindings) code output bodyDemand bodyReq bodyPlan bodyRows)
      (recipe : RecipeTag publicPlan) (refinement : RefinementTag publicRows bodyRows) :
      Annotation entries owners bindings (.lambda parameter code) (.function input output requests latent publicPlan publicRows)
        [] (.request [] []) .pure Rows.pure
  | unsupported (constructor : String) : Annotation entries owners bindings code contract demand requirements plan rows


section
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

private theorem StaticTree.checked_outward {outward : List Instance}
    {source : IndexedSource actualRegistry outward owners world allowed scope valueEnvironment code contract demand requirements plan rows}
    (tree : StaticTree actualRegistry outward source)
    (normal : scope = .none) (checked : RecursiveRequirements.evaluate [] [] OwnerPhaseTransitions.empty requirements = some latent) :
    RecursiveOutward.Outward requirements (some latent) := by
  obtain ⟨row, actual⟩ := tree.outward normal
  have same : row = some latent := (RecursiveOutward.isolated_evaluation actual).symm.trans checked
  cases same
  exact actual

/-- This is the checker output, with exact literal source indices. -/
structure Result (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed : List Instance)
    (scope : Execution.Scope) (bindings : Bindings) (code : Code) (contract : Contract)
    (demand : List Nat) (requirements : RecursiveRequirements.Requirements demand)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : IndexedSource (registry entries policy) outward owners world allowed scope
    (environment bindings) code contract demand requirements plan rows
  authenticated : Authenticated (registry entries policy) outward source lexical receiver
  receivingIssued : receiver ⊆ world
  tree : StaticTree (registry entries policy) outward source

structure BackendResult (backend : CoreCallableStaticRegistryBackend.Backend) (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed : List Instance)
    (scope : Execution.Scope) (bindings : Bindings) (code : Code) (contract : Contract)
    (demand : List Nat) (requirements : RecursiveRequirements.Requirements demand)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : IndexedSource (backend.registry entries policy) outward owners world allowed scope
    (environment bindings) code contract demand requirements plan rows
  authenticated : Authenticated (backend.registry entries policy) outward source lexical receiver
  receivingIssued : receiver ⊆ world
  tree : StaticTree (backend.registry entries policy) outward source

private def finishBackend {backend : CoreCallableStaticRegistryBackend.Backend}
    (source : IndexedSource (backend.registry entries policy) outward owners world allowed scope
      (environment bindings) code contract demand requirements plan rows)
    (tree : StaticTree (backend.registry entries policy) outward source) :
    Except Error (BackendResult backend entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver) :=
  if issued : CoreCallableGraphAnnotationChecks.subsetB receiver world = true then
    if valid : CoreCallableGraphAnnotationChecks.subsetB
        (ScopedPorts.Support.evaluate lexical.environment code.dependencies) receiver = true then
      if known : CoreCallableGraphAnnotationChecks.knownB lexical code.dependencies = true then
        .ok ⟨source, tree.authenticate_world (List.Subset.refl _) (CoreCallableGraphAnnotationChecks.knownB_sound known)
          (SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound valid)),
          CoreCallableGraphAnnotationChecks.subsetB_sound issued, tree⟩
      else .error .missingLexicalSupport
    else .error .support
  else .error .unissuedPort

/-- Execute the finite recursive constructor checks. Every recursive call builds
actual source/authentication from child annotation data. Unsupported branches
return explicit errors; they do not admit a reduced language fragment. -/
private def checkBackend (backend : CoreCallableStaticRegistryBackend.Backend)
    (backendValid : backend.valid entries = true)
    (annotation : Annotation entries owners bindings code contract demand requirements plan rows)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (BackendResult backend entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver) :=
  match annotation with
  | .unit => finishBackend (backend := backend) .unit .unit
  | .boolean _ => finishBackend (backend := backend) .boolean .boolean
  | .integer _ => finishBackend (backend := backend) .integer .integer
  | .reference identity =>
    if issued : decide (identity ∈ world) = true then
      finishBackend (backend := backend) (.reference (of_decide_eq_true issued)) (.reference (issued := of_decide_eq_true issued))
    else .error .unissuedPort
  | @Annotation.variable _ _ bindings name contract reference =>
    if located : reference.check = true then
      if formed : CoreCallableGraphAnnotationChecks.subsetB contract.port.resources world = true then
        if _known : CoreCallableGraphAnnotationChecks.knownB lexical [Syntax.Dependency.variable name] = true then
          finishBackend (backend := backend) (.variable (reference.sound located) (CoreCallableGraphAnnotationChecks.subsetB_sound formed))
            (.variable (known := reference.sound located) (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed))
        else .error .missingLexicalSupport
      else .error .unissuedPort
    else .error .lexicalShadowing
  | .pair first second => do
    let a ← checkBackend backend backendValid first policy outward world allowed scope lexical receiver
    let b ← checkBackend backend backendValid second policy outward world allowed scope lexical receiver
    finishBackend (backend := backend) (.pair a.source b.source) (.pair a.tree b.tree)
  | .bind (parameter := parameter) initializer body => do
    let a ← checkBackend backend backendValid initializer policy outward world allowed scope lexical receiver
    let b ← checkBackend backend backendValid body policy outward world allowed scope (lexical.extend parameter receiver) receiver
    finishBackend (backend := backend) (.bind a.source b.source) (.bind a.tree b.tree)
  | .app (requests := requests) function argument recipe => do
    let f ← checkBackend backend backendValid function policy outward world allowed scope lexical receiver
    let a ← checkBackend backend backendValid argument policy outward world allowed scope lexical receiver
    if admitted : CoreCallableGraphAnnotationChecks.subsetB requests allowed = true then
      if accepted : recipe.check = true then
        finishBackend (backend := backend) (.app f.source a.source (CoreCallableGraphAnnotationChecks.subsetB_sound admitted) (recipe.sound accepted).certified)
          (.app (admitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted)
            (publicCertified := (recipe.sound accepted).certified) f.tree a.tree)
      else .error .unsupportedRecipe
    else .error .unavailableEffect
  | .perform (effect := effect) (output := output) reference operand => do
    let a ← checkBackend backend backendValid operand policy outward world allowed scope lexical receiver
    if known : reference.check = true then
      if admitted : decide (effect ∈ allowed) = true then
        if formed : CoreCallableGraphAnnotationChecks.subsetB output.port.resources world = true then
          finishBackend (backend := backend) (.perform (backend.selected_lookup backendValid (reference.sound known)) (of_decide_eq_true admitted) a.source
            (CoreCallableGraphAnnotationChecks.subsetB_sound formed)) (.perform (known := backend.selected_lookup backendValid (reference.sound known)) (admitted := of_decide_eq_true admitted)
              (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed) a.tree)
        else .error .unissuedPort
      else .error .unavailableEffect
    else .error .operationShadowing
  | .resume (owner := owner) (ownerContract := ownerContract) (binder := binder) reference operand => do
    let value ← checkBackend backend backendValid operand policy outward world allowed scope lexical receiver
    if located : reference.check = true then
      if resolved : decide (scope.resolve binder = some owner) = true then
        if permitted : (policy binder).resume = true then
          if admitted : CoreCallableGraphAnnotationChecks.subsetB ownerContract.resumeEffects allowed = true then
            if formed : CoreCallableGraphAnnotationChecks.subsetB ownerContract.answer.port.resources world = true then
              finishBackend (backend := backend) (.resume (reference.sound located) (of_decide_eq_true resolved) permitted value.source
                (CoreCallableGraphAnnotationChecks.subsetB_sound admitted) (CoreCallableGraphAnnotationChecks.subsetB_sound formed))
                (.resume (known := reference.sound located) (resolved := of_decide_eq_true resolved)
                  (permission := permitted) (admitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted)
                  (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed) value.tree)
            else .error .unissuedPort
          else .error .unavailableEffect
        else .error .capability
      else .error .ownerScope
    else .error .ownerShadowing
  | .discard (owner := owner) (ownerContract := ownerContract) (binder := binder) reference =>
    if located : reference.check = true then
      if resolved : decide (scope.resolve binder = some owner) = true then
        if permitted : (policy binder).dispose = true then
          if unprotected : ownerContract.held = false then
            if admitted : CoreCallableGraphAnnotationChecks.subsetB ownerContract.closeEffects allowed = true then
              finishBackend (backend := backend) (.discard (reference.sound located) (of_decide_eq_true resolved) permitted unprotected
                (CoreCallableGraphAnnotationChecks.subsetB_sound admitted))
                (.discard (reference.sound located) (of_decide_eq_true resolved) permitted unprotected (CoreCallableGraphAnnotationChecks.subsetB_sound admitted))
            else .error .unavailableEffect
          else .error .protectedOwner
        else .error .capability
      else .error .ownerScope
    else .error .ownerShadowing
  | .cleanup (requests := requests) callback body recipe => do
    let action ← checkBackend backend backendValid callback policy outward world allowed scope lexical receiver
    let current ← checkBackend backend backendValid body policy outward world allowed scope lexical receiver
    if admitted : CoreCallableGraphAnnotationChecks.subsetB requests allowed = true then
      if accepted : recipe.check = true then
        finishBackend (backend := backend) (.cleanup action.source current.source (CoreCallableGraphAnnotationChecks.subsetB_sound admitted) (recipe.sound accepted).certified)
          (.cleanup (admitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted)
            (publicCertified := (recipe.sound accepted).certified) action.tree current.tree)
      else .error .unsupportedRecipe
    else .error .unavailableEffect
  | .branch condition yes no same => do
    let tested ← checkBackend backend backendValid condition policy outward world allowed scope lexical receiver
    let first ← checkBackend backend backendValid yes policy outward world allowed scope lexical receiver
    let second ← checkBackend backend backendValid no policy outward world allowed scope lexical receiver
    finishBackend (backend := backend) (.branch tested.source first.source second.source same.sound)
      (.branch (sameDemand := same.sound) tested.tree first.tree second.tree)
  | .lambda (parameter := parameter) (input := input) (output := output) (requests := requests)
      (latent := latent) (publicPlan := publicPlan) (publicRows := publicRows) (bodyReq := bodyReq) (bodyPlan := bodyPlan) (bodyRows := bodyRows) body recipe refinement => do
    let actual ← checkBackend backend backendValid body policy outward world requests .none (lexical.extend parameter receiver) receiver
    if accepted : recipe.check = true then
      if admitted : latent.all (fun request => decide (request.effect ∈ requests)) = true then
        if formed : CoreCallableGraphAnnotationChecks.subsetB
            (Contract.function input output requests latent publicPlan publicRows).port.resources world = true then
          if summary : decide (RecursiveRequirements.evaluate [] [] OwnerPhaseTransitions.empty bodyReq = some latent) = true then
            let source := IndexedSource.receiverLambda
              (privatePlans := fun _ _ => bodyPlan) (privateRows := fun _ _ => bodyRows)
              (fun _ call => actual.source.world_weaken call.worldExtended)
              (actual.tree.checked_outward rfl (of_decide_eq_true summary))
              (fun request member => of_decide_eq_true ((List.all_eq_true.mp admitted) request member))
              (recipe.sound accepted).certified (CoreCallableGraphAnnotationChecks.subsetB_sound formed)
            finishBackend (backend := backend) source (.receiverLambda
              (bodyOutward := actual.tree.checked_outward rfl (of_decide_eq_true summary))
              (latentBound := fun request member => of_decide_eq_true ((List.all_eq_true.mp admitted) request member))
              (publicCertified := (recipe.sound accepted).certified)
              (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed) actual.tree refinement.sound)
          else .error .latentSummary
        else .error .unissuedPort
      else .error .latentAllowance
    else .error .unsupportedRecipe
  | .unsupported constructor => .error (.unsupported constructor)
/-- Execute the finite recursive constructor checks. Every recursive call builds
actual source/authentication from child annotation data. Unsupported branches
return explicit errors; they do not admit a reduced language fragment. -/
def check (annotation : Annotation entries owners bindings code contract demand requirements plan rows)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (Result entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver) := do
  let actual ← checkBackend .literal rfl annotation policy outward world allowed scope lexical receiver
  pure ⟨actual.source,actual.authenticated,actual.receivingIssued,actual.tree⟩

/-- Execute the SAME finite Annotation directly under the existing validated
original cell schema. The complete lookup check runs inside this producer. -/
def check_cell (annotation : Annotation entries owners bindings code contract demand requirements plan rows)
    (api : CoreCallableFiniteCellRegistry.CellApi)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except CoreCallableStaticRegistryBackend.CellError
      (BackendResult (.cell api) entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver) :=
  if compatible : CoreCallableFiniteRegistryCompatibility.compatible api entries = true then
    (checkBackend (.cell api) compatible annotation policy outward world allowed scope lexical receiver).mapError
      CoreCallableStaticRegistryBackend.CellError.originalCheck
  else .error .incompatibleRegistry

/-- The ordinary recursive evidence is connected to one actual graph origin.
Shape is checked on the entire finite arena; literal code agreement uses the
existing translator comparison, never an erased signature. -/
structure GraphResult (graph : CoreSyntax.Graph) (site : Nat) (maps : CoreTranslation.OwnerMap)
    (resources : Instantiation.Environment) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) (bindings : Bindings)
    (code : Code) (contract : Contract) (demand : List Nat) (requirements : RecursiveRequirements.Requirements demand)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  current : Result entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver
  node : CoreSyntax.Node
  raw : Code
  shape : CoreSyntax.ShapeChecked graph
  siteKnown : graph.node site = some node
  metadata : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Metadata
    resources node contract.value (node.effects.map (fun effect => effect.instantiate resources))
  declaredEffects : (node.effects.map (fun effect => effect.instantiate resources)) ⊆
    SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.allowanceEffects allowed
  translated : CoreTranslation.translateFuel graph (graph.nodes.length + 1) maps site = .ok raw
  literalCode : raw.instantiate resources = code

def checkGraph (graph : CoreSyntax.Graph) (site : Nat) (maps : CoreTranslation.OwnerMap)
    (resources : Instantiation.Environment)
    (annotation : Annotation entries owners bindings code contract demand requirements plan rows)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (GraphResult graph site maps resources entries policy outward owners world allowed scope
      bindings code contract demand requirements plan rows lexical receiver) :=
  match checkedShape : CoreSyntax.checkShape graph with
  | .error error => .error (.graphShape error)
  | .ok () => match found : graph.node site with
    | none => .error .graphNode
    | some node =>
      if typed : CoreCallableGraphAnnotationChecks.typeB resources node.type contract = true then
        if effects : CoreCallableGraphAnnotationChecks.subsetB (node.effects.map (fun effect => effect.instantiate resources))
            (SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.allowanceEffects allowed) = true then
          match translated : CoreTranslation.translateFuel graph (graph.nodes.length + 1) maps site with
          | .error error => .error (.graphTranslation error)
          | .ok raw =>
            if same : CoreCallableChecks.codeEq (raw.instantiate resources) code = true then do
              let current ← check annotation policy outward world allowed scope lexical receiver
              pure ⟨current,node,raw,checkedShape,found,⟨CoreCallableGraphAnnotationChecks.typeB_sound typed, fun _ => Iff.rfl⟩,
                CoreCallableGraphAnnotationChecks.subsetB_sound effects,translated,CoreCallableChecks.codeEq_sound _ _ same⟩
            else .error .graphCode
        else .error .graphMetadata
      else .error .graphMetadata
end

end Ash.OneShot.CoreCallableStaticProducer

#print axioms Ash.OneShot.CoreCallableStaticProducer.BindingRef.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.RecipeTag.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.PureTag.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.RefinementTag.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.OperationRef.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.DemandPermutation.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.StaticTree.authenticate_world
#print axioms Ash.OneShot.CoreCallableStaticProducer.StaticTree.outward
#print axioms Ash.OneShot.CoreCallableStaticProducer.StaticTree.checked_outward
#print axioms Ash.OneShot.CoreCallableStaticProducer.check
#print axioms Ash.OneShot.CoreCallableStaticProducer.checkGraph

#print axioms Ash.OneShot.CoreCallableStaticProducer.OwnerRef.sound
