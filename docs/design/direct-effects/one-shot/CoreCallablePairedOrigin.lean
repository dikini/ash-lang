import CoreCallableStaticProducer
import CoreCallableReturnStorageProducer
import CoreCallableAuthenticatedSubstitution

namespace Ash.OneShot.CoreCallablePairedOrigin
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open CoreCallableContractSource (Contract Environment)
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableContractRegistries (Owners)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission

local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Select rich initializer data from the original literal annotation. Only
storage templates/instructions are additional data. -/
inductive BindPath (receiver : List Nat) (entries : CoreCallableStaticProducer.OperationEntries) (owners : Owners)
    {rootCode rootContract rootDemand rootReq rootDeps} {rootPlan : Plan rootDeps} {rootRows}
    (root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows) :
    {bindings : CoreCallableStaticProducer.Bindings} → {code : Code} → {contract : Contract} →
    {demand : List Nat} → {requirements : Requirements demand} →
    {dependencies : Dependencies} → {plan : Plan dependencies} → {rows : Rows (signature plan)} →
    CoreCallableStaticProducer.Annotation entries owners bindings code contract demand requirements plan rows →
    CoreCallableReturnStorageProducer.Bindings → LexicalBounds → List CoreCallableReturnStorageProducer.BindingAnnotation → Type where
  | here : BindPath receiver entries owners root root [] [] []
  | bind
      (previous : BindPath receiver entries owners root (.bind (parameter := parameter) (a := initializer) initial body) beforeStorage beforeLexical beforeRecords)
      (storageAnnotation : CoreCallableReturnStorageProducer.Annotation) (storageInput : CallableContracts.Contract) :
      BindPath receiver entries owners root body
        (CoreCallableReturnStorageProducer.extend beforeStorage parameter storageInput)
        (beforeLexical.extend parameter receiver)
        ({ name := parameter, initializer := initializer, annotation := storageAnnotation,
           expected := storageInput, resources := receiver } :: beforeRecords)

/-- Checker outputs retain both exact initializer derivations. -/
inductive Origins (registry : CoreCallableContractRegistries.Registry)
    (declarations : Instantiation.DeclarationRegistry) (outward : List Instance)
    (owners : Owners) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) (receiver : List Nat)
    (root : Code) : Code → CoreCallableStaticProducer.Bindings → CoreCallableReturnStorageProducer.Bindings → LexicalBounds → List CoreCallableReturnStorageProducer.BindingAnnotation → Prop where
  | initial : Origins registry declarations outward owners world allowed scope receiver root root [] [] [] []
  | bind
      (previous : Origins registry declarations outward owners world allowed scope receiver root
        (.bind parameter initializer body) richBindings storageBindings lexical records)
      (rich : IndexedSource registry outward owners world allowed scope (CoreCallableStaticProducer.environment richBindings)
        initializer richInput initialDemand initialReq initialPlan initialRows)
      (authenticated : Authenticated registry outward rich lexical receiver)
      (storage : CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment storageBindings) world .none initializer storageInput)
      (bounded : storageInput.storageOf ⊆ receiver) :
      Origins registry declarations outward owners world allowed scope receiver root body
        ((parameter, richInput) :: richBindings) (CoreCallableReturnStorageProducer.extend storageBindings parameter storageInput)
        (lexical.extend parameter receiver)
        ({ name := parameter, initializer := initializer, annotation := storageAnnotation,
           expected := storageInput, resources := receiver } :: records)

inductive Error where
  | rich : CoreCallableStaticProducer.Error → Error
  | storageInitializer
  | storageDomain
  | storageReceiver


theorem Origins.binding_at
    (origin : Origins registry declarations outward owners world allowed scope receiver root body richBindings storageBindings lexical records) :
    CoreCallableReturnStorageProducer.BindingAt root body records := by
  induction origin with
  | initial => exact .initial
  | bind previous rich authenticated storage bounded ih => exact .bind ih

theorem Origins.storage_origins
    (origin : Origins registry declarations outward owners world allowed scope receiver root body richBindings storageBindings lexical records) :
    CoreCallableReturnStorageProducer.BindingOrigins declarations world receiver records storageBindings lexical := by
  induction origin with
  | initial => exact .nil
  | bind previous rich authenticated storage bounded ih => exact .cons ih storage bounded (List.Subset.refl _)

theorem Origins.lexical_fits
    (origin : Origins registry declarations outward owners world allowed scope receiver root body richBindings storageBindings lexical records) :
    CoreCallableReturnStorageProducer.LexicalFits storageBindings lexical receiver :=
  origin.storage_origins.lexical_fits

/-- Compose the actual checks on each selected initializer. -/
def checkPath
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings code contract demand requirements plan rows}
    (path : BindPath receiver entries owners root body storageBindings lexical records)
    (policy : Syntax.TicketPolicy) (declarations : Instantiation.DeclarationRegistry)
    (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) :
    Except Error (PLift (Origins (CoreCallableStaticProducer.registry entries policy) declarations outward owners
      world allowed scope receiver rootCode code richBindings storageBindings lexical records)) :=
  match path with
  | .here => .ok ⟨.initial⟩
  | @BindPath.bind _ _ _ _ _ _ _ _ _ _ _ initCode _ _ _ _ _ _ _ _ initAnn _ _ _ _ _ _ _ _ initStorage initLexical _ previous storageAnnotation storageInput => do
      let before ← checkPath previous policy declarations outward world allowed scope
      let checked ← (CoreCallableStaticProducer.check initAnn policy outward world allowed scope initLexical receiver).mapError Error.rich
      match accepted : CoreCallableReturnStorageProducer.check initStorage initCode storageAnnotation with
      | none => .error .storageInitializer
      | some actual =>
          if same : actual = storageInput then
            if bounded : decide (actual.storageOf ⊆ receiver) = true then
              return ⟨.bind before.down checked.source checked.authenticated
                (by simpa only [same] using (CoreCallableReturnStorageProducer.check_sound
                  (declarations := declarations) (world := world) (ticket := .none) accepted))
                (by simpa only [same] using (of_decide_eq_true bounded))⟩
            else .error .storageReceiver
          else .error .storageDomain


/-- The enclosing source is the result of checking the SAME original root
annotation; body and binding judgments are outputs, never annotation fields. -/
structure Admission
    (root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows)
    (body : CoreCallableStaticProducer.Annotation entries owners richBindings code contract demand requirements plan rows)
    (storageBindings : CoreCallableReturnStorageProducer.Bindings) (lexical : LexicalBounds)
    (records : List CoreCallableReturnStorageProducer.BindingAnnotation)
    (storageAnnotation : CoreCallableReturnStorageProducer.Annotation) (storageResult : CallableContracts.Contract)
    (policy : Syntax.TicketPolicy) (declarations : Instantiation.DeclarationRegistry)
    (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (receiver originalBound : List Nat) where
  rootResult : CoreCallableStaticProducer.Result entries policy outward owners world allowed scope []
    rootCode rootContract rootDemand rootReq rootPlan rootRows [] receiver
  rootAccepted : CoreCallableStaticProducer.check root policy outward world allowed scope [] receiver = .ok rootResult
  path : BindPath receiver entries owners root body storageBindings lexical records
  bodyResult : CoreCallableStaticProducer.Result entries policy outward owners world allowed scope richBindings
    code contract demand requirements plan rows lexical receiver
  bodyAccepted : CoreCallableStaticProducer.check body policy outward world allowed scope lexical receiver = .ok bodyResult
  origins : Origins (CoreCallableStaticProducer.registry entries policy) declarations outward owners world allowed scope receiver
    rootCode code richBindings storageBindings lexical records
  storageAccepted : CoreCallableReturnStorageProducer.returnedCheck storageBindings originalBound code storageAnnotation = some storageResult
  storageDerived : CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment storageBindings) world .none code storageResult
  returnedBound : storageResult.storageOf ⊆ originalBound
  returningReceived : originalBound ⊆ receiver

/-- Execute the current root, selected initializer and actual body checks. -/
def admit_origin
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings code contract demand requirements plan rows}
    (path : BindPath receiver entries owners root body storageBindings lexical records)
    (storageAnnotation : CoreCallableReturnStorageProducer.Annotation) (storageResult : CallableContracts.Contract)
    (policy : Syntax.TicketPolicy) (declarations : Instantiation.DeclarationRegistry)
    (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (originalBound : List Nat) :
    Except Error (Admission root body storageBindings lexical records storageAnnotation storageResult
      policy declarations outward world allowed scope receiver originalBound) :=
  if received : CoreCallableGraphAnnotationChecks.subsetB originalBound receiver = true then
    match accepted : CoreCallableStaticProducer.check root policy outward world allowed scope [] receiver with
    | .error error => .error (.rich error)
    | .ok rootResult => do
        let origins ← checkPath path policy declarations outward world allowed scope
        match bodyAccepted : CoreCallableStaticProducer.check body policy outward world allowed scope lexical receiver with
        | .error error => .error (.rich error)
        | .ok bodyResult =>
            match stored : CoreCallableReturnStorageProducer.returnedCheck storageBindings originalBound code storageAnnotation with
            | none => .error .storageInitializer
            | some actual =>
                if same : actual = storageResult then
                  let receipt := CoreCallableReturnStorageProducer.returnedCheck_sound
                    (declarations := declarations) (world := world) (ticket := .none) stored
                  return ⟨rootResult, accepted, path, bodyResult, bodyAccepted, origins.down, by simpa only [same] using stored,
                    by simpa only [same] using receipt.1, by simpa only [same] using receipt.2, CoreCallableGraphAnnotationChecks.subsetB_sound received⟩
                else .error .storageDomain
  else .error .storageReceiver

/-- Current actual resources follow authentication rather than the public port. -/
theorem actual_resources
    (authenticated : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows) lexical receiver) :
    Syntax.resourceDependencies code.dependencies ⊆ receiver := by
  intro identity member
  apply (SourceSupport.bounds_iff.mp authenticated.current_support)
  apply List.mem_flatMap.mpr
  exact ⟨.resource identity, Syntax.mem_resourceDependencies.mp member, by simp⟩

theorem Admission.body_checked
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings code contract demand requirements plan rows}
    (admitted : Admission root body storageBindings lexical records storageAnnotation storageResult
      policy declarations outward world allowed scope receiver originalBound) :
    CoreCallableReturnStorageProducer.check storageBindings code storageAnnotation = some storageResult := by
  have accepted := admitted.storageAccepted
  cases checked : CoreCallableReturnStorageProducer.check storageBindings code storageAnnotation with
  | none => simp [CoreCallableReturnStorageProducer.returnedCheck, checked] at accepted
  | some actual =>
      simp [CoreCallableReturnStorageProducer.returnedCheck, checked] at accepted
      rcases accepted with ⟨bounded, rfl⟩
      rfl



/-- Both transports consume the SAME actual replacement at the exact storage
input; the retained root/path is the current admitted enclosing origin. -/
def substitute_current
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners ((name, input) :: richBindings)
      code result demand requirements plan rows}
    (current : Admission root body (CoreCallableReturnStorageProducer.extend storageBindings name storageInput)
      (lexical.extend name receiver) records storageBody storageResult policy declarations outward world allowed scope receiver originalBound)
    (valueAnnotation : CoreCallableStaticProducer.Annotation entries owners richBindings value input
      valueDemand valueReq valuePlan valueRows)
    (storageValue : CoreCallableReturnStorageProducer.Annotation)
    (stable : SubstitutionPolicyStable outward) (closed : ClosedValue value) :
    Except Error (PLift (∃ nextPlan : Plan _, ∃ nextRows : Rows (signature nextPlan),
      ∃ nextSource : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward owners world allowed scope
        (CoreCallableStaticProducer.environment richBindings) (code.subst name value) result demand requirements nextPlan nextRows,
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward nextSource lexical receiver ∧
      nextPlan = CoreCallablePlanSubstitution.plan code plan name value ∧ signature nextPlan = signature plan ∧ HEq nextRows rows ∧
      CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment storageBindings) world .none
        (code.subst name value) storageResult ∧ storageResult.storageOf ⊆ originalBound)) := do
  let actual ← (CoreCallableStaticProducer.check valueAnnotation policy outward world allowed scope lexical receiver).mapError Error.rich
  match stored : CoreCallableReturnStorageProducer.check storageBindings value storageValue with
  | none => .error .storageInitializer
  | some actualInput =>
      if same : actualInput = storageInput then
        let replacement := actual.source.value_summary closed.1
        have replacementAuth : Authenticated (CoreCallableStaticProducer.registry entries policy) outward replacement lexical receiver :=
          actual.authenticated.value_summary closed.1
        have valueResources := actual_resources replacementAuth
        have next := current.bodyResult.authenticated.substitution_reannotated_at stable
          (CoreCallableStaticProducer.environment richBindings) name input value lexical receiver rfl
          (fun _ _ => rfl) replacement closed valueResources (fun _ => replacementAuth)
        have paired := CoreCallableReturnStorageProducer.substitution_receipt
          (declarations := declarations) (world := world) (ticket := .none) current.body_checked
          (by simpa only [same] using stored) closed
        return ⟨by
          obtain ⟨nextPlan, nextRows, nextSource, auth, computed, sig, fullRows⟩ := next
          exact ⟨nextPlan, nextRows, nextSource, auth, computed, sig, fullRows, paired, current.returnedBound⟩⟩
      else .error .storageDomain


/-- Actual application checks the SAME operand at the exact storage domain
and the original full rich input. Public recipe certification is constructed. -/
def apply_current
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {function : CoreCallableStaticProducer.Annotation entries owners richBindings code
      (.function input output requests latent publicPlan publicRows) functionDemand functionReq functionPlan functionRows}
    (current : Admission root function storageBindings lexical records storageFunction
      (.function captures storageInput storageOutput) policy declarations outward world allowed scope receiver originalBound)
    (argument : CoreCallableStaticProducer.Annotation entries owners richBindings value input argumentDemand argumentReq argumentPlan argumentRows)
    (storageArgument : CoreCallableReturnStorageProducer.Annotation)
    (recipe : CoreCallableStaticProducer.RecipeTag publicPlan) (returnedTo : List Nat) :
    Except Error (PLift (∃ nextSource : IndexedSource (CoreCallableStaticProducer.registry entries policy)
      outward owners world allowed scope (CoreCallableStaticProducer.environment richBindings) (.app code value) output
      (functionDemand ++ argumentDemand) (.emitAfter (.sequence functionReq argumentReq) [] latent)
      (.sequence functionPlan (.sequence argumentPlan publicPlan))
      (CoreCallableContractSource.sequenceRows functionRows (CoreCallableContractSource.sequenceRows argumentRows publicRows)),
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward nextSource lexical receiver ∧
      CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment storageBindings) world .none
        (.app code value) storageOutput ∧ storageOutput.storageOf ⊆ returnedTo ∧ returnedTo ⊆ receiver)) := do
  let actual ← (CoreCallableStaticProducer.check argument policy outward world allowed scope lexical receiver).mapError Error.rich
  match stored : CoreCallableReturnStorageProducer.check storageBindings value storageArgument with
  | none => .error .storageInitializer
  | some actualInput =>
      if same : actualInput = storageInput then
        if admitted : CoreCallableGraphAnnotationChecks.subsetB requests allowed = true then
          if certified : recipe.check = true then
            if received : CoreCallableGraphAnnotationChecks.subsetB returnedTo receiver = true then
              if returned : decide (storageOutput.storageOf ⊆ returnedTo) = true then
                let nextSource := IndexedSource.app current.bodyResult.source actual.source
                  (CoreCallableGraphAnnotationChecks.subsetB_sound admitted) (recipe.sound certified).certified
                have support : SourceSupport.Bounds lexical.environment (Code.app code value).dependencies receiver := by
                  apply SourceSupport.bounds_iff.mpr
                  simpa only [Code.dependencies, ScopedPorts.Support.evaluate, List.flatMap_append] using
                    List.append_subset.mpr ⟨SourceSupport.bounds_iff.mp current.bodyResult.authenticated.current_support,
                      SourceSupport.bounds_iff.mp actual.authenticated.current_support⟩
                have auth : Authenticated (CoreCallableStaticProducer.registry entries policy) outward nextSource lexical receiver :=
                  .checked support (.app (admitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted)
                    (publicCertified := (recipe.sound certified).certified) current.bodyResult.authenticated actual.authenticated)
                have storage := CoreCallableReturnStorageProducer.app_receipt
                  (declarations := declarations) (world := world) (ticket := .none) current.body_checked
                  (by simpa only [same] using stored)
                return ⟨⟨nextSource, auth, storage, of_decide_eq_true returned, CoreCallableGraphAnnotationChecks.subsetB_sound received⟩⟩
              else .error .storageReceiver
            else .error .storageReceiver
          else .error (.rich .unsupportedRecipe)
        else .error (.rich .unavailableEffect)
      else .error .storageDomain

theorem Admission.returning_issued
    (current : Admission root body storageBindings lexical records storageAnnotation storageResult
      policy declarations outward world allowed scope receiver originalBound) : originalBound ⊆ world :=
  current.returningReceived.trans current.bodyResult.receivingIssued

theorem Admission.origin_receipt
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners richBindings code contract demand requirements plan rows}
    (current : Admission root body storageBindings lexical records storageAnnotation storageResult
      policy declarations outward world allowed scope receiver originalBound) :
    CoreCallableReturnStorageProducer.BindingAt rootCode code records ∧
      CoreCallableReturnStorageProducer.LexicalFits storageBindings lexical receiver ∧ storageResult.storageOf ⊆ world :=
  ⟨current.origins.binding_at, current.origins.lexical_fits,
    current.returnedBound.trans current.returning_issued⟩

#print axioms Origins.binding_at
#print axioms Origins.storage_origins
#print axioms Origins.lexical_fits
#print axioms checkPath
#print axioms admit_origin
#print axioms actual_resources
#print axioms Admission.body_checked
#print axioms substitute_current
#print axioms apply_current
#print axioms Admission.returning_issued
#print axioms Admission.origin_receipt
end Ash.OneShot.CoreCallablePairedOrigin
