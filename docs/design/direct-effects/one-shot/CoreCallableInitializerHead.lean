import CoreCallableCapturedLambdaConstructor
import CoreCallableRuntimeBindingOrigins
import CoreCallableCapturedRecipes
namespace Ash.OneShot.CoreCallableInitializerHead
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission CoreCallablePairedOrigin
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

section
variable {record : CoreCallableReturnStorageProducer.BindingAnnotation}
variable {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
variable {body : CoreCallableStaticProducer.Annotation entries owners ((captured,input)::tailRich) code contract demand requirements plan rows}
variable {current : Admission root body storageBindings lexical (record::records) storageAnnotation storageResult
  policy declarations outward world allowed scope receiver originalBound}

/-- Original left initializer data and computed checks, without a fabricated
left-child Admission or independently chosen rich Annotation. -/
structure Checked (current : Admission root body storageBindings lexical (record::records) storageAnnotation storageResult
    policy declarations outward world allowed scope receiver originalBound) where
  beforeStorage : CoreCallableReturnStorageProducer.Bindings
  beforeLexical : LexicalBounds
  initialDemand : List Nat
  initialRequirements : RecursiveRequirements.Requirements initialDemand
  dependencies : SourceDependencyAnnotations.Dependencies
  initialPlan : SourceDeclarationPlans.Plan dependencies
  initialRows : Rows (SourcePlanSignatures.signature initialPlan)
  annotation : CoreCallableStaticProducer.Annotation entries owners tailRich record.initializer input initialDemand initialRequirements initialPlan initialRows
  preceding : BindPath receiver entries owners root (.bind (parameter := captured) annotation body) beforeStorage beforeLexical records
  name : record.name = captured
  recordedResources : record.resources = receiver
  samePath : HEq current.path (BindPath.bind preceding record.annotation record.expected)
  storageBindingsExact : storageBindings = CoreCallableReturnStorageProducer.extend beforeStorage captured record.expected
  lexicalExact : lexical = beforeLexical.extend captured receiver
  actual : CoreCallableStaticProducer.Result entries policy outward owners world allowed scope tailRich
    record.initializer input initialDemand initialRequirements initialPlan initialRows beforeLexical receiver
  richAccepted : CoreCallableStaticProducer.check annotation policy outward world allowed scope beforeLexical receiver = .ok actual
  storageAccepted : CoreCallableReturnStorageProducer.check beforeStorage record.initializer record.annotation = some record.expected
  stored : CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment beforeStorage) world .none record.initializer record.expected
  bounded : record.expected.storageOf ⊆ receiver

def check (current : Admission root body storageBindings lexical (record::records) storageAnnotation storageResult
    policy declarations outward world allowed scope receiver originalBound) : Except Error (Checked current) := by
  cases pathEq : current.path with
  | @bind initializer _ _ _ initialDemand initialReq initialDependencies initialPlan initialRows _ _ _ _ _ _ _ _ _ =>
    rename_i beforeStorage beforeLexical initializerStorage inputStorage initialAnnotation currentBefore previous
    exact do
      match accepted : CoreCallableStaticProducer.check initialAnnotation policy outward world allowed scope beforeLexical receiver with
      | .error failure => .error (.rich failure)
      | .ok actual =>
        match stored : CoreCallableReturnStorageProducer.check beforeStorage initializer initializerStorage with
        | none => .error .storageInitializer
        | some result =>
          if same : result = inputStorage then
            if bounded : decide (inputStorage.storageOf ⊆ receiver) = true then
              return ⟨beforeStorage,beforeLexical,initialDemand,initialReq,initialDependencies,initialPlan,initialRows,
                initialAnnotation,previous,rfl,rfl,heq_of_eq pathEq,rfl,rfl,actual,accepted,
                by simpa only [same] using stored,CoreCallableReturnStorageProducer.check_sound (by simpa only [same] using stored),
                of_decide_eq_true bounded⟩
            else .error .storageReceiver
          else .error .storageDomain
/-- The actual generated initializer value supplies closure readiness. Its
original checked full contract and dependency bound are retained. -/
theorem Checked.value_ready (head : Checked current) (closed : ClosedValue record.initializer) :
    ∃ source : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward owners world allowed scope
      (CoreCallableStaticProducer.environment tailRich) record.initializer input [] (.request [] []) .pure Rows.pure,
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward source head.beforeLexical receiver ∧
      Syntax.resourceDependencies record.initializer.dependencies ⊆ receiver ∧
      Syntax.resourceDependencies record.initializer.dependencies ⊆ world := by
  have received := (CallableContracts.value_support head.stored closed.1).trans head.bounded
  exact ⟨head.actual.source.value_summary closed.1,
    head.actual.authenticated.value_summary closed.1, received, received.trans head.actual.receivingIssued⟩

end

section
open CoreCallableCapturedLambdaConstructor
open CoreCallableContractSource (Environment)
variable {record : CoreCallableReturnStorageProducer.BindingAnnotation}
variable {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
variable {body : CoreCallableStaticProducer.Annotation entries owners ((formal,argument)::(captured,input)::tailRich)
  bodyCode output bodyDemand bodyReq bodyPlan bodyRows}
variable {publicDependencies : SourceDependencyAnnotations.Dependencies}
variable {publicPlan : SourceDeclarationPlans.Plan publicDependencies}
variable {publicRows : Rows (SourcePlanSignatures.signature publicPlan)}
variable {publicRecipe : CoreCallableStaticProducer.RecipeTag publicPlan}
variable {refinement : CoreCallableStaticProducer.RefinementTag publicRows bodyRows}
variable {current : Admission root (.lambda (requests := requests) (latent := latent) body publicRecipe refinement)
  storageBindings lexical (record::records) storageAnnotation storageResult
  policy declarations outward world allowed scope receiver originalBound}

/-- The next finite tree is the deterministic Code-directed substitution of
this original callee tree with this original initializer tree. -/
theorem Checked.finite_substitution (head : Checked current) (closed : ClosedValue record.initializer) :
    CoreCallableReturnStorageProducer.check head.beforeStorage
      ((Code.lambda formal bodyCode).subst captured record.initializer)
      (CoreCallableCapturedRecipes.substitute (.lambda formal bodyCode) storageAnnotation captured record.annotation) = some storageResult := by
  have original := current.body_checked
  rw [head.storageBindingsExact] at original
  exact CoreCallableCapturedRecipes.check_substitute original head.storageAccepted closed

/-- Connect the actual original initializer checks to the SAME original lambda
constructor, without inventing an initializer Admission or future body source. -/
theorem Checked.reconstruct_lambda (head : Checked current)
    (closed : ClosedValue record.initializer) (stable : SubstitutionPolicyStable outward) :
    ∃ replacement : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward owners world allowed scope
      (CoreCallableStaticProducer.environment tailRich) record.initializer input [] (.request [] []) .pure Rows.pure,
    ∃ nextCode, ∃ family : Family (CoreCallableStaticProducer.registry entries policy) outward owners world
      (CoreCallableStaticProducer.environment tailRich) formal nextCode argument output requests latent publicPlan publicRows,
      Receipt current.bodyResult.source replacement stable closed nextCode family ∧
      Code.lambda formal nextCode = (Code.lambda formal bodyCode).subst captured record.initializer ∧
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward
        (family.whole (allowed := allowed) (scope := scope)) head.beforeLexical receiver ∧
      CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment head.beforeStorage)
        world .none ((Code.lambda formal bodyCode).subst captured record.initializer) storageResult ∧
      Syntax.resourceDependencies record.initializer.dependencies ⊆ world := by
  obtain ⟨replacement,authenticated,received,issued⟩ := head.value_ready closed
  have original : Authenticated (CoreCallableStaticProducer.registry entries policy) outward current.bodyResult.source
      (head.beforeLexical.extend captured receiver) receiver := by
    rw [← head.lexicalExact]
    exact current.bodyResult.authenticated
  obtain ⟨nextCode,family,receipt,computed,auth⟩ := reconstruct original stable replacement closed received authenticated
  have originalStored := current.storageDerived
  rw [head.storageBindingsExact] at originalStored
  have stored := CallableContracts.substitution originalStored
    (CallableContracts.closed_value_environment head.stored closed (CoreCallableReturnStorageProducer.environment head.beforeStorage)) closed
  exact ⟨replacement,nextCode,family,receipt,computed,auth,stored,issued⟩
end

section
open CoreValueRelation CoreCallableCapturedLambdaConstructor
variable {binder : CoreSyntax.Binder}
variable {record : CoreCallableReturnStorageProducer.BindingAnnotation}
variable {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
variable {body : CoreCallableStaticProducer.Annotation entries owners ((formal,argument)::(binder.id,input)::tailRich)
  bodyCode output bodyDemand bodyReq bodyPlan bodyRows}
variable {publicDependencies : SourceDependencyAnnotations.Dependencies}
variable {publicPlan : SourceDeclarationPlans.Plan publicDependencies}
variable {publicRows : Rows (SourcePlanSignatures.signature publicPlan)}
variable {publicRecipe : CoreCallableStaticProducer.RecipeTag publicPlan}
variable {refinement : CoreCallableStaticProducer.RefinementTag publicRows bodyRows}
variable {base : CoreMachine.State} {plain : PlainData}
variable {current : Admission root (.lambda (requests := requests) (latent := latent) body publicRecipe refinement)
  storageBindings lexical (record::records) storageAnnotation storageResult
  policy declarations outward world allowed plain.scope receiver originalBound}

/-- Actual generated initializer evaluation supplies the replacement value and
installed environment used by the original checked lambda constructor. -/
theorem Checked.generated_binding (head : Checked current)
    (origin : CoreCallablePairedCall.LambdaOrigin body publicRecipe refinement current)
    (history : CoreCallableGeneralHistory.GeneralHistory graph base.heap physical target)
    (scopeOrigin : CoreCallableReachableResume.CurrentScopeOrigin graph coreOwners plain.scope physical)
    (postorder : CoreTranslationFuel.Postorder graph)
    (lineage : CoreCallableSiteLineage.SiteLineage graph coreOwners plain.scope bindSite)
    (known : graph.node bindSite = some node) (kind : node.kind = .bind binder initializer bodySite)
    (it : CoreTranslation.translateFuel graph fuel coreOwners initializer = .ok (.lambda certificate.parameter certificate.rawBody))
    (bt : CoreTranslation.translateFuel graph fuel coreOwners bodySite = .ok rawBody)
    (closing : EnvCloses graph coreOwners base.heap environment
      (.bind binder.id (.lambda certificate.parameter certificate.rawBody) rawBody)
      (.bind binder.id record.initializer (.lambda formal bodyCode)))
    (closed : ClosedValue record.initializer) (ready : ClosedExcept binder.id (.lambda formal bodyCode))
    (context : plain.context = .bind binder.id (.lambda formal bodyCode))
    (checked : CoreCallableChecks.checkAmbient graph initializer coreOwners = .ok certificate)
    (stable : SubstitutionPolicyStable outward) :
    ∃ entered evaluated completed : CoreMachine.State,
    ∃ replacement : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward owners world allowed plain.scope
      (CoreCallableStaticProducer.environment tailRich) record.initializer input [] (.request [] []) .pure Rows.pure,
    ∃ nextCode, ∃ family : Family (CoreCallableStaticProducer.registry entries policy) outward owners world
      (CoreCallableStaticProducer.environment tailRich) formal nextCode argument output requests latent publicPlan publicRows,
      CoreMachine.next graph {base with control := .evaluate bindSite environment,frames := physical} = .stepped entered ∧
      CoreMachine.next graph entered = .stepped evaluated ∧
      CoreMachine.next graph evaluated = .stepped completed ∧
      completed.control = .evaluate bodySite (.binding binder.id (.closure certificate.parameter certificate.body environment) environment) ∧
      completed.frames = physical ∧
      ValueRel graph coreOwners evaluated.heap (.closure certificate.parameter certificate.body environment) record.initializer ∧
      EnvCloses graph coreOwners completed.heap (.binding binder.id (.closure certificate.parameter certificate.body environment) environment)
        rawBody (.lambda formal nextCode) ∧
      Receipt current.bodyResult.source replacement stable closed nextCode family ∧
      Code.lambda formal nextCode = (Code.lambda formal bodyCode).subst binder.id record.initializer ∧
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward
        (family.whole (allowed := allowed) (scope := plain.scope)) head.beforeLexical receiver ∧
      CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment head.beforeStorage)
        world .none (.lambda formal nextCode) storageResult ∧
      Syntax.resourceDependencies record.initializer.dependencies ⊆ world ∧
      CoreCallableReturnStorageProducer.check head.beforeStorage (.lambda formal nextCode)
        (CoreCallableCapturedRecipes.substitute (.lambda formal bodyCode) storageAnnotation binder.id record.annotation) = some storageResult ∧
      (∃ captures domain result bodyAnnotation,
        storageAnnotation = .node (some (.function captures domain result)) [bodyAnnotation] ∧
        storageResult = .function captures domain result ∧
        CoreCallableStorageRecipes.specialize
          (CoreCallableReturnStorageProducer.extend storageBindings formal domain)
          origin.calleeInst origin.bodyRecipe = some bodyAnnotation) := by
  obtain ⟨_,_,_,_,_,entered,evaluated,completed,entry,evaluate,finish,_,_,_,control,frames,related,_,nextClosing,_,_,_⟩ :=
    CoreCallableRuntimeBindingOrigins.checked_lambda_initializer_binding history scopeOrigin postorder lineage known kind it bt closing
      closed ready context checked current.origins rfl rfl
  obtain ⟨replacement,nextCode,family,receipt,computed,auth,stored,issued⟩ := head.reconstruct_lambda related.closed stable
  have finite := head.finite_substitution related.closed
  rw [← computed] at nextClosing stored finite
  exact ⟨entered,evaluated,completed,replacement,nextCode,family,entry,evaluate,finish,control,frames,related,nextClosing,
    receipt,computed,auth,stored,issued,finite,origin.attachment⟩
end
end Ash.OneShot.CoreCallableInitializerHead

#print axioms Ash.OneShot.CoreCallableInitializerHead.check
#print axioms Ash.OneShot.CoreCallableInitializerHead.Checked.value_ready
#print axioms Ash.OneShot.CoreCallableInitializerHead.Checked.finite_substitution
#print axioms Ash.OneShot.CoreCallableInitializerHead.Checked.reconstruct_lambda
#print axioms Ash.OneShot.CoreCallableInitializerHead.Checked.generated_binding
