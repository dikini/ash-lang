import CoreCallableInitializerHead

namespace Ash.OneShot.CoreCallableOuterLambdaOrigins
open ScopedExpressions ScopedExecution ProtectionContracts CoreValueRelation
open CoreCallableContractAdmission CoreCallableContractSource CoreCallablePairedOrigin
open CoreCallableCapturedLambdaConstructor CoreCallableInitializerHead
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- The actual full storage derivation forbids ticket captures. -/
theorem lambda_no_ticket
    (stored : CallableContracts.Derives declarations environment world ticket (.lambda formal body) contract) :
    ∀ owner, Syntax.Dependency.ticket owner ∉ (Code.lambda formal body).dependencies := by
  intro owner member
  cases stored with
  | leaf value closed captured =>
    have atom := CallableContracts.captures_iff.mp captured _ member
    cases atom
  | lambda body captured =>
    have atom := CallableContracts.captures_iff.mp captured _ member
    cases atom

/-- Current readiness and the unchanged full storage derivation construct
closedness of the actual substituted lambda; no future closed value is input. -/
theorem substituted_lambda_closed
    (stored : CallableContracts.Derives declarations environment world ticket
      ((Code.lambda formal body).subst captured value) contract)
    (closed : ClosedValue value) (ready : ClosedExcept captured (.lambda formal body)) :
    ClosedValue ((Code.lambda formal body).subst captured value) := by
  refine ⟨by simp [Code.subst,Code.IsValue],CallableContracts.resource_closed stored,?_⟩
  intro dependency member
  cases dependency with
  | resource identity => trivial
  | «variable» name =>
    have bound := ScopedTyping.substitution_bound_for_closed_value (Code.lambda formal body) captured closed member
    rcases List.mem_append.mp bound with original | inserted
    · have original := Syntax.mem_without.mp original
      have same := ready name original.1
      subst name
      exact original.2 rfl
    · exact closed.2.2 _ inserted
  | ticket owner =>
    simp only [Code.subst] at stored member
    exact lambda_no_ticket stored owner member

/-- Match the SAME successful current graph translation at any fuel to the
current executable ambient callable check's literal raw lambda. -/
theorem checked_raw_lambda
    (translated : CoreTranslation.translateFuel graph fuel owners site = .ok raw)
    (checked : CoreCallableChecks.checkAmbient graph site owners = .ok certificate) :
    raw = .lambda certificate.parameter certificate.rawBody := by
  have ambient := CoreCallableChecks.checkAmbient_sound checked
  obtain ⟨binder,node,present,kind,parameter⟩ := (CoreCallableChecks.checkFunction_sound ambient.1).2.1
  have current : CoreTranslation.translateFuel graph (graph.nodes.length + 1 + 1) owners site =
      .ok (.lambda certificate.parameter certificate.rawBody) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel,CoreTranslation.requireNode,present]
      change (do pure (Code.lambda binder.id (← CoreTranslation.translateFuel graph (graph.nodes.length + 1) owners certificate.body))) = _
      rw [ambient.2,parameter]
      rfl
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel (graph.nodes.length + 1 + 1)) owners site raw (Nat.le_max_left _ _) translated
  have two := CoreTranslationFuel.success_mono graph (graph.nodes.length + 1 + 1) (max fuel (graph.nodes.length + 1 + 1)) owners site
    (.lambda certificate.parameter certificate.rawBody) (Nat.le_max_right _ _) current
  exact Except.ok.inj (one.symm.trans two)

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

/-- Actual outer lambda evaluation captures the SAME generated environment and
retains the reconstructed full family, original storage result and finite tree. -/
theorem Checked.outer_lambda (head : Checked current)
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
    (stable : SubstitutionPolicyStable outward)
    (calleeChecked : CoreCallableChecks.checkAmbient graph bodySite coreOwners = .ok calleeCertificate) :
    ∃ entered evaluated completed outer : CoreMachine.State,
    ∃ replacement : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward owners world allowed plain.scope
      (CoreCallableStaticProducer.environment tailRich) record.initializer input [] (.request [] []) .pure Rows.pure,
    ∃ nextCode, ∃ family : Family (CoreCallableStaticProducer.registry entries policy) outward owners world
      (CoreCallableStaticProducer.environment tailRich) formal nextCode argument output requests latent publicPlan publicRows,
      CoreMachine.next graph {base with control := .evaluate bindSite environment,frames := physical} = .stepped entered ∧
      CoreMachine.next graph entered = .stepped evaluated ∧
      CoreMachine.next graph evaluated = .stepped completed ∧
      CoreAdministrativeSteps.ValueWitness graph coreOwners completed outer (.lambda formal nextCode) ∧
      outer.control = .returned (.closure calleeCertificate.parameter calleeCertificate.body
        (.binding binder.id (.closure certificate.parameter certificate.body environment) environment)) ∧
      ValueRel graph coreOwners outer.heap (.closure calleeCertificate.parameter calleeCertificate.body
        (.binding binder.id (.closure certificate.parameter certificate.body environment) environment)) (.lambda formal nextCode) ∧
      calleeCertificate.parameter = formal ∧
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
  obtain ⟨entered,evaluated,completed,replacement,nextCode,family,entry,evaluate,finish,control,frames,related,nextClosing,
    receipt,computed,auth,stored,issued,finite,attachment⟩ :=
    head.generated_binding origin history scopeOrigin postorder lineage known kind it bt closing closed ready context checked stable
  have originalClosing := nextClosing
  have rawSame := checked_raw_lambda bt calleeChecked
  rw [rawSame] at nextClosing
  have storedOriginal := stored
  rw [computed] at storedOriginal
  have nextClosed := substituted_lambda_closed storedOriginal related.closed ready
  rw [← computed] at nextClosed
  obtain ⟨nextBody,shape⟩ := nextClosing.lambda_shape_at _ _ rfl
  have sameFormal : calleeCertificate.parameter = formal := (Code.lambda.inj shape).1.symm
  let saved := CoreMachine.Environment.binding binder.id (.closure certificate.parameter certificate.body environment) environment
  let outer : CoreMachine.State := {completed with control := .returned (.closure calleeCertificate.parameter calleeCertificate.body saved), frames := physical, observations := completed.observations ++ [.entered bodySite]}
  obtain ⟨witness,_⟩ := CoreCallableChecks.checked_lambda_evaluate (base := completed) calleeChecked nextClosing nextClosed physical
  have start : {completed with control := .evaluate bodySite saved,frames := physical} = completed := by
    dsimp only [saved]
    rw [← control,← frames]
  rw [start] at witness
  change CoreAdministrativeSteps.ValueWitness graph coreOwners completed outer (.lambda formal nextCode) at witness
  obtain ⟨value,returned,valueRelated⟩ := witness.returned
  have valueSame : value = .closure calleeCertificate.parameter calleeCertificate.body saved := by injection returned.symm
  subst value
  exact ⟨entered,evaluated,completed,outer,replacement,nextCode,family,entry,evaluate,finish,witness,rfl,valueRelated,sameFormal,
    control,frames,related,originalClosing,receipt,computed,auth,stored,issued,finite,attachment⟩
end
end Ash.OneShot.CoreCallableOuterLambdaOrigins

#print axioms Ash.OneShot.CoreCallableOuterLambdaOrigins.lambda_no_ticket
#print axioms Ash.OneShot.CoreCallableOuterLambdaOrigins.substituted_lambda_closed
#print axioms Ash.OneShot.CoreCallableOuterLambdaOrigins.checked_raw_lambda
#print axioms Ash.OneShot.CoreCallableOuterLambdaOrigins.Checked.outer_lambda
