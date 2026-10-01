import CoreCallableCapturedSubstitution
namespace Ash.OneShot.CoreCallableCapturedLambdaConstructor
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (Registry Owners)
open CoreCallableRootRefinement (Refines)
open CoreCallableReceiverRefinement (CallBounds ReceiverRefines LexicalBounds)
open CoreCallableContractAdmission
open SourcePlannedChecks (Certified DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]

/-- Constructor output retains the whole pointwise private family. -/
structure Family (registry : Registry) (outward : List Instance) (owners : Owners)
    (world : List Nat) (environment : Environment) (parameter : Nat) (code : Code)
    (input output : Contract) (requests : List Instance) (latent : Footprint)
    {contractDependencies : Dependencies} (contractPlan : Plan contractDependencies) (contractRows : Rows (signature contractPlan)) where
  demand : List Nat
  requirements : Requirements demand
  dependencies : LexicalBounds → CallBounds world → Dependencies
  plans : ∀ lexical call, Plan (dependencies lexical call)
  rows : ∀ lexical call, Rows (signature (plans lexical call))
  body : ∀ lexical call, IndexedSource registry outward owners call.world requests .none
    (environment.extend parameter input) code output demand requirements (plans lexical call) (rows lexical call)
  bodyOutward : RecursiveOutward.Outward requirements (some latent)
  latentBound : ∀ request ∈ latent, request.effect ∈ requests
  publicCertified : Certified outward world contractPlan
  formed : ScopedPorts.InWorld world (Contract.function input output requests latent contractPlan contractRows).port

theorem Family.whole (family : Family registry outward owners world environment parameter code input output requests latent contractPlan contractRows) :
    IndexedSource registry outward owners world allowed scope environment (.lambda parameter code)
      (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure :=
  .receiverLambda family.body family.bodyOutward family.latentBound family.publicCertified family.formed

/-- Ordinary lambdas retain the original actual fixed body under world transport;
receiver lambdas retain the original actual lexical/call-indexed family. -/
inductive Origin {registry : Registry} {outward : List Instance} {owners : Owners}
    {world : List Nat} {environment : Environment} {parameter : Nat} {code : Code}
    {input output : Contract} {requests : List Instance} {latent : Footprint}
    {contractDependencies : Dependencies} {contractPlan : Plan contractDependencies} {contractRows : Rows (signature contractPlan)}
    {allowed : List Instance} {scope : Execution.Scope} :
    IndexedSource registry outward owners world allowed scope environment (.lambda parameter code)
      (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure →
    Family registry outward owners world environment parameter code input output requests latent contractPlan contractRows → Prop where
  | receiver (family : Family registry outward owners world environment parameter code input output requests latent contractPlan contractRows) :
      Origin family.whole family
  | ordinary
      (body : IndexedSource registry outward owners world requests .none (environment.extend parameter input)
        code output demand requirements plan rows)
      (refinement : Refines contractRows rows)
      (bodyOutward : RecursiveOutward.Outward requirements (some latent))
      (latentBound : ∀ request ∈ latent, request.effect ∈ requests)
      (publicCertified : Certified outward world contractPlan)
      (formed : ScopedPorts.InWorld world (Contract.function input output requests latent contractPlan contractRows).port) :
      Origin (IndexedSource.lambda body refinement bodyOutward latentBound publicCertified formed)
        ⟨demand,requirements,(fun _ _ => _),(fun _ _ => plan),(fun _ _ => rows),
          (fun _ call => body.world_weaken call.worldExtended),bodyOutward,latentBound,publicCertified,formed⟩

def Family.Authentic (family : Family registry outward owners world environment parameter code input output requests latent contractPlan contractRows) : Prop :=
  (∀ lexical call, LexicalBounds.Known lexical (Code.lambda parameter code).dependencies →
    ScopedPorts.Support.evaluate lexical.environment (Code.lambda parameter code).dependencies ⊆ call.receiver →
    Authenticated registry outward (family.body lexical call) (lexical.extend parameter call.argument) call.receiver) ∧
  (∀ lexical call, LexicalBounds.Known lexical (Code.lambda parameter code).dependencies →
    ScopedPorts.Support.evaluate lexical.environment (Code.lambda parameter code).dependencies ⊆ call.receiver →
    ReceiverRefines contractRows (family.rows lexical call) call.receiver
      (ScopedPorts.Support.evaluate (lexical.extend parameter call.argument).environment code.dependencies))

theorem extract
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment (.lambda parameter code)
        (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure)
      lexical receiver) :
    ∃ family : Family registry outward owners world environment parameter code input output requests latent contractPlan contractRows,
      Origin source family ∧ family.Authentic ∧ LexicalBounds.Known lexical (Code.lambda parameter code).dependencies := by
  cases checked with
  | checked current hereditary =>
    cases hereditary with
    | lambda refinement bodyOutward latentBound publicCertified formed known body =>
      rename_i originalBody
      let family : Family registry outward owners world environment parameter code input output requests latent contractPlan contractRows :=
        ⟨_,_,(fun _ _ => _),(fun _ _ => _),(fun _ _ => _),(fun _ call => originalBody.world_weaken call.worldExtended),
          bodyOutward,latentBound,publicCertified,formed⟩
      exact ⟨family,.ordinary originalBody refinement bodyOutward latentBound publicCertified formed,
        ⟨body,fun _ _ _ _ => ReceiverRefines.of_universal refinement _ _⟩,known⟩
    | receiverLambda bodyOutward latentBound publicCertified formed known body refinement =>
      rename_i originalBody
      let family : Family registry outward owners world environment parameter code input output requests latent contractPlan contractRows :=
        ⟨_,_,_,_,_,originalBody,bodyOutward,latentBound,publicCertified,formed⟩
      exact ⟨family,.receiver family,⟨body,refinement⟩,known⟩

omit evidence in
private theorem cast_rows_heq {first second : SourcePlanSignatures.Signature dependencies}
    (same : first = second) (rows : Rows second) : HEq (same.symm ▸ rows) rows := by cases same; rfl

omit evidence in
private theorem closed_evaluation {value : Code} (closed : ClosedValue value) (environment : ScopedPorts.Support.Env) :
    ScopedPorts.Support.evaluate environment value.dependencies = Syntax.resourceDependencies value.dependencies := by
  rw [ScopedPorts.Support.evaluation_congr (destination := ScopedPorts.Support.empty)
    (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))]
  exact ScopedPorts.Support.empty_evaluation _

omit evidence in
private theorem refinement_rows {first second : SourcePlanSignatures.Signature dependencies}
    {original : Rows first} {changed : Rows second}
    (refinement : ReceiverRefines contractRows original receiver required) (same : second = first)
    (aligned : HEq changed original) (received : required ⊆ receiver) :
    ReceiverRefines contractRows changed receiver nextRequired := by
  cases same; cases eq_of_heq aligned
  exact {
    code := refinement.code
    checked := by
      intro ambient outward actions budget phases world installations scope hints context retained certificate _ issued visible pending checked
      exact refinement.checked ambient outward actions budget phases world installations context retained certificate received issued visible pending checked
    accounting := refinement.accounting }

/-- The restoration slot is computed from the actual closed replacement. -/
def restored (lexical : LexicalBounds) (name : Nat) (value : Code) : LexicalBounds :=
  lexical.extend name (Syntax.resourceDependencies value.dependencies)

/-- Every private family member is transformed at its exact restored point. -/
def Family.changed
    (family : Family registry outward owners world (environment.extend name replacementType) parameter code input output requests latent contractPlan contractRows)
    (stable : SubstitutionPolicyStable outward) (different : name ≠ parameter)
    (replacement : IndexedSource registry outward owners world allowed scope environment value replacementType [] (.request [] []) .pure Rows.pure)
    (closed : ClosedValue value) :
    Family registry outward owners world environment parameter (code.subst name value) input output requests latent contractPlan contractRows := {
  demand := family.demand
  requirements := family.requirements
  dependencies := fun lexical call => family.dependencies (restored lexical name value) call
  plans := fun lexical call => CoreCallablePlanSubstitution.plan code (family.plans (restored lexical name value) call) name value
  rows := fun lexical call => (CoreCallablePlanSubstitution.plan_signature code (family.plans (restored lexical name value) call) name closed.1).symm ▸ family.rows (restored lexical name value) call
  body := by
    intro lexical call
    let replacementAt := (((replacement.world_weaken call.worldExtended).value_allowed closed.1 requests .none).closed_environment closed (environment.extend parameter input))
    obtain ⟨nextPlan,nextRows,nextSource,computed,same,aligned⟩ :=
      (family.body (restored lexical name value) call).substitution_reannotated_at stable
        (environment.extend parameter input) name replacementType value
        (Environment.extend_commute environment name parameter replacementType input different) replacementAt closed
    cases computed
    have exactRows : HEq nextRows ((CoreCallablePlanSubstitution.plan_signature code (family.plans (restored lexical name value) call) name closed.1).symm ▸ family.rows (restored lexical name value) call) :=
      aligned.trans (cast_rows_heq (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) _).symm
    cases eq_of_heq exactRows
    exact nextSource
  bodyOutward := family.bodyOutward
  latentBound := family.latentBound
  publicCertified := family.publicCertified
  formed := family.formed }

theorem Family.changed_authentic
    (family : Family registry outward owners world (environment.extend name replacementType) parameter code input output requests latent contractPlan contractRows)
    (authentic : family.Authentic)
    (stable : SubstitutionPolicyStable outward) (different : name ≠ parameter)
    (replacement : IndexedSource registry outward owners world allowed scope environment value replacementType [] (.request [] []) .pure Rows.pure)
    (closed : ClosedValue value)
    (authenticated : Authenticated registry outward replacement sourceLexical sourceReceiver) :
    (family.changed stable different replacement closed).Authentic := by
  have callFacts : ∀ lexical : LexicalBounds, ∀ call : CallBounds world,
      LexicalBounds.Known lexical (Code.lambda parameter (code.subst name value)).dependencies →
      ScopedPorts.Support.evaluate lexical.environment (Code.lambda parameter (code.subst name value)).dependencies ⊆ call.receiver →
      LexicalBounds.Known (restored lexical name value) (Code.lambda parameter code).dependencies ∧
      ScopedPorts.Support.evaluate (restored lexical name value).environment (Code.lambda parameter code).dependencies ⊆ call.receiver := by
    intro lexical call known received
    have knownWhole : LexicalBounds.Known lexical ((Code.lambda parameter code).subst name value).dependencies :=
      by simpa only [Code.subst,if_neg different] using known
    have receivedWhole : ScopedPorts.Support.evaluate lexical.environment ((Code.lambda parameter code).subst name value).dependencies ⊆ call.receiver :=
      by simpa only [Code.subst,if_neg different] using received
    exact ⟨known_substitution_restore knownWhole closed,by
      simpa only [restored,LexicalBounds.environment_extend] using
        (substitution_support_reverse (environment := lexical.environment) (Code.lambda parameter code) name closed).trans receivedWhole⟩
  constructor
  · intro lexical call known received
    obtain ⟨oldKnown,oldReceived⟩ := callFacts lexical call known received
    let replacementAt := (((replacement.world_weaken call.worldExtended).value_allowed closed.1 requests .none).closed_environment closed (environment.extend parameter input))
    have lexicalAgree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
        ((restored lexical name value).extend parameter call.argument).lookup n =
          ((lexical.extend parameter call.argument).extend name (Syntax.resourceDependencies value.dependencies)).lookup n := by
      intro n _
      by_cases same : n = parameter
      · subst n; simp [restored,lexical_lookup_extend,Ne.symm different]
      · simp [restored,lexical_lookup_extend,same]
    have replacementAuth : Syntax.Dependency.variable name ∈ code.dependencies →
        Authenticated registry outward replacementAt (lexical.extend parameter call.argument) call.receiver := by
      intro occurs
      have free : Syntax.Dependency.variable name ∈ (Code.lambda parameter code).dependencies :=
        Syntax.mem_without.mpr ⟨occurs,by simpa using different⟩
      have actualReceived : Syntax.resourceDependencies value.dependencies ⊆ call.receiver := by
        intro identity member
        apply oldReceived
        exact List.mem_flatMap.mpr ⟨.variable name,free,by
          simp only [restored,LexicalBounds.environment,lexical_lookup_extend,↓reduceIte,Option.getD_some]
          exact member⟩
      apply (((authenticated.value_world_weaken closed.1 call.worldExtended).value_allowed closed.1 requests .none).closed_environment closed _).value_reauthenticate closed
      rw [closed_evaluation closed]
      exact actualReceived
    obtain ⟨nextPlan,nextRows,nextSource,nextAuth,computed,same,aligned⟩ :=
      (authentic.1 (restored lexical name value) call oldKnown oldReceived).substitution_reannotated_at stable
        (environment.extend parameter input) name replacementType value (lexical.extend parameter call.argument) (Syntax.resourceDependencies value.dependencies)
        (Environment.extend_commute environment name parameter replacementType input different) lexicalAgree replacementAt closed (List.Subset.refl _) replacementAuth
    cases computed
    have exactRows : HEq nextRows ((family.changed stable different replacement closed).rows lexical call) :=
      aligned.trans (cast_rows_heq (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) _).symm
    cases eq_of_heq exactRows
    exact nextAuth
  · intro lexical call known received
    obtain ⟨oldKnown,oldReceived⟩ := callFacts lexical call known received
    exact refinement_rows (authentic.2 (restored lexical name value) call oldKnown oldReceived)
      (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1)
      (cast_rows_heq (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) _)
      (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp
        (authentic.1 (restored lexical name value) call oldKnown oldReceived).current_support)


/-- Shadowing preserves the same private family at the same lexical/call point. -/
def Family.shadow {environment : Environment}
    (family : Family registry outward owners world (environment.extend parameter replacementType) parameter code input output requests latent contractPlan contractRows) :
    Family registry outward owners world environment parameter code input output requests latent contractPlan contractRows := {
  demand := family.demand
  requirements := family.requirements
  dependencies := family.dependencies
  plans := family.plans
  rows := family.rows
  body := fun lexical call => (family.body lexical call).environment_congr (by
    intro n _; by_cases same : n = parameter <;> simp [Environment.extend,same])
  bodyOutward := family.bodyOutward
  latentBound := family.latentBound
  publicCertified := family.publicCertified
  formed := family.formed }

theorem Family.shadow_authentic {environment : Environment}
    (family : Family registry outward owners world (environment.extend parameter replacementType) parameter code input output requests latent contractPlan contractRows)
    (authentic : family.Authentic) : family.shadow.Authentic := by
  constructor
  · intro lexical call known received
    exact (authentic.1 lexical call known received).environment_congr
      (by intro n _; by_cases same : n = parameter <;> simp [Environment.extend,same])
      (family.shadow.body lexical call)
  · exact authentic.2

/-- The endpoint family is forced to the deterministic constructor output. -/
inductive Receipt
    {registry : Registry} {outward : List Instance} {owners : Owners} {world : List Nat}
    {environment : Environment} {name parameter : Nat} {code value : Code}
    {replacementType input output : Contract} {requests : List Instance} {latent : Footprint}
    {contractDependencies : Dependencies} {contractPlan : Plan contractDependencies} {contractRows : Rows (signature contractPlan)}
    {allowed : List Instance} {scope : Execution.Scope}
    (source : IndexedSource registry outward owners world allowed scope (environment.extend name replacementType)
      (.lambda parameter code) (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure)
    (replacement : IndexedSource registry outward owners world allowed scope environment value replacementType [] (.request [] []) .pure Rows.pure)
    (stable : SubstitutionPolicyStable outward) (closed : ClosedValue value) :
    (nextCode : Code) → Family registry outward owners world environment parameter nextCode input output requests latent contractPlan contractRows → Prop where
  | changed
      (original : Family registry outward owners world (environment.extend name replacementType) parameter code input output requests latent contractPlan contractRows)
      (origin : Origin source original) (different : name ≠ parameter) :
      Receipt source replacement stable closed (code.subst name value) (original.changed stable different replacement closed)
  | shadow
      (same : name = parameter)
      (original : Family registry outward owners world (environment.extend parameter replacementType) parameter code input output requests latent contractPlan contractRows)
      (origin : Origin (same ▸ source) original) :
      Receipt source replacement stable closed code original.shadow

theorem reconstruct {environment : Environment}
    {source : IndexedSource registry outward owners world allowed scope (environment.extend name replacementType)
      (.lambda parameter code) (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure}
    (checked : Authenticated registry outward source (lexical.extend name bound) receiver)
    (stable : SubstitutionPolicyStable outward)
    (replacement : IndexedSource registry outward owners world allowed scope environment value replacementType [] (.request [] []) .pure Rows.pure)
    (closed : ClosedValue value) (actual : Syntax.resourceDependencies value.dependencies ⊆ bound)
    (authenticated : Authenticated registry outward replacement lexical receiver) :
    ∃ nextCode, ∃ family : Family registry outward owners world environment parameter nextCode input output requests latent contractPlan contractRows,
      Receipt (registry := registry) (owners := owners) (world := world) (environment := environment)
        (name := name) (parameter := parameter) (code := code) (value := value)
        (replacementType := replacementType) (input := input) (output := output)
        (requests := requests) (latent := latent) (contractPlan := contractPlan) (contractRows := contractRows)
        (allowed := allowed) (scope := scope) source replacement stable closed nextCode family ∧
      Code.lambda parameter nextCode = (Code.lambda parameter code).subst name value ∧
      Authenticated registry outward (family.whole (allowed := allowed) (scope := scope)) lexical receiver := by
  obtain ⟨original,origin,bodyAuthentic,known⟩ := extract checked
  have currentReceived : ScopedPorts.Support.evaluate lexical.environment ((Code.lambda parameter code).subst name value).dependencies ⊆ receiver :=
    (ScopedPorts.Support.substitution_support_bound (environment := lexical.environment) _ name closed actual).trans
      (by simpa only [LexicalBounds.environment_extend] using
        SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp checked.current_support)
  have nextKnown : LexicalBounds.Known lexical ((Code.lambda parameter code).subst name value).dependencies :=
    known_substitution_remove known closed
  by_cases same : name = parameter
  · subst name
    have authentic := original.shadow_authentic bodyAuthentic
    refine ⟨code,original.shadow,.shadow rfl original origin,?_,?_⟩
    · simp only [Code.subst,↓reduceIte]
    · refine Authenticated.checked (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr ?_) ?_
      · simpa only [Code.subst,↓reduceIte] using currentReceived
      · exact Hereditary.receiverLambda original.shadow.bodyOutward original.shadow.latentBound original.shadow.publicCertified original.shadow.formed
          (by simpa only [Code.subst,↓reduceIte] using nextKnown) authentic.1 authentic.2
  · let changed := original.changed stable same replacement closed
    have authentic := original.changed_authentic bodyAuthentic stable same replacement closed authenticated
    refine ⟨code.subst name value,changed,.changed original origin same,?_,?_⟩
    · simp only [Code.subst,if_neg same]
    · refine Authenticated.checked (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr ?_) ?_
      · simpa only [Code.subst,if_neg same] using currentReceived
      · exact Hereditary.receiverLambda changed.bodyOutward changed.latentBound changed.publicCertified changed.formed
          (by simpa only [Code.subst,if_neg same] using nextKnown) authentic.1 authentic.2


theorem Family.changed_plan
    (family : Family registry outward owners world (environment.extend name replacementType) parameter code input output requests latent contractPlan contractRows)
    (stable : SubstitutionPolicyStable outward) (different : name ≠ parameter)
    (replacement : IndexedSource registry outward owners world allowed scope environment value replacementType [] (.request [] []) .pure Rows.pure)
    (closed : ClosedValue value) (lexical : LexicalBounds) (call : CallBounds world) :
    HEq ((family.changed stable different replacement closed).plans lexical call)
      (CoreCallablePlanSubstitution.plan code (family.plans (restored lexical name value) call) name value) := HEq.rfl

theorem Family.changed_rows
    (family : Family registry outward owners world (environment.extend name replacementType) parameter code input output requests latent contractPlan contractRows)
    (stable : SubstitutionPolicyStable outward) (different : name ≠ parameter)
    (replacement : IndexedSource registry outward owners world allowed scope environment value replacementType [] (.request [] []) .pure Rows.pure)
    (closed : ClosedValue value) (lexical : LexicalBounds) (call : CallBounds world) :
    HEq ((family.changed stable different replacement closed).rows lexical call)
      (family.rows (restored lexical name value) call) :=
  cast_rows_heq (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) _
end

local instance : DeclarationPolicy := SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

section
variable {tailLexical : LexicalBounds}
variable {publicDependencies : SourceDependencyAnnotations.Dependencies}
variable {publicPlan : SourceDeclarationPlans.Plan publicDependencies}
variable {publicRows : Rows (SourcePlanSignatures.signature publicPlan)}
variable {calleeRoot : CoreCallableStaticProducer.Annotation entries calleeOwners []
  rootCode rootContract rootDemand rootReq rootPlan rootRows}
variable {calleeBody : CoreCallableStaticProducer.Annotation entries calleeOwners
  ((formal,input)::(captured,richInput)::tailRich) bodyCode output bodyDemand bodyReq bodyPlan bodyRows}
variable {publicRecipe : CoreCallableStaticProducer.RecipeTag publicPlan}
variable {refinement : CoreCallableStaticProducer.RefinementTag publicRows bodyRows}
variable {calleeCurrent : CoreCallablePairedOrigin.Admission calleeRoot
  (.lambda (requests := requests) (latent := latent) calleeBody publicRecipe refinement)
  (CoreCallableReturnStorageProducer.extend tailStorage captured storageInput)
  (tailLexical.extend captured receiver) records storageLambda storageContract
  policy declarations outward world calleeAllowed calleeScope receiver originalBound}
variable {callerRoot : CoreCallableStaticProducer.Annotation entries callerOwners []
  callerRootCode callerRootContract callerRootDemand callerRootReq callerRootPlan callerRootRows}
variable {callerBody : CoreCallableStaticProducer.Annotation entries callerOwners callerRich
  callerBodyCode callerBodyContract callerBodyDemand callerBodyReq callerBodyPlan callerBodyRows}
variable {callerCurrent : CoreCallablePairedOrigin.Admission callerRoot callerBody callerStorage callerLexical callerRecords
  callerStorageAnnotation callerStorageResult policy declarations outward world callerAllowed callerScope callerReceiver callerBound}
variable {valueAnnotation : CoreCallableStaticProducer.Annotation entries callerOwners callerRich value richInput
  valueDemand valueReq valuePlan valueRows}


/-- Actual same admitted origin and produced replacement return a whole source
constructed from the receipt's deterministic private family. -/
def close_callee_constructor
    (origin : CoreCallablePairedCall.LambdaOrigin calleeBody publicRecipe refinement calleeCurrent)
    (actualReplacement : CoreCallableCapturedSubstitution.Replacement origin callerCurrent valueAnnotation callerInst recipe)
    (stable : SubstitutionPolicyStable outward) :
    PLift (∃ nextCode, ∃ family : Family (CoreCallableStaticProducer.registry entries policy) outward calleeOwners world
      (CoreCallableStaticProducer.environment tailRich) formal nextCode input output requests latent publicPlan publicRows,
      Receipt (environment := CoreCallableStaticProducer.environment tailRich) (name := captured) (parameter := formal)
        (code := bodyCode) (value := value) (replacementType := richInput) (input := input) (output := output)
        (requests := requests) (latent := latent) (contractPlan := publicPlan) (contractRows := publicRows)
        (allowed := calleeAllowed) (scope := calleeScope)
        calleeCurrent.bodyResult.source actualReplacement.source stable actualReplacement.closed nextCode family ∧
      Code.lambda formal nextCode = (Code.lambda formal bodyCode).subst captured value ∧
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward
        (family.whole (allowed := calleeAllowed) (scope := calleeScope)) tailLexical receiver ∧
      CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment tailStorage) world .none
        (.lambda formal nextCode) storageContract ∧
      Syntax.resourceDependencies value.dependencies ⊆ world) := by
  refine ⟨?_⟩
  obtain ⟨nextCode,family,receipt,computed,authenticated⟩ := reconstruct calleeCurrent.bodyResult.authenticated stable
    actualReplacement.source actualReplacement.closed actualReplacement.resourcesReceived actualReplacement.authenticated
  have stored := CallableContracts.substitution calleeCurrent.storageDerived
    (CallableContracts.closed_value_environment actualReplacement.stored actualReplacement.closed (CoreCallableReturnStorageProducer.environment tailStorage)) actualReplacement.closed
  exact ⟨nextCode,family,receipt,computed,authenticated,by simpa only [computed,CoreCallableReturnStorageProducer.environment] using stored,
    actualReplacement.resourcesReceived.trans calleeCurrent.bodyResult.receivingIssued⟩
end

end Ash.OneShot.CoreCallableCapturedLambdaConstructor

#print axioms Ash.OneShot.CoreCallableCapturedLambdaConstructor.extract
#print axioms Ash.OneShot.CoreCallableCapturedLambdaConstructor.Family.changed
#print axioms Ash.OneShot.CoreCallableCapturedLambdaConstructor.Family.changed_authentic
#print axioms Ash.OneShot.CoreCallableCapturedLambdaConstructor.Family.shadow
#print axioms Ash.OneShot.CoreCallableCapturedLambdaConstructor.Family.shadow_authentic
#print axioms Ash.OneShot.CoreCallableCapturedLambdaConstructor.reconstruct
#print axioms Ash.OneShot.CoreCallableCapturedLambdaConstructor.Family.changed_plan
#print axioms Ash.OneShot.CoreCallableCapturedLambdaConstructor.Family.changed_rows
#print axioms Ash.OneShot.CoreCallableCapturedLambdaConstructor.close_callee_constructor
