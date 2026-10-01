import CoreCallablePairedCall
import CoreCallableAuthenticatedLambdaSubstitution

namespace Ash.OneShot.CoreCallableCapturedSubstitution
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableReceiverRefinement (CallBounds LexicalBounds)
open CoreCallableContractSource (Contract)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

private theorem closed_evaluation {value : Code} (closed : ClosedValue value) (environment : ScopedPorts.Support.Env) :
    ScopedPorts.Support.evaluate environment value.dependencies = Syntax.resourceDependencies value.dependencies := by
  rw [ScopedPorts.Support.evaluation_congr (destination := ScopedPorts.Support.empty)
    (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))]
  exact ScopedPorts.Support.empty_evaluation _

private theorem refinement_rows {first second : SourcePlanSignatures.Signature dependencies}
    {original : Rows first} {changed : Rows second}
    (refinement : CoreCallableReceiverRefinement.ReceiverRefines contractRows original receiver required) (same : second = first)
    (aligned : HEq changed original) (received : required ⊆ receiver) :
    CoreCallableReceiverRefinement.ReceiverRefines contractRows changed receiver nextRequired := by
  cases same; cases eq_of_heq aligned
  exact {
    code := refinement.code
    checked := by
      intro ambient outward actions budget phases world installations scope hints context retained certificate _ issued visible pending checked
      exact refinement.checked ambient outward actions budget phases world installations context retained certificate received issued visible pending checked
    accounting := refinement.accounting }

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

/-- Produced actual replacement: the finite annotation remains tied to its
caller specialization while the full rich value is transported to the callee. -/
structure Replacement
    (origin : CoreCallablePairedCall.LambdaOrigin calleeBody publicRecipe refinement calleeCurrent)
    (caller : CoreCallablePairedOrigin.Admission callerRoot callerBody callerStorage callerLexical callerRecords
      callerStorageAnnotation callerStorageResult policy declarations outward world callerAllowed callerScope callerReceiver callerBound)
    (annotation : CoreCallableStaticProducer.Annotation entries callerOwners callerRich value richInput
      valueDemand valueReq valuePlan valueRows)
    (callerInst : Instantiation.Environment) (recipe : CoreCallableStorageRecipes.Recipe) where
  actual : CoreCallableStaticProducer.Result entries policy outward callerOwners world callerAllowed callerScope callerRich
    value richInput valueDemand valueReq valuePlan valueRows callerLexical callerReceiver
  richAccepted : CoreCallableStaticProducer.check annotation policy outward world callerAllowed callerScope callerLexical callerReceiver = .ok actual
  finite : CoreCallableReturnStorageProducer.Annotation
  callerSpecialized : CoreCallableStorageRecipes.specialize callerStorage callerInst recipe = some finite
  storageChecked : CoreCallableReturnStorageProducer.check callerStorage value finite = some storageInput
  stored : CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment callerStorage) world .none value storageInput
  closed : ClosedValue value
  resourcesReceived : Syntax.resourceDependencies value.dependencies ⊆ receiver
  source : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward calleeOwners world calleeAllowed calleeScope
    (CoreCallableStaticProducer.environment tailRich) value richInput [] (.request [] []) .pure Rows.pure
  authenticated : Authenticated (CoreCallableStaticProducer.registry entries policy) outward source tailLexical receiver

def replacement
    (origin : CoreCallablePairedCall.LambdaOrigin calleeBody publicRecipe refinement calleeCurrent)
    (caller : CoreCallablePairedOrigin.Admission callerRoot callerBody callerStorage callerLexical callerRecords
      callerStorageAnnotation callerStorageResult policy declarations outward world callerAllowed callerScope callerReceiver callerBound)
    (annotation : CoreCallableStaticProducer.Annotation entries callerOwners callerRich value richInput
      valueDemand valueReq valuePlan valueRows)
    (callerInst : Instantiation.Environment) (recipe : CoreCallableStorageRecipes.Recipe) (closed : ClosedValue value) :
    Except CoreCallablePairedOrigin.Error (Replacement origin caller annotation callerInst recipe) := do
  match richAccepted : CoreCallableStaticProducer.check annotation policy outward world callerAllowed callerScope callerLexical callerReceiver with
  | .error error => .error (.rich error)
  | .ok actual =>
    match specialized : CoreCallableStorageRecipes.specialize callerStorage callerInst recipe with
    | none => .error .storageInitializer
    | some finite =>
      match checked : CoreCallableReturnStorageProducer.check callerStorage value finite with
      | none => .error .storageInitializer
      | some stored =>
        if exact : stored = storageInput then
          have storedProof : CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment callerStorage) world .none value storageInput :=
            CoreCallableReturnStorageProducer.check_sound (by simpa only [exact] using checked)
          have known : CoreCallableReturnStorageProducer.lookup
              (CoreCallableReturnStorageProducer.extend tailStorage captured storageInput) captured = some storageInput := by
            simp [CoreCallableReturnStorageProducer.lookup, CoreCallableReturnStorageProducer.extend]
          have actualReceived : Syntax.resourceDependencies value.dependencies ⊆ receiver := by
            obtain ⟨resources, found, storageBound, received⟩ := calleeCurrent.origins.lexical_fits captured storageInput known
            exact (CallableContracts.value_support storedProof closed.1).trans (storageBound.trans received)
          let neutral := (actual.source.value_summary closed.1).value_allowed closed.1 calleeAllowed .none
          have neutralAuth : Authenticated (CoreCallableStaticProducer.registry entries policy) outward neutral callerLexical callerReceiver :=
            (actual.authenticated.value_summary closed.1).value_allowed closed.1 calleeAllowed .none
          have agree : ∀ binder owner, Execution.Scope.none.resolve binder = some owner → callerOwners owner = calleeOwners owner := by
            intro binder owner resolved
            cases resolved
          let named := neutral.owners_congr agree
          have namedAuth : Authenticated (CoreCallableStaticProducer.registry entries policy) outward named callerLexical callerReceiver :=
            neutralAuth.owners_congr agree named
          let placed := (named.value_allowed closed.1 calleeAllowed calleeScope).closed_environment closed (CoreCallableStaticProducer.environment tailRich)
          have placedAuth : Authenticated (CoreCallableStaticProducer.registry entries policy) outward placed tailLexical receiver := by
            apply (((namedAuth.value_allowed closed.1 calleeAllowed calleeScope).closed_environment closed _).value_reauthenticate closed)
            rw [closed_evaluation closed]
            exact actualReceived
          return ⟨actual, richAccepted, finite, specialized, by simpa only [exact] using checked,
            storedProof, closed, actualReceived, placed, placedAuth⟩
        else .error .storageDomain

/-- The original origin and caller specialization remain identifiable in the
actual substituted lambda output. No desired next Source/Auth/Derives is input. -/
def close_callee
    (origin : CoreCallablePairedCall.LambdaOrigin calleeBody publicRecipe refinement calleeCurrent)
    (actualReplacement : Replacement origin callerCurrent valueAnnotation callerInst recipe)
    (stable : SubstitutionPolicyStable outward) :
    PLift (∃ nextPlan : SourceDeclarationPlans.Plan _, ∃ nextRows : Rows (SourcePlanSignatures.signature nextPlan),
      ∃ nextSource : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward calleeOwners world calleeAllowed calleeScope
        (CoreCallableStaticProducer.environment tailRich) ((Code.lambda formal bodyCode).subst captured value)
        (Contract.function input output requests latent publicPlan publicRows) [] (.request [] []) nextPlan nextRows,
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward nextSource tailLexical receiver ∧
      nextPlan = CoreCallablePlanSubstitution.plan (Code.lambda formal bodyCode) .pure captured value ∧
      SourcePlanSignatures.signature nextPlan = SourcePlanSignatures.signature SourceDeclarationPlans.Plan.pure ∧ HEq nextRows Rows.pure ∧
      CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment tailStorage) world .none
        ((Code.lambda formal bodyCode).subst captured value) storageContract) := by
  have next := calleeCurrent.bodyResult.authenticated.substitution_reannotated_at stable
    (CoreCallableStaticProducer.environment tailRich) captured richInput value tailLexical receiver rfl
    (fun _ _ => rfl) actualReplacement.source actualReplacement.closed actualReplacement.resourcesReceived (fun _ => actualReplacement.authenticated)
  have stored := CallableContracts.substitution calleeCurrent.storageDerived
    (CallableContracts.closed_value_environment actualReplacement.stored actualReplacement.closed (CoreCallableReturnStorageProducer.environment tailStorage)) actualReplacement.closed
  exact ⟨by
    obtain ⟨nextPlan,nextRows,nextSource,auth,computed,sig,rows⟩ := next
    exact ⟨nextPlan,nextRows,nextSource,auth,computed,sig,rows,stored⟩⟩

/-- Select and substitute the actual original private body at the restored
lexical/call point. The caller's finite replacement origin is retained by the
Replacement parameter; no desired next body judgment is an input. -/
theorem body_at
    (origin : CoreCallablePairedCall.LambdaOrigin calleeBody publicRecipe refinement calleeCurrent)
    (actualReplacement : Replacement origin callerCurrent valueAnnotation callerInst recipe)
    (stable : SubstitutionPolicyStable outward) (different : captured ≠ formal)
    (nextLexical : LexicalBounds) (call : CallBounds world)
    (known : LexicalBounds.Known nextLexical ((Code.lambda formal bodyCode).subst captured value).dependencies)
    (received : ScopedPorts.Support.evaluate nextLexical.environment
      ((Code.lambda formal bodyCode).subst captured value).dependencies ⊆ call.receiver) :
    ∃ oldDemand, ∃ oldReq : RecursiveRequirements.Requirements oldDemand, ∃ dependencies,
    ∃ oldPlan : SourceDeclarationPlans.Plan dependencies, ∃ oldRows : Rows (SourcePlanSignatures.signature oldPlan),
    ∃ oldSource : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward calleeOwners call.world requests .none
      ((CoreCallableStaticProducer.environment tailRich).extend captured richInput |>.extend formal input)
      bodyCode output oldDemand oldReq oldPlan oldRows,
    Authenticated (CoreCallableStaticProducer.registry entries policy) outward oldSource
      ((nextLexical.extend captured (Syntax.resourceDependencies value.dependencies)).extend formal call.argument) call.receiver ∧
    ∃ nextPlan : SourceDeclarationPlans.Plan dependencies, ∃ nextRows : Rows (SourcePlanSignatures.signature nextPlan),
    ∃ nextSource : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward calleeOwners call.world requests .none
      ((CoreCallableStaticProducer.environment tailRich).extend formal input)
      (bodyCode.subst captured value) output oldDemand oldReq nextPlan nextRows,
    Authenticated (CoreCallableStaticProducer.registry entries policy) outward nextSource
      (nextLexical.extend formal call.argument) call.receiver ∧
    nextPlan = CoreCallablePlanSubstitution.plan bodyCode oldPlan captured value ∧
    SourcePlanSignatures.signature nextPlan = SourcePlanSignatures.signature oldPlan ∧ HEq nextRows oldRows ∧
    CoreCallableReceiverRefinement.ReceiverRefines publicRows nextRows call.receiver
      (ScopedPorts.Support.evaluate (nextLexical.extend formal call.argument).environment (bodyCode.subst captured value).dependencies) ∧
    RecursiveOutward.Outward oldReq (some latent) := by
  let restored := nextLexical.extend captured (Syntax.resourceDependencies value.dependencies)
  have oldKnown : LexicalBounds.Known restored (Code.lambda formal bodyCode).dependencies :=
    known_substitution_restore known actualReplacement.closed
  have oldReceived : ScopedPorts.Support.evaluate restored.environment (Code.lambda formal bodyCode).dependencies ⊆ call.receiver := by
    simpa only [restored, LexicalBounds.environment_extend] using
      (substitution_support_reverse (environment := nextLexical.environment) (Code.lambda formal bodyCode) captured actualReplacement.closed).trans received
  obtain ⟨oldDemand,oldReq,deps,oldPlan,oldRows,oldSource,oldAuth,oldRefinement,oldOutward⟩ :=
    calleeCurrent.bodyResult.authenticated.lambda_current restored call oldKnown oldReceived
  let replacementAt := (((actualReplacement.source.world_weaken call.worldExtended).value_allowed actualReplacement.closed.1 requests .none).closed_environment actualReplacement.closed ((CoreCallableStaticProducer.environment tailRich).extend formal input))
  have lexicalAgree : ∀ n, Syntax.Dependency.variable n ∈ bodyCode.dependencies →
      (restored.extend formal call.argument).lookup n =
        ((nextLexical.extend formal call.argument).extend captured (Syntax.resourceDependencies value.dependencies)).lookup n := by
    intro n _
    by_cases same : n = formal
    · subst n; simp [restored, lexical_lookup_extend, Ne.symm different]
    · simp [restored, lexical_lookup_extend, same]
  have replacementAuth : Syntax.Dependency.variable captured ∈ bodyCode.dependencies →
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward replacementAt
        (nextLexical.extend formal call.argument) call.receiver := by
    intro occurs
    have free : Syntax.Dependency.variable captured ∈ (Code.lambda formal bodyCode).dependencies :=
      Syntax.mem_without.mpr ⟨occurs, by simpa using different⟩
    have actualReceived : Syntax.resourceDependencies value.dependencies ⊆ call.receiver := by
      intro identity member
      apply oldReceived
      exact List.mem_flatMap.mpr ⟨.variable captured, free, by
        simp only [restored, LexicalBounds.environment, lexical_lookup_extend, ↓reduceIte, Option.getD_some]
        exact member⟩
    apply (((actualReplacement.authenticated.value_world_weaken actualReplacement.closed.1 call.worldExtended).value_allowed actualReplacement.closed.1 requests .none).closed_environment actualReplacement.closed _).value_reauthenticate actualReplacement.closed
    rw [closed_evaluation actualReplacement.closed]
    exact actualReceived
  obtain ⟨nextPlan,nextRows,nextSource,nextAuth,computed,same,aligned⟩ :=
    oldAuth.substitution_reannotated_at stable ((CoreCallableStaticProducer.environment tailRich).extend formal input)
      captured richInput value (nextLexical.extend formal call.argument) (Syntax.resourceDependencies value.dependencies)
      (CoreCallableContractSource.Environment.extend_commute _ captured formal richInput input different)
      lexicalAgree replacementAt actualReplacement.closed (List.Subset.refl _) replacementAuth
  have nextRefinement : CoreCallableReceiverRefinement.ReceiverRefines publicRows nextRows call.receiver
      (ScopedPorts.Support.evaluate (nextLexical.extend formal call.argument).environment (bodyCode.subst captured value).dependencies) :=
    refinement_rows oldRefinement same aligned (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp oldAuth.current_support)
  exact ⟨oldDemand,oldReq,deps,oldPlan,oldRows,oldSource,oldAuth,nextPlan,nextRows,nextSource,nextAuth,computed,same,aligned,nextRefinement,oldOutward⟩


/-- A captured-variable body uses the already computed caller annotation,
without reinterpreting its slots in the callee environment. -/
theorem captured_storage
    (origin : CoreCallablePairedCall.LambdaOrigin calleeBody publicRecipe refinement calleeCurrent)
    (actualReplacement : Replacement origin callerCurrent valueAnnotation callerInst recipe) :
    CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment tailStorage) world .none
      ((Code.variable captured).subst captured value) storageInput ∧
    CoreCallableStorageRecipes.specialize callerStorage callerInst recipe = some actualReplacement.finite ∧
    Syntax.resourceDependencies value.dependencies ⊆ receiver := by
  exact ⟨by simpa only [Code.subst, ↓reduceIte] using
    (CallableContracts.closed_value_environment actualReplacement.stored actualReplacement.closed
      (CoreCallableReturnStorageProducer.environment tailStorage)),
    actualReplacement.callerSpecialized, actualReplacement.resourcesReceived⟩
end

/-- The formal slot remains the exact arbitrary full storage contract. -/
theorem formal_slot_check (bindings : CoreCallableReturnStorageProducer.Bindings)
    (formal captured : Nat) (replacement : Code) (slot : CallableContracts.Contract) (different : captured ≠ formal) :
    CoreCallableReturnStorageProducer.check (CoreCallableReturnStorageProducer.extend bindings formal slot)
      ((Code.variable formal).subst captured replacement) (.node none []) = some slot := by
  simp [Code.subst, different, CoreCallableReturnStorageProducer.check,
    CoreCallableReturnStorageProducer.lookup, CoreCallableReturnStorageProducer.extend]

theorem formal_lambda_code (formal captured : Nat) (replacement : Code) :
    (Code.lambda formal (.variable formal)).subst captured replacement = .lambda formal (.variable formal) := by
  by_cases same : captured = formal
  · simp [Code.subst, same]
  · simp [Code.subst, same]

theorem captured_lambda_code (formal captured : Nat) (replacement : Code) (different : captured ≠ formal) :
    (Code.lambda formal (.variable captured)).subst captured replacement = .lambda formal replacement := by
  simp [Code.subst, different]

/-- Variable shape is derived from the original actual source, at each selected
restored lexical point. It does not replace a functional family by a sample. -/
theorem variable_plan_rows
    (source : IndexedSource registry outward owners world allowed scope environment (.variable name) contract demand requirements plan rows) :
    HEq plan SourceDeclarationPlans.Plan.pure ∧ HEq rows Rows.pure := by
  cases source with
  | «variable» known formed => exact ⟨HEq.rfl,HEq.rfl⟩
end Ash.OneShot.CoreCallableCapturedSubstitution

#print axioms Ash.OneShot.CoreCallableCapturedSubstitution.replacement
#print axioms Ash.OneShot.CoreCallableCapturedSubstitution.close_callee
#print axioms Ash.OneShot.CoreCallableCapturedSubstitution.body_at
#print axioms Ash.OneShot.CoreCallableCapturedSubstitution.captured_storage
#print axioms Ash.OneShot.CoreCallableCapturedSubstitution.formal_slot_check
#print axioms Ash.OneShot.CoreCallableCapturedSubstitution.formal_lambda_code
#print axioms Ash.OneShot.CoreCallableCapturedSubstitution.captured_lambda_code
#print axioms Ash.OneShot.CoreCallableCapturedSubstitution.variable_plan_rows
