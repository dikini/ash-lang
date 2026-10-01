import CoreCallableStorageRecipes

namespace Ash.OneShot.CoreCallablePairedCall
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableReceiverRefinement (CallBounds LexicalBounds)
open CoreCallableContractSource (Contract)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission
mutual
def annotationEq : CoreCallableReturnStorageProducer.Annotation → CoreCallableReturnStorageProducer.Annotation → Bool
  | .node left children, .node right others => decide (left = right) && annotationsEq children others
termination_by left _ => sizeOf left
decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

def annotationsEq : List CoreCallableReturnStorageProducer.Annotation → List CoreCallableReturnStorageProducer.Annotation → Bool
  | [], [] => true
  | first :: rest, other :: tail => annotationEq first other && annotationsEq rest tail
  | _, _ => false
termination_by left _ => sizeOf left
decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega
end

mutual
theorem annotationEq_sound {left right : CoreCallableReturnStorageProducer.Annotation}
    (same : annotationEq left right = true) : left = right := by
  cases left with
  | node data children =>
    cases right with
    | node other tail =>
      obtain ⟨dataSame, childrenSame⟩ : decide (data = other) = true ∧ annotationsEq children tail = true :=
        by simpa only [annotationEq, Bool.and_eq_true] using same
      have head : data = other := of_decide_eq_true dataSame
      have body := annotationsEq_sound childrenSame
      rw [head, body]
termination_by sizeOf left
decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

theorem annotationsEq_sound {left right : List CoreCallableReturnStorageProducer.Annotation}
    (same : annotationsEq left right = true) : left = right := by
  cases left with
  | nil => cases right <;> simp_all [annotationsEq]
  | cons first rest =>
    cases right with
    | nil => simp [annotationsEq] at same
    | cons other tail =>
      obtain ⟨headSame, tailSame⟩ : annotationEq first other = true ∧ annotationsEq rest tail = true :=
        by simpa only [annotationsEq, Bool.and_eq_true] using same
      have head := annotationEq_sound headSame
      have body := annotationsEq_sound tailSame
      rw [head, body]
termination_by sizeOf left
decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega
end

local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- The callee is indexed by its original literal lambda annotation and actual
paired initializer origin. The recipe is finite data, never a future judgment. -/
structure LambdaOrigin
    (body : CoreCallableStaticProducer.Annotation entries owners ((formal,input)::richBindings)
      bodyCode output bodyDemand bodyReq bodyPlan bodyRows)
    (publicRecipe : CoreCallableStaticProducer.RecipeTag publicPlan)
    (refinement : CoreCallableStaticProducer.RefinementTag publicRows bodyRows)
    (current : CoreCallablePairedOrigin.Admission root
      (.lambda (requests := requests) (latent := latent) body publicRecipe refinement)
      capturedBindings lexical records storageLambda storageContract policy declarations outward
      creationWorld allowed scope creationReceiver originalBound) where
  bodyRecipe : CoreCallableStorageRecipes.Recipe
  calleeInst : Instantiation.Environment
  attachment : ∃ captures domain result bodyAnnotation,
    storageLambda = .node (some (.function captures domain result)) [bodyAnnotation] ∧
    storageContract = .function captures domain result ∧
    CoreCallableStorageRecipes.specialize
      (CoreCallableReturnStorageProducer.extend capturedBindings formal domain)
      calleeInst bodyRecipe = some bodyAnnotation

def lambda_origin
    {body : CoreCallableStaticProducer.Annotation entries owners ((formal,input)::richBindings)
      bodyCode output bodyDemand bodyReq bodyPlan bodyRows}
    (current : CoreCallablePairedOrigin.Admission root
      (.lambda (requests := requests) (latent := latent) body publicRecipe refinement)
      capturedBindings lexical records storageLambda storageContract policy declarations outward
      creationWorld allowed scope creationReceiver originalBound)
    (calleeInst : Instantiation.Environment) (bodyRecipe : CoreCallableStorageRecipes.Recipe) :
    Option (LambdaOrigin body publicRecipe refinement current) :=
  match storageLambda with
  | .node (some (.function captures domain result)) [bodyAnnotation] =>
    match specialized : CoreCallableStorageRecipes.specialize
        (CoreCallableReturnStorageProducer.extend capturedBindings formal domain) calleeInst bodyRecipe with
    | none => none
    | some actual =>
      if same : annotationEq actual bodyAnnotation = true then
        if full : storageContract = .function captures domain result then
          some ⟨bodyRecipe, calleeInst, captures, domain, result, bodyAnnotation, rfl, full, by simpa only [annotationEq_sound same] using specialized⟩
        else none
      else none
  | _ => none

/-- Only nearest free captured entries used by this body are checked. -/
def capturesReceived (bindings : CoreCallableReturnStorageProducer.Bindings)
    (formal : Nat) (body : Code) (receiver : List Nat) : Bool :=
  body.dependencies.all fun dep => match dep with
    | .variable name => if name = formal then true else
        match CoreCallableReturnStorageProducer.lookup bindings name with
        | none => false
        | some stored => decide (stored.storageOf ⊆ receiver)
    | _ => true

theorem captured_received (accepted : capturesReceived bindings formal body receiver = true)
    (retained : Syntax.Dependency.variable name ∈ body.dependencies) (different : name ≠ formal) :
    ∃ stored, CoreCallableReturnStorageProducer.lookup bindings name = some stored ∧ stored.storageOf ⊆ receiver := by
  have check := List.all_eq_true.mp accepted (.variable name) retained
  change (if name = formal then true else match CoreCallableReturnStorageProducer.lookup bindings name with
    | none => false | some stored => decide (stored.storageOf ⊆ receiver)) = true at check
  rw [if_neg different] at check
  cases found : CoreCallableReturnStorageProducer.lookup bindings name with
  | none => simp [found] at check
  | some stored => exact ⟨stored, rfl, of_decide_eq_true (by simpa [found] using check)⟩

/-- Actual call specialization uses the callee captures and the exact actual
argument storage contract, not the caller's lexical environment. -/
def call_body_check {call : CallBounds creationWorld}
    (origin : LambdaOrigin (formal := formal) (input := input) (bodyCode := bodyCode)
      (capturedBindings := capturedBindings) (declarations := declarations) (creationWorld := creationWorld) body publicRecipe refinement current)
    {callerRoot : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners []
      callerRootCode callerRootContract callerRootDemand callerRootReq callerRootPlan callerRootRows}
    {callerBody : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      callerCode callerContract callerDemand callerReq callerPlan callerRows}
    {caller : CoreCallablePairedOrigin.Admission callerRoot callerBody callerBindings callerLexical
      callerRecords callerStorageAnnotation callerStorageResult callerPolicy declarations callerOutward
      call.world callerAllowed callerScope call.receiver callerOriginalBound}
    {argumentAnnotation : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      value input valueDemand valueReq valuePlan valueRows}
    (argument : CoreCallableStorageRecipes.ArgumentReceipt (declarations := declarations) call caller argumentAnnotation inst argumentRecipe) :
    Option CallableContracts.Contract := do
  if capturesReceived capturedBindings formal bodyCode call.receiver then
    let result ← CoreCallableStorageRecipes.check
      (CoreCallableReturnStorageProducer.extend capturedBindings formal argument.stored)
      origin.calleeInst bodyCode origin.bodyRecipe
    if result.storageOf ⊆ call.receiver then some result else none
  else none

theorem call_body_check_sound {call : CallBounds creationWorld}
    (origin : LambdaOrigin (formal := formal) (input := input) (bodyCode := bodyCode)
      (capturedBindings := capturedBindings) (declarations := declarations) (creationWorld := creationWorld) body publicRecipe refinement current)
    {callerRoot : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners []
      callerRootCode callerRootContract callerRootDemand callerRootReq callerRootPlan callerRootRows}
    {callerBody : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      callerCode callerContract callerDemand callerReq callerPlan callerRows}
    {caller : CoreCallablePairedOrigin.Admission callerRoot callerBody callerBindings callerLexical
      callerRecords callerStorageAnnotation callerStorageResult callerPolicy declarations callerOutward
      call.world callerAllowed callerScope call.receiver callerOriginalBound}
    {argumentAnnotation : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      value input valueDemand valueReq valuePlan valueRows}
    (argument : CoreCallableStorageRecipes.ArgumentReceipt (declarations := declarations) call caller argumentAnnotation inst argumentRecipe)
    (accepted : call_body_check origin argument = some result) :
    CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment capturedBindings)
      call.world .none (bodyCode.subst formal value) result ∧ result.storageOf ⊆ call.receiver := by
  unfold call_body_check at accepted
  split at accepted
  · cases checked : CoreCallableStorageRecipes.check
      (CoreCallableReturnStorageProducer.extend capturedBindings formal argument.stored)
      origin.calleeInst bodyCode origin.bodyRecipe with
    | none => simp [checked] at accepted
    | some stored =>
      simp [checked] at accepted
      obtain ⟨bounded, rfl⟩ := accepted
      constructor
      · apply CallableContracts.substitution
        · exact CoreCallableStorageRecipes.check_sound checked
        · exact CallableContracts.closed_value_environment argument.storageDerived argument.closed _
        · exact argument.closed
      · exact bounded
  · simp_all


/-- Computed exact agreement with the original stored callee domain/result. -/
def agrees (callee argument result : CallableContracts.Contract) : Bool :=
  match callee with
  | .function _ domain output => decide (domain = argument ∧ output = result)
  | _ => false

theorem agrees_sound (accepted : agrees callee argument result = true) :
    ∃ captures, callee = .function captures argument result := by
  cases callee with
  | storage bound => simp [agrees] at accepted
  | pair left right => simp [agrees] at accepted
  | function captures domain output =>
    have same : domain = argument ∧ output = result := of_decide_eq_true accepted
    exact ⟨captures, by rw [same.1, same.2]⟩

def paired_call {call : CallBounds creationWorld}
    (origin : LambdaOrigin (formal := formal) (input := input) (bodyCode := bodyCode)
      (capturedBindings := capturedBindings) (declarations := declarations) (storageContract := storageContract) (creationWorld := creationWorld) body publicRecipe refinement current)
    {callerRoot : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners []
      callerRootCode callerRootContract callerRootDemand callerRootReq callerRootPlan callerRootRows}
    {callerBody : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      callerCode callerContract callerDemand callerReq callerPlan callerRows}
    {caller : CoreCallablePairedOrigin.Admission callerRoot callerBody callerBindings callerLexical
      callerRecords callerStorageAnnotation callerStorageResult callerPolicy declarations callerOutward
      call.world callerAllowed callerScope call.receiver callerOriginalBound}
    {argumentAnnotation : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      value input valueDemand valueReq valuePlan valueRows}
    (argument : CoreCallableStorageRecipes.ArgumentReceipt (declarations := declarations) call caller argumentAnnotation inst argumentRecipe) :
    Option (PLift (∃ result,
      CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment capturedBindings)
        call.world .none (bodyCode.subst formal value) result ∧ result.storageOf ⊆ call.receiver ∧
      result.storageOf ⊆ call.world ∧ ∃ captures, storageContract = .function captures argument.stored result)) :=
  match accepted : call_body_check origin argument with
  | none => none
  | some result =>
    if exact : agrees storageContract argument.stored result = true then
      some ⟨⟨result, (call_body_check_sound origin argument accepted).1,
        (call_body_check_sound origin argument accepted).2,
        (call_body_check_sound origin argument accepted).2.trans call.receivingIssued, agrees_sound exact⟩⟩
    else none

theorem formal_specialization {call : CallBounds creationWorld}
    (origin : LambdaOrigin (formal := formal) (input := input) (bodyCode := .variable formal)
      (capturedBindings := capturedBindings) (declarations := declarations) (creationWorld := creationWorld) body publicRecipe refinement current)
    {callerRoot : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners []
      callerRootCode callerRootContract callerRootDemand callerRootReq callerRootPlan callerRootRows}
    {callerBody : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      callerCode callerContract callerDemand callerReq callerPlan callerRows}
    {caller : CoreCallablePairedOrigin.Admission callerRoot callerBody callerBindings callerLexical
      callerRecords callerStorageAnnotation callerStorageResult callerPolicy declarations callerOutward
      call.world callerAllowed callerScope call.receiver callerOriginalBound}
    {argumentAnnotation : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      value input valueDemand valueReq valuePlan valueRows}
    (argument : CoreCallableStorageRecipes.ArgumentReceipt (declarations := declarations) call caller argumentAnnotation inst argumentRecipe)
    (recipe : origin.bodyRecipe = .node none []) :
    call_body_check origin argument = some argument.stored := by
  have bounded := argument.argumentBounded.trans call.argumentReceived
  simp [call_body_check, capturesReceived, Code.dependencies, recipe,
    CoreCallableStorageRecipes.check, CoreCallableStorageRecipes.specialize,
    CoreCallableStorageRecipes.specializeList, CoreCallableReturnStorageProducer.check,
    CoreCallableReturnStorageProducer.extend, CoreCallableReturnStorageProducer.lookup, bounded]

theorem captured_specialization {call : CallBounds creationWorld}
    (origin : LambdaOrigin (formal := formal) (input := input) (bodyCode := .variable name)
      (capturedBindings := capturedBindings) (declarations := declarations) (creationWorld := creationWorld) body publicRecipe refinement current)
    {callerRoot : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners []
      callerRootCode callerRootContract callerRootDemand callerRootReq callerRootPlan callerRootRows}
    {callerBody : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      callerCode callerContract callerDemand callerReq callerPlan callerRows}
    {caller : CoreCallablePairedOrigin.Admission callerRoot callerBody callerBindings callerLexical
      callerRecords callerStorageAnnotation callerStorageResult callerPolicy declarations callerOutward
      call.world callerAllowed callerScope call.receiver callerOriginalBound}
    {argumentAnnotation : CoreCallableStaticProducer.Annotation argumentEntries argumentOwners callerRichBindings
      value input valueDemand valueReq valuePlan valueRows}
    (argument : CoreCallableStorageRecipes.ArgumentReceipt (declarations := declarations) call caller argumentAnnotation inst argumentRecipe)
    (recipe : origin.bodyRecipe = .node none []) (different : name ≠ formal)
    (known : CoreCallableReturnStorageProducer.lookup capturedBindings name = some stored)
    (received : stored.storageOf ⊆ call.receiver) :
    call_body_check origin argument = some stored := by
  simp [call_body_check, capturesReceived, Code.dependencies, recipe, different, known,
    CoreCallableStorageRecipes.check, CoreCallableStorageRecipes.specialize,
    CoreCallableStorageRecipes.specializeList, CoreCallableReturnStorageProducer.check,
    CoreCallableReturnStorageProducer.extend, CoreCallableReturnStorageProducer.lookup, received]

#print axioms lambda_origin
#print axioms captured_received
#print axioms call_body_check_sound
#print axioms agrees_sound
#print axioms paired_call
#print axioms formal_specialization
#print axioms captured_specialization
end Ash.OneShot.CoreCallablePairedCall
