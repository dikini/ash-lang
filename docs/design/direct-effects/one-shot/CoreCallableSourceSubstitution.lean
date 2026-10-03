import CoreCallablePlanSubstitution
import CoreCallableReceiverRefinement
import CoreCallableContractOperandDomain

/-! Experimental authenticated contract source. Exact global operation contracts,
execution scope, scalar requirements, actual declaration plans and contextual
rows are separate indices. This is not legacy Auth or M4 admission. -/
namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (signature clauseSignatures modeSignatures)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableContractRegistries (Registry OwnerContract Owners)
open CoreCallableRootRefinement (Refines RootTransport)
open CoreCallableReceiverRefinement (CallBounds ReceiverRefines LexicalBounds)
open SourceDependencyAnnotations (RowAnnotation)
open RecursiveRequirements (Checked)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (Certified DeclarationPolicy)

/-- Fixed registry and owner policy shared by every recursive constructor.
Owner endpoints are mutable source indices; operations and policy are fixed. -/
structure Globals where
  operations : Instance → Nat → Option (Contract × Contract)
  policy : Syntax.TicketPolicy
  owners : Owners

def Globals.registry (globals : Globals) : Registry := ⟨globals.operations, globals.policy⟩
def Globals.withOwner (globals : Globals) (owner : Nat) (contract : OwnerContract) : Globals :=
  { globals with owners := globals.owners.insert owner contract }
@[simp] theorem Globals.registry_withOwner {globals : Globals} {owner : Nat} {contract : OwnerContract} : (globals.withOwner owner contract).registry = globals.registry := rfl

def Globals.ports (globals : Globals) : ScopedPorts.Signature :=
  fun effect operation => (globals.operations effect operation).map (fun pair => (pair.1.port, pair.2.port))

def Registry.lowerOperations (registry : Registry) : CoherentSourceTypes.Operations :=
  fun effect operation => (registry.operations effect operation).map (fun pair =>
    (pair.1.value.erase.erase, pair.2.value.erase.erase))

section
variable [evidence : DeclarationPolicy]

mutual
/-- Each lambda recursively authenticates its private body. Public-plan
certification is static declaration evidence, independent of port formation;
application cannot infer it from a function's immediate pure plan. -/
inductive IndexedSource (registry : Registry) (outward : List Instance) :
    Owners → List Nat → List Instance → Execution.Scope → Environment → Code → Contract →
    (demand : List Nat) → Requirements demand → {dependencies : Dependencies} →
    (plan : Plan dependencies) → Rows (signature plan) → Prop where
  | unit : IndexedSource registry outward owners world allowed scope environment .unit .unit [] (.request [] []) .pure Rows.pure
  | boolean : IndexedSource registry outward owners world allowed scope environment (.boolean value) .boolean [] (.request [] []) .pure Rows.pure
  | integer : IndexedSource registry outward owners world allowed scope environment (.integer value) .integer [] (.request [] []) .pure Rows.pure
  | reference (issued : identity ∈ world) :
      IndexedSource registry outward owners world allowed scope environment (.resourceRef (.activation identity)) (.reference identity) [] (.request [] []) .pure Rows.pure
  | variable (known : environment name = some contract) (formed : ScopedPorts.InWorld world contract.port) :
      IndexedSource registry outward owners world allowed scope environment (.variable name) contract [] (.request [] []) .pure Rows.pure
  | lambda {contractDependencies : Dependencies} {contractPlan : Plan contractDependencies}
      {contractRows : Rows (signature contractPlan)}
      (body : IndexedSource registry outward owners world requests .none (environment.extend parameter input) code output bodyDemand bodyReq actualPlan actualRows)
      (refinement : Refines contractRows actualRows)
      (bodyOutward : RecursiveOutward.Outward bodyReq (some latent))
      (latentBound : ∀ request ∈ latent, request.effect ∈ requests)
      (publicCertified : Certified outward world contractPlan)
      (formed : ScopedPorts.InWorld world (Contract.function input output requests latent contractPlan contractRows).port) :
      IndexedSource registry outward owners world allowed scope environment (.lambda parameter code)
        (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure
  /-- Open type evidence selects the same private rows at the actual call.
  Receiver-dependent refinement and hereditary support belong to the companion,
  rather than an unjustified universal checked premise in this type rule. -/
  | receiverLambda {contractDependencies : Dependencies} {contractPlan : Plan contractDependencies}
      {contractRows : Rows (signature contractPlan)}
      {privateDependencies : LexicalBounds → CallBounds world → Dependencies}
      {privatePlans : ∀ lexical call, Plan (privateDependencies lexical call)}
      {privateRows : ∀ lexical call, Rows (signature (privatePlans lexical call))}
      (body : ∀ lexical : LexicalBounds, ∀ call : CallBounds world,
        IndexedSource registry outward owners call.world requests .none
          (environment.extend parameter input) code output bodyDemand bodyReq
          (privatePlans lexical call) (privateRows lexical call))
      (bodyOutward : RecursiveOutward.Outward bodyReq (some latent))
      (latentBound : ∀ request ∈ latent, request.effect ∈ requests)
      (publicCertified : Certified outward world contractPlan)
      (formed : ScopedPorts.InWorld world (Contract.function input output requests latent contractPlan contractRows).port) :
      IndexedSource registry outward owners world allowed scope environment (.lambda parameter code)
        (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure
  | purePair (left : IndexedSource registry outward owners world allowed scope environment a first [] (.request [] []) .pure Rows.pure)
      (right : IndexedSource registry outward owners world allowed scope environment b second [] (.request [] []) .pure Rows.pure) :
      IndexedSource registry outward owners world allowed scope environment (.pair a b) (.pair first second) [] (.request [] []) .pure Rows.pure
  | pair (left : IndexedSource registry outward owners world allowed scope environment a first leftDemand leftReq leftPlan leftRows)
      (right : IndexedSource registry outward owners world allowed scope environment b second rightDemand rightReq rightPlan rightRows) :
      IndexedSource registry outward owners world allowed scope environment (.pair a b) (.pair first second)
        (leftDemand ++ rightDemand) (.sequence leftReq rightReq) (.sequence leftPlan rightPlan) (sequenceRows leftRows rightRows)
  | app (function : IndexedSource registry outward owners world allowed scope environment f
        (Contract.function input output requests latent contractPlan contractRows) functionDemand functionReq functionPlan functionRows)
      (argument : IndexedSource registry outward owners world allowed scope environment a input argumentDemand argumentReq argumentPlan argumentRows)
      (admitted : requests ⊆ allowed)
      (publicCertified : Certified outward world contractPlan) :
      IndexedSource registry outward owners world allowed scope environment (.app f a) output
        (functionDemand ++ argumentDemand) (.emitAfter (.sequence functionReq argumentReq) [] latent)
        (.sequence functionPlan (.sequence argumentPlan contractPlan)) (sequenceRows functionRows (sequenceRows argumentRows contractRows))
  | bind (initializer : IndexedSource registry outward owners world allowed scope environment a input initialDemand initialReq initialPlan initialRows)
      (body : IndexedSource registry outward owners world allowed scope (environment.extend parameter input) b output bodyDemand bodyReq bodyPlan bodyRows) :
      IndexedSource registry outward owners world allowed scope environment (.bind parameter a b) output
        (initialDemand ++ bodyDemand) (.sequence initialReq bodyReq) (.sequence initialPlan bodyPlan) (sequenceRows initialRows bodyRows)
  | branch (condition : IndexedSource registry outward owners world allowed scope environment test .boolean conditionDemand conditionReq conditionPlan conditionRows)
      (yes : IndexedSource registry outward owners world allowed scope environment a output yesDemand yesReq yesPlan yesRows)
      (no : IndexedSource registry outward owners world allowed scope environment b output noDemand noReq noPlan noRows)
      (same : yesDemand.Perm noDemand) :
      IndexedSource registry outward owners world allowed scope environment (.branch test a b) output
        (conditionDemand ++ yesDemand) (.sequence conditionReq (.choice yesReq noReq same))
        (.sequence conditionPlan (.choice yesPlan noPlan)) (sequenceRows conditionRows (choiceRows yesRows noRows))
  | perform (known : registry.operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operand : IndexedSource registry outward owners world allowed scope environment value input operandDemand operandReq operandPlan operandRows)
      (formed : ScopedPorts.InWorld world output.port) :
      IndexedSource registry outward owners world allowed scope environment (.perform (Instantiation.freezeEffect effect) operation value) output
        operandDemand (.emitAfter operandReq [] [⟨effect, operation, false⟩])
        (.sequence operandPlan (.request (effect := effect) (operation := operation))) (sequenceRows operandRows Rows.request)


  | handler {plans : ClausePlans arms families} {declarationRows : ClauseRows (clauseSignatures plans)}
      (body : IndexedSource registry outward owners world (effect :: residual) scope environment
        code answer demand requirements bodyPlan bodyRows)
      (clauses : ScopedPorts.ClausesTyped registry.ports world environment.ports effect answer.port residual arms)
      (capabilities : ClausesUse registry.policy arms)
      (coverage : ScopedPorts.Covers registry.ports effect arms)
      (unique : (ScopedTyping.clauseKeys arms).Nodup) (admitted : residual ⊆ allowed)
      (table : List (Nat × ClauseContract)) (modes : SourceTemplates.ClauseModes arms table)
      (declarations : SourceDeclarations registry outward owners world environment residual effect answer arms table plans declarationRows)
      (recipes : evidence.accepts outward required plans) :
      IndexedSource registry outward owners world allowed scope environment
        (.handle (Instantiation.freezeEffect effect) code arms) answer demand
        (requirements.prepend [.ordinary (.handler effect 0 table)])
        (.handler (effect := effect) (table := table) (clauses := arms) (families := families) required plans bodyPlan)
        (by simpa only [signature] using
          (@Rows.handler families (clauseSignatures plans) _ (signature bodyPlan) effect table required declarationRows bodyRows))


  | resume (known : owners owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (registry.policy binder).resume = true)
      (operand : IndexedSource registry outward owners world allowed scope environment value contract.input operandDemand operandReq operandPlan operandRows)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port) :
      IndexedSource registry outward owners world allowed scope environment (.resume binder value) contract.answer
        (operandDemand ++ owner :: contract.resumeDemand) (.sequence operandReq (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
        (.sequence operandPlan (.invoke (key := ⟨owner, .resume⟩))) (sequenceRows operandRows Rows.invoke)
  | cleanup {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
      {callbackRows : Rows (signature callbackPlan)}
      (callback : IndexedSource registry outward owners world allowed scope environment action
        (Contract.function .unit .unit requests latent callbackPlan callbackRows)
        callbackDemand callbackReq actualCallbackPlan actualCallbackRows)
      (body : IndexedSource registry outward owners world allowed scope environment code output bodyDemand bodyReq bodyPlan bodyRows)
      (admitted : requests ⊆ allowed) (publicCertified : Certified outward world callbackPlan) :
      IndexedSource registry outward owners world allowed scope environment (.cleanup action code) output
        (callbackDemand ++ bodyDemand)
        (.emitAfter (.sequence callbackReq bodyReq) [] (qualify true latent))
        (.sequence actualCallbackPlan (.cleanup (needs := requests) callbackPlan bodyPlan))
        (by simpa only [signature] using (Rows.sequence actualCallbackRows (Rows.cleanup (needs := requests) latent callbackRows bodyRows)))
  /-- Resource families remain total at every identity; recursive evidence is
  required only at fresh openings of this SAME original body template. -/
  | resource {bodyRequirements : Nat → Requirements bodyDemand}
      {bodyDependencies : Nat → Dependencies}
      {bodyPlans : ∀ identity, Plan (bodyDependencies identity)}
      {bodyRows : ∀ identity, Rows (signature (bodyPlans identity))}
      (initializer : IndexedSource registry outward owners world allowed scope environment
        initial .integer initialDemand initialRequirements initialPlan initialRows)
      (body : ∀ identity, identity ∉ world →
        IndexedSource registry outward owners (world ++ [identity]) (.cell identity :: residual)
          scope environment (code.instantiate (Instantiation.Environment.empty.bind binder identity))
          output bodyDemand (bodyRequirements identity) (bodyPlans identity) (bodyRows identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world →
        ResourceRequirements.Hides identity (bodyRequirements identity) outwardRequirements) :
      IndexedSource registry outward owners world allowed scope environment (.resource binder initial code)
        output (initialDemand ++ bodyDemand) (.sequence initialRequirements outwardRequirements)
        (.sequence initialPlan (.resource bodyPlans))
        (sequenceRows initialRows (Rows.resource bodyRows))
  | discard (known : owners owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (registry.policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed) :
      IndexedSource registry outward owners world allowed scope environment (.discard binder) .unit
        (owner :: contract.closeDemand) (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) (.invoke (key := ⟨owner, .dispose⟩)) Rows.invoke


/-- Scalar row authentication and the recursively derived actual private body
share one source, requirement tree, plan and complete row decoration. -/
inductive SourceBody (registry : Registry) (outward : List Instance) :
    Owners → List Nat → List Instance → Execution.Scope → Environment → Code → Contract →
    ClauseRowAdmission.Header → {dependencies : Dependencies} →
    (plan : Plan dependencies) → Rows (signature plan) → Prop where
  | typed (source : IndexedSource registry outward owners world allowed scope environment code answer demand requirements plan rows)
      (normal : ClauseRowAdmission.Rows header requirements
        (ClauseRowAdmission.SourceStore (Registry.lowerOperations registry) header.owner header.contract))
      (closing : ClauseRowAdmission.ProtectedRows header requirements
        (ClauseRowAdmission.SourceStore (Registry.lowerOperations registry) header.owner header.contract)) :
      SourceBody registry outward owners world allowed scope environment code answer header plan rows

/-- Both offered modes authenticate every owner-indexed private body. Logical
owner substitution is universal; allocation freshness is a separate runtime fact. -/
inductive SourceOffer (registry : Registry) (outward : List Instance) :
    Owners → List Nat → Environment → List Instance → Nat → Nat → Contract → Contract → Contract →
    List Instance → List Instance → Code → Bool → Bool → Option Footprint →
    {family : Option (Nat → Dependencies)} → (plans : ModePlans family) →
    ModeRows (modeSignatures plans) → Prop where
  | unavailable : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes none .unavailable .unavailable
  | available {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
      {rows : ∀ owner, Rows (signature (plans owner))}
      (resumeInterface : code.requiredActions.resume = true → resumeEffects = allowed)
      (closeInterface : code.requiredActions.dispose = true → closeEffects = allowed)
      (source : ∀ owner (contract : OwnerContract),
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceBody registry outward (owners.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.lower, disposes, row⟩ (plans owner) (rows owner)) :
      SourceOffer registry outward owners world environment allowed parameter binder argument input answer
        resumeEffects closeEffects code held disposes (some row) (.available plans) (.available rows)

inductive SourceDeclarations (registry : Registry) (outward : List Instance) :
    Owners → List Nat → Environment → List Instance → Instance → Contract → (clauses : Clauses) →
    List (Nat × ClauseContract) → {families : ClauseDependencies} →
    (plans : ClausePlans clauses families) → ClauseRows (clauseSignatures plans) → Prop where
  | nil : SourceDeclarations registry outward owners world environment allowed requested answer .nil [] .nil .nil
  | cons (supportBound : List Nat) (known : registry.operations requested operation = some (argument, input))
      (ordinary : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body false dispose ordinaryRow ordinaryPlan ordinaryRows)
      (protectedMode : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body true dispose protectedRow protectedPlan protectedRows)
      (rest : SourceDeclarations registry outward owners world environment allowed requested answer clauses table restPlan restRows) :
      SourceDeclarations registry outward owners world environment allowed requested answer
        (.cons operation parameter binder body clauses)
        ((operation, ⟨dispose, ordinaryRow, protectedRow⟩) :: table)
        (.cons (operation := operation) (parameter := parameter) (binder := binder) (body := body) ordinaryPlan protectedPlan restPlan)
        (by simpa only [clauseSignatures] using
          (@ClauseRows.cons _ (modeSignatures ordinaryPlan) _ (modeSignatures protectedPlan) _ (clauseSignatures restPlan)
            operation body.requiredActions ordinaryRows protectedRows restRows supportBound))
end

/-- Current closed operand support is bounded by its SAME full operation domain. -/
theorem IndexedSource.closed_support_in_domain
    (source : IndexedSource registry outward owners world allowed scope environment code argument demand requirements plan rows)
    (closed : ClosedValue code)
    (received : ScopedPorts.Support.evaluate ScopedPorts.Support.empty code.dependencies ⊆ receiver) :
    ScopedPorts.Support.evaluate ScopedPorts.Support.empty code.dependencies ⊆
      CoreCallableContractOperandDomain.domainSupport argument receiver := by
  cases argument <;> simp only [CoreCallableContractOperandDomain.domainSupport]
  all_goals first
    | exact received
    | cases code <;> simp_all [ClosedValue, Code.IsValue]
      all_goals cases source <;> simp [Code.dependencies, ScopedPorts.Support.evaluate]

/-- Compatibility view: the immutable registry is a parameter; owner table
and historical world are genuine recursive indices. -/
abbrev Source (globals : Globals) (outward : List Instance) (world : List Nat) :=
  IndexedSource globals.registry outward globals.owners world

abbrev Source.unit := @IndexedSource.unit
abbrev Source.boolean := @IndexedSource.boolean
abbrev Source.integer := @IndexedSource.integer
abbrev Source.reference := @IndexedSource.reference
abbrev Source.variable := @IndexedSource.variable
abbrev Source.lambda := @IndexedSource.lambda
abbrev Source.receiverLambda := @IndexedSource.receiverLambda
abbrev Source.purePair := @IndexedSource.purePair
abbrev Source.pair := @IndexedSource.pair
abbrev Source.app := @IndexedSource.app
abbrev Source.bind := @IndexedSource.bind
abbrev Source.branch := @IndexedSource.branch
abbrev Source.perform := @IndexedSource.perform
abbrev Source.handler := @IndexedSource.handler
abbrev Source.resume := @IndexedSource.resume
abbrev Source.discard := @IndexedSource.discard
abbrev Source.cleanup := @IndexedSource.cleanup
abbrev Source.resource := @IndexedSource.resource

/-- Actual-plan declaration certification follows structural derivation;
application separately checks its exposed plan, and lambda bodies stay recursive. -/
theorem IndexedSource.certified (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows) :
    Certified outward world plan := by
  induction source using IndexedSource.rec
      (motive_2 := fun _ world _ _ _ _ _ _ _ plan _ _ => Certified outward world plan)
      (motive_3 := fun _ world _ _ _ _ _ _ _ _ _ _ _ _ _ _ plans _ _ => SourcePlannedChecks.CertifiedModes outward world plans)
      (motive_4 := fun _ world _ _ _ _ _ _ _ plans _ _ => SourcePlannedChecks.CertifiedClauses outward world plans) with
  | unit | boolean | integer | reference | «variable» | lambda | receiverLambda | purePair => exact .pure
  | pair left right ihL ihR | bind left right ihL ihR => exact .sequence ihL ihR
  | app function argument admitted publicCertified ihF ihA => exact .sequence ihF (.sequence ihA publicCertified)
  | cleanup callback body admitted publicCertified ihC ihB => exact .sequence ihC (.cleanup publicCertified ihB)
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      exact .sequence ihI (.resource ihB)
  | branch condition yes no same ihC ihY ihN => exact .sequence ihC (.choice ihY ihN)
  | perform known admitted operand formed ih => exact .sequence ih .request
  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl =>
      exact .handler recipes ihDecl ihBody
  | resume known resolved permission operand admitted formed ih => exact .sequence ih .invoke
  | discard => exact .invoke
  | typed source normal closing ih => exact ih
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source ih =>
      exact .available (fun owner => ih owner ⟨_, _, _, [], [], [], none, _, _⟩ rfl rfl rfl rfl rfl (.refl _))
  | nil => exact .nil
  | cons supportBound known ordinary protectedMode rest ihOrd ihProt ihRest => exact .cons ihOrd ihProt ihRest


abbrev Source.certified := @IndexedSource.certified

/-- Owner transport depends only on the ticket resolved by the current scope.
A lambda resets its body scope, so it does not require agreement at unrelated
historical owner keys. This is not a global owner-table extension. -/
theorem IndexedSource.owners_congr
    (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (agree : ∀ binder owner, scope.resolve binder = some owner → owners owner = destination owner) :
    IndexedSource registry outward destination world allowed scope environment code contract demand requirements plan rows := by
  induction source using IndexedSource.rec
      (motive_2 := fun owners world allowed scope environment code answer header _ plan rows _ =>
        ∀ destination, (∀ binder owner, scope.resolve binder = some owner → owners owner = destination owner) →
          SourceBody registry outward destination world allowed scope environment code answer header plan rows)
      (motive_3 := fun _ world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ plans rows _ =>
        ∀ destination, SourceOffer registry outward destination world environment allowed parameter binder argument input answer
          resumeEffects closeEffects code held disposes row plans rows)
      (motive_4 := fun _ world environment allowed requested answer clauses table _ plans rows _ =>
        ∀ destination, SourceDeclarations registry outward destination world environment allowed requested answer clauses table plans rows)
      generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      exact .lambda (ih (by intro binder owner resolved; cases resolved)) refinement bodyOutward latentBound publicCertified formed
  | receiverLambda body bodyOutward latentBound publicCertified formed ih =>
      exact .receiverLambda (fun lexical call => ih lexical call (by intro binder owner resolved; cases resolved))
        bodyOutward latentBound publicCertified formed
  | purePair left right ihL ihR => exact .purePair (ihL agree) (ihR agree)
  | pair left right ihL ihR => exact .pair (ihL agree) (ihR agree)
  | app function argument admitted publicCertified ihF ihA => exact .app (ihF agree) (ihA agree) admitted publicCertified
  | bind initial body ihI ihB => exact .bind (ihI agree) (ihB agree)
  | cleanup callback body admitted publicCertified ihC ihB => exact .cleanup (ihC agree) (ihB agree) admitted publicCertified
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      exact .resource (ihI agree) (fun identity fresh => ihB identity fresh agree)
        formed effectsBound admitted hidden
  | branch condition yes no same ihC ihY ihN => exact .branch (ihC agree) (ihY agree) (ihN agree) same
  | perform known admitted operand formed ih => exact .perform known admitted (ih agree) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl =>
      exact .handler (ihBody agree) clauses capabilities coverage unique admitted table modes (ihDecl destination) recipes
  | resume known resolved permission operand admitted formed ih =>
      exact .resume ((agree _ _ resolved).symm.trans known) resolved permission (ih agree) admitted formed
  | discard known resolved permission unprotected admitted =>
      exact .discard ((agree _ _ resolved).symm.trans known) resolved permission unprotected admitted
  | typed source normal closing ih =>
      rename_i destination agree
      exact .typed (ih agree) normal closing
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source ih =>
      rename_i destination
      apply SourceOffer.available resumeInterface closeInterface
      intro owner contract inputSame answerSame resumeSame closeSame heldSame balanced
      apply ih owner contract inputSame answerSame resumeSame closeSame heldSame balanced
      intro binder resolvedOwner resolved
      simp only [Execution.Scope.resolve] at resolved
      split at resolved
      · cases Option.some.inj resolved
        simp only [CoreCallableContractRegistries.Owners.insert_here]
      · cases resolved
  | nil => exact .nil
  | cons supportBound known ordinary protectedMode rest ihOrd ihProt ihRest =>
      rename_i destination
      exact .cons supportBound known (ihOrd destination) (ihProt destination) (ihRest destination)

abbrev Source.owners_congr := @IndexedSource.owners_congr


theorem IndexedSource.erase_at (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (scopeTyped : ScopedPorts.EffectScope owners.lower.ports scope ticket) :
    ScopedPorts.Typed registry.ports world environment.ports ticket allowed code contract.port := by
  induction source using IndexedSource.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True) generalizing ticket with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable (by simp [Environment.ports, known]) formed
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      exact .lambda (by simpa only [Environment.ports_extend, Contract.port] using ih ScopedPorts.EffectScope.none) formed
  | receiverLambda body bodyOutward latentBound publicCertified formed ih =>
      exact .lambda (by simpa only [CallBounds.current, Environment.ports_extend, Contract.port] using
        (ih [] (CallBounds.current _) ScopedPorts.EffectScope.none)) formed
  | purePair left right ihL ihR | pair left right ihL ihR => exact .pair (ihL scopeTyped) (ihR scopeTyped)
  | app function argument admitted publicCertified ihF ihA => exact .app (ihF scopeTyped) (ihA scopeTyped) admitted
  | bind initial body ihI ihB => exact .bind (ihI scopeTyped) (by simpa using ihB scopeTyped)
  | cleanup callback body admitted publicCertified ihC ihB => exact .cleanup (ihC scopeTyped) (ihB scopeTyped) admitted
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      exact .resource (ihI scopeTyped) (fun identity fresh => ihB identity fresh scopeTyped)
        formed effectsBound admitted
  | branch condition yes no same ihC ihY ihN => exact .branch (ihC scopeTyped) (ihY scopeTyped) (ihN scopeTyped)
  | perform known admitted operand formed ih => exact .perform (by simp only [Registry.ports, known, Option.map_some]) admitted (ih scopeTyped) formed

  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl =>
      exact .handle (ihBody scopeTyped) clauses coverage unique admitted
  | resume known resolved permission operand admitted formed ih =>
      have same := CoherentSourceTypes.Owners.scope_resolved scopeTyped (CoreCallableContractRegistries.Owners.known_lower known) resolved
      subst ticket
      exact .resume (ih scopeTyped) admitted formed
  | discard known resolved permission unprotected admitted =>
      have same := CoherentSourceTypes.Owners.scope_resolved scopeTyped (CoreCallableContractRegistries.Owners.known_lower known) resolved
      subst ticket
      exact .discard admitted
  | typed | unavailable | available | nil | cons => trivial

abbrev Source.erase_at := @IndexedSource.erase_at

/-- Owner-free execution scope erases to the empty ticket interface. -/
theorem IndexedSource.erase (source : IndexedSource registry outward owners world allowed .none environment code contract demand requirements plan rows) :
    ScopedPorts.Typed registry.ports world environment.ports .none allowed code contract.port :=
  source.erase_at .none

abbrev Source.erase := @IndexedSource.erase

theorem IndexedSource.environment_congr (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (agree : ∀ name, Syntax.Dependency.variable name ∈ code.dependencies → environment name = destination name) :
    IndexedSource registry outward owners world allowed scope destination code contract demand requirements plan rows := by
  induction source using IndexedSource.rec
      (motive_2 := fun owners world allowed scope environment code answer header _ plan rows _ =>
        ∀ destination, (∀ name, Syntax.Dependency.variable name ∈ code.dependencies → environment name = destination name) →
          SourceBody registry outward owners world allowed scope destination code answer header plan rows)
      (motive_3 := fun owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ plans rows _ =>
        ∀ destination, (∀ name, Syntax.Dependency.variable name ∈ Syntax.without (.variable parameter) code.dependencies → environment name = destination name) →
          SourceOffer registry outward owners world destination allowed parameter binder argument input answer
            resumeEffects closeEffects code held disposes row plans rows)
      (motive_4 := fun owners world environment allowed requested answer clauses table _ plans rows _ =>
        ∀ destination, (∀ name, Syntax.Dependency.variable name ∈ clauses.dependencies → environment name = destination name) →
          SourceDeclarations registry outward owners world destination allowed requested answer clauses table plans rows)
      generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable ((agree _ (by simp [Code.dependencies])).symm.trans known) formed
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      rename_i parameter contractDependencies contractPlan contractRows
      apply Source.lambda (ih ?_) refinement bodyOutward latentBound publicCertified formed
      intro name member
      by_cases same : name = parameter
      · subst name; simp [Environment.extend]
      · simp only [Environment.extend, same, ↓reduceIte]
        exact agree name (Syntax.mem_without.mpr ⟨member, by simpa using same⟩)
  | receiverLambda body bodyOutward latentBound publicCertified formed ih =>
      rename_i parameter contractDependencies contractPlan contractRows privateDependencies privatePlans privateRows
      apply Source.receiverLambda (privateDependencies := privateDependencies)
        (privatePlans := privatePlans) (privateRows := privateRows) _ bodyOutward latentBound publicCertified formed
      intro lexical call
      apply ih lexical call
      intro name member
      by_cases same : name = parameter
      · subst name; simp [Environment.extend]
      · simp only [Environment.extend, same, ↓reduceIte]
        exact agree name (Syntax.mem_without.mpr ⟨member, by simpa using same⟩)
  | purePair left right ihL ihR =>
      exact .purePair (ihL (fun name member => agree name (List.mem_append_left _ member)))
        (ihR (fun name member => agree name (List.mem_append_right _ member)))
  | pair left right ihL ihR =>
      exact .pair (ihL (fun name member => agree name (List.mem_append_left _ member)))
        (ihR (fun name member => agree name (List.mem_append_right _ member)))
  | app function argument admitted publicCertified ihF ihA =>
      exact .app (ihF (fun name member => agree name (List.mem_append_left _ member)))
        (ihA (fun name member => agree name (List.mem_append_right _ member))) admitted publicCertified
  | cleanup callback body admitted publicCertified ihC ihB =>
      exact .cleanup (ihC (fun name member => agree name (List.mem_append_left _ member)))
        (ihB (fun name member => agree name (List.mem_append_right _ member))) admitted publicCertified
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      apply IndexedSource.resource
        (ihI (fun name member => agree name (List.mem_append_left _ member)))
        (fun identity fresh => ihB identity fresh ?_) formed effectsBound admitted hidden
      intro name member
      rcases List.mem_append.mp (ScopedExpressions.acquisition_dependency_bound _ _ _ member) with old | introduced
      · exact agree name (List.mem_append_right _ old)
      · simp at introduced
  | bind initial body ihI ihB =>
      rename_i parameter b output bodyDemand bodyReq bodyDependencies bodySignature bodyRows
      apply Source.bind (ihI (fun name member => agree name (List.mem_append_left _ member))) (ihB ?_)
      intro name member
      by_cases same : name = parameter
      · subst name; simp [Environment.extend]
      · simp only [Environment.extend, same, ↓reduceIte]
        exact agree name (List.mem_append_right _ (Syntax.mem_without.mpr ⟨member, by simpa using same⟩))
  | branch condition yes no sameDemand ihC ihY ihN =>
      exact .branch
        (ihC (fun name member => agree name (List.mem_append_left _ (List.mem_append_left _ member))))
        (ihY (fun name member => agree name (List.mem_append_left _ (List.mem_append_right _ member))))
        (ihN (fun name member => agree name (List.mem_append_right _ member))) sameDemand

  | perform known admitted operand formed ih =>
      exact .perform known admitted (ih (fun name member => agree name (List.mem_append_right _ member))) formed

  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl =>
      apply IndexedSource.handler (ihBody ?_) ?_ capabilities coverage unique admitted table modes (ihDecl destination ?_) recipes
      · intro name member
        exact agree name (List.mem_append_left _ (List.mem_append_right _ member))
      · apply ScopedPorts.clauses_environment_congr clauses
        intro name member
        exact congrArg (fun binding => binding.map Contract.port) (agree name (List.mem_append_right _ member))
      · intro name member
        exact agree name (List.mem_append_right _ member)
  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission (ih (fun name member => agree name (List.mem_cons_of_mem _ member))) admitted formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted

  | typed source normal closing ih =>
      rename_i destination agree
      exact .typed (ih agree) normal closing
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source ih =>
      rename_i resumeEffects' allowed' closeEffects' input' answer' held' world' binder' code' disposes' row' owners' environment' parameter' argument' family' plans' rows' destination agree
      apply SourceOffer.available resumeInterface closeInterface
      intro owner contract inputSame answerSame resumeSame closeSame heldSame balanced
      apply ih owner contract inputSame answerSame resumeSame closeSame heldSame balanced
      intro name member
      by_cases same : name = parameter'
      · subst name; simp only [Environment.extend, ↓reduceIte]
      · simp only [Environment.extend, same, ↓reduceIte]
        exact agree name (Syntax.mem_without.mpr ⟨member, by simpa using same⟩)
  | nil => exact .nil
  | cons supportBound known ordinary protectedMode rest ihOrd ihProt ihRest =>
      rename_i destination agree
      apply SourceDeclarations.cons supportBound known (ihOrd destination ?_) (ihProt destination ?_) (ihRest destination ?_)
      · intro name member
        exact agree name (List.mem_append_left _ (Syntax.mem_without.mpr ⟨member, by simp⟩))
      · intro name member
        exact agree name (List.mem_append_left _ (Syntax.mem_without.mpr ⟨member, by simp⟩))
      · intro name member
        exact agree name (List.mem_append_right _ member)

abbrev Source.environment_congr := @IndexedSource.environment_congr

theorem IndexedSource.closed_environment (source : IndexedSource registry outward owners world allowed scope environment value contract [] (.request [] []) .pure Rows.pure)
    (closed : ClosedValue value) (destination : Environment) : IndexedSource registry outward owners world allowed scope destination value contract [] (.request [] []) .pure Rows.pure :=
  source.environment_congr (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))


abbrev Source.closed_environment := @IndexedSource.closed_environment

/-- Closed values retain their public contract when the caller's allowed row
changes. The private lambda body continues under its own declared requests. -/
theorem IndexedSource.value_allowed (source : IndexedSource registry outward owners world allowed scope environment value contract demand requirements plan rows)
    (valueIsValue : value.IsValue) (next : List Instance) (nextScope : Execution.Scope) : IndexedSource registry outward owners world next nextScope environment value contract demand requirements plan rows := by
  induction source using IndexedSource.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body refinement bodyOutward latentBound publicCertified formed ih => exact .lambda body refinement bodyOutward latentBound publicCertified formed
  | receiverLambda body bodyOutward latentBound publicCertified formed ih => exact .receiverLambda body bodyOutward latentBound publicCertified formed
  | purePair left right ihL ihR => exact .purePair (ihL valueIsValue.1) (ihR valueIsValue.2)
  | pair left right ihL ihR => exact .pair (ihL valueIsValue.1) (ihR valueIsValue.2)
  | «variable» | app | bind | branch | perform | handler | resume | discard | cleanup | resource => cases valueIsValue

  | typed | unavailable | available | nil | cons => trivial

abbrev Source.value_allowed := @IndexedSource.value_allowed

/-- A closed value can be used under an inserted owner without assuming that
insertion preserves unrelated old keys. Its executable scope is first reset. -/
theorem IndexedSource.value_owner_insert
    (source : IndexedSource registry outward owners world allowed scope environment value contract demand requirements plan rows)
    (isValue : value.IsValue) (ticket : Nat) (inserted : OwnerContract) :
    IndexedSource registry outward (owners.insert ticket inserted) world allowed .none environment value contract demand requirements plan rows := by
  apply (source.value_allowed isValue allowed .none).owners_congr
  intro binder owner resolved
  cases resolved


abbrev Source.value_owner_insert := @IndexedSource.value_owner_insert

/-- Normalize only immediate checking rows of a value. The public contract
and each lambda's private recursive body/refinement remain unchanged. -/
theorem IndexedSource.value_summary (source : IndexedSource registry outward owners world allowed scope environment value contract demand requirements plan rows)
    (valueIsValue : value.IsValue) : IndexedSource registry outward owners world allowed scope environment value contract [] (.request [] []) .pure Rows.pure := by
  induction source using IndexedSource.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body refinement bodyOutward latentBound publicCertified formed ih => exact .lambda body refinement bodyOutward latentBound publicCertified formed
  | receiverLambda body bodyOutward latentBound publicCertified formed ih => exact .receiverLambda body bodyOutward latentBound publicCertified formed
  | purePair left right ihL ihR | pair left right ihL ihR =>
      exact .purePair (ihL valueIsValue.1) (ihR valueIsValue.2)
  | «variable» | app | bind | branch | perform | handler | resume | discard | cleanup | resource => cases valueIsValue

  | typed | unavailable | available | nil | cons => trivial

abbrev Source.value_summary := @IndexedSource.value_summary

/-- Reuse the existing generic nested certification world proof by enclosing
this single plan in one available mode. No declaration policy monotonicity law
is added: declaration recipes are independent of the world. -/
theorem certified_world (checked : Certified outward world plan) (larger : world ⊆ nextWorld) :
    Certified outward nextWorld plan := by
  have declarations : SourcePlannedChecks.CertifiedClauses outward world
      (ClausePlans.cons (operation := 0) (parameter := 0) (binder := 0) (body := Code.unit)
        (.available (fun _ => plan)) .unavailable .nil) :=
    .cons (.available (fun _ => checked)) .unavailable .nil
  have advanced := SourcePlannedPhases.certified_clauses_world declarations larger
  cases advanced with
  | cons ordinary protectedMode rest =>
      cases ordinary with
      | available bodies => exact bodies 0

omit evidence in
private theorem port_clauses_world {ports : ScopedPorts.Signature} (checked : ScopedPorts.ClausesTyped ports world environment effect answer residual clauses)
    (larger : world ⊆ nextWorld) :
    ScopedPorts.ClausesTyped ports nextWorld environment effect answer residual clauses := by
  induction checked using ScopedPorts.ClausesTyped.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | nil => exact .nil
  | cons known body rest ihBody ihRest => exact .cons known (ScopedPorts.typed_world_weaken body _ larger) (ihRest larger)
  | unit | boolean | integer | «variable» | reference | pair | lambda | app | bind | branch | perform | handle | resume | discard | resource | cleanup => trivial

/-- Transport the SAME open code and scalar requirements into a larger issued
world. Private open families rebase their finite call data; they are not restricted
to the original creation world. -/
theorem IndexedSource.world_weaken
    (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (larger : world ⊆ nextWorld) :
    IndexedSource registry outward owners nextWorld allowed scope environment code contract demand requirements plan rows := by
  induction source using IndexedSource.rec
      (motive_2 := fun owners world allowed scope environment code answer header _ plan rows _ =>
        ∀ nextWorld, world ⊆ nextWorld → SourceBody registry outward owners nextWorld allowed scope environment code answer header plan rows)
      (motive_3 := fun owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ plans rows _ =>
        ∀ nextWorld, world ⊆ nextWorld → SourceOffer registry outward owners nextWorld environment allowed parameter binder argument input answer
          resumeEffects closeEffects code held disposes row plans rows)
      (motive_4 := fun owners world environment allowed requested answer clauses table _ plans rows _ =>
        ∀ nextWorld, world ⊆ nextWorld → SourceDeclarations registry outward owners nextWorld environment allowed requested answer clauses table plans rows)
      generalizing nextWorld with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference (larger issued)
  | «variable» known formed => exact .variable known (ScopedPorts.in_world_mono formed larger)
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      exact .lambda (ih larger) refinement bodyOutward latentBound (certified_world publicCertified larger)
        (ScopedPorts.in_world_mono formed larger)
  | receiverLambda body bodyOutward latentBound publicCertified formed ih =>
      exact .receiverLambda (fun lexical call => body lexical (call.rebase larger)) bodyOutward latentBound
        (certified_world publicCertified larger) (ScopedPorts.in_world_mono formed larger)
  | purePair left right ihL ihR => exact .purePair (ihL larger) (ihR larger)
  | pair left right ihL ihR => exact .pair (ihL larger) (ihR larger)
  | app function argument admitted publicCertified ihF ihA => exact .app (ihF larger) (ihA larger) admitted (certified_world publicCertified larger)
  | bind initial body ihI ihB => exact .bind (ihI larger) (ihB larger)
  | cleanup callback body admitted publicCertified ihC ihB => exact .cleanup (ihC larger) (ihB larger) admitted (certified_world publicCertified larger)
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      rename_i bodyRequirements bodyDependencies bodyPlans bodyRows
      apply IndexedSource.resource (bodyRequirements := bodyRequirements)
        (ihI larger) ?_ (ScopedPorts.in_world_mono formed larger)
        (List.Subset.trans effectsBound larger) admitted ?_
      · intro identity fresh
        exact ihB identity (fun old => fresh (larger old))
          (by intro name member; rcases List.mem_append.mp member with old | current; exact List.mem_append_left _ (larger old); exact List.mem_append_right _ current)
      · intro identity fresh
        exact hidden identity (fun old => fresh (larger old))
  | branch condition yes no same ihC ihY ihN => exact .branch (ihC larger) (ihY larger) (ihN larger) same
  | perform known admitted operand formed ih => exact .perform known admitted (ih larger) (ScopedPorts.in_world_mono formed larger)
  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl =>
      exact .handler (ihBody larger) (port_clauses_world clauses larger) capabilities coverage unique admitted table modes (ihDecl _ larger) recipes
  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission (ih larger) admitted (ScopedPorts.in_world_mono formed larger)
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | typed source normal closing ih =>
      rename_i nextWorld larger
      exact .typed (ih larger) normal closing
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source ih =>
      rename_i nextWorld larger
      exact .available resumeInterface closeInterface (fun owner contract a b c d e balanced => ih owner contract a b c d e balanced _ larger)
  | nil => exact .nil
  | cons supportBound known ordinary protectedMode rest ihOrd ihProt ihRest =>
      rename_i nextWorld larger
      exact .cons supportBound known (ihOrd _ larger) (ihProt _ larger) (ihRest _ larger)

abbrev Source.world_weaken := @IndexedSource.world_weaken

/-- Finite bindings authenticate every ordinary dependency actually read.
The total Bounds projection alone does not authenticate a missing variable. -/
def LexicalBounds.Known (lexical : LexicalBounds) (dependencies : List Syntax.Dependency) : Prop :=
  ∀ name, Syntax.Dependency.variable name ∈ dependencies → ∃ resources, lexical.lookup name = some resources

mutual
/-- Support authentication is indexed by the SAME recursive type derivation.
The aggregate bound is accompanied by hereditary lambda/declaration evidence. -/
inductive Authenticated (registry : Registry) (outward : List Instance) :
    {owners : Owners} → {world : List Nat} → {allowed : List Instance} → {scope : Execution.Scope} →
    {environment : Environment} → {code : Code} → {contract : Contract} →
    {demand : List Nat} → {requirements : Requirements demand} → {dependencies : Dependencies} →
    {plan : Plan dependencies} → {rows : Rows (signature plan)} →
    IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows →
    LexicalBounds → List Nat → Prop where
  | checked {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
      (current : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds lexical.environment code.dependencies receiver)
      (hereditary : Hereditary registry outward source lexical receiver) : Authenticated registry outward source lexical receiver

inductive Hereditary (registry : Registry) (outward : List Instance) :
    {owners : Owners} → {world : List Nat} → {allowed : List Instance} → {scope : Execution.Scope} →
    {environment : Environment} → {code : Code} → {contract : Contract} →
    {demand : List Nat} → {requirements : Requirements demand} → {dependencies : Dependencies} →
    {plan : Plan dependencies} → {rows : Rows (signature plan)} →
    IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows →
    LexicalBounds → List Nat → Prop where
  | unit : Hereditary registry outward IndexedSource.unit lexical receiver
  | boolean : Hereditary registry outward IndexedSource.boolean lexical receiver
  | integer : Hereditary registry outward IndexedSource.integer lexical receiver
  | reference : Hereditary registry outward (IndexedSource.reference issued) lexical receiver
  | variable (knownSupport : ∃ resources, lexical.lookup name = some resources) :
      Hereditary registry outward (IndexedSource.variable (name := name) known formed) lexical receiver
  | purePair (left : Authenticated registry outward leftSource lexical receiver)
      (right : Authenticated registry outward rightSource lexical receiver) :
      Hereditary registry outward (IndexedSource.purePair leftSource rightSource) lexical receiver
  | pair (left : Authenticated registry outward leftSource lexical receiver)
      (right : Authenticated registry outward rightSource lexical receiver) :
      Hereditary registry outward (IndexedSource.pair leftSource rightSource) lexical receiver
  | app (function : Authenticated registry outward functionSource lexical receiver)
      (argument : Authenticated registry outward argumentSource lexical receiver) :
      Hereditary registry outward (IndexedSource.app functionSource argumentSource admitted publicCertified) lexical receiver
  | bind
      {initialSource : IndexedSource registry outward owners world allowed scope environment a input initialDemand initialReq initialPlan initialRows}
      {bodySource : IndexedSource registry outward owners world allowed scope (environment.extend parameter input) b output bodyDemand bodyReq bodyPlan bodyRows}
      (initial : Authenticated registry outward initialSource lexical receiver)
      (body : Authenticated registry outward bodySource (lexical.extend parameter receiver) receiver) :
      Hereditary registry outward (IndexedSource.bind (parameter := parameter) initialSource bodySource) lexical receiver
  | branch (condition : Authenticated registry outward conditionSource lexical receiver)
      (yes : Authenticated registry outward yesSource lexical receiver)
      (no : Authenticated registry outward noSource lexical receiver) :
      Hereditary registry outward (IndexedSource.branch conditionSource yesSource noSource sameDemand) lexical receiver
  | perform (operand : Authenticated registry outward operandSource lexical receiver) :
      Hereditary registry outward (IndexedSource.perform known admitted operandSource formed) lexical receiver
  | cleanup (callback : Authenticated registry outward callbackSource lexical receiver)
      (body : Authenticated registry outward bodySource lexical receiver) :
      Hereditary registry outward (IndexedSource.cleanup callbackSource bodySource admitted publicCertified) lexical receiver
  | resource {code : Code}
      {bodyRequirements : Nat → Requirements bodyDemand}
      {bodyDependencies : Nat → Dependencies}
      {bodyPlans : ∀ identity, Plan (bodyDependencies identity)}
      {bodyRows : ∀ identity, Rows (signature (bodyPlans identity))}
      {initialSource : IndexedSource registry outward owners world allowed scope environment
        initial .integer initialDemand initialRequirements initialPlan initialRows}
      {bodySource : ∀ identity, identity ∉ world →
        IndexedSource registry outward owners (world ++ [identity]) (.cell identity :: residual)
          scope environment (code.instantiate (Instantiation.Environment.empty.bind binder identity))
          output bodyDemand (bodyRequirements identity) (bodyPlans identity) (bodyRows identity)}
      {outwardRequirements : Requirements bodyDemand}
      {formed : ScopedPorts.InWorld world output.port}
      {effectsBound : residual.flatMap Instance.resources ⊆ world} {admitted : residual ⊆ allowed}
      {hidden : ∀ identity, identity ∉ world →
        ResourceRequirements.Hides identity (bodyRequirements identity) outwardRequirements}
      (initial : Authenticated registry outward initialSource lexical receiver)
      (body : ∀ identity (fresh : identity ∉ world),
        Authenticated registry outward (bodySource identity fresh) lexical (identity :: receiver)) :
      Hereditary registry outward
        (IndexedSource.resource initialSource bodySource formed effectsBound admitted hidden) lexical receiver
  | resume (operand : Authenticated registry outward operandSource lexical receiver) :
      Hereditary registry outward (IndexedSource.resume known resolved permission operandSource admitted formed) lexical receiver
  | discard {owners : Owners} {scope : Execution.Scope} {contract : OwnerContract}
      (known : owners owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (registry.policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed) :
      Hereditary registry outward (IndexedSource.discard (registry := registry) (outward := outward)
        (world := world) (environment := environment) known resolved permission unprotected admitted) lexical receiver
  | lambda {environment : Environment}
      {bodySource : IndexedSource registry outward owners world requests .none
        (environment.extend parameter input) code output bodyDemand bodyReq actualPlan actualRows}
      {contractDependencies : Dependencies} {contractPlan : Plan contractDependencies}
      {contractRows : Rows (signature contractPlan)}
      (refinement : Refines contractRows actualRows)
      (bodyOutward : RecursiveOutward.Outward bodyReq (some latent))
      (latentBound : ∀ request ∈ latent, request.effect ∈ requests)
      (publicCertified : Certified outward world contractPlan)
      (formed : ScopedPorts.InWorld world (Contract.function input output requests latent contractPlan contractRows).port)
      (known : LexicalBounds.Known lexical (Code.lambda parameter code).dependencies)
      (body : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
        LexicalBounds.Known nextLexical (Code.lambda parameter code).dependencies →
        ScopedPorts.Support.evaluate nextLexical.environment (Code.lambda parameter code).dependencies ⊆ call.receiver →
        Authenticated registry outward (bodySource.world_weaken call.worldExtended)
          (nextLexical.extend parameter call.argument) call.receiver) :
      Hereditary registry outward (IndexedSource.lambda (parameter := parameter) (world := world)
        (code := code) bodySource refinement bodyOutward latentBound publicCertified formed) lexical receiver
  | receiverLambda {owners : Owners} {world : List Nat} {environment : Environment}
      {privateDependencies : LexicalBounds → CallBounds world → Dependencies}
      {privatePlans : ∀ lexical call, Plan (privateDependencies lexical call)}
      {privateRows : ∀ lexical call, Rows (signature (privatePlans lexical call))}
      {bodySource : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
        IndexedSource registry outward owners call.world requests .none
          (environment.extend parameter input) code output bodyDemand bodyReq
          (privatePlans nextLexical call) (privateRows nextLexical call)}
      (bodyOutward : RecursiveOutward.Outward bodyReq (some latent))
      (latentBound : ∀ request ∈ latent, request.effect ∈ requests)
      {contractDependencies : Dependencies} {contractPlan : Plan contractDependencies}
      {contractRows : Rows (signature contractPlan)}
      (publicCertified : Certified outward world contractPlan)
      (formed : ScopedPorts.InWorld world (Contract.function input output requests latent contractPlan contractRows).port)
      (known : LexicalBounds.Known lexical (Code.lambda parameter code).dependencies)
      (body : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
        LexicalBounds.Known nextLexical (Code.lambda parameter code).dependencies →
        ScopedPorts.Support.evaluate nextLexical.environment (Code.lambda parameter code).dependencies ⊆ call.receiver →
        Authenticated registry outward (bodySource nextLexical call)
          (nextLexical.extend parameter call.argument) call.receiver)
      (refinement : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
        LexicalBounds.Known nextLexical (Code.lambda parameter code).dependencies →
        ScopedPorts.Support.evaluate nextLexical.environment (Code.lambda parameter code).dependencies ⊆ call.receiver →
        ReceiverRefines contractRows (privateRows nextLexical call) call.receiver
          (ScopedPorts.Support.evaluate (nextLexical.extend parameter call.argument).environment code.dependencies)) :
      Hereditary registry outward (IndexedSource.receiverLambda (parameter := parameter) (world := world)
        (code := code) (contractRows := contractRows) (privateRows := privateRows)
        bodySource bodyOutward latentBound publicCertified formed) lexical receiver
  | handler
      {bodySource : IndexedSource registry outward owners world (effect :: residual) scope environment code answer demand requirements bodyPlan bodyRows}
      {declarationSource : SourceDeclarations registry outward owners world environment residual effect answer arms table plans declarationRows}
      (clauses : ScopedPorts.ClausesTyped registry.ports world environment.ports effect answer.port residual arms)
      (capabilities : ClausesUse registry.policy arms)
      (coverage : ScopedPorts.Covers registry.ports effect arms)
      (unique : (ScopedTyping.clauseKeys arms).Nodup) (admitted : residual ⊆ allowed)
      (modes : SourceTemplates.ClauseModes arms table)
      (recipes : evidence.accepts outward required plans)
      (body : Authenticated registry outward bodySource lexical receiver)
      (declarations : DeclarationAuthentication registry outward declarationSource lexical receiver) :
      Hereditary registry outward (IndexedSource.handler bodySource clauses capabilities coverage unique admitted table modes declarationSource recipes) lexical receiver
  | handlerDomain
      {bodySource : IndexedSource registry outward owners world (effect :: residual) scope environment code answer demand requirements bodyPlan bodyRows}
      {declarationSource : SourceDeclarations registry outward owners world environment residual effect answer arms table plans declarationRows}
      (clauses : ScopedPorts.ClausesTyped registry.ports world environment.ports effect answer.port residual arms)
      (capabilities : ClausesUse registry.policy arms)
      (coverage : ScopedPorts.Covers registry.ports effect arms)
      (unique : (ScopedTyping.clauseKeys arms).Nodup) (admitted : residual ⊆ allowed)
      (modes : SourceTemplates.ClauseModes arms table)
      (recipes : evidence.accepts outward required plans)
      (body : Authenticated registry outward bodySource lexical receiver)
      (declarations : DomainDeclarationAuthentication registry outward declarationSource lexical receiver) :
      Hereditary registry outward (IndexedSource.handler bodySource clauses capabilities coverage unique admitted table modes declarationSource recipes) lexical receiver

inductive BodyAuthentication (registry : Registry) (outward : List Instance) :
    {owners : Owners} → {world : List Nat} → {allowed : List Instance} → {scope : Execution.Scope} →
    {environment : Environment} → {code : Code} → {answer : Contract} → {header : ClauseRowAdmission.Header} →
    {dependencies : Dependencies} → {plan : Plan dependencies} → {rows : Rows (signature plan)} →
    SourceBody registry outward owners world allowed scope environment code answer header plan rows → LexicalBounds → List Nat → Prop where
  | typed (source : Authenticated registry outward sourceProof lexical receiver) :
      BodyAuthentication registry outward (SourceBody.typed sourceProof normal closing) lexical receiver

inductive OfferAuthentication (registry : Registry) (outward : List Instance) :
    {owners : Owners} → {world : List Nat} → {environment : Environment} → {allowed : List Instance} →
    {parameter binder : Nat} → {argument input answer : Contract} → {resumeEffects closeEffects : List Instance} →
    {code : Code} → {held disposes : Bool} → {row : Option Footprint} →
    {family : Option (Nat → Dependencies)} → {plans : ModePlans family} → {rows : ModeRows (modeSignatures plans)} →
    SourceOffer registry outward owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row plans rows →
    LexicalBounds → List Nat → Prop where
  | unavailable : OfferAuthentication registry outward SourceOffer.unavailable lexical receiver
  | available {owners : Owners} {world : List Nat} {environment : Environment}
      {argument input answer : Contract}
      {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
      {rows : ∀ owner, Rows (signature (plans owner))}
      {bodySource : ∀ owner (contract : OwnerContract),
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceBody registry outward (owners.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.lower, disposes, row⟩ (plans owner) (rows owner)}
      (resumeInterface : code.requiredActions.resume = true → resumeEffects = allowed)
      (closeInterface : code.requiredActions.dispose = true → closeEffects = allowed)
      (body : ∀ owner contract a b c d e balanced,
        BodyAuthentication registry outward (bodySource owner contract a b c d e balanced) lexical receiver) :
      OfferAuthentication registry outward (SourceOffer.available resumeInterface closeInterface bodySource) lexical receiver

inductive DeclarationAuthentication (registry : Registry) (outward : List Instance) :
    {owners : Owners} → {world : List Nat} → {environment : Environment} → {allowed : List Instance} →
    {requested : Instance} → {answer : Contract} → {clauses : Clauses} → {table : List (Nat × ClauseContract)} →
    {families : ClauseDependencies} → {plans : ClausePlans clauses families} → {rows : ClauseRows (clauseSignatures plans)} →
    SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows →
    LexicalBounds → List Nat → Prop where
  | nil : DeclarationAuthentication registry outward SourceDeclarations.nil lexical receiver
  | cons
      {ordinarySource : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body false dispose ordinaryRow ordinaryPlan ordinaryRows}
      {protectedSource : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body true dispose protectedRow protectedPlan protectedRows}
      {restSource : SourceDeclarations registry outward owners world environment allowed requested answer clauses table restPlan restRows}
      (known : registry.operations requested operation = some (argument, input))
      (bodyBound : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds
        (lexical.extend parameter receiver).environment body.dependencies supportBound)
      (storedReceived : supportBound ⊆ receiver)
      (ordinary : OfferAuthentication registry outward ordinarySource (lexical.extend parameter receiver) receiver)
      (protectedMode : OfferAuthentication registry outward protectedSource (lexical.extend parameter receiver) receiver)
      (rest : DeclarationAuthentication registry outward restSource lexical receiver) :
      DeclarationAuthentication registry outward (SourceDeclarations.cons (parameter := parameter) (body := body)
        supportBound known ordinarySource protectedSource restSource) lexical receiver

/-- Authenticate every operation domain at an explicit admissible formal bound. -/
inductive DomainDeclarationAuthentication (registry : Registry) (outward : List Instance) :
    {owners : Owners} → {world : List Nat} → {environment : Environment} → {allowed : List Instance} →
    {requested : Instance} → {answer : Contract} → {clauses : Clauses} → {table : List (Nat × ClauseContract)} →
    {families : ClauseDependencies} → {plans : ClausePlans clauses families} → {rows : ClauseRows (clauseSignatures plans)} →
    SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows →
    LexicalBounds → List Nat → Prop where
  | domainNil : DomainDeclarationAuthentication registry outward SourceDeclarations.nil lexical receiver
  | domainCons
      {ordinarySource : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body false dispose ordinaryRow ordinaryPlan ordinaryRows}
      {protectedSource : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body true dispose protectedRow protectedPlan protectedRows}
      {restSource : SourceDeclarations registry outward owners world environment allowed requested answer clauses table restPlan restRows}
      (known : registry.operations requested operation = some (argument, input))
      (domainCovered : CoreCallableContractOperandDomain.domainSupport argument receiver ⊆ formalSupport)
      (formalReceived : formalSupport ⊆ receiver)
      (bodyBound : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds
        (lexical.extend parameter formalSupport).environment body.dependencies supportBound)
      (storedReceived : supportBound ⊆ receiver)
      (ordinary : OfferAuthentication registry outward ordinarySource (lexical.extend parameter formalSupport) receiver)
      (protectedMode : OfferAuthentication registry outward protectedSource (lexical.extend parameter formalSupport) receiver)
      (rest : DomainDeclarationAuthentication registry outward restSource lexical receiver) :
      DomainDeclarationAuthentication registry outward (SourceDeclarations.cons (parameter := parameter) (body := body)
        supportBound known ordinarySource protectedSource restSource) lexical receiver
end

/-- The receiver bound comes from the same recursive authentication, not
from the public callable port or a separate source-proof inversion. -/
theorem Authenticated.current_support
    (authenticated : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
      lexical receiver) :
    SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds lexical.environment code.dependencies receiver := by
  cases authenticated with
  | checked current _ => exact current

/-- Invocation selects the private source and checking refinement by inverting
hereditary authentication first. No separate type-proof inversion chooses a
potentially different private family. The caller supplies finite current call
and lexical support data, not a substituted successor derivation. -/
theorem Authenticated.lambda_current
    {source : IndexedSource registry outward owners world allowed scope environment
      (.lambda parameter code) (Contract.function input output requests latent contractPlan contractRows)
      demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (nextLexical : LexicalBounds) (call : CallBounds world)
    (known : LexicalBounds.Known nextLexical (Code.lambda parameter code).dependencies)
    (received : ScopedPorts.Support.evaluate nextLexical.environment (Code.lambda parameter code).dependencies ⊆ call.receiver) :
    ∃ bodyDemand, ∃ bodyReq : Requirements bodyDemand, ∃ dependencies,
      ∃ actualPlan : Plan dependencies, ∃ actualRows : Rows (signature actualPlan),
      ∃ actualSource : IndexedSource registry outward owners call.world requests .none
        (environment.extend parameter input) code output bodyDemand bodyReq actualPlan actualRows,
      Authenticated registry outward actualSource (nextLexical.extend parameter call.argument) call.receiver ∧
      ReceiverRefines contractRows actualRows call.receiver
        (ScopedPorts.Support.evaluate (nextLexical.extend parameter call.argument).environment code.dependencies) ∧
      RecursiveOutward.Outward bodyReq (some latent) := by
  cases authenticated with
  | checked current hereditary =>
    cases hereditary with
    | lambda refinement bodyOutward latentBound publicCertified formed captured body =>
      exact ⟨_, _, _, _, _, _, body nextLexical call known received,
        ReceiverRefines.of_universal refinement _ _, bodyOutward⟩
    | receiverLambda bodyOutward latentBound publicCertified formed captured body refinement =>
      exact ⟨_, _, _, _, _, _, body nextLexical call known received,
        refinement nextLexical call known received, bodyOutward⟩

omit evidence in
private theorem sequence_rows_heq
    {first nextFirst : SourcePlanSignatures.Signature firstDependencies}
    {second nextSecond : SourcePlanSignatures.Signature secondDependencies}
    {left : Rows first} {nextLeft : Rows nextFirst} {right : Rows second} {nextRight : Rows nextSecond}
    (sameLeft : nextFirst = first) (sameRight : nextSecond = second)
    (alignedLeft : HEq nextLeft left) (alignedRight : HEq nextRight right) :
    HEq (Rows.sequence nextLeft nextRight) (Rows.sequence left right) := by
  cases sameLeft
  cases sameRight
  cases eq_of_heq alignedLeft
  cases eq_of_heq alignedRight
  rfl

omit evidence in
private theorem cleanup_rows_heq
    {callback : SourcePlanSignatures.Signature callbackDependencies}
    {body nextBody : SourcePlanSignatures.Signature bodyDependencies}
    {callbackRows : Rows callback} {bodyRows : Rows body} {nextBodyRows : Rows nextBody}
    (same : nextBody = body) (aligned : HEq nextBodyRows bodyRows) :
    HEq (Rows.cleanup (needs := needs) latent callbackRows nextBodyRows)
      (Rows.cleanup (needs := needs) latent callbackRows bodyRows) := by
  cases same
  cases eq_of_heq aligned
  rfl

omit evidence in
private theorem choice_rows_heq
    {first nextFirst : SourcePlanSignatures.Signature firstDependencies}
    {second nextSecond : SourcePlanSignatures.Signature secondDependencies}
    {left : Rows first} {nextLeft : Rows nextFirst} {right : Rows second} {nextRight : Rows nextSecond}
    (sameLeft : nextFirst = first) (sameRight : nextSecond = second)
    (alignedLeft : HEq nextLeft left) (alignedRight : HEq nextRight right) :
    HEq (Rows.choice nextLeft nextRight) (Rows.choice left right) := by
  cases sameLeft
  cases sameRight
  cases eq_of_heq alignedLeft
  cases eq_of_heq alignedRight
  rfl

omit evidence in
private theorem refines_rows_heq
    {first nextFirst : SourcePlanSignatures.Signature dependencies}
    {firstRows : Rows first} {nextRows : Rows nextFirst}
    (refinement : Refines contractRows firstRows) (same : nextFirst = first)
    (aligned : HEq nextRows firstRows) : Refines contractRows nextRows := by
  cases same
  cases eq_of_heq aligned
  exact refinement
omit evidence in
private theorem signature_sequence_same
    {first nextFirst : SourcePlanSignatures.Signature firstDependencies}
    {second nextSecond : SourcePlanSignatures.Signature secondDependencies}
    (sameLeft : nextFirst = first) (sameRight : nextSecond = second) :
    SourcePlanSignatures.Signature.sequence nextFirst nextSecond = .sequence first second := by
  cases sameLeft
  cases sameRight
  rfl
omit evidence in
private theorem signature_choice_same
    {first nextFirst : SourcePlanSignatures.Signature firstDependencies}
    {second nextSecond : SourcePlanSignatures.Signature secondDependencies}
    (sameLeft : nextFirst = first) (sameRight : nextSecond = second) :
    SourcePlanSignatures.Signature.choice nextFirst nextSecond = .choice first second := by
  cases sameLeft
  cases sameRight
  rfl
omit evidence in
private theorem rows_cast_heq {first second : SourcePlanSignatures.Signature dependencies}
    (same : first = second) (rows : Rows second) : HEq (same.symm ▸ rows) rows := by
  cases same
  rfl

omit evidence in
private theorem resource_rows_heq
    {family : Nat → Dependencies}
    {first second : ∀ identity, SourcePlanSignatures.Signature (family identity)}
    {firstRows : ∀ identity, Rows (first identity)} {secondRows : ∀ identity, Rows (second identity)}
    (same : ∀ identity, first identity = second identity)
    (aligned : ∀ identity, HEq (firstRows identity) (secondRows identity)) :
    HEq (Rows.resource firstRows) (Rows.resource secondRows) := by
  have sameFunctions : first = second := funext same
  cases sameFunctions
  have sameRows : firstRows = secondRows := funext (fun identity => eq_of_heq (aligned identity))
  cases sameRows
  rfl

omit evidence in
private theorem available_rows_heq
    {family : Nat → Dependencies}
    {first second : ∀ owner, SourcePlanSignatures.Signature (family owner)}
    {firstRows : ∀ owner, Rows (first owner)} {secondRows : ∀ owner, Rows (second owner)}
    (same : ∀ owner, first owner = second owner)
    (aligned : ∀ owner, HEq (firstRows owner) (secondRows owner)) :
    HEq (ModeRows.available firstRows) (ModeRows.available secondRows) := by
  have sameFunctions : first = second := funext same
  cases sameFunctions
  have sameRows : firstRows = secondRows := funext (fun owner => eq_of_heq (aligned owner))
  cases sameRows
  rfl

omit evidence in
private theorem declaration_cons_heq
    {ordinary nextOrdinary : SourcePlanSignatures.ModeSignatures ordinaryFamily}
    {protectedMode nextProtected : SourcePlanSignatures.ModeSignatures protectedFamily}
    {rest nextRest : SourcePlanSignatures.ClauseSignatures restFamily}
    {ordinaryRows : ModeRows ordinary} {nextOrdinaryRows : ModeRows nextOrdinary}
    {protectedRows : ModeRows protectedMode} {nextProtectedRows : ModeRows nextProtected}
    {restRows : ClauseRows rest} {nextRestRows : ClauseRows nextRest}
    (sameOrdinary : nextOrdinary = ordinary) (sameProtected : nextProtected = protectedMode)
    (sameRest : nextRest = rest) (sameRights : nextRights = rights)
    (alignedOrdinary : HEq nextOrdinaryRows ordinaryRows) (alignedProtected : HEq nextProtectedRows protectedRows)
    (alignedRest : HEq nextRestRows restRows) :
    HEq (ClauseRows.cons (operation := operation) (rights := nextRights) nextOrdinaryRows nextProtectedRows nextRestRows supportBound)
      (ClauseRows.cons (operation := operation) (rights := rights) ordinaryRows protectedRows restRows supportBound) := by
  cases sameOrdinary
  cases sameProtected
  cases sameRest
  cases sameRights
  cases eq_of_heq alignedOrdinary
  cases eq_of_heq alignedProtected
  cases eq_of_heq alignedRest
  rfl

omit evidence in
private theorem handler_rows_heq
    {first nextFirst : SourcePlanSignatures.ClauseSignatures families}
    {body nextBody : SourcePlanSignatures.Signature dependencies}
    {declarations : ClauseRows first} {nextDeclarations : ClauseRows nextFirst}
    {bodyRows : Rows body} {nextBodyRows : Rows nextBody}
    (sameDeclarations : nextFirst = first) (sameBody : nextBody = body)
    (alignedDeclarations : HEq nextDeclarations declarations) (alignedBody : HEq nextBodyRows bodyRows) :
    HEq (Rows.handler (effect := effect) (table := table) (required := required) nextDeclarations nextBodyRows)
      (Rows.handler (effect := effect) (table := table) (required := required) declarations bodyRows) := by
  cases sameDeclarations
  cases sameBody
  cases eq_of_heq alignedDeclarations
  cases eq_of_heq alignedBody
  rfl

private theorem IndexedSource.owner_free_usage
    (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (empty : scope = .none) : ScopedExpressions.Uses registry.policy .none .available code .available := by
  induction source using IndexedSource.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .resourceRef
  | «variable» => exact .variable
  | lambda body refinement bodyOutward latentBound publicCertified formed ih => exact .lambda (ih rfl)
  | receiverLambda body bodyOutward latentBound publicCertified formed ih => exact .lambda (ih [] (CallBounds.current _) rfl)
  | purePair left right ihL ihR | pair left right ihL ihR => exact .pair (ihL empty) (ihR empty)
  | app function argument admitted publicCertified ihF ihA => exact .app (ihF empty) (ihA empty)
  | bind initial body ihI ihB => exact .bind (ihI empty) (ihB empty)
  | cleanup callback body admitted publicCertified ihC ihB => exact .cleanup (ihC empty) (ihB empty)
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource (ihI empty)
        ((ScopedExpressions.instantiation_preserves_usage_iff _ _).mp (ihB identity fresh empty))
  | branch condition yes no same ihC ihY ihN => exact .branch (ihC empty) (ihY empty) (ihN empty)
  | perform known admitted operand formed ih => exact .perform (ih empty)
  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl => exact .handle (ihBody empty) capabilities
  | resume known resolved permission operand admitted formed ih => subst_vars; cases resolved
  | discard known resolved permission unprotected admitted => subst_vars; cases resolved
  | typed | unavailable | available | nil | cons => trivial
omit evidence in
private theorem signature_handler_same
    {first nextFirst : SourcePlanSignatures.ClauseSignatures families}
    {body nextBody : SourcePlanSignatures.Signature dependencies}
    (sameDeclarations : nextFirst = first) (sameBody : nextBody = body) :
    SourcePlanSignatures.Signature.handler (effect := effect) (table := table) required nextFirst nextBody =
      SourcePlanSignatures.Signature.handler (effect := effect) (table := table) required first body := by
  cases sameDeclarations
  cases sameBody
  rfl
omit evidence in
private theorem signature_declaration_cons_same
    {ordinary nextOrdinary : SourcePlanSignatures.ModeSignatures ordinaryFamily}
    {protectedMode nextProtected : SourcePlanSignatures.ModeSignatures protectedFamily}
    {rest nextRest : SourcePlanSignatures.ClauseSignatures restFamily}
    (sameOrdinary : nextOrdinary = ordinary) (sameProtected : nextProtected = protectedMode)
    (sameRest : nextRest = rest) (sameRights : nextRights = rights) :
    SourcePlanSignatures.ClauseSignatures.cons (operation := operation) nextRights nextOrdinary nextProtected nextRest =
      SourcePlanSignatures.ClauseSignatures.cons (operation := operation) rights ordinary protectedMode rest := by
  cases sameOrdinary
  cases sameProtected
  cases sameRest
  cases sameRights
  rfl
theorem IndexedSource.substitution_reannotated_at
    (stable : ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      evidence.accepts outward required first → clauseSignatures first = clauseSignatures second →
      evidence.accepts outward required second)
    {dependencies : Dependencies} {plan : Plan dependencies} {rows : Rows (signature plan)}
    (source : IndexedSource registry outward owners world allowed scope sourceEnvironment code result demand requirements plan rows) :
    ∀ environment name input value, sourceEnvironment = environment.extend name input →
      IndexedSource registry outward owners world allowed scope environment value input [] (.request [] []) .pure Rows.pure → ClosedValue value →
      ∃ nextPlan : Plan dependencies, ∃ nextRows : Rows (signature nextPlan),
        IndexedSource registry outward owners world allowed scope environment (code.subst name value)
          result demand requirements nextPlan nextRows ∧ nextPlan = CoreCallablePlanSubstitution.plan code plan name value ∧ signature nextPlan = signature plan ∧ HEq nextRows rows := by
  induction source using IndexedSource.rec
    (motive_2 := fun owners world allowed scope sourceEnvironment code answer header dependencies plan rows _ =>
      ∀ environment name input value, sourceEnvironment = environment.extend name input →
        IndexedSource registry outward owners world allowed scope environment value input [] (.request [] []) .pure Rows.pure → ClosedValue value →
        ∃ nextPlan : Plan dependencies, ∃ nextRows : Rows (signature nextPlan),
          SourceBody registry outward owners world allowed scope environment (code.subst name value)
            answer header nextPlan nextRows ∧ nextPlan = CoreCallablePlanSubstitution.plan code plan name value ∧ signature nextPlan = signature plan ∧ HEq nextRows rows)
    (motive_3 := fun owners world sourceEnvironment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows _ =>
      ∀ environment name replacementType value, sourceEnvironment = environment.extend name replacementType →
        IndexedSource registry outward owners world allowed .none environment value replacementType [] (.request [] []) .pure Rows.pure → ClosedValue value →
        ∃ nextPlans : ModePlans family, ∃ nextRows : ModeRows (modeSignatures nextPlans),
          SourceOffer registry outward owners world environment allowed parameter binder argument input answer
            resumeEffects closeEffects (if name = parameter then code else code.subst name value) held disposes row nextPlans nextRows ∧
          nextPlans = (if name = parameter then plans else CoreCallablePlanSubstitution.modes code plans name value) ∧ modeSignatures nextPlans = modeSignatures plans ∧ HEq nextRows rows)
    (motive_4 := fun owners world sourceEnvironment allowed requested answer clauses table families plans rows _ =>
      ∀ environment name input value, sourceEnvironment = environment.extend name input →
        IndexedSource registry outward owners world allowed .none environment value input [] (.request [] []) .pure Rows.pure → ClosedValue value →
        ∃ nextPlans : ClausePlans (clauses.subst name value) families, ∃ nextRows : ClauseRows (clauseSignatures nextPlans),
          SourceDeclarations registry outward owners world environment allowed requested answer (clauses.subst name value) table nextPlans nextRows ∧
          nextPlans = CoreCallablePlanSubstitution.clauses plans name value ∧ clauseSignatures nextPlans = clauseSignatures plans ∧ HEq nextRows rows) with
  | unit | boolean | integer | reference =>
      intro environment name input value same replacement closed
      cases same
      refine ⟨_, _, ?_, rfl, rfl, HEq.rfl⟩
      first | exact .unit | exact .boolean | exact .integer | apply IndexedSource.reference; assumption
  | «variable» known formed =>
      intro environment name input value same replacement closed
      cases same
      simp only [Code.subst]
      split
      · rename_i equal
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact ⟨_, _, replacement, rfl, rfl, HEq.rfl⟩
      · rename_i different
        exact ⟨_, _, .variable (by simpa [Environment.extend, Ne.symm different] using known) formed, rfl, rfl, HEq.rfl⟩
  | discard known resolved permission unprotected admitted =>
      intro environment name input value same replacement closed
      cases same
      exact ⟨_, _, .discard known resolved permission unprotected admitted, rfl, rfl, HEq.rfl⟩
  | typed source normal closing ih =>
      rename_i environment name input value same replacement closed
      obtain ⟨nextPlan, nextRows, nextSource, phiSame, signatureSame, rowsSame⟩ := ih environment name input value same replacement closed
      exact ⟨nextPlan, nextRows, .typed nextSource normal closing, phiSame, signatureSame, rowsSame⟩
  | unavailable =>
      exact ⟨.unavailable, .unavailable, .unavailable, by simp [CoreCallablePlanSubstitution.modes], rfl, HEq.rfl⟩
  | nil =>
      simp only [Clauses.subst]
      exact ⟨.nil, .nil, .nil, rfl, rfl, HEq.rfl⟩
  | pair left right ihL ihR =>
      intro environment name input value same replacement closed
      obtain ⟨nextL, rowsL, sourceL, phiL, sigL, alignedL⟩ := ihL environment name input value same replacement closed
      obtain ⟨nextR, rowsR, sourceR, phiR, sigR, alignedR⟩ := ihR environment name input value same replacement closed
      refine ⟨.sequence nextL nextR, sequenceRows rowsL rowsR, .pair sourceL sourceR, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiL, phiR]
      · simp only [signature]; exact congr (congrArg SourcePlanSignatures.Signature.sequence sigL) sigR
      · exact sequence_rows_heq sigL sigR alignedL alignedR
  | purePair left right ihL ihR =>
      intro environment name input value same replacement closed
      obtain ⟨nextL, rowsL, sourceL, phiL, sigL, alignedL⟩ := ihL environment name input value same replacement closed
      obtain ⟨nextR, rowsR, sourceR, phiR, sigR, alignedR⟩ := ihR environment name input value same replacement closed
      cases nextL
      cases nextR
      cases rowsL
      cases rowsR
      exact ⟨_, _, .purePair sourceL sourceR, rfl, rfl, HEq.rfl⟩
  | app function argument admitted publicCertified ihF ihA =>
      intro environment name input value same replacement closed
      obtain ⟨nextF, rowsF, sourceF, phiF, sigF, alignedF⟩ := ihF environment name input value same replacement closed
      obtain ⟨nextA, rowsA, sourceA, phiA, sigA, alignedA⟩ := ihA environment name input value same replacement closed
      refine ⟨_, _, .app sourceF sourceA admitted publicCertified, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiF, phiA]
      · simp only [signature]; exact congr (congrArg SourcePlanSignatures.Signature.sequence sigF)
          (signature_sequence_same sigA rfl)
      · exact sequence_rows_heq sigF (signature_sequence_same sigA rfl)
          alignedF (sequence_rows_heq sigA rfl alignedA HEq.rfl)
  | perform known admitted operand formed ih =>
      intro environment name input value same replacement closed
      obtain ⟨next, nextRows, nextSource, phiSame, sameSig, aligned⟩ := ih environment name input value same replacement closed
      refine ⟨.sequence next .request, sequenceRows nextRows Rows.request, ?_, ?_, ?_, ?_⟩
      · simpa only [Code.subst] using IndexedSource.perform known admitted nextSource formed
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiSame]
      · simp only [signature]; exact congr (congrArg SourcePlanSignatures.Signature.sequence sameSig) rfl
      · exact sequence_rows_heq sameSig rfl aligned HEq.rfl
  | resume known resolved permission operand admitted formed ih =>
      intro environment name input value same replacement closed
      obtain ⟨next, nextRows, nextSource, phiSame, sameSig, aligned⟩ := ih environment name input value same replacement closed
      refine ⟨.sequence next .invoke, sequenceRows nextRows Rows.invoke, ?_, ?_, ?_, ?_⟩
      · simpa only [Code.subst] using IndexedSource.resume known resolved permission nextSource admitted formed
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiSame]
      · simp only [signature]; exact congr (congrArg SourcePlanSignatures.Signature.sequence sameSig) rfl
      · exact sequence_rows_heq sameSig rfl aligned HEq.rfl
  | cleanup callback body admitted publicCertified ihC ihB =>
      intro environment name input value same replacement closed
      obtain ⟨nextC, rowsC, sourceC, phiC, sigC, alignedC⟩ := ihC environment name input value same replacement closed
      obtain ⟨nextB, rowsB, sourceB, phiB, sigB, alignedB⟩ := ihB environment name input value same replacement closed
      refine ⟨_, _, .cleanup sourceC sourceB admitted publicCertified, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiC, phiB]
      · simp only [signature]
        exact congr (congrArg SourcePlanSignatures.Signature.sequence sigC)
          (congrArg (fun body => SourcePlanSignatures.Signature.cleanup _ body) sigB)
      · exact sequence_rows_heq sigC
          (congrArg (fun body => SourcePlanSignatures.Signature.cleanup _ body) sigB)
          alignedC (cleanup_rows_heq sigB alignedB)
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      rename_i bodyDemand owners world allowed scope sourceEnvironment initial initialDemand
        initialRequirements initialDependencies initialPlan initialRows residual output outwardRequirements
        binder template bodyRequirements bodyDependencies bodyPlans bodyRows
      intro environment name input value same replacement closed
      obtain ⟨nextI, rowsI, sourceI, phiI, sigI, alignedI⟩ :=
        ihI environment name input value same replacement closed
      let nextPlans := fun identity => CoreCallablePlanSubstitution.plan
        (template.instantiate (Instantiation.Environment.empty.bind binder identity)) (bodyPlans identity) name value
      have sigB : ∀ identity, signature (nextPlans identity) = signature (bodyPlans identity) :=
        fun identity => CoreCallablePlanSubstitution.plan_signature _ _ name closed.1
      let nextRows := fun identity => (sigB identity).symm ▸ bodyRows identity
      have alignedB : ∀ identity, HEq (nextRows identity) (bodyRows identity) :=
        fun identity => rows_cast_heq (sigB identity) (bodyRows identity)
      have opened : ∀ identity, identity ∉ world →
          IndexedSource registry outward owners (world ++ [identity]) (.cell identity :: residual)
            scope environment
            ((template.subst name value).instantiate (Instantiation.Environment.empty.bind binder identity))
            output bodyDemand (bodyRequirements identity) (nextPlans identity) (nextRows identity) := by
        intro identity fresh
        obtain ⟨newPlan, newRows, newSource, phi, sig, aligned⟩ :=
          ihB identity fresh environment name input value same
            ((replacement.world_weaken (by intro identity member; exact List.mem_append_left _ member)).value_allowed
              closed.1 (.cell identity :: residual) scope) closed
        change newPlan = nextPlans identity at phi
        cases phi
        have rowSame : newRows = nextRows identity := eq_of_heq (aligned.trans (alignedB identity).symm)
        cases rowSame
        rw [Code.instantiation_subst _ name value _ closed.2.1]
        exact newSource
      refine ⟨.sequence nextI (.resource nextPlans), sequenceRows rowsI (Rows.resource nextRows),
        ?_, ?_, ?_, ?_⟩
      · simpa only [Code.subst] using IndexedSource.resource sourceI opened formed effectsBound admitted hidden
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiI]
      · exact signature_sequence_same sigI (congrArg SourcePlanSignatures.Signature.resource (funext sigB))
      · exact sequence_rows_heq sigI (congrArg SourcePlanSignatures.Signature.resource (funext sigB))
          alignedI (resource_rows_heq sigB alignedB)
  | branch condition yes no sameDemand ihC ihY ihN =>
      intro environment name input value same replacement closed
      obtain ⟨nextC, rowsC, sourceC, phiC, sigC, alignedC⟩ := ihC environment name input value same replacement closed
      obtain ⟨nextY, rowsY, sourceY, phiY, sigY, alignedY⟩ := ihY environment name input value same replacement closed
      obtain ⟨nextN, rowsN, sourceN, phiN, sigN, alignedN⟩ := ihN environment name input value same replacement closed
      refine ⟨_, _, .branch sourceC sourceY sourceN sameDemand, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiC, phiY, phiN]
      · simp only [signature]
        exact congr (congrArg SourcePlanSignatures.Signature.sequence sigC)
          (signature_choice_same sigY sigN)
      · exact sequence_rows_heq sigC (signature_choice_same sigY sigN)
          alignedC (choice_rows_heq sigY sigN alignedY alignedN)
  | bind initial body ihI ihB =>
      rename_i bodyPlan bodyRows
      intro environment name input value same replacement closed
      cases same
      obtain ⟨nextI, rowsI, sourceI, phiI, sigI, alignedI⟩ := ihI environment name input value rfl replacement closed
      simp only [Code.subst]
      split
      · rename_i equal
        subst name
        refine ⟨.sequence nextI bodyPlan, sequenceRows rowsI bodyRows, .bind sourceI ?_, ?_, ?_, ?_⟩
        · simpa only [Environment.extend_shadow] using body
        · simp only [CoreCallablePlanSubstitution.plan, ↓reduceIte]; rw [phiI]
        · simp only [signature]; exact congr (congrArg SourcePlanSignatures.Signature.sequence sigI) rfl
        · exact sequence_rows_heq sigI rfl alignedI HEq.rfl
      · rename_i different
        obtain ⟨nextB, rowsB, sourceB, phiB, sigB, alignedB⟩ := ihB _ name input value
          (Environment.extend_commute environment name _ input _ different)
          (replacement.closed_environment closed _) closed
        refine ⟨_, _, .bind sourceI sourceB, ?_, ?_, ?_⟩
        · simp only [CoreCallablePlanSubstitution.plan, if_neg different]; rw [phiI, phiB]
        · simp only [signature]; exact congr (congrArg SourcePlanSignatures.Signature.sequence sigI) sigB
        · exact sequence_rows_heq sigI sigB alignedI alignedB
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      intro environment name input value same replacement closed
      cases same
      simp only [Code.subst]
      split
      · rename_i equal
        subst name
        refine ⟨_, _, .lambda ?_ refinement bodyOutward latentBound publicCertified formed, rfl, rfl, HEq.rfl⟩
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        obtain ⟨nextBody, nextBodyRows, nextSource, phiBody, sameBody, alignedBody⟩ := ih _ name input value
          (Environment.extend_commute environment name _ input _ different)
          ((replacement.value_allowed closed.1 _ .none).closed_environment closed _) closed
        exact ⟨_, _, .lambda nextSource (refines_rows_heq refinement sameBody alignedBody)
          bodyOutward latentBound publicCertified formed, rfl, rfl, HEq.rfl⟩
  | available resumeInterface closeInterface body ih =>
      rename_i environment name input value same replacement closed
      rename_i clauseCode disposes row clauseOwners sourceEnv parameter argument family originalPlans originalRows
      cases same
      split
      · rename_i shadow
        subst name
        refine ⟨_, _, ?_, by simp, rfl, HEq.rfl⟩
        apply SourceOffer.available resumeInterface closeInterface
        intro owner contract inputSame answerSame resumeSame closeSame heldSame balanced
        simpa only [Environment.extend_shadow] using body owner contract inputSame answerSame resumeSame closeSame heldSame balanced
      · rename_i different
        let changedPlans := fun owner => CoreCallablePlanSubstitution.plan clauseCode (originalPlans owner) name value
        let changedRows := fun owner =>
          (CoreCallablePlanSubstitution.plan_signature clauseCode (originalPlans owner) name closed.1).symm ▸ (originalRows owner)
        refine ⟨.available changedPlans, .available changedRows, ?_, rfl, ?_, ?_⟩
        · apply SourceOffer.available
            (by simpa only [Code.substitution_required_actions clauseCode name closed.1] using resumeInterface)
            (by simpa only [Code.substitution_required_actions clauseCode name closed.1] using closeInterface)
          intro owner contract inputSame answerSame resumeSame closeSame heldSame balanced
          obtain ⟨nextPlan, nextRows, actualBody, exactPlan, sameSignature, alignedRows⟩ :=
            ih owner contract inputSame answerSame resumeSame closeSame heldSame balanced
              _ name input value (Environment.extend_commute environment name _ input _ different)
              (((replacement.value_owner_insert closed.1 owner contract).value_allowed closed.1 _ _).closed_environment closed _) closed
          cases exactPlan
          have aligned : HEq nextRows (changedRows owner) := alignedRows.trans
            (rows_cast_heq (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) _).symm
          cases eq_of_heq aligned
          exact actualBody
        · exact CoreCallablePlanSubstitution.modes_signature clauseCode (.available originalPlans) name closed.1
        · exact available_rows_heq (fun owner => CoreCallablePlanSubstitution.plan_signature clauseCode (originalPlans owner) name closed.1)
            (fun owner => rows_cast_heq (CoreCallablePlanSubstitution.plan_signature clauseCode (originalPlans owner) name closed.1) (originalRows owner))
  | receiverLambda body bodyOutward latentBound publicCertified formed ih =>
      rename_i creationWorld bodyOwners requests bodyCode output bodyDemand bodyReq latent parameterInput lambdaAllowed lambdaScope sourceEnv parameter contractDeps contractPlan contractRows privateDeps privatePlans privateRows
      intro environment name input value same replacement closed
      cases same
      simp only [Code.subst]
      split
      · rename_i shadow
        subst name
        refine ⟨_, _, .receiverLambda (privatePlans := privatePlans) (privateRows := privateRows) ?_ bodyOutward latentBound publicCertified formed, rfl, rfl, HEq.rfl⟩
        intro lexical call
        simpa only [Environment.extend_shadow] using body lexical call
      · rename_i different
        let changedPlans := fun lexical call => CoreCallablePlanSubstitution.plan bodyCode (privatePlans lexical call) name value
        let changedRows := fun lexical call =>
          (CoreCallablePlanSubstitution.plan_signature bodyCode (privatePlans lexical call) name closed.1).symm ▸ privateRows lexical call
        refine ⟨_, _, IndexedSource.receiverLambda (privatePlans := changedPlans) (privateRows := changedRows)
          ?_ bodyOutward latentBound publicCertified formed, rfl, rfl, HEq.rfl⟩
        intro lexical call
        obtain ⟨nextPlan, nextRows, actual, exactPlan, sameSignature, aligned⟩ := ih lexical call
          _ name input value (Environment.extend_commute environment name _ input _ different)
          (((replacement.world_weaken call.worldExtended).value_allowed closed.1 _ .none).closed_environment closed _) closed
        cases exactPlan
        have sameRows : HEq nextRows (changedRows lexical call) := aligned.trans
          (rows_cast_heq (CoreCallablePlanSubstitution.plan_signature bodyCode (privatePlans lexical call) name closed.1) _).symm
        cases eq_of_heq sameRows
        exact actual
  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl =>
      intro environment name input value same replacement closed
      cases same
      obtain ⟨nextBody, rowsBody, sourceBody, phiBody, sigBody, alignedBody⟩ := ihBody environment name input value rfl
        (replacement.value_allowed closed.1 _ _) closed
      obtain ⟨nextDecl, rowsDecl, sourceDecl, phiDecl, sigDecl, alignedDecl⟩ := ihDecl environment name input value rfl
        (replacement.value_allowed closed.1 _ .none) closed
      refine ⟨_, _, IndexedSource.handler sourceBody ?_ ?_ ?_ ?_ admitted table ?_ sourceDecl (stable recipes sigDecl.symm), ?_, ?_, ?_⟩
      · simpa only [Environment.ports_extend] using ScopedPorts.clauses_typed_substitution (by simpa only [Environment.ports_extend] using clauses)
          ((replacement.value_allowed closed.1 [] .none).erase) closed
      · exact ScopedExpressions.clauses_usage_substitution capabilities closed.1
          ((replacement.value_allowed closed.1 [] .none).owner_free_usage rfl) name
      · simpa only [ScopedPorts.Covers, ScopedTyping.clause_keys_substitution] using coverage
      · simpa only [ScopedTyping.clause_keys_substitution] using unique
      · exact SourceTemplates.clause_modes_substitution modes closed.1 name
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiBody, phiDecl]
      · simp only [signature]; exact signature_handler_same sigDecl sigBody
      · exact handler_rows_heq sigDecl sigBody alignedDecl alignedBody
  | cons supportBound known ordinary protectedMode rest ihOrd ihProt ihRest =>
      rename_i environment name input value same replacement closed
      rename_i requested operation argument resumeInput declarationOwners declarationWorld sourceEnv declarationAllowed parameter binder answer resumeEffects closeEffects bodyCode dispose ordinaryRow ordinaryFamily ordinaryPlan ordinaryRows protectedRow protectedFamily protectedPlan protectedRows arms table restFamily restPlan restRows
      obtain ⟨nextOrd, rowsOrd, sourceOrd, phiOrd, sigOrd, alignedOrd⟩ := ihOrd environment name input value same replacement closed
      obtain ⟨nextProt, rowsProt, sourceProt, phiProt, sigProt, alignedProt⟩ := ihProt environment name input value same replacement closed
      obtain ⟨nextRest, rowsRest, sourceRest, phiRest, sigRest, alignedRest⟩ := ihRest environment name input value same replacement closed
      have rights : (if name = parameter then bodyCode else bodyCode.subst name value).requiredActions = bodyCode.requiredActions := by
        split
        · rfl
        · exact Code.substitution_required_actions bodyCode name closed.1
      simp only [Clauses.subst]
      refine ⟨_, _, SourceDeclarations.cons supportBound known sourceOrd sourceProt sourceRest, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.clauses]
        rw [phiOrd, phiProt, phiRest]
        split <;> simp_all
      · simp only [clauseSignatures]
        exact signature_declaration_cons_same sigOrd sigProt sigRest rights
      · exact declaration_cons_heq sigOrd sigProt sigRest rights alignedOrd alignedProt alignedRest

end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.IndexedSource.substitution_reannotated_at

#print axioms Ash.OneShot.CoreCallableContractAdmission.IndexedSource.closed_support_in_domain
#print axioms Ash.OneShot.CoreCallableContractAdmission.Hereditary.handlerDomain
#print axioms Ash.OneShot.CoreCallableContractAdmission.DomainDeclarationAuthentication.domainCons
