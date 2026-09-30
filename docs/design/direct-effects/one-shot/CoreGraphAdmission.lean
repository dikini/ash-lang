import CoreExportedAdmission
import CoreGraphCapabilities

/-! A static graph derivation for the supported ordinary, ticket, cleanup and
handler constructors. Core node equations, declared annotations and lexical
checks are inputs; translated source typing, row authentication and clause
usage are constructed outputs. Deriving these annotations from Core validation
and admitting resource entry remain separate obligations. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Environment Operations Contracts Contract)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open InstallationSupport
open CoreSyntax (Graph Node Binder)

/-- Core rows are unordered idempotent sets of exact instantiated effects. -/
def EffectsSame (first second : List Instantiation.Effect) : Prop :=
  ∀ effect, effect ∈ first ↔ effect ∈ second

def allowanceEffects (requests : List Instance) : List Instantiation.Effect :=
  requests.map Instantiation.freezeEffect

/-- This conservative component preserves the original declared callable
allowance. D4 support refinement is a separate obligation, not row widening. -/
inductive TypeAgreement (resources : Instantiation.Environment) : CoreSyntax.ValueType → Value → Prop where
  | unit : TypeAgreement resources .unit .unit
  | boolean : TypeAgreement resources .boolean .boolean
  | integer : TypeAgreement resources .integer .integer
  | reference (resolved : name.instantiate resources = .activation identity) :
      TypeAgreement resources (.reference name) (.reference identity)
  | product : TypeAgreement resources left first → TypeAgreement resources right second →
      TypeAgreement resources (.product left right) (.pair first second)
  | function : TypeAgreement resources input first → TypeAgreement resources output second →
      EffectsSame (effects.map (fun effect => effect.instantiate resources)) (allowanceEffects requests) →
      (∀ request ∈ latent, request.effect ∈ requests) →
      TypeAgreement resources (.function input output effects) (.function first second requests latent checking)

/-- Metadata retains the declared expression row, which may exceed the actual
outward footprint. Constructor rows include declared callee effects at apps. -/
structure Metadata (resources : Instantiation.Environment) (node : Node) (value : Value)
    (effects : List Instantiation.Effect) : Prop where
  type : TypeAgreement resources node.type value
  effects : EffectsSame (node.effects.map (fun effect => effect.instantiate resources)) effects

variable {contracts : Contracts} {owners : ContractRows contracts}
  {world : List Nat} {ownerMap : CoreTranslation.OwnerMap}

mutual
inductive Checked (graph : Graph)
    (operations : Operations) (policy : Syntax.TicketPolicy) (ports : OperationRows operations) :
    (resources : Instantiation.Environment) → (contracts : Contracts) → ContractRows contracts →
    (world : List Nat) → CoreTranslation.OwnerMap →
    (allowed : List Instance) → (scope : Execution.Scope) →
    (environment : Environment) → EnvironmentRows environment →
    Nat → Nat → Code → (value : Value) → (demand : List Nat) → Requirements demand →
    {dependencies : SourceDependencyAnnotations.Dependencies} →
    (plan : Plan dependencies) → ValueRows value → Rows (signature plan) → List Instantiation.Effect → Prop where
  | unit {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node) (kind : node.kind = .unit)
      (metadata : Metadata resources node .unit []) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index .unit .unit [] CoreInitialExample.empty .pure .unit .pure []
  | boolean {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node) (kind : node.kind = .boolean flag)
      (metadata : Metadata resources node .boolean []) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.boolean flag) .boolean [] CoreInitialExample.empty .pure .boolean .pure []
  | integer {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node) (kind : node.kind = .integer number)
      (metadata : Metadata resources node .integer []) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.integer number) .integer [] CoreInitialExample.empty .pure .integer .pure []
  | variable {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node) (kind : node.kind = .variable name)
      (binding : environment name = some value)
      (formed : ScopedPorts.InWorld world value.erase.erase.port)
      (metadata : Metadata resources node value []) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.variable name) value [] CoreInitialExample.empty .pure
        (environmentRows name value binding) .pure []
  | lambda {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node) (kind : node.kind = .function binder bodyIndex)
      (inputType : TypeAgreement resources binder.type input)
      (body : Checked graph operations policy ports resources contracts owners world ownerMap requests .none
        (environment.extend binder.id input) (environmentRows.extend binder.id inputRows)
        fuel bodyIndex code output bodyDemand bodyRequirements bodyPlan outputRows bodyRows bodyEffects)
      (bodyBound : bodyEffects ⊆ allowanceEffects requests)
      (outward : RecursiveOutward.Outward bodyRequirements (some latent))
      (captured : LambdaPortCaptureSupport.captures environment binder.id code input output requests)
      (formed : ScopedPorts.InWorld world (Value.function input output requests latent (signature bodyPlan)).erase.erase.port)
      (latentBound : ∀ request ∈ latent, request.effect ∈ requests)
      (metadata : Metadata resources node (.function input output requests latent (signature bodyPlan)) []) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.lambda binder.id code) (.function input output requests latent (signature bodyPlan))
        [] CoreInitialExample.empty .pure (.function inputRows outputRows bodyRows) .pure []
  | app {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node) (kind : node.kind = .apply functionIndex argumentIndex)
      (function : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel functionIndex f (.function input output requests latent (signature bodyPlan))
        functionDemand functionReq functionPlan (.function inputRows outputRows bodyRows) functionRows functionEffects)
      (argument : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel argumentIndex a input argumentDemand argumentReq argumentPlan inputRows argumentRows argumentEffects)
      (admitted : requests ⊆ allowed)
      (metadata : Metadata resources node output (functionEffects ++ argumentEffects ++ allowanceEffects requests)) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.app f a) output (functionDemand ++ argumentDemand)
        (.emitAfter (.sequence functionReq argumentReq) [] latent)
        (.sequence functionPlan (.sequence argumentPlan bodyPlan)) outputRows
        (by simpa only [signature] using Rows.sequence functionRows (Rows.sequence argumentRows bodyRows))
        (functionEffects ++ argumentEffects ++ allowanceEffects requests)
  | bind {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node) (kind : node.kind = .bind binder initialIndex bodyIndex)
      (inputType : TypeAgreement resources binder.type input)
      (initializer : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel initialIndex a input initialDemand initialReq initialPlan inputRows initialRows initialEffects)
      (body : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
        (environment.extend binder.id input) (environmentRows.extend binder.id inputRows)
        fuel bodyIndex b output bodyDemand bodyReq bodyPlan outputRows bodyRows bodyEffects)
      (metadata : Metadata resources node output (initialEffects ++ bodyEffects)) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.bind binder.id a b) output (initialDemand ++ bodyDemand)
        (.sequence initialReq bodyReq) (.sequence initialPlan bodyPlan) outputRows (by simpa only [signature] using Rows.sequence initialRows bodyRows) (initialEffects ++ bodyEffects)
  | pair {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node) (kind : node.kind = .tuple [leftIndex, rightIndex])
      (left : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel leftIndex a first leftDemand leftReq leftPlan firstRows leftRows leftEffects)
      (right : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel rightIndex b second rightDemand rightReq rightPlan secondRows rightRows rightEffects)
      (metadata : Metadata resources node (.pair first second) (leftEffects ++ rightEffects)) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.pair a b) (.pair first second) (leftDemand ++ rightDemand)
        (.sequence leftReq rightReq) (.sequence leftPlan rightPlan) (.pair firstRows secondRows)
        (by simpa only [signature] using Rows.sequence leftRows rightRows) (leftEffects ++ rightEffects)
  | branch {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node)
      (kind : node.kind = .matchCases conditionIndex
        [⟨.boolean true, yesIndex⟩, ⟨.boolean false, noIndex⟩] ∨
        node.kind = .matchCases conditionIndex [⟨.boolean false, noIndex⟩, ⟨.boolean true, yesIndex⟩])
      (condition : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel conditionIndex test .boolean conditionDemand conditionReq conditionPlan .boolean conditionRows conditionEffects)
      (yes : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel yesIndex a output yesDemand yesReq yesPlan outputRows yesRows yesEffects)
      (no : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel noIndex b output noDemand noReq noPlan outputRows noRows noEffects)
      (same : yesDemand.Perm noDemand)
      (metadata : Metadata resources node output (conditionEffects ++ yesEffects ++ noEffects)) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.branch test a b) output (conditionDemand ++ yesDemand)
        (.sequence conditionReq (.choice yesReq noReq same)) (.sequence conditionPlan (.choice yesPlan noPlan)) outputRows
        (by simpa only [signature] using Rows.sequence conditionRows (Rows.choice yesRows noRows))
        (conditionEffects ++ yesEffects ++ noEffects)
  | unitMatch {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node)
      (kind : node.kind = .matchCases initialIndex [⟨.unit, bodyIndex⟩])
      (initializer : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel initialIndex a .unit initialDemand initialReq initialPlan .unit initialRows initialEffects)
      (body : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
        (environment.extend (CoreTranslation.dummy graph index) .unit)
        (environmentRows.extend (CoreTranslation.dummy graph index) .unit)
        fuel bodyIndex b output bodyDemand bodyReq bodyPlan outputRows bodyRows bodyEffects)
      (metadata : Metadata resources node output (initialEffects ++ bodyEffects)) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.bind (CoreTranslation.dummy graph index) a b) output (initialDemand ++ bodyDemand)
        (.sequence initialReq bodyReq) (.sequence initialPlan bodyPlan) outputRows
        (by simpa only [signature] using Rows.sequence initialRows bodyRows) (initialEffects ++ bodyEffects)
  | nonrecursive {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node)
      (kind : node.kind = .recursiveBind [⟨binder, initialIndex⟩] bodyIndex)
      (functionShape : ∃ initialNode parameter functionBody, graph.node initialIndex = some initialNode ∧
        initialNode.kind = .function parameter functionBody)
      (inputType : TypeAgreement resources binder.type input)
      (initializer : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel initialIndex a input initialDemand initialReq initialPlan inputRows initialRows initialEffects)
      (rawTranslated : CoreTranslation.translateFuel graph fuel ownerMap initialIndex = .ok initialRaw)
      (notRecursive : initialRaw.dependencies.contains (.variable binder.id) = false)
      (body : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
        (environment.extend binder.id input) (environmentRows.extend binder.id inputRows)
        fuel bodyIndex b output bodyDemand bodyReq bodyPlan outputRows bodyRows bodyEffects)
      (metadata : Metadata resources node output (initialEffects ++ bodyEffects)) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.bind binder.id a b) output (initialDemand ++ bodyDemand)
        (.sequence initialReq bodyReq) (.sequence initialPlan bodyPlan) outputRows
        (by simpa only [signature] using Rows.sequence initialRows bodyRows) (initialEffects ++ bodyEffects)
  | perform {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node) (kind : node.kind = .request rawEffect operation operandIndex)
      (instantiated : rawEffect.instantiate resources = Instantiation.freezeEffect effect)
      (operationType : operations effect operation = some (input, output))
      (operand : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel operandIndex value input operandDemand operandReq operandPlan
        (ports effect operation input output operationType).1 operandRows operandEffects)
      (admitted : effect ∈ allowed) (formed : ScopedPorts.InWorld world output.erase.erase.port)
      (metadata : Metadata resources node output (operandEffects ++ [Instantiation.freezeEffect effect])) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.perform (Instantiation.freezeEffect effect) operation value) output operandDemand
        (.emitAfter operandReq [] [⟨effect, operation, false⟩]) (.sequence operandPlan .request)
        (ports effect operation input output operationType).2 (by simpa only [signature] using Rows.sequence operandRows (Rows.request (effect := effect) (operation := operation)))
        (operandEffects ++ [Instantiation.freezeEffect effect])
  | resume {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node)
      (kind : node.kind = .resume handler coreOwner .consumed operandIndex)
      (mapped : CoreTranslation.resolveOwner ownerMap index handler coreOwner = .ok binder)
      (contractKnown : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (operand : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel operandIndex value contract.input operandDemand operandReq operandPlan
        (owners owner contract contractKnown).1 operandRows operandEffects)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.erase.erase.port)
      (metadata : Metadata resources node contract.answer (operandEffects ++ allowanceEffects contract.resumeEffects)) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.resume binder value) contract.answer (operandDemand ++ owner :: contract.resumeDemand)
        (.sequence operandReq (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
        (.sequence operandPlan (.invoke (key := ⟨owner, .resume⟩))) (owners owner contract contractKnown).2
        (by simpa only [signature] using Rows.sequence operandRows (Rows.invoke (key := ⟨owner, .resume⟩)))
        (operandEffects ++ allowanceEffects contract.resumeEffects)
  | discard {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} (known : graph.node index = some node)
      (kind : node.kind = .discard handler coreOwner .consumed)
      (mapped : CoreTranslation.resolveOwner ownerMap index handler coreOwner = .ok binder)
      (contractKnown : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed)
      (metadata : Metadata resources node .unit (allowanceEffects contract.closeEffects)) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.discard binder) .unit (owner :: contract.closeDemand)
        (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) (.invoke (key := ⟨owner, .dispose⟩)) .unit .invoke
        (allowanceEffects contract.closeEffects)

  | cleanup {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap}
      (known : graph.node index = some node) (kind : node.kind = .cleanup callbackBinder actionIndex bodyIndex)
      (actionShape : CoreTranslation.checkCleanup graph index callbackBinder actionIndex = .ok ())
      (callbackType : TypeAgreement resources callbackBinder.type
        (.function .unit .unit requests latent (signature callbackBodyPlan)))
      (callback : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel callbackIndex (.variable callbackBinder.id) (.function .unit .unit requests latent (signature callbackBodyPlan))
        callbackDemand callbackReq callbackPlan (.function .unit .unit callbackBodyRows) callbackRows callbackEffects)
      (action : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel actionIndex (.app (.variable callbackBinder.id) .unit) .unit
        actionDemand actionReq actionPlan .unit actionRows actionEffects)
      (body : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        fuel bodyIndex code output bodyDemand bodyReq bodyPlan outputRows bodyRows bodyEffects)
      (admitted : requests ⊆ allowed)
      (metadata : Metadata resources node output (callbackEffects ++ bodyEffects ++ allowanceEffects requests)) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.cleanup (.variable callbackBinder.id) code) output
        (callbackDemand ++ bodyDemand) (.emitAfter (.sequence callbackReq bodyReq) [] (qualify true latent))
        (Plan.sequence callbackPlan (Plan.cleanup (needs := requests) callbackBodyPlan bodyPlan)) outputRows
        (by simpa only [signature] using Rows.sequence callbackRows (Rows.cleanup latent callbackBodyRows bodyRows))
        (callbackEffects ++ bodyEffects ++ allowanceEffects requests)

  | handler {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap}
      (known : graph.node index = some node) (kind : node.kind = .handler handler rawEffect bodyIndex coreClauses)
      (instantiated : rawEffect.instantiate resources = Instantiation.freezeEffect effect)
      (shapes : CoreSyntax.checkClauseShapes index coreClauses = .ok ())
      (body : Checked graph operations policy ports resources contracts owners world ownerMap (effect :: residual) scope environment environmentRows
        fuel bodyIndex code answer demand requirements bodyPlan answerRows bodyRows bodyEffects)
      (declarations : CheckedDeclarations graph operations policy ports resources contracts owners world ownerMap residual environment environmentRows
        fuel handler effect answer answerRows coreClauses arms table plans declarationRows)
      (coverage : ScopedPorts.Covers operations.erase.erase.ports effect arms)
      (unique : (ScopedTyping.clauseKeys arms).Nodup)
      (admitted : residual ⊆ allowed)
      (effectsAdmitted : handlerEffects ⊆ allowanceEffects residual)
      (metadata : Metadata resources node answer handlerEffects) :
      Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
        (fuel + 1) index (.handle (Instantiation.freezeEffect effect) code arms) answer demand
        (requirements.prepend [.ordinary (.handler effect 0 table)])
        (Plan.handler (effect := effect) (table := table) required plans bodyPlan) answerRows
        (by simpa only [signature] using Rows.handler (required := required) declarationRows bodyRows) handlerEffects

inductive CheckedOffer (graph : Graph) (operations : Operations) (policy : Syntax.TicketPolicy) (ports : OperationRows operations) :
    (resources : Instantiation.Environment) → (contracts : Contracts) → ContractRows contracts →
    (world : List Nat) → CoreTranslation.OwnerMap → (allowed : List Instance) →
    (environment : Environment) → EnvironmentRows environment →
    Nat → Nat → Nat → Nat → Nat → Nat →
    (argument : Value) → ValueRows argument → (input : Value) → ValueRows input →
    (answer : Value) → ValueRows answer → List Instance → List Instance → Code → Bool → Bool → Option Footprint →
    {family : Option (Nat → SourceDependencyAnnotations.Dependencies)} →
    (plans : SourceDeclarationPlans.ModePlans family) → ModeRows (SourcePlanSignatures.modeSignatures plans) → Prop where
  | unavailable {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} :
      CheckedOffer graph operations policy ports resources contracts owners world ownerMap allowed environment environmentRows
        fuel handler coreOwner bodyIndex parameter binder argument argumentRows input inputRows answer answerRows
        resumeEffects closeEffects code held disposes none .unavailable .unavailable
  | available {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap}
      {family : Nat → SourceDependencyAnnotations.Dependencies}
      {plans : ∀ owner, Plan (family owner)}
      {bodyRows : ∀ owner, Rows (signature (plans owner))}
      {bodyDemand : Nat → Contract → List Nat}
      {bodyReq : ∀ owner contract, contract.closeDemand.Perm contract.resumeDemand → Requirements (bodyDemand owner contract)}
      (resumeInterface : code.requiredActions.resume = true → resumeEffects = allowed)
      (closeInterface : code.requiredActions.dispose = true → closeEffects = allowed)
      (body : ∀ owner (contract : Contract) (_fresh : contracts owner = none)
          (inputSame : contract.input = input) (answerSame : contract.answer = answer)
          (_resumeSame : contract.resumeEffects = resumeEffects) (_closeSame : contract.closeEffects = closeEffects)
          (_heldSame : contract.held = held) (balance : contract.closeDemand.Perm contract.resumeDemand),
        Checked graph operations policy ports resources (contracts.insert owner contract)
          (owners.insert owner (inputSame.symm ▸ inputRows) (answerSame.symm ▸ answerRows)) world
          (⟨handler, coreOwner, binder⟩ :: ownerMap) allowed (.ticket binder owner)
          (environment.extend parameter argument) (environmentRows.extend parameter argumentRows)
          fuel bodyIndex code answer (bodyDemand owner contract) (bodyReq owner contract balance)
          (plans owner) answerRows (bodyRows owner) bodyEffects)
      (rows : ∀ owner (contract : Contract), contracts owner = none →
          contract.input = input → contract.answer = answer → contract.resumeEffects = resumeEffects →
          contract.closeEffects = closeEffects → contract.held = held →
          ∀ balance : contract.closeDemand.Perm contract.resumeDemand,
        ClauseRowAdmission.Rows ⟨owner, contract.erase.erase, disposes, row⟩ (bodyReq owner contract balance)
          (ClauseRowAdmission.SourceStore operations.erase.erase owner contract.erase.erase))
      (closingRows : ∀ owner (contract : Contract), contracts owner = none →
          contract.input = input → contract.answer = answer → contract.resumeEffects = resumeEffects →
          contract.closeEffects = closeEffects → contract.held = held →
          ∀ balance : contract.closeDemand.Perm contract.resumeDemand,
        ClauseRowAdmission.ProtectedRows ⟨owner, contract.erase.erase, disposes, row⟩ (bodyReq owner contract balance)
          (ClauseRowAdmission.SourceStore operations.erase.erase owner contract.erase.erase)) :
      CheckedOffer graph operations policy ports resources contracts owners world ownerMap allowed environment environmentRows
        fuel handler coreOwner bodyIndex parameter binder argument argumentRows input inputRows answer answerRows
        resumeEffects closeEffects code held disposes (some row) (.available plans)
        (by simpa only [SourcePlanSignatures.modeSignatures] using ModeRows.available bodyRows)

inductive CheckedDeclarations (graph : Graph) (operations : Operations) (policy : Syntax.TicketPolicy) (ports : OperationRows operations) :
    (resources : Instantiation.Environment) → (contracts : Contracts) → ContractRows contracts →
    (world : List Nat) → CoreTranslation.OwnerMap → (allowed : List Instance) →
    (environment : Environment) → EnvironmentRows environment → Nat → Nat →
    Instance → (answer : Value) → ValueRows answer → List CoreSyntax.Clause →
    (clauses : Clauses) → List (Nat × ClauseContract) →
    {families : SourceDependencyAnnotations.ClauseDependencies} →
    (plans : SourceDeclarationPlans.ClausePlans clauses families) →
    ClauseRows (SourcePlanSignatures.clauseSignatures plans) → Prop where
  | nil {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap} :
      CheckedDeclarations graph operations policy ports resources contracts owners world ownerMap allowed environment environmentRows
        fuel handler effect answer answerRows [] .nil [] .nil .nil
  | cons {resources : Instantiation.Environment} {contracts : Contracts} {owners : ContractRows contracts}
      {world : List Nat} {ownerMap : CoreTranslation.OwnerMap}
      (operationKnown : operations effect operation = some (argument, input))
      (argumentType : TypeAgreement resources parameter.type argument)
      (distinct : ownerMap.any (fun binding => binding.owner == coreOwner) = false)
      (mapped : binder = CoreTranslation.ticket graph coreOwner)
      (witnessFresh : contracts witness = none)
      (witnessInput : witnessContract.input = input) (witnessAnswer : witnessContract.answer = answer)
      (witnessResume : witnessContract.resumeEffects = allowed) (witnessClose : witnessContract.closeEffects = allowed)
      (witnessHeld : witnessContract.held = false)
      (portBody : Checked graph operations policy ports resources (contracts.insert witness witnessContract)
        (owners.insert witness (witnessInput.symm ▸ (ports effect operation argument input operationKnown).2)
          (witnessAnswer.symm ▸ answerRows)) world (⟨handler, coreOwner, binder⟩ :: ownerMap) allowed
        (.ticket binder witness) (environment.extend parameter.id argument)
        (environmentRows.extend parameter.id (ports effect operation argument input operationKnown).1)
        fuel bodyIndex code answer portDemand portReq portPlan answerRows portRows bodyEffects)
      (disposeMode : code.requiredActions.dispose = true → disposes = true)
      (usage : CoreGraphCapabilities.state policy (.ticket binder (policy binder)) .available usageFuel code = some .consumed)
      (ordinary : CheckedOffer graph operations policy ports resources contracts owners world ownerMap allowed environment environmentRows
        fuel handler coreOwner bodyIndex parameter.id binder argument (ports effect operation argument input operationKnown).1
        input (ports effect operation argument input operationKnown).2 answer answerRows
        resumeEffects closeEffects code false disposes ordinaryRow ordinaryPlan ordinaryRows)
      (protectedMode : CheckedOffer graph operations policy ports resources contracts owners world ownerMap allowed environment environmentRows
        fuel handler coreOwner bodyIndex parameter.id binder argument (ports effect operation argument input operationKnown).1
        input (ports effect operation argument input operationKnown).2 answer answerRows
        resumeEffects closeEffects code true disposes protectedRow protectedPlan protectedRows)
      (rest : CheckedDeclarations graph operations policy ports resources contracts owners world ownerMap allowed environment environmentRows
        fuel handler effect answer answerRows restCore restClauses restTable restPlan restRows)
      (support : ScopedPorts.Support.evaluate (LambdaPortCaptureSupport.portSupport (environment.extend parameter.id argument))
        code.dependencies ⊆ supportBound) :
      CheckedDeclarations graph operations policy ports resources contracts owners world ownerMap allowed environment environmentRows
        fuel handler effect answer answerRows
        (⟨operation, .binder parameter, coreOwner, bodyIndex⟩ :: restCore) (.cons operation parameter.id binder code restClauses)
        ((operation, ⟨disposes, ordinaryRow, protectedRow⟩) :: restTable)
        (.cons ordinaryPlan protectedPlan restPlan)
        (by simpa only [SourcePlanSignatures.clauseSignatures] using
          ClauseRows.cons (operation := operation) (rights := code.requiredActions) ordinaryRows protectedRows restRows supportBound)
end

private def translateClauseList (graph : Graph) (fuel : Nat) (ownerMap : CoreTranslation.OwnerMap)
    (handler index : Nat) (clauses : List CoreSyntax.Clause) : Except CoreSyntax.Error (List (Nat × Nat × Nat × Code)) :=
  clauses.mapM fun clause => do
    if ownerMap.any (fun binding => binding.owner == clause.owner) then
      throw (.duplicateOwner index clause.owner)
    match clause.argument with
    | .binder argument =>
        let mapped := CoreTranslation.ticket graph clause.owner
        let clauseOwners := ⟨handler, clause.owner, mapped⟩ :: ownerMap
        let translated ← CoreTranslation.translateFuel graph fuel clauseOwners clause.body
        pure (clause.operation, argument.id, mapped, translated)
    | _ => throw (.unsupportedClausePattern index clause.operation)

private def packClauses (entries : List (Nat × Nat × Nat × Code)) : Clauses :=
  entries.foldr (fun (operation, parameter, binder, body) rest => .cons operation parameter binder body rest) .nil

private theorem handlerTranslation (known : graph.node index = some node)
    (kind : node.kind = .handler handler effect bodyIndex clauses)
    (shapes : CoreSyntax.checkClauseShapes index clauses = .ok ())
    (body : CoreTranslation.translateFuel graph fuel ownerMap bodyIndex = .ok rawBody)
    (declarations : translateClauseList graph fuel ownerMap handler index clauses = .ok entries) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.handle effect rawBody (packClauses entries)) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do
      CoreSyntax.checkClauseShapes index clauses
      let translatedBody ← CoreTranslation.translateFuel graph fuel ownerMap bodyIndex
      let translatedClauses ← translateClauseList graph fuel ownerMap handler index clauses
      pure (Code.handle effect translatedBody (packClauses translatedClauses))) = _
    rw [shapes, body, declarations]
    rfl

def CheckedOffer.Compiled
    (_checked : CheckedOffer graph operations policy ports resources contracts owners world ownerMap allowed environment environmentRows
      fuel handler coreOwner bodyIndex parameter binder argument argumentRows input inputRows answer answerRows
      resumeEffects closeEffects code held disposes row plans rows) : Prop :=
    ∃ source : SourcePlannedSources.Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans,
      AuthOffer operations policy ports owners environmentRows argumentRows inputRows answerRows source rows

def CheckedDeclarations.Compiled
    (_checked : CheckedDeclarations graph operations policy ports resources contracts owners world ownerMap allowed environment environmentRows
      fuel handler effect answer answerRows core clauses table plans rows) : Prop :=
    ∃ source : SourcePlannedSources.Declarations operations policy contracts world environment allowed effect answer clauses table plans,
      AuthDeclarations operations policy ports owners environmentRows answerRows source rows ∧
      ScopedPorts.ClausesTyped operations.erase.erase.ports world environment.erase.erase.ports effect answer.erase.erase.port allowed clauses ∧
      ClausesUse policy clauses ∧ SourceTemplates.ClauseModes clauses table

private theorem ticketScope (known : contracts owner = some contract) :
    ScopedPorts.EffectScope contracts.erase.erase.ports (.ticket binder owner)
      (.bound binder contract.input.erase.erase.port contract.answer.erase.erase.port contract.resumeEffects contract.closeEffects) :=
  .bound (CoherentSourceTypes.Owners.ports_lookup
    (SourceDependencyAnnotations.contract_erase_known (SourcePlannedSources.contract_erase_known known)))

/-- The graph certificate constructs both source layers; neither is an input. -/
theorem Checked.sourceAuth
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
      fuel index code value demand requirements plan valueRows rows effects) :
    ∃ source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      code value demand requirements (signature plan), Auth operations policy ports owners environmentRows source valueRows rows := by
  induction checked using Checked.rec
    (motive_2 := fun resources contracts owners world ownerMap allowed environment environmentRows fuel handler coreOwner bodyIndex parameter binder argument argumentRows input inputRows answer answerRows resumeEffects closeEffects code held disposes row family plans rows checked => CheckedOffer.Compiled checked)
    (motive_3 := fun resources contracts owners world ownerMap allowed environment environmentRows fuel handler effect answer answerRows core clauses table families plans rows checked => CheckedDeclarations.Compiled checked) with
  | unit => exact ⟨.unit, .unit⟩
  | boolean => exact ⟨.boolean, .boolean⟩
  | integer => exact ⟨.integer, .integer⟩
  | «variable» known kind binding formed => exact ⟨.variable binding formed, .variable (formed := formed)⟩
  | lambda known kind inputType body bodyBound outward captured formed latentBound metadata ih =>
      obtain ⟨source, authenticated⟩ := ih
      exact ⟨.lambda source outward formed latentBound, .lambda authenticated captured (outward := outward) (formed := formed) (latentBound := latentBound)⟩
  | app known kind function argument admitted metadata ihF ihA =>
      obtain ⟨sourceF, authF⟩ := ihF
      obtain ⟨sourceA, authA⟩ := ihA
      exact ⟨.app sourceF sourceA admitted, .app (admitted := admitted) authF authA⟩
  | bind known kind inputType initializer body metadata ihI ihB =>
      obtain ⟨sourceI, authI⟩ := ihI
      obtain ⟨sourceB, authB⟩ := ihB
      exact ⟨.bind sourceI sourceB, .bind authI authB⟩
  | pair known kind left right metadata ihL ihR =>
      obtain ⟨sourceL, authL⟩ := ihL
      obtain ⟨sourceR, authR⟩ := ihR
      exact ⟨.pair sourceL sourceR, .pair authL authR⟩
  | branch known kind condition yes no same metadata ihC ihY ihN =>
      obtain ⟨sourceC, authC⟩ := ihC
      obtain ⟨sourceY, authY⟩ := ihY
      obtain ⟨sourceN, authN⟩ := ihN
      exact ⟨.branch sourceC sourceY sourceN same, .branch authC authY authN⟩
  | unitMatch known kind initializer body metadata ihI ihB =>
      obtain ⟨sourceI, authI⟩ := ihI
      obtain ⟨sourceB, authB⟩ := ihB
      exact ⟨.bind sourceI sourceB, .bind authI authB⟩
  | nonrecursive known kind functionShape inputType initializer rawTranslated notRecursive body metadata ihI ihB =>
      obtain ⟨sourceI, authI⟩ := ihI
      obtain ⟨sourceB, authB⟩ := ihB
      exact ⟨.bind sourceI sourceB, .bind authI authB⟩
  | perform known kind instantiated operationType operand admitted formed metadata ih =>
      obtain ⟨source, authenticated⟩ := ih
      exact ⟨.perform operationType admitted source formed, .perform (known := operationType) (admitted := admitted) (formed := formed) authenticated⟩
  | resume known kind mapped contractKnown resolved permission operand admitted formed metadata ih =>
      obtain ⟨source, authenticated⟩ := ih
      exact ⟨.resume contractKnown resolved permission source admitted formed,
        .resume (known := contractKnown) (resolved := resolved) (permission := permission)
          (admitted := admitted) (formed := formed) authenticated⟩
  | discard known kind mapped contractKnown resolved permission unprotected admitted metadata =>
      exact ⟨.discard contractKnown resolved permission unprotected admitted,
        .discard (known := contractKnown) (resolved := resolved) (permission := permission)
          (unprotected := unprotected) (admitted := admitted)⟩

  | cleanup known kind actionShape callbackType callback action body admitted metadata ihCallback _ihAction ihBody =>
      obtain ⟨sourceC, authC⟩ := ihCallback
      obtain ⟨sourceB, authB⟩ := ihBody
      exact ⟨.cleanup sourceC sourceB admitted, .cleanup (admitted := admitted) authC authB⟩

  | handler known kind instantiated shapes body declarations coverage unique admitted effectsAdmitted metadata ihBody ihDecl =>
      obtain ⟨sourceB, authB⟩ := ihBody
      obtain ⟨sourceD, authD, typed, capabilities, modes⟩ := ihDecl
      exact ⟨.handler sourceB typed capabilities coverage unique admitted _ modes sourceD,
        .handler (clauses := typed) (capabilities := capabilities) (coverage := coverage) (unique := unique)
          (admitted := admitted) (modes := modes) authB authD⟩
  | unavailable => exact ⟨.unavailable, .unavailable⟩
  | available resumeInterface closeInterface body rows closingRows ihBody =>
      refine (let sourceBodies := ?_;
        ⟨.available resumeInterface closeInterface sourceBodies,
          AuthOffer.available (source := sourceBodies) (resumeInterface := resumeInterface)
            (closeInterface := closeInterface) ?_⟩)
      · intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
        obtain ⟨source, authenticated⟩ := ihBody owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
        exact .typed source (rows owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance)
          (closingRows owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance)
      · intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
        obtain ⟨source, authenticated⟩ := ihBody owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
        exact AuthBody.typed (source := source)
          (rows := rows owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance)
          (closingRows := closingRows owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance) authenticated
  | nil => exact ⟨.nil, .nil, .nil, .nil, .nil⟩
  | cons operationKnown argumentType distinct mapped witnessFresh witnessInput witnessAnswer witnessResume witnessClose witnessHeld
      portBody disposeMode usage ordinary protectedMode rest support ihPort ihOrdinary ihProtected ihRest =>
      obtain ⟨sourceP, authP⟩ := ihPort
      obtain ⟨sourceO, authO⟩ := ihOrdinary
      obtain ⟨sourceH, authH⟩ := ihProtected
      obtain ⟨sourceR, authR, typedR, useR, modesR⟩ := ihRest
      have portTyped := SourceTemplates.expression_ports
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
          (SourcePlannedSources.expression_erase sourceP)))
        (ticketScope (by simp [SourcePlannedTyping.Contracts.insert]; rfl))
      refine ⟨.cons operationKnown sourceO sourceH sourceR, .cons authO authH authR support, ?_,
        .cons (CoreGraphCapabilities.sound usage) useR, .cons disposeMode modesR⟩
      apply ScopedPorts.ClausesTyped.cons
        (CoherentSourceTypes.port_lookup (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase operationKnown)))
      · simpa only [SourceDependencyAnnotations.environment_erase_extend,
          SourcePlannedTyping.environment_erase_extend, CoherentSourceTypes.ports_extend,
          witnessInput, witnessAnswer, witnessResume, witnessClose] using portTyped
      · exact typedR

private theorem cleanupTranslation (known : graph.node index = some node)
    (kind : node.kind = .cleanup callback action bodyIndex)
    (authenticated : CoreTranslation.checkCleanup graph index callback action = .ok ())
    (body : CoreTranslation.translateFuel graph fuel ownerMap bodyIndex = .ok raw) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.cleanup (.variable callback.id) raw) := by
  rw [CoreTranslation.cleanup_equation _ _ _ _ _ _ _ _ known kind authenticated, body]
  rfl

private theorem pairTranslation (known : graph.node index = some node)
    (kind : node.kind = .tuple [leftIndex, rightIndex])
    (left : CoreTranslation.translateFuel graph fuel ownerMap leftIndex = .ok rawL)
    (right : CoreTranslation.translateFuel graph fuel ownerMap rightIndex = .ok rawR) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.pair rawL rawR) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do pure (Code.pair (← CoreTranslation.translateFuel graph fuel ownerMap leftIndex)
      (← CoreTranslation.translateFuel graph fuel ownerMap rightIndex))) = _
    rw [left, right]
    rfl

private theorem branchTranslation (known : graph.node index = some node)
    (kind : node.kind = .matchCases conditionIndex [⟨.boolean true, yesIndex⟩, ⟨.boolean false, noIndex⟩] ∨
      node.kind = .matchCases conditionIndex [⟨.boolean false, noIndex⟩, ⟨.boolean true, yesIndex⟩])
    (condition : CoreTranslation.translateFuel graph fuel ownerMap conditionIndex = .ok rawC)
    (yes : CoreTranslation.translateFuel graph fuel ownerMap yesIndex = .ok rawY)
    (no : CoreTranslation.translateFuel graph fuel ownerMap noIndex = .ok rawN) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.branch rawC rawY rawN) := by
  cases node with
  | mk original type effects span nodeKind =>
    rcases kind with kind | kind <;> cases kind <;>
      simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known] <;>
      change (do pure (Code.branch (← CoreTranslation.translateFuel graph fuel ownerMap conditionIndex)
        (← CoreTranslation.translateFuel graph fuel ownerMap yesIndex)
        (← CoreTranslation.translateFuel graph fuel ownerMap noIndex))) = _ <;>
      rw [condition, yes, no] <;> rfl

private theorem unitMatchTranslation (known : graph.node index = some node)
    (kind : node.kind = .matchCases initialIndex [⟨.unit, bodyIndex⟩])
    (initializer : CoreTranslation.translateFuel graph fuel ownerMap initialIndex = .ok rawI)
    (body : CoreTranslation.translateFuel graph fuel ownerMap bodyIndex = .ok rawB) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index =
      .ok (.bind (CoreTranslation.dummy graph index) rawI rawB) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do pure (Code.bind (CoreTranslation.dummy graph index)
      (← CoreTranslation.translateFuel graph fuel ownerMap initialIndex)
      (← CoreTranslation.translateFuel graph fuel ownerMap bodyIndex))) = _
    rw [initializer, body]
    rfl

private theorem nonrecursiveTranslation (known : graph.node index = some node)
    (kind : node.kind = .recursiveBind [⟨binder, initialIndex⟩] bodyIndex)
    (initializer : CoreTranslation.translateFuel graph fuel ownerMap initialIndex = .ok rawI)
    (notRecursive : rawI.dependencies.contains (.variable binder.id) = false)
    (body : CoreTranslation.translateFuel graph fuel ownerMap bodyIndex = .ok rawB) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.bind binder.id rawI rawB) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do
      let initial ← CoreTranslation.translateFuel graph fuel ownerMap initialIndex
      if initial.dependencies.contains (.variable binder.id) then
        throw (CoreSyntax.Error.recursiveInitializer index binder.id)
      pure (Code.bind binder.id initial (← CoreTranslation.translateFuel graph fuel ownerMap bodyIndex))) = _
    rw [initializer]
    change (do
      if rawI.dependencies.contains (.variable binder.id) then
        throw (CoreSyntax.Error.recursiveInitializer index binder.id)
      pure (Code.bind binder.id rawI (← CoreTranslation.translateFuel graph fuel ownerMap bodyIndex))) = _
    simp only [notRecursive, Bool.false_eq_true, ↓reduceIte]
    change (do pure (Code.bind binder.id rawI (← CoreTranslation.translateFuel graph fuel ownerMap bodyIndex))) = _
    rw [body]
    rfl

/-- Fresh Unit-match bindings cannot shadow any original graph name. -/
theorem dummyFresh (member : name ∈ graph.nodes.flatMap (fun node => node.kind.names)) :
    name ≠ CoreTranslation.dummy graph index := by
  apply Nat.ne_of_lt
  exact Nat.lt_of_lt_of_le (graph.name_lt_freshBase name member) (Nat.le_add_right _ _)

private theorem unitTranslation (known : graph.node index = some node) (kind : node.kind = .unit) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.unit) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    rfl

private theorem booleanTranslation (known : graph.node index = some node) (kind : node.kind = .boolean flag) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.boolean flag) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    rfl

private theorem integerTranslation (known : graph.node index = some node) (kind : node.kind = .integer number) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.integer number) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    rfl

private theorem variableTranslation (known : graph.node index = some node) (kind : node.kind = .variable name) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.variable name) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    rfl

private theorem lambdaTranslation (known : graph.node index = some node) (kind : node.kind = .function binder bodyIndex)
    (body : CoreTranslation.translateFuel graph fuel ownerMap bodyIndex = .ok raw) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok ( .lambda binder.id raw) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do pure (Code.lambda binder.id (← CoreTranslation.translateFuel graph fuel ownerMap bodyIndex))) = _
    rw [body]
    rfl

private theorem appTranslation (known : graph.node index = some node) (kind : node.kind = .apply functionIndex argumentIndex)
    (function : CoreTranslation.translateFuel graph fuel ownerMap functionIndex = .ok rawF)
    (argument : CoreTranslation.translateFuel graph fuel ownerMap argumentIndex = .ok rawA) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.app rawF rawA) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do pure (Code.app (← CoreTranslation.translateFuel graph fuel ownerMap functionIndex) (← CoreTranslation.translateFuel graph fuel ownerMap argumentIndex))) = _
    rw [function, argument]
    rfl

private theorem bindTranslation (known : graph.node index = some node) (kind : node.kind = .bind binder initialIndex bodyIndex)
    (initializer : CoreTranslation.translateFuel graph fuel ownerMap initialIndex = .ok rawI)
    (body : CoreTranslation.translateFuel graph fuel ownerMap bodyIndex = .ok rawB) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.bind binder.id rawI rawB) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do pure (Code.bind binder.id (← CoreTranslation.translateFuel graph fuel ownerMap initialIndex) (← CoreTranslation.translateFuel graph fuel ownerMap bodyIndex))) = _
    rw [initializer, body]
    rfl

private theorem performTranslation (known : graph.node index = some node) (kind : node.kind = .request rawEffect operation operandIndex)
    (operand : CoreTranslation.translateFuel graph fuel ownerMap operandIndex = .ok raw) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.perform rawEffect operation raw) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do pure (Code.perform rawEffect operation (← CoreTranslation.translateFuel graph fuel ownerMap operandIndex))) = _
    rw [operand]
    rfl

private theorem resumeTranslation (known : graph.node index = some node)
    (kind : node.kind = .resume handler coreOwner .consumed operandIndex)
    (mapped : CoreTranslation.resolveOwner ownerMap index handler coreOwner = .ok binder)
    (operand : CoreTranslation.translateFuel graph fuel ownerMap operandIndex = .ok raw) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.resume binder raw) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do pure (Code.resume (← CoreTranslation.resolveOwner ownerMap index handler coreOwner)
      (← CoreTranslation.translateFuel graph fuel ownerMap operandIndex))) = _
    rw [mapped, operand]
    rfl

private theorem discardTranslation (known : graph.node index = some node)
    (kind : node.kind = .discard handler coreOwner .consumed)
    (mapped : CoreTranslation.resolveOwner ownerMap index handler coreOwner = .ok binder) :
    CoreTranslation.translateFuel graph (fuel + 1) ownerMap index = .ok (.discard binder) := by
  cases node with
  | mk original type effects span nodeKind =>
    cases kind
    simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
    change (do pure (Code.discard (← CoreTranslation.resolveOwner ownerMap index handler coreOwner))) = _
    rw [mapped]
    rfl

/-- Translation uses the actual indexed lexical owner map. -/
theorem Checked.translation
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
      fuel index code value demand requirements plan valueRows rows effects) :
    ∃ raw, CoreTranslation.translateFuel graph fuel ownerMap index = .ok raw ∧ raw.instantiate resources = code := by
  induction checked using Checked.rec
    (motive_2 := fun resources contracts owners world ownerMap allowed environment environmentRows fuel handler coreOwner bodyIndex parameter binder argument argumentRows input inputRows answer answerRows resumeEffects closeEffects code held disposes row family plans rows checked => True)
    (motive_3 := fun resources contracts owners world ownerMap allowed environment environmentRows fuel handler effect answer answerRows core clauses table families plans rows checked =>
      ∀ index, ∃ entries, translateClauseList graph fuel ownerMap handler index core = .ok entries ∧
        (packClauses entries).instantiate resources = clauses) with
  | unit known kind => exact ⟨_, unitTranslation known kind, rfl⟩
  | boolean known kind => exact ⟨_, booleanTranslation known kind, rfl⟩
  | integer known kind => exact ⟨_, integerTranslation known kind, rfl⟩
  | «variable» known kind => exact ⟨_, variableTranslation known kind, rfl⟩
  | lambda known kind inputType body bodyBound outward captured formed latentBound metadata ih =>
      obtain ⟨raw, translated, instantiated⟩ := ih
      refine ⟨_, lambdaTranslation known kind translated, ?_⟩
      simp [Code.instantiate, instantiated]
  | app known kind function argument admitted metadata ihF ihA =>
      obtain ⟨rawF, translatedF, instantiatedF⟩ := ihF
      obtain ⟨rawA, translatedA, instantiatedA⟩ := ihA
      refine ⟨_, appTranslation known kind translatedF translatedA, ?_⟩
      simp [Code.instantiate, instantiatedF, instantiatedA]
  | bind known kind inputType initializer body metadata ihI ihB =>
      obtain ⟨rawI, translatedI, instantiatedI⟩ := ihI
      obtain ⟨rawB, translatedB, instantiatedB⟩ := ihB
      refine ⟨_, bindTranslation known kind translatedI translatedB, ?_⟩
      simp [Code.instantiate, instantiatedI, instantiatedB]
  | pair known kind left right metadata ihL ihR =>
      obtain ⟨rawL, translatedL, instantiatedL⟩ := ihL
      obtain ⟨rawR, translatedR, instantiatedR⟩ := ihR
      refine ⟨_, pairTranslation known kind translatedL translatedR, ?_⟩
      simp [Code.instantiate, instantiatedL, instantiatedR]
  | branch known kind condition yes no same metadata ihC ihY ihN =>
      obtain ⟨rawC, translatedC, instantiatedC⟩ := ihC
      obtain ⟨rawY, translatedY, instantiatedY⟩ := ihY
      obtain ⟨rawN, translatedN, instantiatedN⟩ := ihN
      refine ⟨_, branchTranslation known kind translatedC translatedY translatedN, ?_⟩
      simp [Code.instantiate, instantiatedC, instantiatedY, instantiatedN]
  | unitMatch known kind initializer body metadata ihI ihB =>
      obtain ⟨rawI, translatedI, instantiatedI⟩ := ihI
      obtain ⟨rawB, translatedB, instantiatedB⟩ := ihB
      refine ⟨_, unitMatchTranslation known kind translatedI translatedB, ?_⟩
      simp [Code.instantiate, instantiatedI, instantiatedB]
  | nonrecursive known kind functionShape inputType initializer rawTranslated notRecursive body metadata ihI ihB =>
      obtain ⟨rawI, translatedI, instantiatedI⟩ := ihI
      obtain ⟨rawB, translatedB, instantiatedB⟩ := ihB
      have same := Except.ok.inj (translatedI.symm.trans rawTranslated)
      subst rawI
      refine ⟨_, nonrecursiveTranslation known kind translatedI notRecursive translatedB, ?_⟩
      simp [Code.instantiate, instantiatedI, instantiatedB]
  | perform known kind instantiated operationType operand admitted formed metadata ih =>
      obtain ⟨raw, translated, instantiatedOperand⟩ := ih
      refine ⟨_, performTranslation known kind translated, ?_⟩
      simp [Code.instantiate, instantiated, instantiatedOperand]
  | resume known kind mapped contractKnown resolved permission operand admitted formed metadata ih =>
      obtain ⟨raw, translated, instantiated⟩ := ih
      refine ⟨_, resumeTranslation known kind mapped translated, ?_⟩
      simp [Code.instantiate, instantiated]
  | discard known kind mapped => exact ⟨_, discardTranslation known kind mapped, rfl⟩

  | cleanup known kind actionShape callbackType callback action body admitted metadata _ihCallback _ihAction ihBody =>
      obtain ⟨raw, translated, instantiated⟩ := ihBody
      refine ⟨_, cleanupTranslation known kind actionShape translated, ?_⟩
      simp [Code.instantiate, instantiated]

  | handler known kind instantiated shapes body declarations coverage unique admitted effectsAdmitted metadata ihBody ihDecl =>
      obtain ⟨rawBody, translatedBody, instantiatedBody⟩ := ihBody
      obtain ⟨entries, translatedDecl, instantiatedDecl⟩ := ihDecl _
      refine ⟨_, handlerTranslation known kind shapes translatedBody translatedDecl, ?_⟩
      simp [Code.instantiate, instantiated, instantiatedBody, instantiatedDecl]
  | unavailable | available => trivial
  | nil _index => exact ⟨[], rfl, rfl⟩
  | cons operationKnown argumentType distinct mapped witnessFresh witnessInput witnessAnswer witnessResume witnessClose witnessHeld
      portBody disposeMode usage ordinary protectedMode rest support ihPort ihOrdinary ihProtected ihRest index =>
      rename_i effect operation argument input coreOwner binder witness answer allowed witnessContract answerRows handler fuel bodyIndex code portDemand portReq portDeps portPlan portRows bodyEffects disposes usageFuel environment environmentRows resumeEffects closeEffects ordinaryRow ordinaryFamily ordinaryPlan ordinaryRows protectedRow protectedFamily protectedPlan protectedRows restCore restClauses restTable restFamilies restPlan restRows supportBound parameter resources contracts owners world ownerMap
      obtain ⟨rawBody, translatedBody, instantiatedBody⟩ := ihPort
      obtain ⟨entries, translatedRest, instantiatedRest⟩ := ihRest index
      refine ⟨(operation, parameter.id, binder, rawBody) :: entries, ?_, ?_⟩
      · simp only [translateClauseList, List.mapM_cons, distinct, Bool.false_eq_true, if_false]
        rw [← mapped, translatedBody]
        change (do let tail ← translateClauseList graph _ _ _ index _; pure (_ :: tail)) = _
        rw [translatedRest]
        rfl
      · simp [packClauses, Clauses.instantiate, instantiatedBody, ← instantiatedRest]


/-- A syntactic restriction for the owner-map-independent ordinary subset.
Owner-bearing terms are handled by the indexed translation theorem instead. -/
def ticketFree : Code → Bool
  | .unit | .boolean _ | .integer _ | .variable _ | .resourceRef _ => true
  | .lambda _ body | .perform _ _ body => ticketFree body
  | .pair left right | .app left right | .bind _ left right => ticketFree left && ticketFree right
  | .branch condition yes no => ticketFree condition && ticketFree yes && ticketFree no
  | .resume _ _ | .discard _ | .handle _ _ _ | .resource _ _ _ | .cleanup _ _ => false

theorem Checked.ticketFreeSyntax
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
      fuel index code value demand requirements plan valueRows rows effects)
    (free : ticketFree code = true) :
    ∃ raw, (∀ otherMap, CoreTranslation.translateFuel graph fuel otherMap index = .ok raw) ∧
      raw.instantiate resources = code := by
  revert free
  induction checked using Checked.rec
    (motive_2 := fun resources contracts owners world ownerMap allowed environment environmentRows fuel handler coreOwner bodyIndex parameter binder argument argumentRows input inputRows answer answerRows resumeEffects closeEffects code held disposes row family plans rows checked => True)
    (motive_3 := fun resources contracts owners world ownerMap allowed environment environmentRows fuel handler effect answer answerRows core clauses table families plans rows checked => True) with
  | unit known kind => intro free; exact ⟨_, fun otherMap => unitTranslation known kind, rfl⟩
  | boolean known kind => intro free; exact ⟨_, fun otherMap => booleanTranslation known kind, rfl⟩
  | integer known kind => intro free; exact ⟨_, fun otherMap => integerTranslation known kind, rfl⟩
  | «variable» known kind => intro free; exact ⟨_, fun otherMap => variableTranslation known kind, rfl⟩
  | lambda known kind inputType body bodyBound outward captured formed latentBound metadata ih =>
      intro free
      obtain ⟨raw, translated, instantiated⟩ := ih free
      refine ⟨_, fun otherMap => lambdaTranslation known kind (translated otherMap), ?_⟩
      simp [Code.instantiate, instantiated]
  | app known kind function argument admitted metadata ihF ihA =>
      intro free
      simp only [ticketFree, Bool.and_eq_true] at free
      obtain ⟨rawF, translatedF, instantiatedF⟩ := ihF free.1
      obtain ⟨rawA, translatedA, instantiatedA⟩ := ihA free.2
      refine ⟨_, fun otherMap => appTranslation known kind (translatedF otherMap) (translatedA otherMap), ?_⟩
      simp [Code.instantiate, instantiatedF, instantiatedA]
  | bind known kind inputType initializer body metadata ihI ihB =>
      intro free
      simp only [ticketFree, Bool.and_eq_true] at free
      obtain ⟨rawI, translatedI, instantiatedI⟩ := ihI free.1
      obtain ⟨rawB, translatedB, instantiatedB⟩ := ihB free.2
      refine ⟨_, fun otherMap => bindTranslation known kind (translatedI otherMap) (translatedB otherMap), ?_⟩
      simp [Code.instantiate, instantiatedI, instantiatedB]
  | pair known kind left right metadata ihL ihR =>
      intro free
      simp only [ticketFree, Bool.and_eq_true] at free
      obtain ⟨rawL, translatedL, instantiatedL⟩ := ihL free.1
      obtain ⟨rawR, translatedR, instantiatedR⟩ := ihR free.2
      refine ⟨_, fun otherMap => pairTranslation known kind (translatedL otherMap) (translatedR otherMap), ?_⟩
      simp [Code.instantiate, instantiatedL, instantiatedR]
  | branch known kind condition yes no same metadata ihC ihY ihN =>
      intro free
      simp only [ticketFree, Bool.and_eq_true] at free
      obtain ⟨rawC, translatedC, instantiatedC⟩ := ihC free.1.1
      obtain ⟨rawY, translatedY, instantiatedY⟩ := ihY free.1.2
      obtain ⟨rawN, translatedN, instantiatedN⟩ := ihN free.2
      refine ⟨_, fun otherMap => branchTranslation known kind (translatedC otherMap) (translatedY otherMap) (translatedN otherMap), ?_⟩
      simp [Code.instantiate, instantiatedC, instantiatedY, instantiatedN]
  | unitMatch known kind initializer body metadata ihI ihB =>
      intro free
      simp only [ticketFree, Bool.and_eq_true] at free
      obtain ⟨rawI, translatedI, instantiatedI⟩ := ihI free.1
      obtain ⟨rawB, translatedB, instantiatedB⟩ := ihB free.2
      refine ⟨_, fun otherMap => unitMatchTranslation known kind (translatedI otherMap) (translatedB otherMap), ?_⟩
      simp [Code.instantiate, instantiatedI, instantiatedB]
  | nonrecursive known kind functionShape inputType initializer rawTranslated notRecursive body metadata ihI ihB =>
      intro free
      simp only [ticketFree, Bool.and_eq_true] at free
      obtain ⟨rawI, translatedI, instantiatedI⟩ := ihI free.1
      obtain ⟨rawB, translatedB, instantiatedB⟩ := ihB free.2
      have same := Except.ok.inj ((translatedI _).symm.trans rawTranslated)
      subst rawI
      refine ⟨_, fun otherMap => nonrecursiveTranslation known kind (translatedI otherMap) notRecursive (translatedB otherMap), ?_⟩
      simp [Code.instantiate, instantiatedI, instantiatedB]
  | perform known kind instantiated operationType operand admitted formed metadata ih =>
      intro free
      obtain ⟨raw, translated, instantiatedOperand⟩ := ih free
      refine ⟨_, fun otherMap => performTranslation known kind (translated otherMap), ?_⟩
      simp [Code.instantiate, instantiated, instantiatedOperand]
  | resume => intro free; cases free
  | discard => intro free; cases free
  | cleanup => intro free; cases free
  | handler => intro free; cases free

  | unavailable | available | nil | cons => trivial

/-- A compiled fragment is tied to the raw graph translation as well as its
resource-instantiated source. No target derivation is supplied by the caller. -/
theorem Checked.compiled
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
      fuel index code value demand requirements plan valueRows rows effects)
    : ∃ raw, CoreTranslation.translateFuel graph fuel ownerMap index = .ok raw ∧
      raw.instantiate resources = code ∧
      ∃ source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
        code value demand requirements (signature plan),
        Auth operations policy ports owners environmentRows source valueRows rows := by
  obtain ⟨raw, translated, instantiated⟩ := checked.translation
  exact ⟨raw, translated, instantiated, checked.sourceAuth⟩

/-- Exact preservation of an empty declared callable row leaves no resource
support in the existing combined callable request allowance. -/
theorem emptyAllowance (same : EffectsSame [] (allowanceEffects requests)) : requests = [] := by
  cases requests with
  | nil => rfl
  | cons head tail =>
      have impossible := (same (Instantiation.freezeEffect head)).mpr (List.mem_cons_self)
      cases impossible

/-- The D4 support example cannot simultaneously keep its exact Core callable
allowance and satisfy the current target capture guard. This boundary remains
explicit, especially for higher-order operation inputs with fixed ports. -/
theorem retainedSupportBoundary :
    ¬ (TypeAgreement resources (.function .unit .unit [])
        (.function .unit .unit requests [] (signature CoreCallableSupport.bodyPlan)) ∧
      LambdaPortCaptureSupport.captures environment 2 (CoreCallableSupport.body identity) .unit .unit requests) := by
  rintro ⟨typed, capture⟩
  cases typed with
  | function input output same latentBound =>
      have empty := emptyAllowance same
      subst requests
      exact CoreCallableSupport.empty_allowance_does_not_supply_capture_guard identity capture

namespace Getter
open CoreInitialExample CoreExportedAdmission CoreKernelProgram

def resources (identity : Nat) := Instantiation.Environment.empty.bind 0 identity
private def node (index : Nat) : Node :=
  (CoreExportedFixture.graph.node index).getD ⟨0, .unit, [], none, .unit⟩

variable {world : List Nat} {environment : Environment} {environmentRows : EnvironmentRows environment}

/-- The original getter annotation has exactly the instantiated declared read
allowance, while its actual operation/footprint is separately retained. -/
theorem getterType : TypeAgreement (resources identity) (node 4).type (getterValue identity) :=
  .function (.reference rfl) .integer (by intro effect; rfl)
    (by intro request member; simp only [getterFootprint, List.mem_singleton] at member; subst request; exact List.mem_cons_self)

theorem bodyChecked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (resources identity) contracts owners world ownerMap
      [.cell identity] .none ((savedEnvironment identity environment).extend 1 (.reference identity))
      ((environmentRows.extend 4 .reference).extend 1 .reference)
      (fuel + 2) 3 (getterBody identity) .integer [] (readRequirements identity)
      (readPlan identity) .integer (operationRows identity 0) [Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.perform (graph := CoreExportedFixture.graph) (resources := resources identity)
    (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
    (fuel := fuel + 1) (operandPlan := Plan.pure) (operandRows := Rows.pure) (operandEffects := [])
    (node := node 3) (rawEffect := .cell (.bound 0)) (operandIndex := 2)
    (known := rfl) (kind := rfl) (instantiated := rfl)
    (operationType := (rfl : operations (.cell identity) 0 = some (.reference identity, .integer)))
    (admitted := List.mem_cons_self) (formed := List.nil_subset _)
  · change Checked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ .reference _ _
    simpa [EnvironmentRows.extend, savedEnvironment] using
      (Checked.variable (graph := CoreExportedFixture.graph) (resources := resources identity)
        (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
        (world := world) (environmentRows := (environmentRows.extend 4 .reference).extend 1 .reference)
        (fuel := fuel) (node := node 2) (index := 2) (known := rfl) (kind := rfl)
        (binding := (by simp [Environment.extend] :
          ((savedEnvironment identity environment).extend 1 (.reference identity)) 1 = some (.reference identity)))
        (formed := referenceFormed issued)
        (metadata := ⟨.reference rfl, by intro effect; rfl⟩))
  · exact ⟨.integer, by intro effect; rfl⟩

theorem checked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (resources identity) contracts owners world ownerMap
      allowed .none (savedEnvironment identity environment) (environmentRows.extend 4 .reference)
      (fuel + 3) 4 (getter identity) (getterValue identity) [] empty .pure (getterValueRows identity) .pure [] := by
  apply Checked.lambda (node := node 4) (binder := ⟨1, .reference (.bound 0)⟩) (bodyIndex := 3)
    (known := rfl) (kind := rfl) (inputType := .reference rfl)
    (body := bodyChecked issued) (bodyBound := List.Subset.refl _) (outward := getterOutward)
    (formed := getterFormed issued)
    (latentBound := by intro request member; simp only [getterFootprint, List.mem_singleton] at member; subst request; exact List.mem_cons_self)
  · apply CoreCallableSupport.capture_guard_from_cell_support (resources := [identity])
    simp [getterBody, Code.dependencies, Instantiation.freezeEffect,
      effectAtoms, Instantiation.Effect.resources, Syntax.without, ScopedPorts.Support.evaluate]
  · exact ⟨getterType, by intro effect; rfl⟩

theorem applicationChecked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (resources identity) contracts owners world ownerMap
      [.cell identity] .none (applicationEnvironment identity environment)
      (applicationEnvironmentRows identity environmentRows)
      (fuel + 2) 44 getterApplication .integer [] (applicationRequirements identity)
      (applicationPlan identity) .integer (applicationRows identity) [Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.app (graph := CoreExportedFixture.graph) (resources := resources identity)
    (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
    (world := world) (allowed := [.cell identity]) (scope := .none)
    (environmentRows := applicationEnvironmentRows identity environmentRows) (fuel := fuel + 1)
    (input := .reference identity) (output := .integer) (requests := [.cell identity])
    (latent := getterFootprint identity) (inputRows := .reference) (outputRows := .integer)
    (functionDemand := []) (argumentDemand := []) (functionReq := empty) (argumentReq := empty)
    (node := node 44) (functionIndex := 42) (argumentIndex := 43) (known := rfl) (kind := rfl)
    (bodyPlan := readPlan identity) (bodyRows := operationRows identity 0)
    (functionPlan := Plan.pure) (argumentPlan := Plan.pure) (functionRows := Rows.pure) (argumentRows := Rows.pure)
    (functionEffects := []) (argumentEffects := []) (admitted := List.Subset.refl _)
  · simpa [applicationEnvironmentRows, EnvironmentRows.extend, getterValue, getterValueRows] using
      (Checked.variable (graph := CoreExportedFixture.graph) (resources := resources identity)
        (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
        (world := world) (environmentRows := applicationEnvironmentRows identity environmentRows)
        (fuel := fuel) (node := node 42) (index := 42) (known := rfl) (kind := rfl)
        (binding := (by simp [applicationEnvironment, Environment.extend] :
          applicationEnvironment identity environment 11 = some (getterValue identity)))
        (formed := getterFormed issued) (metadata := ⟨getterType, by intro effect; rfl⟩))
  · simpa [applicationEnvironmentRows, EnvironmentRows.extend, getterValue, getterValueRows] using
      (Checked.variable (graph := CoreExportedFixture.graph) (resources := resources identity)
        (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
        (world := world) (environmentRows := applicationEnvironmentRows identity environmentRows)
        (fuel := fuel) (node := node 43) (index := 43) (known := rfl) (kind := rfl)
        (binding := (by simp [applicationEnvironment, savedEnvironment, Environment.extend] :
          applicationEnvironment identity environment 4 = some (.reference identity)))
        (formed := referenceFormed issued) (metadata := ⟨.reference rfl, by intro effect; rfl⟩))
  · exact ⟨.integer, by intro effect; rfl⟩

/-- The actual exported getter binding can be compiled around any separately
checked continuation at its actual child index. The continuation input is a
Core static derivation, never a target admission or future-validity judgment. -/
theorem bindingChecked (issued : identity ∈ world)
    (body : Checked CoreExportedFixture.graph operations policy ports (resources identity) contracts owners world ownerMap
      allowed .none (applicationEnvironment identity environment) (applicationEnvironmentRows identity environmentRows)
      (fuel + 3) 46 code output bodyDemand bodyReq bodyPlan outputRows bodyRows bodyEffects)
    (metadata : Metadata (resources identity) (node 47) output bodyEffects) :
    Checked CoreExportedFixture.graph operations policy ports (resources identity) contracts owners world ownerMap
      allowed .none (savedEnvironment identity environment) (environmentRows.extend 4 .reference)
      (fuel + 4) 47 (.bind 11 (getter identity) code) output bodyDemand (.sequence empty bodyReq)
      (.sequence .pure bodyPlan) outputRows
      (by simpa only [signature] using Rows.sequence Rows.pure bodyRows) bodyEffects := by
  exact Checked.bind (node := node 47) (binder := ⟨11, (node 4).type⟩)
    (initialIndex := 4) (bodyIndex := 46) (known := rfl) (kind := rfl)
    getterType (checked issued) body metadata

end Getter

namespace Setter
open CoreInitialExample CoreExportedAdmission CoreKernelProgram

def body (identity : Nat) : Code := .perform (Instantiation.freezeEffect (.cell identity)) 1 (.variable 2)
def closure (identity : Nat) : Code := .lambda 2 (body identity)
def input (identity : Nat) : Value := .pair (.reference identity) .integer
def footprint (identity : Nat) : Footprint := [⟨.cell identity, 1, false⟩]
def value (identity : Nat) : Value :=
  .function (input identity) .unit [.cell identity] (footprint identity) (signature (writePlan identity))
def valueRows (identity : Nat) : ValueRows (value identity) :=
  .function (.pair .reference .integer) .unit (operationRows identity 1)
private def node (index : Nat) : Node :=
  (CoreExportedFixture.graph.node index).getD ⟨0, .unit, [], none, .unit⟩
variable {world : List Nat} {environment : Environment} {environmentRows : EnvironmentRows environment}

theorem inputFormed (issued : identity ∈ world) : ScopedPorts.InWorld world (input identity).erase.erase.port := by
  intro resource member
  simp [input, Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port,
    ScopedPorts.Port.resources] at member
  subst resource
  exact issued

theorem formed (issued : identity ∈ world) : ScopedPorts.InWorld world (value identity).erase.erase.port := by
  intro resource member
  simp [value, input, Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port,
    ScopedPorts.Port.resources, Instance.resources] at member
  subst resource
  exact issued

theorem type : TypeAgreement (Getter.resources identity) (node 7).type (value identity) :=
  .function (.product (.reference rfl) .integer) .unit (by intro effect; rfl)
    (by intro request member; simp only [footprint, List.mem_singleton] at member; subst request; exact List.mem_cons_self)

theorem bodyChecked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none (environment.extend 2 (input identity)) (environmentRows.extend 2 (.pair .reference .integer))
      (fuel + 2) 6 (body identity) .unit [] (writeRequirements identity)
      (writePlan identity) .unit (operationRows identity 1) [Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.perform (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
    (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
    (fuel := fuel + 1) (operandPlan := Plan.pure) (operandRows := Rows.pure) (operandEffects := [])
    (node := node 6) (rawEffect := .cell (.bound 0)) (operandIndex := 5)
    (known := rfl) (kind := rfl) (instantiated := rfl)
    (operationType := (rfl : operations (.cell identity) 1 = some (input identity, .unit)))
    (admitted := List.mem_cons_self) (formed := List.nil_subset _)
  · change Checked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.pair .reference .integer) _ _
    simpa [EnvironmentRows.extend, input] using
      (Checked.variable (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
        (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
        (world := world) (environmentRows := environmentRows.extend 2 (.pair .reference .integer))
        (fuel := fuel) (node := node 5) (index := 5) (known := rfl) (kind := rfl)
        (binding := (by simp [Environment.extend] : (environment.extend 2 (input identity)) 2 = some (input identity)))
        (formed := inputFormed issued) (metadata := ⟨.product (.reference rfl) .integer, by intro effect; rfl⟩))
  · exact ⟨.unit, by intro effect; rfl⟩

theorem checked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      allowed .none environment environmentRows (fuel + 3) 7 (closure identity) (value identity)
      [] empty .pure (valueRows identity) .pure [] := by
  apply Checked.lambda (node := node 7) (binder := ⟨2, (node 5).type⟩) (bodyIndex := 6)
    (known := rfl) (kind := rfl) (inputType := .product (.reference rfl) .integer)
    (body := bodyChecked issued) (bodyBound := List.Subset.refl _) (latent := footprint identity)
    (outward := .emitAfter (layers := []) (raw := footprint identity) (.request (layers := []) (raw := [])))
    (formed := formed issued)
    (latentBound := by intro request member; simp only [footprint, List.mem_singleton] at member; subst request; exact List.mem_cons_self)
  · apply CoreCallableSupport.capture_guard_from_cell_support (resources := [identity])
    simp [body, Code.dependencies, Instantiation.freezeEffect, effectAtoms,
      Instantiation.Effect.resources, Syntax.without, ScopedPorts.Support.evaluate]
  · exact ⟨type, by intro effect; rfl⟩

end Setter

namespace Writes
open CoreInitialExample CoreExportedAdmission CoreKernelProgram

inductive Site where | callback | skipped | suffix
  deriving DecidableEq

def Site.functionIndex : Site → Nat | .callback => 8 | .skipped => 18 | .suffix => 33
def Site.leftIndex : Site → Nat | .callback => 9 | .skipped => 19 | .suffix => 34
def Site.rightIndex : Site → Nat | .callback => 10 | .skipped => 20 | .suffix => 35
def Site.tupleIndex : Site → Nat | .callback => 11 | .skipped => 21 | .suffix => 36
def Site.applicationIndex : Site → Nat | .callback => 12 | .skipped => 22 | .suffix => 37
def Site.number : Site → Int | .callback => 7 | .skipped => 99 | .suffix => 11
private def node (index : Nat) : Node :=
  (CoreExportedFixture.graph.node index).getD ⟨0, .unit, [], none, .unit⟩

def storeEnvironment (identity : Nat) (base : Environment) :=
  (applicationEnvironment identity base).extend 3 (Setter.value identity)
def storeEnvironmentRows (identity : Nat) (base : EnvironmentRows environment) :
    EnvironmentRows (storeEnvironment identity environment) :=
  (applicationEnvironmentRows identity base).extend 3 (Setter.valueRows identity)
def argument (site : Site) : Code := .pair (.variable 4) (.integer site.number)
def application (site : Site) : Code := .app (.variable 3) (argument site)
def tuplePlan := Plan.sequence Plan.pure Plan.pure
def tupleRequirements : Requirements [] := .sequence empty empty
def tupleRows : Rows (signature tuplePlan) := .sequence .pure .pure
def plan (identity : Nat) := Plan.sequence Plan.pure (Plan.sequence tuplePlan (writePlan identity))
def requirements (identity : Nat) : Requirements [] :=
  .emitAfter (.sequence empty tupleRequirements) [] (Setter.footprint identity)
def rows (identity : Nat) : Rows (signature (plan identity)) :=
  .sequence .pure (.sequence tupleRows (operationRows identity 1))

variable {world : List Nat} {environment : Environment} {environmentRows : EnvironmentRows environment}

/-- Exact lexical values and rows for an existing resource/setter pair. -/
structure WriteBindings (identity : Nat) (environment : Environment) (rows : EnvironmentRows environment) : Prop where
  reference : environment 4 = some (.reference identity)
  setter : environment 3 = some (Setter.value identity)
  referenceRows : rows 4 (.reference identity) reference = .reference
  setterRows : rows 3 (Setter.value identity) setter = Setter.valueRows identity

variable {scope : Execution.Scope}

/-- An unrelated ordinary binding preserves the exact resource/helper rows. -/
theorem WriteBindings.extend (bindings : WriteBindings identity environment environmentRows)
    (referenceFresh : name ≠ 4) (setterFresh : name ≠ 3) (valueRows : ValueRows value) :
    WriteBindings identity (environment.extend name value) (environmentRows.extend name valueRows) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Environment.extend, Ne.symm referenceFresh] using bindings.reference
  · simpa [Environment.extend, Ne.symm setterFresh] using bindings.setter
  · simpa [EnvironmentRows.extend, Ne.symm referenceFresh] using bindings.referenceRows
  · simpa [EnvironmentRows.extend, Ne.symm setterFresh] using bindings.setterRows

theorem storeBindings : WriteBindings identity (storeEnvironment identity environment)
    (storeEnvironmentRows identity environmentRows) :=
  ⟨by simp [storeEnvironment, applicationEnvironment, savedEnvironment, Environment.extend],
   by simp [storeEnvironment, Environment.extend],
   by simp [storeEnvironmentRows, applicationEnvironmentRows, EnvironmentRows.extend],
   by simp [storeEnvironmentRows, EnvironmentRows.extend]⟩

theorem functionChecked (site : Site) (issued : identity ∈ world) (bindings : WriteBindings identity environment environmentRows) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      allowed scope environment environmentRows
      (fuel + 1) site.functionIndex (.variable 3) (Setter.value identity) [] empty .pure (Setter.valueRows identity) .pure [] := by
  simpa only [bindings.setterRows] using
    (Checked.variable (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
      (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
      (world := world) (environmentRows := environmentRows)
      (fuel := fuel) (node := node site.functionIndex) (index := site.functionIndex)
      (known := by cases site <;> rfl) (kind := by cases site <;> rfl)
      (binding := bindings.setter)
      (formed := Setter.formed issued)
      (metadata := ⟨by cases site <;> exact Setter.type, by intro effect; cases site <;> rfl⟩))

theorem argumentChecked (site : Site) (issued : identity ∈ world) (bindings : WriteBindings identity environment environmentRows) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      allowed scope environment environmentRows
      (fuel + 2) site.tupleIndex (argument site) (Setter.input identity) [] tupleRequirements tuplePlan
      (.pair .reference .integer) tupleRows [] := by
  unfold argument Setter.input tupleRequirements tuplePlan tupleRows
  apply Checked.pair (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
    (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
    (world := world) (environmentRows := environmentRows) (fuel := fuel + 1)
    (first := .reference identity) (second := .integer) (firstRows := .reference) (secondRows := .integer)
    (leftDemand := []) (rightDemand := []) (leftReq := empty) (rightReq := empty)
    (leftPlan := Plan.pure) (rightPlan := Plan.pure) (leftRows := Rows.pure) (rightRows := Rows.pure)
    (leftEffects := []) (rightEffects := []) (node := node site.tupleIndex)
    (leftIndex := site.leftIndex) (rightIndex := site.rightIndex)
    (known := by cases site <;> rfl) (kind := by cases site <;> rfl)
  · simpa only [bindings.referenceRows] using
      (Checked.variable (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
        (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
        (world := world) (environmentRows := environmentRows)
        (fuel := fuel) (node := node site.leftIndex) (index := site.leftIndex)
        (known := by cases site <;> rfl) (kind := by cases site <;> rfl)
        (binding := bindings.reference)
        (formed := referenceFormed issued) (metadata := ⟨by cases site <;> exact .reference rfl, by intro effect; cases site <;> rfl⟩))
  · exact Checked.integer (node := node site.rightIndex) (known := by cases site <;> rfl)
      (kind := by cases site <;> rfl) ⟨by cases site <;> exact .integer, by intro effect; cases site <;> rfl⟩
  · exact ⟨by cases site <;> exact .product (.reference rfl) .integer, by intro effect; cases site <;> rfl⟩

theorem checkedAllowed (site : Site) (issued : identity ∈ world) (bindings : WriteBindings identity environment environmentRows)
    (admitted : .cell identity ∈ allowed) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      allowed scope environment environmentRows
      (fuel + 3) site.applicationIndex (application site) .unit [] (requirements identity) (plan identity)
      .unit (rows identity) [Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.app (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
    (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
    (world := world) (allowed := allowed) (scope := scope)
    (environmentRows := environmentRows) (fuel := fuel + 2)
    (input := Setter.input identity) (output := .unit) (requests := [.cell identity])
    (latent := Setter.footprint identity) (inputRows := .pair .reference .integer) (outputRows := .unit)
    (bodyPlan := writePlan identity) (bodyRows := operationRows identity 1)
    (functionDemand := []) (argumentDemand := []) (functionReq := empty) (argumentReq := tupleRequirements)
    (functionPlan := Plan.pure) (argumentPlan := tuplePlan) (functionRows := Rows.pure) (argumentRows := tupleRows)
    (functionEffects := []) (argumentEffects := []) (node := node site.applicationIndex)
    (functionIndex := site.functionIndex) (argumentIndex := site.tupleIndex)
    (known := by cases site <;> rfl) (kind := by cases site <;> rfl)
    (admitted := by intro effect member; simp only [List.mem_singleton] at member; subst effect; exact admitted)
  · simpa [Setter.value, Setter.valueRows] using (functionChecked (fuel := fuel + 1) site issued bindings)
  · exact argumentChecked site issued bindings
  · exact ⟨by cases site <;> exact .unit, by intro effect; cases site <;> rfl⟩


theorem checked (site : Site) (issued : identity ∈ world) (bindings : WriteBindings identity environment environmentRows) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] scope environment environmentRows
      (fuel + 3) site.applicationIndex (application site) .unit [] (requirements identity) (plan identity)
      .unit (rows identity) [Instantiation.freezeEffect (.cell identity)] :=
  checkedAllowed site issued bindings List.mem_cons_self

end Writes

namespace Callback
open CoreInitialExample CoreExportedAdmission CoreKernelProgram
private def node (index : Nat) : Node :=
  (CoreExportedFixture.graph.node index).getD ⟨0, .unit, [], none, .unit⟩
def code := Code.lambda 5 (Writes.application .callback)
def value (identity : Nat) := Value.function .unit .unit [.cell identity] (Setter.footprint identity) (signature (Writes.plan identity))
def valueRows (identity : Nat) : ValueRows (value identity) := .function .unit .unit (Writes.rows identity)
variable {world : List Nat} {base : Environment} {baseRows : EnvironmentRows base}
theorem bindings : Writes.WriteBindings identity ((Writes.storeEnvironment identity base).extend 5 .unit)
    ((Writes.storeEnvironmentRows identity baseRows).extend 5 .unit) :=
  ⟨by simp [Writes.storeEnvironment, applicationEnvironment, savedEnvironment, Environment.extend],
   by simp [Writes.storeEnvironment, Environment.extend],
   by simp [Writes.storeEnvironmentRows, applicationEnvironmentRows, EnvironmentRows.extend],
   by simp [Writes.storeEnvironmentRows, EnvironmentRows.extend]⟩

theorem checked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      allowed .none (Writes.storeEnvironment identity base) (Writes.storeEnvironmentRows identity baseRows)
      (fuel + 4) 13 code (value identity) [] empty .pure (valueRows identity) .pure [] := by
  apply Checked.lambda (node := node 13) (binder := ⟨5, .unit⟩) (bodyIndex := 12)
    (known := rfl) (kind := rfl) (inputType := .unit)
    (body := Writes.checked (fuel := fuel) (scope := .none) .callback issued bindings)
    (bodyBound := List.Subset.refl _) (latent := Setter.footprint identity)
    (outward := .emitAfter (layers := []) (raw := Setter.footprint identity)
      (.sequence (.request (layers := []) (raw := []))
        (.sequence (.request (layers := []) (raw := [])) (.request (layers := []) (raw := [])))))
    (latentBound := by intro request member; simp only [Setter.footprint, List.mem_singleton] at member; subst request; exact List.mem_cons_self)
  · apply CoreCallableSupport.capture_guard_from_cell_support (resources := [identity])
    simp [Writes.application, Writes.argument, Code.dependencies, Syntax.without,
      LambdaPortCaptureSupport.portSupport, ScopedPorts.Support.evaluate, Writes.storeEnvironment,
      applicationEnvironment, savedEnvironment, Environment.extend, Setter.value, Setter.input,
      Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port,
      ScopedPorts.Port.resources, Instance.resources]
  · intro resource member
    simp [Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port,
      ScopedPorts.Port.resources, Instance.resources] at member
    subst resource
    exact issued
  · exact ⟨.function .unit .unit (by intro effect; rfl)
      (by intro request member; simp only [Setter.footprint, List.mem_singleton] at member; subst request; exact List.mem_cons_self),
      by intro effect; rfl⟩
end Callback

namespace Requests
open CoreInitialExample
private def node (index : Nat) : Node :=
  (CoreExportedFixture.graph.node index).getD ⟨0, .unit, [], none, .unit⟩
def operandIndex (flag : Bool) := if flag then 14 else 16
def index (flag : Bool) := if flag then 15 else 17
theorem checked (flag : Bool) (admitted : effect ∈ allowed) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      allowed scope environment environmentRows (fuel + 2) (index flag) (request flag) .unit []
      requestRequirements requestPlan .unit (.sequence .pure .request) [Instantiation.freezeEffect effect] := by
  apply Checked.perform (node := node (index flag)) (rawEffect := .user 0 []) (operandIndex := operandIndex flag)
    (known := by cases flag <;> rfl) (kind := by cases flag <;> rfl) (instantiated := rfl)
    (operationType := (rfl : operations effect 0 = some (.boolean, .unit)))
    (admitted := admitted) (formed := List.nil_subset _)
    (operandPlan := Plan.pure) (operandRows := Rows.pure) (operandEffects := [])
  · exact Checked.boolean (node := node (operandIndex flag)) (known := by cases flag <;> rfl)
      (kind := by cases flag <;> rfl) ⟨by cases flag <;> exact .boolean, by intro effect; cases flag <;> rfl⟩
  · exact ⟨by cases flag <;> exact .unit, by intro effect; cases flag <;> rfl⟩
end Requests

namespace Guarded
open CoreInitialExample CoreExportedAdmission CoreKernelProgram
private def node (index : Nat) : Node :=
  (CoreExportedFixture.graph.node index).getD ⟨0, .unit, [], none, .unit⟩
def environment (identity : Nat) (base : Environment) := (Writes.storeEnvironment identity base).extend 8 (Callback.value identity)
def environmentRows (identity : Nat) (base : EnvironmentRows original) : EnvironmentRows (environment identity original) :=
  (Writes.storeEnvironmentRows identity base).extend 8 (Callback.valueRows identity)
variable {world : List Nat} {base : Environment} {baseRows : EnvironmentRows base}
def afterSecond := Code.bind 6 (request false) (Writes.application .skipped)
def afterSecondReq (identity : Nat) : Requirements [] := .sequence requestRequirements (Writes.requirements identity)
def afterSecondPlan (identity : Nat) := Plan.sequence requestPlan (Writes.plan identity)
def afterSecondRows (identity : Nat) : Rows (signature (afterSecondPlan identity)) := .sequence (.sequence .pure .request) (Writes.rows identity)
theorem skippedBindings : Writes.WriteBindings identity ((environment identity base).extend 6 .unit)
    ((environmentRows identity baseRows).extend 6 .unit) :=
  ⟨by simp [environment, Writes.storeEnvironment, applicationEnvironment, savedEnvironment, Environment.extend],
   by simp [environment, Writes.storeEnvironment, Environment.extend],
   by simp [environmentRows, Writes.storeEnvironmentRows, applicationEnvironmentRows, EnvironmentRows.extend],
   by simp [environmentRows, Writes.storeEnvironmentRows, EnvironmentRows.extend]⟩

theorem afterSecondChecked (issued : identity ∈ world)
    (bindings : Writes.WriteBindings identity current currentRows) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [effect, .cell identity] .none current currentRows
      (fuel + 4) 23 afterSecond .unit [] (afterSecondReq identity) (afterSecondPlan identity) .unit (afterSecondRows identity)
      [Instantiation.freezeEffect effect, Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.bind (node := node 23) (binder := ⟨6, .unit⟩) (initialIndex := 17) (bodyIndex := 22)
    (known := rfl) (kind := rfl) .unit
    (Requests.checked (fuel := fuel + 1) false List.mem_cons_self)
    (Writes.checkedAllowed .skipped issued (bindings.extend (by decide) (by decide) ValueRows.unit) (by simp))
  exact ⟨.unit, by intro effect; rfl⟩

def bodyCode := Code.bind 7 (request true) afterSecond
def bodyReq (identity : Nat) : Requirements [] := .sequence requestRequirements (afterSecondReq identity)
def bodyPlan (identity : Nat) := Plan.sequence requestPlan (afterSecondPlan identity)
def bodyRows (identity : Nat) : Rows (signature (bodyPlan identity)) := .sequence (.sequence .pure .request) (afterSecondRows identity)

theorem bodyChecked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [effect, .cell identity] .none (environment identity base) (environmentRows identity baseRows)
      (fuel + 5) 24 bodyCode .unit [] (bodyReq identity) (bodyPlan identity) .unit (bodyRows identity)
      [Instantiation.freezeEffect effect, Instantiation.freezeEffect effect, Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.bind (node := node 24) (binder := ⟨7, .unit⟩) (initialIndex := 15) (bodyIndex := 23)
    (known := rfl) (kind := rfl) .unit
    (Requests.checked (fuel := fuel + 2) true List.mem_cons_self)
    (afterSecondChecked issued (((Writes.storeBindings (identity := identity) (environment := base) (environmentRows := baseRows)).extend (by decide) (by decide)
      (Callback.valueRows identity)).extend (by decide) (by decide) ValueRows.unit))
  exact ⟨.unit, by intro effect; change effect ∈ [Instantiation.freezeEffect CoreInitialExample.effect,
    Instantiation.freezeEffect (.cell identity)] ↔ effect ∈ [Instantiation.freezeEffect CoreInitialExample.effect,
    Instantiation.freezeEffect CoreInitialExample.effect, Instantiation.freezeEffect (.cell identity)]; simp⟩

theorem callbackChecked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [effect, .cell identity] .none (environment identity base) (environmentRows identity baseRows)
      (fuel + 1) 25 (.variable 8) (Callback.value identity) [] empty .pure (Callback.valueRows identity) .pure [] := by
  simpa [environmentRows, EnvironmentRows.extend] using
    (Checked.variable (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
      (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
      (world := world) (environmentRows := environmentRows identity baseRows) (fuel := fuel)
      (node := node 25) (index := 25) (known := rfl) (kind := rfl)
      (binding := (by simp [environment, Environment.extend] : environment identity base 8 = some (Callback.value identity)))
      (formed := (by intro resource member; simp [Callback.value, Value.erase, SourceDependencyAnnotations.Value.erase,
        CoherentSourceTypes.Value.port, ScopedPorts.Port.resources, Instance.resources] at member; subst resource; exact issued))
      (metadata := ⟨.function .unit .unit (by intro effect; rfl)
        (by intro request member; simp only [Setter.footprint, List.mem_singleton] at member; subst request; exact List.mem_cons_self),
        by intro effect; rfl⟩))

def actionReq (identity : Nat) : Requirements [] := .emitAfter (.sequence empty empty) [] (Setter.footprint identity)
def actionPlan (identity : Nat) := Plan.sequence Plan.pure (Plan.sequence Plan.pure (Writes.plan identity))
def actionRows (identity : Nat) : Rows (signature (actionPlan identity)) := .sequence .pure (.sequence .pure (Writes.rows identity))
theorem actionChecked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [effect, .cell identity] .none (environment identity base) (environmentRows identity baseRows)
      (fuel + 2) 27 (.app (.variable 8) .unit) .unit [] (actionReq identity) (actionPlan identity)
      .unit (actionRows identity) [Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.app (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
    (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
    (world := world) (ownerMap := ownerMap) (allowed := [effect, .cell identity]) (scope := .none)
    (environmentRows := environmentRows identity baseRows) (fuel := fuel + 1)
    (functionDemand := []) (argumentDemand := []) (functionReq := empty) (argumentReq := empty)
    (node := node 27) (functionIndex := 25) (argumentIndex := 26)
    (known := rfl) (kind := rfl) (input := .unit) (output := .unit)
    (requests := [.cell identity]) (latent := Setter.footprint identity)
    (inputRows := .unit) (outputRows := .unit) (bodyPlan := Writes.plan identity) (bodyRows := Writes.rows identity)
    (functionPlan := Plan.pure) (argumentPlan := Plan.pure) (functionRows := Rows.pure) (argumentRows := Rows.pure)
    (functionEffects := []) (argumentEffects := []) (admitted := by intro effect member; simp only [List.mem_singleton] at member; subst effect; simp)
  · exact callbackChecked issued
  · exact Checked.unit (node := node 26) (known := rfl) (kind := rfl) ⟨.unit, by intro effect; rfl⟩
  · exact ⟨.unit, by intro effect; rfl⟩

def cleanupCode := Code.cleanup (.variable 8) bodyCode
def cleanupReq (identity : Nat) : Requirements [] := .emitAfter (.sequence empty (bodyReq identity)) [] (qualify true (Setter.footprint identity))
def cleanupPlan (identity : Nat) := Plan.sequence Plan.pure (Plan.cleanup (needs := [.cell identity]) (Writes.plan identity) (bodyPlan identity))
def cleanupRows (identity : Nat) : Rows (signature (cleanupPlan identity)) := .sequence .pure (.cleanup (Setter.footprint identity) (Writes.rows identity) (bodyRows identity))
theorem cleanupChecked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [effect, .cell identity] .none (environment identity base) (environmentRows identity baseRows)
      (fuel + 6) 28 cleanupCode .unit [] (cleanupReq identity) (cleanupPlan identity) .unit (cleanupRows identity)
      [Instantiation.freezeEffect effect, Instantiation.freezeEffect effect,
        Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.cleanup (node := node 28) (callbackBinder := ⟨8, .function .unit .unit [.cell (.bound 0)]⟩)
    (actionIndex := 27) (bodyIndex := 24) (callbackIndex := 25)
    (known := rfl) (kind := rfl) (actionShape := rfl)
    (callbackType := .function .unit .unit (by intro effect; rfl)
      (by intro request member; simp only [Setter.footprint, List.mem_singleton] at member; subst request; exact List.mem_cons_self))
    (callback := callbackChecked (fuel := fuel + 4) issued)
    (action := actionChecked (fuel := fuel + 3) issued)
    (body := bodyChecked issued)
    (admitted := by intro effect member; simp only [List.mem_singleton] at member; subst effect; simp)
  exact ⟨.unit, by intro effect; change effect ∈ [Instantiation.freezeEffect CoreInitialExample.effect,
    Instantiation.freezeEffect (.cell identity)] ↔ effect ∈ [Instantiation.freezeEffect CoreInitialExample.effect,
    Instantiation.freezeEffect CoreInitialExample.effect, Instantiation.freezeEffect (.cell identity),
    Instantiation.freezeEffect (.cell identity)]; simp⟩

def code := Code.bind 8 Callback.code cleanupCode
def requirements (identity : Nat) : Requirements [] := .sequence empty (cleanupReq identity)
def plan (identity : Nat) := Plan.sequence Plan.pure (cleanupPlan identity)
def rows (identity : Nat) : Rows (signature (plan identity)) := .sequence .pure (cleanupRows identity)
theorem checked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [effect, .cell identity] .none (Writes.storeEnvironment identity base) (Writes.storeEnvironmentRows identity baseRows)
      (fuel + 7) 29 code .unit [] (requirements identity) (plan identity) .unit (rows identity)
      [Instantiation.freezeEffect effect, Instantiation.freezeEffect effect,
        Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.bind (node := node 29) (binder := ⟨8, .function .unit .unit [.cell (.bound 0)]⟩)
    (initialIndex := 13) (bodyIndex := 28) (known := rfl) (kind := rfl)
    (.function .unit .unit (by intro effect; rfl)
      (by intro request member; simp only [Setter.footprint, List.mem_singleton] at member; subst request; exact List.mem_cons_self))
    (Callback.checked (fuel := fuel + 2) issued) (cleanupChecked issued)
  exact ⟨.unit, by intro effect; change effect ∈ [Instantiation.freezeEffect CoreInitialExample.effect,
    Instantiation.freezeEffect (.cell identity)] ↔ effect ∈ [Instantiation.freezeEffect CoreInitialExample.effect,
    Instantiation.freezeEffect CoreInitialExample.effect, Instantiation.freezeEffect (.cell identity),
    Instantiation.freezeEffect (.cell identity)]; simp⟩

end Guarded

namespace Spine
open CoreInitialExample CoreExportedAdmission CoreKernelProgram
private def node (index : Nat) : Node :=
  (CoreExportedFixture.graph.node index).getD ⟨0, .unit, [], none, .unit⟩

/-- Finite lexical annotation checks for the actual getter/resource names. -/
structure ReadBindings (identity : Nat) (environment : Environment) (rows : EnvironmentRows environment) : Prop where
  reference : environment 4 = some (.reference identity)
  getter : environment 11 = some (getterValue identity)
  referenceRows : rows 4 (.reference identity) reference = .reference
  getterRows : rows 11 (getterValue identity) getter = getterValueRows identity

variable {world : List Nat} {environment : Environment} {environmentRows : EnvironmentRows environment}

theorem readChecked (issued : identity ∈ world) (bindings : ReadBindings identity environment environmentRows) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none environment environmentRows (fuel + 2) 44 getterApplication .integer []
      (applicationRequirements identity) (applicationPlan identity) .integer (applicationRows identity)
      [Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.app (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
    (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
    (world := world) (allowed := [.cell identity]) (scope := .none) (environmentRows := environmentRows) (fuel := fuel + 1)
    (input := .reference identity) (output := .integer) (requests := [.cell identity])
    (latent := getterFootprint identity) (inputRows := .reference) (outputRows := .integer)
    (functionDemand := []) (argumentDemand := []) (functionReq := empty) (argumentReq := empty)
    (node := node 44) (functionIndex := 42) (argumentIndex := 43) (known := rfl) (kind := rfl)
    (bodyPlan := readPlan identity) (bodyRows := operationRows identity 0)
    (functionPlan := Plan.pure) (argumentPlan := Plan.pure) (functionRows := Rows.pure) (argumentRows := Rows.pure)
    (functionEffects := []) (argumentEffects := []) (admitted := List.Subset.refl _)
  · have child : Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
        [.cell identity] .none environment environmentRows (fuel + 1) 42 (.variable 11) (getterValue identity)
        [] empty .pure (getterValueRows identity) .pure [] := by
      simpa only [bindings.getterRows] using
        (Checked.variable (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
          (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
          (world := world) (environmentRows := environmentRows) (fuel := fuel) (node := node 42) (index := 42)
          (known := rfl) (kind := rfl) (binding := bindings.getter) (formed := getterFormed issued)
          (metadata := ⟨Getter.getterType, by intro effect; rfl⟩))
    simpa only [getterValue, getterValueRows] using child
  · simpa only [bindings.referenceRows] using
      (Checked.variable (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
        (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
        (world := world) (environmentRows := environmentRows) (fuel := fuel) (node := node 43) (index := 43)
        (known := rfl) (kind := rfl) (binding := bindings.reference) (formed := referenceFormed issued)
        (metadata := ⟨.reference rfl, by intro effect; rfl⟩))
  · exact ⟨.integer, by intro effect; rfl⟩

/-- The final read retains the setter and the handler-result binding, rather
than reconstructing a smaller lexical environment. -/
theorem finalReadChecked (issued : identity ∈ world) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none ((Writes.storeEnvironment identity environment).extend 12 .unit)
      ((Writes.storeEnvironmentRows identity environmentRows).extend 12 .unit)
      (fuel + 2) 44 getterApplication .integer [] (applicationRequirements identity)
      (applicationPlan identity) .integer (applicationRows identity) [Instantiation.freezeEffect (.cell identity)] := by
  apply readChecked issued
  exact ⟨by simp [Writes.storeEnvironment, applicationEnvironment, savedEnvironment, Environment.extend],
    by simp [Writes.storeEnvironment, applicationEnvironment, Environment.extend],
    by simp [EnvironmentRows.extend, Writes.storeEnvironmentRows, applicationEnvironmentRows],
    by simp [EnvironmentRows.extend, Writes.storeEnvironmentRows, applicationEnvironmentRows]⟩

/-- Only the named handler node is a residual Core derivation input. Every
ordinary frame after it is constructed from the actual exported graph. -/
theorem afterHandlerChecked (issued : identity ∈ world)
    (handler : Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none (Writes.storeEnvironment identity environment) (Writes.storeEnvironmentRows identity environmentRows)
      (fuel + 2) 41 handlerCode .unit handlerDemand handlerReq handlerPlan .unit handlerRows
      [Instantiation.freezeEffect (.cell identity)]) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none (Writes.storeEnvironment identity environment) (Writes.storeEnvironmentRows identity environmentRows)
      (fuel + 3) 45 (.bind 12 handlerCode getterApplication) .integer (handlerDemand ++ [])
      (.sequence handlerReq (applicationRequirements identity)) (.sequence handlerPlan (applicationPlan identity)) .integer
      (by simpa only [signature] using Rows.sequence handlerRows (applicationRows identity))
      [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] := by
  exact Checked.bind (node := node 45) (binder := ⟨12, .unit⟩) (initialIndex := 41) (bodyIndex := 44)
    (index := 45) (known := rfl) (kind := rfl) .unit handler (finalReadChecked issued)
    ⟨.integer, by intro effect; change (effect ∈ [Instantiation.freezeEffect (.cell identity)]) ↔
      effect ∈ [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)]; simp⟩

/-- The actual setter binding precedes the handler and final read. -/
theorem setterBindingChecked (issued : identity ∈ world)
    (handler : Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none (Writes.storeEnvironment identity environment) (Writes.storeEnvironmentRows identity environmentRows)
      (fuel + 2) 41 handlerCode .unit handlerDemand handlerReq handlerPlan .unit handlerRows
      [Instantiation.freezeEffect (.cell identity)]) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none (applicationEnvironment identity environment) (applicationEnvironmentRows identity environmentRows)
      (fuel + 4) 46 (.bind 3 (Setter.closure identity) (.bind 12 handlerCode getterApplication)) .integer ([] ++ (handlerDemand ++ []))
      (.sequence empty (.sequence handlerReq (applicationRequirements identity)))
      (.sequence .pure (.sequence handlerPlan (applicationPlan identity))) .integer
      (by simpa only [signature] using Rows.sequence Rows.pure (Rows.sequence handlerRows (applicationRows identity)))
      [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] := by
  exact Checked.bind (node := node 46) (binder := ⟨3, (node 7).type⟩) (initialIndex := 7) (bodyIndex := 45)
    (index := 46) (known := rfl) (kind := rfl) Setter.type (Setter.checked issued) (afterHandlerChecked issued handler)
    ⟨.integer, by intro effect; change (effect ∈ [Instantiation.freezeEffect (.cell identity)]) ↔
      effect ∈ [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)]; simp⟩

/-- Lift a handler derivation through the actual ordinary resource-body spine.
The concrete `Spine.checked` below constructs that derivation from the graph;
resource48 remains a separate effect-node obligation. -/
theorem getterBindingChecked (issued : identity ∈ world)
    (handler : Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none (Writes.storeEnvironment identity environment) (Writes.storeEnvironmentRows identity environmentRows)
      (fuel + 2) 41 handlerCode .unit handlerDemand handlerReq handlerPlan .unit handlerRows
      [Instantiation.freezeEffect (.cell identity)]) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none (savedEnvironment identity environment) (environmentRows.extend 4 .reference)
      (fuel + 5) 47 (.bind 11 (getter identity) (.bind 3 (Setter.closure identity) (.bind 12 handlerCode getterApplication)))
      .integer ([] ++ ([] ++ (handlerDemand ++ [])))
      (.sequence empty (.sequence empty (.sequence handlerReq (applicationRequirements identity))))
      (.sequence .pure (.sequence .pure (.sequence handlerPlan (applicationPlan identity)))) .integer
      (by simpa only [signature] using Rows.sequence Rows.pure (Rows.sequence Rows.pure (Rows.sequence handlerRows (applicationRows identity))))
      [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] := by
  exact Getter.bindingChecked (fuel := fuel + 1) issued (setterBindingChecked issued handler)
    ⟨.integer, by intro effect; change (effect ∈ [Instantiation.freezeEffect (.cell identity)]) ↔
      effect ∈ [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)]; simp⟩

end Spine

namespace Clause
open CoreInitialExample CoreExportedAdmission CoreKernelProgram

/-- The remaining ordinary contract annotations are retained exactly. The
fixed Unit input/answer, cell allowances and unprotected disposal are the
existing source obligations of this particular exported clause. -/
structure Data where
  resumeDemand : List Nat
  resumeRow : Footprint
  closeDemand : List Nat
  closeRow : Option Footprint

def contract (identity : Nat) (data : Data) : Contract :=
  ⟨.unit, .unit, false, data.resumeDemand, data.resumeRow, data.closeDemand, data.closeRow,
    [.cell identity], [.cell identity]⟩
def ticket := CoreTranslation.ticket CoreExportedFixture.graph 0
def map (tail : CoreTranslation.OwnerMap) : CoreTranslation.OwnerMap := ⟨0, 0, ticket⟩ :: tail
private def node (index : Nat) : Node :=
  (CoreExportedFixture.graph.node index).getD ⟨0, .unit, [], none, .unit⟩
def environment (identity : Nat) (base : Environment) := (Writes.storeEnvironment identity base).extend 9 .boolean
def environmentRows (identity : Nat) (base : EnvironmentRows original) : EnvironmentRows (environment identity original) :=
  (Writes.storeEnvironmentRows identity base).extend 9 .boolean

def resumeRequirements (owner : Nat) (data : Data) : Requirements ([] ++ owner :: data.resumeDemand) :=
  .sequence empty (.invoke ⟨owner, .resume⟩ data.resumeDemand [])
def resumePlan (owner : Nat) := Plan.sequence Plan.pure (Plan.invoke (key := ⟨owner, .resume⟩))
def resumeRows (owner : Nat) : Rows (signature (resumePlan owner)) := by
  simpa only [resumePlan, signature] using Rows.sequence (Rows.pure : Rows (signature Plan.pure))
    (Rows.invoke (key := ⟨owner, .resume⟩))

private theorem resumeRowsUnique (decoration : Rows (signature (resumePlan owner))) : decoration = resumeRows owner := by
  cases decoration with
  | sequence first second => cases first; cases second; rfl

variable {world : List Nat} {base : Environment} {baseRows : EnvironmentRows base}

theorem resumeChecked (_issued : identity ∈ world) (data : Data) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity)
      (contracts.insert owner (contract identity data)) (owners.insert owner .unit .unit) world (map ownerMap)
      [.cell identity] (.ticket ticket owner) (environment identity base) (environmentRows identity baseRows)
      (fuel + 2) 32 (.resume ticket .unit) .unit ([] ++ owner :: data.resumeDemand)
      (resumeRequirements owner data) (resumePlan owner) .unit (resumeRows owner)
      [Instantiation.freezeEffect (.cell identity)] := by
  have operandProof : Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity)
      (contracts.insert owner (contract identity data)) (owners.insert owner .unit .unit) world (map ownerMap)
      [.cell identity] (.ticket ticket owner) (environment identity base) (environmentRows identity baseRows)
      (fuel + 1) 31 Code.unit .unit [] empty .pure .unit .pure [] :=
    Checked.unit (node := node 31) (known := rfl) (kind := rfl) ⟨.unit, by intro effect; rfl⟩
  have known : contracts.insert owner (contract identity data) owner = some (contract identity data) := by simp [Contracts.insert]
  have operandRows : (owners.insert owner .unit .unit owner (contract identity data) known).1 = ValueRows.unit := by
    simp only [ContractRows.insert]
    rfl
  have answerRows : (owners.insert owner .unit .unit owner (contract identity data) known).2 = ValueRows.unit := by
    simp only [ContractRows.insert]
    rfl
  have step := Checked.resume (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
    (operations := operations) (policy := policy) (ports := ports)
    (contracts := contracts.insert owner (contract identity data)) (owners := owners.insert owner .unit .unit)
    (ownerMap := map ownerMap) (world := world) (allowed := [.cell identity])
    (scope := .ticket ticket owner) (environmentRows := environmentRows identity baseRows)
    (owner := owner) (contract := contract identity data) (index := 32)
    (operandDemand := []) (operandReq := empty) (value := Code.unit)
    (node := node 32) (handler := 0) (coreOwner := 0) (operandIndex := 31)
    (fuel := fuel + 1) (operandPlan := Plan.pure) (operandRows := Rows.pure) (operandEffects := [])
    (known := rfl) (kind := rfl) (mapped := rfl)
    (contractKnown := known) (resolved := rfl) (permission := rfl)
    (admitted := List.Subset.refl _) (formed := List.nil_subset _)
    (operand := operandRows.symm ▸ operandProof)
    (metadata := (⟨.unit, by intro effect; rfl⟩ : Metadata (Getter.resources identity) (node 32) (contract identity data).answer
      ([] ++ allowanceEffects (contract identity data).resumeEffects)))
  rw [answerRows] at step
  exact resumeRowsUnique (owner := owner) _ ▸ step

theorem discardChecked (data : Data) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity)
      (contracts.insert owner (contract identity data)) (owners.insert owner .unit .unit) world (map ownerMap)
      [.cell identity] (.ticket ticket owner) (environment identity base) (environmentRows identity baseRows)
      (fuel + 1) 39 (.discard ticket) .unit (owner :: data.closeDemand)
      (.invoke ⟨owner, .dispose⟩ data.closeDemand []) (.invoke (key := ⟨owner, .dispose⟩)) .unit .invoke
      [Instantiation.freezeEffect (.cell identity)] := by
  exact Checked.discard (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
    (operations := operations) (policy := policy) (ports := ports)
    (contracts := contracts.insert owner (contract identity data)) (owners := owners.insert owner .unit .unit)
    (ownerMap := map ownerMap) (world := world) (allowed := [.cell identity])
    (scope := .ticket ticket owner) (environmentRows := environmentRows identity baseRows)
    (owner := owner) (contract := contract identity data) (index := 39) (node := node 39) (handler := 0) (coreOwner := 0) (known := rfl) (kind := rfl)
    (mapped := rfl) (contractKnown := by simp [Contracts.insert]) (resolved := rfl) (permission := rfl)
    (unprotected := rfl) (admitted := List.Subset.refl _) ⟨.unit, by intro effect; rfl⟩

def yesCode := Code.bind 10 (.resume ticket .unit) (Writes.application .suffix)
def yesRequirements (identity owner : Nat) (data : Data) :
    Requirements (([] ++ owner :: data.resumeDemand) ++ []) :=
  .sequence (resumeRequirements owner data) (Writes.requirements identity)
def yesPlan (identity owner : Nat) := Plan.sequence (resumePlan owner) (Writes.plan identity)
def yesRows (identity owner : Nat) : Rows (signature (yesPlan identity owner)) :=
  .sequence (resumeRows owner) (Writes.rows identity)

theorem suffixBindings : Writes.WriteBindings identity ((environment identity base).extend 10 .unit)
    ((environmentRows identity baseRows).extend 10 .unit) :=
  ⟨by simp [environment, Writes.storeEnvironment, applicationEnvironment, savedEnvironment, Environment.extend],
   by simp [environment, Writes.storeEnvironment, Environment.extend],
   by simp [environmentRows, Writes.storeEnvironmentRows, applicationEnvironmentRows, EnvironmentRows.extend],
   by simp [environmentRows, Writes.storeEnvironmentRows, EnvironmentRows.extend]⟩

theorem yesChecked (issued : identity ∈ world) (data : Data) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity)
      (contracts.insert owner (contract identity data)) (owners.insert owner .unit .unit) world (map ownerMap)
      [.cell identity] (.ticket ticket owner) (environment identity base) (environmentRows identity baseRows)
      (fuel + 4) 38 yesCode .unit (([] ++ owner :: data.resumeDemand) ++ [])
      (yesRequirements identity owner data) (yesPlan identity owner) .unit (yesRows identity owner)
      [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] := by
  exact Checked.bind (node := node 38) (binder := ⟨10, .unit⟩) (index := 38) (initialIndex := 32) (bodyIndex := 37)
    (known := rfl) (kind := rfl) .unit (resumeChecked (fuel := fuel + 1) issued data)
    (Writes.checked (contracts := contracts.insert owner (contract identity data))
      (owners := owners.insert owner .unit .unit) (ownerMap := map ownerMap) (scope := .ticket ticket owner)
      .suffix issued suffixBindings)
    ⟨.unit, by intro effect; change (effect ∈ [Instantiation.freezeEffect (.cell identity)]) ↔
      effect ∈ [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)]; simp⟩

theorem balanced {data : Data} (balance : data.closeDemand.Perm data.resumeDemand) :
    (([] ++ owner :: data.resumeDemand) ++ []).Perm (owner :: data.closeDemand) := by
  simpa only [List.nil_append, List.append_nil] using balance.symm.cons owner

def code := Code.branch (.variable 9) yesCode (.discard ticket)
/-- The checked translated clause consumes its own ticket on both arms. -/
theorem capability : ScopedExpressions.Uses policy (.ticket ticket (policy ticket)) .available code .consumed :=
  CoreGraphCapabilities.sound (fuel := 8) rfl


def requirements (identity owner : Nat) (data : Data) (balance : data.closeDemand.Perm data.resumeDemand) :
    Requirements ([] ++ (([] ++ owner :: data.resumeDemand) ++ [])) :=
  .sequence empty (.choice (yesRequirements identity owner data)
    (.invoke ⟨owner, .dispose⟩ data.closeDemand []) (balanced balance))
def plan (identity owner : Nat) :=
  Plan.sequence Plan.pure (Plan.choice (yesPlan identity owner) (Plan.invoke (key := ⟨owner, .dispose⟩)))
def rows (identity owner : Nat) : Rows (signature (plan identity owner)) :=
  .sequence .pure (.choice (yesRows identity owner) .invoke)

/-- The actual exported clause is constructed at a fresh source owner and the
actual translated Core ticket. Contract demands/footprints are retained; the
ordinary unprotected mode is explicit, not imposed on other offered modes. -/
theorem checked (issued : identity ∈ world) (data : Data) (_fresh : contracts owner = none)
    (balance : data.closeDemand.Perm data.resumeDemand) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity)
      (contracts.insert owner (contract identity data)) (owners.insert owner .unit .unit) world (map ownerMap)
      [.cell identity] (.ticket ticket owner) (environment identity base) (environmentRows identity baseRows)
      (fuel + 5) 40 code .unit ([] ++ (([] ++ owner :: data.resumeDemand) ++ []))
      (requirements identity owner data balance) (plan identity owner) .unit (rows identity owner)
      [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.branch (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
    (operations := operations) (policy := policy) (ports := ports)
    (contracts := contracts.insert owner (contract identity data)) (owners := owners.insert owner .unit .unit)
    (world := world) (ownerMap := map ownerMap) (allowed := [.cell identity]) (scope := .ticket ticket owner)
    (environmentRows := environmentRows identity baseRows) (fuel := fuel + 4)
    (node := node 40) (conditionIndex := 30) (yesIndex := 38) (noIndex := 39) (known := rfl) (kind := .inl rfl)
    (conditionPlan := Plan.pure) (conditionRows := Rows.pure) (conditionEffects := [])
    (conditionDemand := []) (conditionReq := empty) (yesPlan := yesPlan identity owner)
    (yesRows := yesRows identity owner) (yesEffects := [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)])
    (noPlan := Plan.invoke (key := ⟨owner, .dispose⟩)) (noRows := Rows.invoke)
    (noEffects := [Instantiation.freezeEffect (.cell identity)]) (same := balanced balance)
  · simpa [environmentRows, EnvironmentRows.extend] using
      (Checked.variable (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
        (operations := operations) (policy := policy) (ports := ports)
        (contracts := contracts.insert owner (contract identity data)) (owners := owners.insert owner .unit .unit)
        (world := world) (ownerMap := map ownerMap) (environmentRows := environmentRows identity baseRows)
        (fuel := fuel + 3) (node := node 30) (index := 30) (known := rfl) (kind := rfl)
        (binding := (by simp [environment, Environment.extend] : environment identity base 9 = some .boolean))
        (formed := List.nil_subset _) (metadata := ⟨.boolean, by intro effect; rfl⟩))
  · exact yesChecked issued data
  · exact discardChecked (fuel := fuel + 3) data
  · exact ⟨.unit, by intro effect; change (effect ∈ [Instantiation.freezeEffect (.cell identity)]) ↔
      effect ∈ [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)]; simp⟩

/-- Static construction for the actual node 40, including its instantiated
translation and authenticated source, without a supplied target judgment. -/
theorem compiled (issued : identity ∈ world) (data : Data) (fresh : contracts owner = none)
    (balance : data.closeDemand.Perm data.resumeDemand) :
    ∃ raw, CoreTranslation.translateFuel CoreExportedFixture.graph (fuel + 5) (map ownerMap) 40 = .ok raw ∧
      raw.instantiate (Getter.resources identity) = code ∧
      ∃ source : SourcePlannedSources.Expression operations policy
        (contracts.insert owner (contract identity data)) world [.cell identity] (.ticket ticket owner)
        (environment identity base) code .unit ([] ++ (([] ++ owner :: data.resumeDemand) ++ []))
        (requirements identity owner data balance) (signature (plan identity owner)),
        Auth operations policy ports (owners.insert owner .unit .unit) (environmentRows identity baseRows)
          source .unit (rows identity owner) :=
  (checked (fuel := fuel) issued data fresh balance).compiled

def Data.ofContract (contract : Contract) : Data :=
  ⟨contract.resumeDemand, contract.resumeRow, contract.closeDemand, contract.closeRow⟩

def contractRequirements (identity owner : Nat) (contract : Contract)
    (balance : contract.closeDemand.Perm contract.resumeDemand) :=
  requirements identity owner (Data.ofContract contract) balance

theorem checkedContract (issued : identity ∈ world) (contract : Contract) (fresh : contracts owner = none)
    (inputSame : contract.input = .unit) (answerSame : contract.answer = .unit)
    (resumeSame : contract.resumeEffects = [.cell identity]) (closeSame : contract.closeEffects = [.cell identity])
    (heldSame : contract.held = false) (balance : contract.closeDemand.Perm contract.resumeDemand) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity)
      (contracts.insert owner contract) (owners.insert owner (inputSame.symm ▸ ValueRows.unit) (answerSame.symm ▸ ValueRows.unit))
      world (map ownerMap) [.cell identity] (.ticket ticket owner) (environment identity base) (environmentRows identity baseRows)
      (fuel + 5) 40 code .unit ([] ++ (([] ++ owner :: contract.resumeDemand) ++ []))
      (contractRequirements identity owner contract balance) (plan identity owner) .unit (rows identity owner)
      [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] := by
  rcases contract with ⟨input, answer, held, resumeDemand, resumeRow, closeDemand, closeRow, resumeEffects, closeEffects⟩
  cases inputSame; cases answerSame; cases resumeSame; cases closeSame; cases heldSame
  exact checked issued ⟨resumeDemand, resumeRow, closeDemand, closeRow⟩ fresh balance

private theorem mergeEmpty (row : Option Footprint) : ProtectionResiduals.merge (some []) row = row := by
  cases row <;> rfl

theorem yesAdmissionRows {templates : RecursiveRequirements.Store → Prop} {contract : Contract}
    (balance : contract.closeDemand.Perm contract.resumeDemand) :
    ClauseRowAdmission.Rows ⟨owner, contract.erase.erase, true, Setter.footprint identity⟩
      (yesRequirements identity owner (Data.ofContract contract)) templates := by
  intro store tail before requestRow interface exported
  obtain ⟨checked, bounded⟩ := interface.resume_then_suffix_checked rfl balance exported
  obtain ⟨firstRow, secondRow, first, suffix, same⟩ := RecursiveRequirements.checked_sequence_parts checked
  have suffixExport := RecursiveRequirements.checked_complete suffix
  have expanded : RecursiveRequirements.Checked store (.live owner contract.held :: tail)
      (OwnerPhaseTransitions.spendAll before ([] ++ owner :: contract.resumeDemand))
      (Writes.requirements identity) secondRow := by
    apply RecursiveRequirements.Checked.emitAfter (bodyRow := [])
    · apply RecursiveRequirements.Checked.sequence (firstRow := []) (secondRow := [])
      · exact .request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
      · apply RecursiveRequirements.Checked.sequence (firstRow := []) (secondRow := [])
        · exact .request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
        · exact .request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
    · simpa [RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel, OwnerSource.exportAt,
        ProtectionResiduals.residual_empty, mergeEmpty, SourcePlannedTyping.Contract.erase,
        SourceDependencyAnnotations.Contract.erase] using suffixExport
  have complete := RecursiveRequirements.Checked.sequence first expanded
  obtain ⟨calls, derived, supplied⟩ := ContextualClauseChecks.open_checked complete
  rw [same] at bounded
  exact ⟨_, calls, derived, supplied, bounded⟩

theorem admissionRows {templates : RecursiveRequirements.Store → Prop} {contract : Contract}
    (balance : contract.closeDemand.Perm contract.resumeDemand) :
    ClauseRowAdmission.Rows ⟨owner, contract.erase.erase, true, Setter.footprint identity⟩
      (contractRequirements identity owner contract balance) templates := by
  apply ClauseRowAdmission.Rows.pure_prefix
  apply ClauseRowAdmission.Rows.alternatives
  · exact yesAdmissionRows balance
  · exact ClauseRowAdmission.discard_rows

theorem admissionProtectedRows {templates : RecursiveRequirements.Store → Prop} {contract : Contract}
    (balance : contract.closeDemand.Perm contract.resumeDemand) :
    ClauseRowAdmission.ProtectedRows ⟨owner, contract.erase.erase, true, Setter.footprint identity⟩
      (contractRequirements identity owner contract balance) templates := by
  apply ClauseRowAdmission.ProtectedRows.pure_prefix
  apply ClauseRowAdmission.ProtectedRows.alternatives
  · exact .of_unchanged (yesAdmissionRows balance) rfl
  · exact ClauseRowAdmission.protected_discard_rows

end Clause

namespace Handler
open CoreInitialExample CoreExportedAdmission CoreKernelProgram
private def node (index : Nat) : Node :=
  (CoreExportedFixture.graph.node index).getD ⟨0, .unit, [], none, .unit⟩
def arms : Clauses := .cons 0 9 Clause.ticket Clause.code .nil
def table (identity : Nat) : List (Nat × ClauseContract) := [(0, ⟨true, some (Setter.footprint identity), none⟩)]
def declarationPlans (identity : Nat) :=
  SourceDeclarationPlans.ClausePlans.cons (operation := 0) (parameter := 9) (binder := Clause.ticket) (body := Clause.code)
    (SourceDeclarationPlans.ModePlans.available (Clause.plan identity)) SourceDeclarationPlans.ModePlans.unavailable
    SourceDeclarationPlans.ClausePlans.nil
def declarationRows (identity : Nat) : ClauseRows (SourcePlanSignatures.clauseSignatures (declarationPlans identity)) :=
  .cons (.available (Clause.rows identity)) .unavailable .nil [identity]
variable {world : List Nat} {base : Environment} {baseRows : EnvironmentRows base}

theorem ordinary (issued : identity ∈ world) :
    CheckedOffer CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] (Writes.storeEnvironment identity base) (Writes.storeEnvironmentRows identity baseRows)
      (fuel + 5) 0 0 40 9 Clause.ticket .boolean .boolean .unit .unit .unit .unit
      [.cell identity] [.cell identity] Clause.code false true (some (Setter.footprint identity))
      (.available (Clause.plan identity)) (.available (Clause.rows identity)) := by
  apply CheckedOffer.available
    (bodyDemand := fun owner contract => [] ++ (([] ++ owner :: contract.resumeDemand) ++ []))
    (bodyReq := Clause.contractRequirements identity)
    (resumeInterface := fun _ => rfl) (closeInterface := fun _ => rfl)
  · intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
    exact Clause.checkedContract issued contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  · intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
    exact Clause.admissionRows balance
  · intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
    exact Clause.admissionProtectedRows balance

def witnessContract (identity : Nat) : Contract := Clause.contract identity ⟨[], [], [], none⟩

/-- A finite current registry witness supplies port checking independently of
whether an offered mode admits row evidence. Both modes remain explicit. -/
theorem declarations (issued : identity ∈ world) (fresh : contracts witness = none)
    (distinct : ownerMap.any (fun binding => binding.owner == 0) = false) :
    CheckedDeclarations CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] (Writes.storeEnvironment identity base) (Writes.storeEnvironmentRows identity baseRows)
      (fuel + 7) 0 effect .unit .unit [⟨0, .binder ⟨9, .boolean⟩, 0, 40⟩] arms (table identity)
      (declarationPlans identity) (declarationRows identity) := by
  apply CheckedDeclarations.cons (operationKnown := (rfl : operations effect 0 = some (.boolean, .unit)))
    (argumentType := .boolean) (distinct := distinct) (mapped := rfl)
    (witnessFresh := fresh) (witnessContract := witnessContract identity)
    (witnessInput := rfl) (witnessAnswer := rfl) (witnessResume := rfl) (witnessClose := rfl) (witnessHeld := rfl)
    (portBody := Clause.checkedContract (fuel := fuel + 2) issued (witnessContract identity) fresh
      rfl rfl rfl rfl rfl (List.Perm.refl []))
    (disposeMode := fun _ => rfl) (usageFuel := 8) (usage := rfl)
    (ordinary := ordinary (fuel := fuel + 2) issued) (protectedMode := .unavailable) (rest := .nil)
  simp [Clause.code, Clause.yesCode, Writes.application, Writes.argument, Code.dependencies, Syntax.without,
    LambdaPortCaptureSupport.portSupport, ScopedPorts.Support.evaluate, Writes.storeEnvironment,
    applicationEnvironment, savedEnvironment, Environment.extend, Setter.value, Setter.input,
    Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port,
    ScopedPorts.Port.resources, Instance.resources]

theorem coverage : ScopedPorts.Covers operations.erase.erase.ports effect arms := by
  intro operation input output known
  cases operation with
  | zero => simp [arms, ScopedTyping.clauseKeys]
  | succ operation => simp [operations, effect, SourcePlannedTyping.Operations.erase,
      SourceDependencyAnnotations.Operations.erase, CoherentSourceTypes.Operations.ports] at known

def code := Code.handle (Instantiation.freezeEffect effect) Guarded.code arms
def requirements (identity : Nat) : Requirements [] :=
  (Guarded.requirements identity).prepend [.ordinary (.handler effect 0 (table identity))]
def plan (identity : Nat) := Plan.handler (effect := effect) (table := table identity)
  [(.cell identity, 1)] (declarationPlans identity) (Guarded.plan identity)
def rows (identity : Nat) : Rows (signature (plan identity)) := .handler (declarationRows identity) (Guarded.rows identity)

theorem checked (issued : identity ∈ world) (fresh : contracts witness = none)
    (distinct : ownerMap.any (fun binding => binding.owner == 0) = false) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none (Writes.storeEnvironment identity base) (Writes.storeEnvironmentRows identity baseRows)
      (fuel + 8) 41 code .unit [] (requirements identity) (plan identity) .unit (rows identity)
      [Instantiation.freezeEffect (.cell identity)] := by
  exact Checked.handler (node := node 41) (handler := 0) (rawEffect := .user 0 []) (bodyIndex := 29)
    (known := rfl) (kind := rfl) (instantiated := rfl) (shapes := rfl)
    (body := Guarded.checked issued) (declarations := declarations issued fresh distinct)
    (coverage := coverage) (unique := by simp [arms, ScopedTyping.clauseKeys]) (admitted := List.Subset.refl _)
    (effectsAdmitted := List.Subset.refl _) ⟨.unit, by intro effect; rfl⟩
end Handler

namespace Spine
open CoreInitialExample CoreExportedAdmission CoreKernelProgram
variable {world : List Nat} {environment : Environment} {environmentRows : EnvironmentRows environment}
def code (identity : Nat) :=
  Code.bind 11 (getter identity) (.bind 3 (Setter.closure identity) (.bind 12 Handler.code getterApplication))
def requirements (identity : Nat) : Requirements [] :=
  .sequence empty (.sequence empty (.sequence (Handler.requirements identity) (applicationRequirements identity)))
def plan (identity : Nat) :=
  Plan.sequence Plan.pure (Plan.sequence Plan.pure (Plan.sequence (Handler.plan identity) (applicationPlan identity)))
def rows (identity : Nat) : Rows (signature (plan identity)) := by
  unfold plan
  simpa only [signature] using Rows.sequence Rows.pure
    (Rows.sequence Rows.pure (Rows.sequence (Handler.rows identity) (applicationRows identity)))

/-- Every ordinary node through handler41 is constructed. The only registry
inputs are finite current freshness/lexical-map checks, not a handler derivation. -/
theorem checked (issued : identity ∈ world) (fresh : contracts witness = none)
    (distinct : ownerMap.any (fun binding => binding.owner == 0) = false) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] .none (savedEnvironment identity environment) (environmentRows.extend 4 .reference)
      (fuel + 11) 47 (code identity) .integer [] (requirements identity) (plan identity) .integer (rows identity)
      [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] := by
  exact getterBindingChecked (fuel := fuel + 6) issued
    (Handler.checked (fuel := fuel) (base := environment) (baseRows := environmentRows) issued fresh distinct)

theorem compiled (issued : identity ∈ world) (fresh : contracts witness = none)
    (distinct : ownerMap.any (fun binding => binding.owner == 0) = false) :
    ∃ raw, CoreTranslation.translateFuel CoreExportedFixture.graph (fuel + 11) ownerMap 47 = .ok raw ∧
      raw.instantiate (Getter.resources identity) = code identity ∧
      ∃ source : SourcePlannedSources.Expression operations policy contracts world [.cell identity] .none
        (savedEnvironment identity environment) (code identity) .integer [] (requirements identity) (signature (plan identity)),
        Auth operations policy ports owners (environmentRows.extend 4 .reference) source .integer (rows identity) :=
  (checked (fuel := fuel) issued fresh distinct).compiled

def emptyContracts : Contracts := fun _ => none
def emptyOwners : ContractRows emptyContracts := by intro _ _ known; cases known
def emptyEnvironmentRows : EnvironmentRows (fun _ => none) := by intro _ _ known; cases known

/-- The actual resource body at its fresh activation has no supplied structural
certificate: the finite registry/map witnesses are discharged here. Resource
entry itself remains a separate Core constructor obligation. -/
theorem closedChecked (identity fuel : Nat) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) emptyContracts emptyOwners [identity] []
      [.cell identity] .none (savedEnvironment identity (fun _ => none)) (emptyEnvironmentRows.extend 4 .reference)
      (fuel + 11) 47 (code identity) .integer [] (requirements identity) (plan identity) .integer (rows identity)
      [Instantiation.freezeEffect (.cell identity), Instantiation.freezeEffect (.cell identity)] :=
  checked (witness := 0) List.mem_cons_self rfl rfl
theorem closedCompiled (identity fuel : Nat) :
    ∃ raw, CoreTranslation.translateFuel CoreExportedFixture.graph (fuel + 11) [] 47 = .ok raw ∧
      raw.instantiate (Getter.resources identity) = code identity ∧
      ∃ source : SourcePlannedSources.Expression operations policy emptyContracts [identity] [.cell identity] .none
        (savedEnvironment identity (fun _ => none)) (code identity) .integer [] (requirements identity) (signature (plan identity)),
        Auth operations policy ports emptyOwners (emptyEnvironmentRows.extend 4 .reference) source .integer (rows identity) :=
  (closedChecked identity fuel).compiled

end Spine

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Checked.sourceAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Checked.translation
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Getter.checked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Getter.applicationChecked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Checked.compiled
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.retainedSupportBoundary

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Getter.bindingChecked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Setter.checked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Writes.checked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Spine.setterBindingChecked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Spine.getterBindingChecked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.dummyFresh

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Checked.ticketFreeSyntax

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Clause.resumeChecked
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Clause.discardChecked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Clause.checked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Clause.compiled

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Callback.checked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Clause.capability

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Guarded.checked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Handler.checked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Handler.ordinary

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Handler.declarations

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Clause.admissionRows

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Clause.admissionProtectedRows

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Spine.checked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Spine.compiled

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Spine.closedChecked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Spine.closedCompiled
