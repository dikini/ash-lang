import CoreExportedAdmission

/-! A distinct static graph derivation for the administrative fragment. Checked
Core node equations, declared annotations and lexical bindings are inputs;
translated source typing and row authentication are constructed outputs. -/
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

/-- The graph certificate constructs both source layers; neither is an input. -/
theorem Checked.sourceAuth
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope environment environmentRows
      fuel index code value demand requirements plan valueRows rows effects) :
    ∃ source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      code value demand requirements (signature plan), Auth operations policy ports owners environmentRows source valueRows rows := by
  induction checked with
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
  induction checked with
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
  induction checked with
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

theorem storeBindings : WriteBindings identity (storeEnvironment identity environment)
    (storeEnvironmentRows identity environmentRows) :=
  ⟨by simp [storeEnvironment, applicationEnvironment, savedEnvironment, Environment.extend],
   by simp [storeEnvironment, Environment.extend],
   by simp [storeEnvironmentRows, applicationEnvironmentRows, EnvironmentRows.extend],
   by simp [storeEnvironmentRows, EnvironmentRows.extend]⟩

theorem functionChecked (site : Site) (issued : identity ∈ world) (bindings : WriteBindings identity environment environmentRows) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] scope environment environmentRows
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
      [.cell identity] scope environment environmentRows
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

theorem checked (site : Site) (issued : identity ∈ world) (bindings : WriteBindings identity environment environmentRows) :
    Checked CoreExportedFixture.graph operations policy ports (Getter.resources identity) contracts owners world ownerMap
      [.cell identity] scope environment environmentRows
      (fuel + 3) site.applicationIndex (application site) .unit [] (requirements identity) (plan identity)
      .unit (rows identity) [Instantiation.freezeEffect (.cell identity)] := by
  apply Checked.app (graph := CoreExportedFixture.graph) (resources := Getter.resources identity)
    (operations := operations) (policy := policy) (ports := ports) (contracts := contracts) (owners := owners)
    (world := world) (allowed := [.cell identity]) (scope := scope)
    (environmentRows := environmentRows) (fuel := fuel + 2)
    (input := Setter.input identity) (output := .unit) (requests := [.cell identity])
    (latent := Setter.footprint identity) (inputRows := .pair .reference .integer) (outputRows := .unit)
    (bodyPlan := writePlan identity) (bodyRows := operationRows identity 1)
    (functionDemand := []) (argumentDemand := []) (functionReq := empty) (argumentReq := tupleRequirements)
    (functionPlan := Plan.pure) (argumentPlan := tuplePlan) (functionRows := Rows.pure) (argumentRows := tupleRows)
    (functionEffects := []) (argumentEffects := []) (node := node site.applicationIndex)
    (functionIndex := site.functionIndex) (argumentIndex := site.tupleIndex)
    (known := by cases site <;> rfl) (kind := by cases site <;> rfl)
    (admitted := List.Subset.refl _)
  · simpa [Setter.value, Setter.valueRows] using (functionChecked (fuel := fuel + 1) site issued bindings)
  · exact argumentChecked site issued bindings
  · exact ⟨by cases site <;> exact .unit, by intro effect; cases site <;> rfl⟩

end Writes

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

/-- The complete ordinary resource-body spine is conditional only on the named
handler41 Core derivation. Resource48 remains a separate effect-node obligation. -/
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

end Clause

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
