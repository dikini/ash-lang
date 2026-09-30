import CoreEffectFrames
import CoreOrdinaryCompletion

/-! Actual handler/cell transition components. All successor lexical evidence
is derived from current closing derivations. Target scopes/answers remain
supplied; resource freshness and source authentication remain separate. -/
namespace Ash.OneShot.CoreEffectEntry
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreEffectFrames Instantiation

/-- Handler body and header are projected from the same current interpretation.
Activation synchronization uses the actual nextHandler counter. -/
theorem handler_enter {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .handler handlerId effect body clauses)
    (translated : CoreTranslation.translateFuel graph fuel owners site = .ok (.handle effect rawBody rawClauses))
    (bodyTranslated : CoreTranslation.translateFuel graph bodyFuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment (.handle effect rawBody rawClauses)
      (.handle (freezeEffect data.effectInst) bodyCode data.clauses))
    (activation : data.activation = base.nextHandler) (tail : List CoreMachine.Frame) (target : Stack) :
    CoreMachine.next graph { base with control := .evaluate site environment, frames := tail } =
      .stepped { base with control := .evaluate body environment, frames := .handlerBoundary site environment data.activation :: tail, nextHandler := base.nextHandler + 1, observations := base.observations ++ [.entered site, .handlerEntered site data.activation] } ∧
    RawStep ⟨.handle (freezeEffect data.effectInst) bodyCode data.clauses, data.scope, target⟩
      ⟨bodyCode, data.scope, .push (.handler data) target⟩ [] [] ∧
    BoundaryRel graph owners base.heap (.handlerBoundary site environment data.activation) (.handler data) ∧
    EnvCloses graph owners base.heap environment rawBody bodyCode ∧
    effect.instantiate environment.instantiation = freezeEffect data.effectInst ∧
    CoreTranslation.translateFuel graph bodyFuel owners body = .ok rawBody := by
  obtain ⟨savedBody, header⟩ := handle_components current
  have effectEqual := handle_effect_at current _ _ _ _ _ _ rfl rfl
  refine ⟨?_, .enterHandler data bodyCode target, .handler known kind translated header,
    savedBody, effectEqual, bodyTranslated⟩
  simp [CoreMachine.next, known, kind, activation, List.append_assoc]

/-- Acquisition opens the resource barrier, then the generated handle bind.
The source enters the actual resource/handle environment directly. -/
theorem cell_acquire {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .resource identity handle initializer body)
    (bodyTranslated : CoreTranslation.translateFuel graph fuel savedOwners body = .ok rawBody)
    (current : EnvCloses graph savedOwners base.heap environment
      (.resource identity (.integer payload) (.bind handle.id (.resourceRef (.bound identity)) rawBody))
      (.resource identity (.integer payload) (.bind handle.id (.resourceRef (.bound identity)) bodyCode)))
    (resourceReady : (Code.resource identity (.integer payload) (.bind handle.id (.resourceRef (.bound identity)) bodyCode)).ResourceClosed)
    (ready : ClosedExcept handle.id bodyCode) (scope : Scope) (answer : Ty)
    (tail : List CoreMachine.Frame) (target : Stack) :
    CoreMachine.next graph { base with control := .returned (.integer payload), frames := .resourceInitializer site identity handle body environment :: tail } =
      .stepped { base with control := .evaluate body (.binding handle.id (.handle base.nextActivation) (.resource identity base.nextActivation environment)), frames := .resourceBoundary site base.nextActivation payload :: tail, nextActivation := base.nextActivation + 1, observations := base.observations ++ [.acquired site base.nextActivation] } ∧
    RawStep ⟨.resource identity (.integer payload) (.bind handle.id (.resourceRef (.bound identity)) bodyCode), scope, target⟩
      ⟨.bind handle.id (.resourceRef (.activation base.nextActivation))
        (bodyCode.instantiate (Instantiation.Environment.empty.bind identity base.nextActivation)), scope,
        .push (.cell base.nextActivation payload scope answer) target⟩ [.resource base.nextActivation] [] ∧
    RawStep ⟨.bind handle.id (.resourceRef (.activation base.nextActivation))
        (bodyCode.instantiate (Instantiation.Environment.empty.bind identity base.nextActivation)), scope,
        .push (.cell base.nextActivation payload scope answer) target⟩
      ⟨(bodyCode.instantiate (Instantiation.Environment.empty.bind identity base.nextActivation)).subst handle.id
        (.resourceRef (.activation base.nextActivation)), scope, .push (.cell base.nextActivation payload scope answer) target⟩ [] [] ∧
    BoundaryRel graph savedOwners base.heap (.resourceBoundary site base.nextActivation payload)
      (.cell base.nextActivation payload scope answer) ∧
    EnvCloses graph savedOwners base.heap
      (.binding handle.id (.handle base.nextActivation) (.resource identity base.nextActivation environment)) rawBody
      ((bodyCode.instantiate (Instantiation.Environment.empty.bind identity base.nextActivation)).subst handle.id
        (.resourceRef (.activation base.nextActivation))) ∧
    CoreTranslation.translateFuel graph fuel savedOwners body = .ok rawBody := by
  obtain ⟨initializerSaved, opened⟩ := resource_body current base.nextActivation
  simp only [Code.instantiate, ResourceName.instantiate, Instantiation.Environment.bind, ↓reduceIte] at opened
  obtain ⟨handleSaved, bodySaved⟩ := CoreOrdinaryCompletion.bind_components opened
  have handleValue : ValueRel graph savedOwners base.heap (.handle base.nextActivation)
      (.resourceRef (.activation base.nextActivation)) := .handle
  have openedReady : ClosedExcept handle.id (bodyCode.instantiate (Instantiation.Environment.empty.bind identity base.nextActivation)) := by
    intro name member
    have bounded := acquisition_dependency_bound identity base.nextActivation bodyCode member
    rcases List.mem_append.mp bounded with old | fresh
    · exact ready name old
    · simp at fresh
  have enter := RawStep.enterCell identity base.nextActivation payload
    (.bind handle.id (.resourceRef (.bound identity)) bodyCode) scope answer target resourceReady
  simp only [Code.instantiate, ResourceName.instantiate, Instantiation.Environment.bind, ↓reduceIte] at enter
  exact ⟨rfl, enter, .bind handle.id _ _ scope _ handleValue.closed openedReady,
    .cell known kind, bodySaved.beta_argument handleValue, bodyTranslated⟩

/-- Normal handler return restores the exact boundary's supplied scope/map. -/
theorem handler_leave {base : CoreMachine.State}
    (_boundary : BoundaryRel graph savedOwners base.heap
      (.handlerBoundary site environment data.activation) (.handler data))
    (value : ValueRel graph codeOwners base.heap coreValue code)
    (runtimeScope : Scope) (tail : List CoreMachine.Frame) (target : Stack) :
    CoreMachine.next graph { base with control := .returned coreValue, frames := .handlerBoundary site environment data.activation :: tail } =
      .stepped { base with control := .returned coreValue, frames := tail } ∧
    RawStep ⟨code, runtimeScope, .push (.handler data) target⟩
      ⟨code, data.scope, target⟩ [] [] ∧
    ValueRel graph savedOwners base.heap coreValue code := by
  exact ⟨rfl, .leaveHandler data code value.closed runtimeScope target, value.owner_transport savedOwners⟩

/-- Normal cell return releases exactly its boundary identity and payload;
freshness/world validity and escape prevention are separate obligations. -/
theorem cell_leave {base : CoreMachine.State}
    (boundary : BoundaryRel graph savedOwners base.heap
      (.resourceBoundary site key payload) (.cell key payload scope answer))
    (value : ValueRel graph codeOwners base.heap coreValue code)
    (runtimeScope : Scope) (tail : List CoreMachine.Frame) (target : Stack) :
    CoreMachine.next graph { base with control := .returned coreValue, frames := .resourceBoundary site key payload :: tail } =
      .stepped { base with control := .returned coreValue, frames := tail, observations := base.observations ++ [.released key] } ∧
    RawStep ⟨code, runtimeScope, .push (.cell key payload scope answer) target⟩
      ⟨code, scope, target⟩ [] [.resource key] ∧
    ValueRel graph savedOwners base.heap coreValue code := by
  cases boundary
  exact ⟨rfl, .leaveCell key payload answer scope runtimeScope code value.closed target,
    value.owner_transport savedOwners⟩

#print axioms handler_leave
#print axioms cell_leave

/-- Exact handler entry composed with arbitrary explicit mapped tails. -/
theorem handler_enter_mapped {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .handler handlerId effect body clauses)
    (translated : CoreTranslation.translateFuel graph fuel owners site = .ok (.handle effect rawBody rawClauses))
    (bodyTranslated : CoreTranslation.translateFuel graph bodyFuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment (.handle effect rawBody rawClauses)
      (.handle (freezeEffect data.effectInst) bodyCode data.clauses))
    (activation : data.activation = base.nextHandler)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations { base with control := .evaluate site environment, frames := framesOf annotations }
      ⟨.handle (freezeEffect data.effectInst) bodyCode data.clauses, data.scope, target⟩ ∧
    CoreMachine.next graph { base with control := .evaluate site environment, frames := framesOf annotations } =
      .stepped { base with control := .evaluate body environment, frames := .handlerBoundary site environment data.activation :: framesOf annotations, nextHandler := base.nextHandler + 1, observations := base.observations ++ [.entered site, .handlerEntered site data.activation] } ∧
    RawStep ⟨.handle (freezeEffect data.effectInst) bodyCode data.clauses, data.scope, target⟩
      ⟨bodyCode, data.scope, .push (.handler data) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners, .handlerBoundary site environment data.activation) :: annotations)
      { base with control := .evaluate body environment, frames := .handlerBoundary site environment data.activation :: framesOf annotations, nextHandler := base.nextHandler + 1, observations := base.observations ++ [.entered site, .handlerEntered site data.activation] }
      ⟨bodyCode, data.scope, .push (.handler data) target⟩ := by
  obtain ⟨next, step, boundary, saved, instantiated, bodyTranslation⟩ :=
    handler_enter known kind translated bodyTranslated current activation (framesOf annotations) target
  exact ⟨⟨rfl, _, data.scope, .evaluate translated current, pushed_mapped older⟩,
    next, step, ⟨rfl, bodyCode, data.scope, .evaluate bodyTranslation saved, pushed_mapped (.boundary boundary older)⟩⟩

/-- Value-ready resource entry retains the identical target resource expression.
It derives initializer and saved body carrier from one current interpretation. -/
theorem resource_entry_same_target {base : CoreMachine.State}
    (ordered : CoreStrictPotential.Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .resource identity handle initializer body)
    (it : CoreTranslation.translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.resource identity rawInitializer (.bind handle.id (.resourceRef (.bound identity)) rawBody))
      (.resource identity initializerCode suffix))
    (ready : ClosedValue initializerCode) (plain : PlainData)
    (context : plain.context = .resource identity suffix)
    (older : PushedWithMaps graph base.heap annotations target) :
    CoreStrictPotential.SilentMapped graph owners owners annotations
      ((owners, .resourceInitializer site identity handle body environment) :: annotations)
      { base with control := .evaluate site environment, frames := framesOf annotations }
      { base with control := .evaluate initializer environment, frames := .resourceInitializer site identity handle body environment :: framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨.resource identity initializerCode suffix, plain.scope, target⟩ := by
  obtain ⟨initializerSaved, carrier⟩ := resource_components current
  have frame : InitializerRel graph owners base.heap (.resourceInitializer site identity handle body environment) plain :=
    .resource known kind bt carrier context
  have stack := prepend_initializer frame ready (pushed_mapped older) plain.scope
  simp only [context, Context.plug] at stack
  have translation : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.resource identity rawInitializer (.bind handle.id (.resourceRef (.bound identity)) rawBody)) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
      change (do pure (Code.resource identity (← CoreTranslation.translateFuel graph fuel owners initializer)
        (.bind handle.id (.resourceRef (.bound identity)) (← CoreTranslation.translateFuel graph fuel owners body)))) = _
      rw [it, bt]; rfl
  obtain ⟨next, decrease⟩ := CoreStrictPotential.resource_entry_decreases ordered known kind (framesOf annotations)
  exact ⟨next, decrease, by simp [CoreStrictPotential.traversalReady, known, kind],
    ⟨rfl, _, plain.scope, .evaluate translation current, pushed_mapped older⟩,
    ⟨rfl, initializerCode, plain.scope, .evaluate it initializerSaved, stack⟩⟩

/-- Acquisition from a ready flattened initializer builds the exact cell
boundary and restores its saved lexical map. Older map annotations persist. -/
theorem cell_acquire_mapped {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .resource identity handle initializer body)
    (bt : CoreTranslation.translateFuel graph fuel savedOwners body = .ok rawBody)
    (current : EnvCloses graph savedOwners base.heap environment
      (.resource identity (.integer payload) (.bind handle.id (.resourceRef (.bound identity)) rawBody))
      (.resource identity (.integer payload) (.bind handle.id (.resourceRef (.bound identity)) bodyCode)))
    (resourceReady : (Code.resource identity (.integer payload) (.bind handle.id (.resourceRef (.bound identity)) bodyCode)).ResourceClosed)
    (ready : ClosedExcept handle.id bodyCode)
    (plain : PlainData) (context : plain.context = .resource identity (.bind handle.id (.resourceRef (.bound identity)) bodyCode))
    (older : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope)
    (codeOwners : CoreTranslation.OwnerMap) (answer : Ty) :
    ComponentMapped graph codeOwners ((savedOwners, .resourceInitializer site identity handle body environment) :: annotations)
      { base with control := .returned (.integer payload), frames := .resourceInitializer site identity handle body environment :: framesOf annotations }
      ⟨.resource identity (.integer payload) (.bind handle.id (.resourceRef (.bound identity)) bodyCode), plain.scope, target⟩ ∧
    CoreMachine.next graph { base with control := .returned (.integer payload), frames := .resourceInitializer site identity handle body environment :: framesOf annotations } =
      .stepped { base with control := .evaluate body (.binding handle.id (.handle base.nextActivation) (.resource identity base.nextActivation environment)), frames := .resourceBoundary site base.nextActivation payload :: framesOf annotations, nextActivation := base.nextActivation + 1, observations := base.observations ++ [.acquired site base.nextActivation] } ∧
    RawStep ⟨.resource identity (.integer payload) (.bind handle.id (.resourceRef (.bound identity)) bodyCode), plain.scope, target⟩
      ⟨.bind handle.id (.resourceRef (.activation base.nextActivation)) (bodyCode.instantiate (Instantiation.Environment.empty.bind identity base.nextActivation)),
        plain.scope, .push (.cell base.nextActivation payload plain.scope answer) target⟩ [.resource base.nextActivation] [] ∧
    RawStep ⟨.bind handle.id (.resourceRef (.activation base.nextActivation)) (bodyCode.instantiate (Instantiation.Environment.empty.bind identity base.nextActivation)),
        plain.scope, .push (.cell base.nextActivation payload plain.scope answer) target⟩
      ⟨(bodyCode.instantiate (Instantiation.Environment.empty.bind identity base.nextActivation)).subst handle.id (.resourceRef (.activation base.nextActivation)),
        plain.scope, .push (.cell base.nextActivation payload plain.scope answer) target⟩ [] [] ∧
    ComponentMapped graph savedOwners ((savedOwners, .resourceBoundary site base.nextActivation payload) :: annotations)
      { base with control := .evaluate body (.binding handle.id (.handle base.nextActivation) (.resource identity base.nextActivation environment)), frames := .resourceBoundary site base.nextActivation payload :: framesOf annotations, nextActivation := base.nextActivation + 1, observations := base.observations ++ [.acquired site base.nextActivation] }
      ⟨(bodyCode.instantiate (Instantiation.Environment.empty.bind identity base.nextActivation)).subst handle.id (.resourceRef (.activation base.nextActivation)),
        plain.scope, .push (.cell base.nextActivation payload plain.scope answer) target⟩ := by
  obtain ⟨init, carrier⟩ := resource_components current
  have frame : InitializerRel graph savedOwners base.heap (.resourceInitializer site identity handle body environment) plain :=
    .resource known kind bt carrier context
  have value : ValueRel graph codeOwners base.heap (.integer payload) (.integer payload) := .integer
  have stack := prepend_initializer frame value.closed (pushed_mapped older) runtimeScope
  simp only [context, Context.plug] at stack
  obtain ⟨next, enter, bind, boundary, saved, bodyTranslation⟩ := cell_acquire known kind bt current resourceReady ready
    plain.scope answer (framesOf annotations) target
  exact ⟨⟨rfl, _, runtimeScope, .returned value, stack⟩, next, enter, bind,
    ⟨rfl, _, plain.scope, .evaluate bodyTranslation saved, pushed_mapped (.boundary boundary older)⟩⟩

#print axioms handler_enter_mapped
#print axioms resource_entry_same_target
#print axioms cell_acquire_mapped

theorem handler_leave_mapped {base : CoreMachine.State}
    (boundary : BoundaryRel graph savedOwners base.heap (.handlerBoundary site environment data.activation) (.handler data))
    (value : ValueRel graph codeOwners base.heap coreValue code)
    (older : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope) :
    ComponentMapped graph codeOwners ((savedOwners, .handlerBoundary site environment data.activation) :: annotations)
      { base with control := .returned coreValue, frames := .handlerBoundary site environment data.activation :: framesOf annotations }
      ⟨code, runtimeScope, .push (.handler data) target⟩ ∧
    CoreMachine.next graph { base with control := .returned coreValue, frames := .handlerBoundary site environment data.activation :: framesOf annotations } =
      .stepped { base with control := .returned coreValue, frames := framesOf annotations } ∧
    RawStep ⟨code, runtimeScope, .push (.handler data) target⟩ ⟨code, data.scope, target⟩ [] [] ∧
    ComponentMapped graph savedOwners annotations { base with control := .returned coreValue, frames := framesOf annotations }
      ⟨code, data.scope, target⟩ := by
  obtain ⟨next, step, saved⟩ := handler_leave boundary value runtimeScope (framesOf annotations) target
  exact ⟨⟨rfl, code, runtimeScope, .returned value, pushed_mapped (.boundary boundary older)⟩,
    next, step, ⟨rfl, code, data.scope, .returned saved, pushed_mapped older⟩⟩

theorem cell_leave_mapped {base : CoreMachine.State}
    (boundary : BoundaryRel graph savedOwners base.heap (.resourceBoundary site key payload) (.cell key payload savedScope answer))
    (value : ValueRel graph codeOwners base.heap coreValue code)
    (older : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope) :
    ComponentMapped graph codeOwners ((savedOwners, .resourceBoundary site key payload) :: annotations)
      { base with control := .returned coreValue, frames := .resourceBoundary site key payload :: framesOf annotations }
      ⟨code, runtimeScope, .push (.cell key payload savedScope answer) target⟩ ∧
    CoreMachine.next graph { base with control := .returned coreValue, frames := .resourceBoundary site key payload :: framesOf annotations } =
      .stepped { base with control := .returned coreValue, frames := framesOf annotations, observations := base.observations ++ [.released key] } ∧
    RawStep ⟨code, runtimeScope, .push (.cell key payload savedScope answer) target⟩ ⟨code, savedScope, target⟩ [] [.resource key] ∧
    ComponentMapped graph savedOwners annotations
      { base with control := .returned coreValue, frames := framesOf annotations, observations := base.observations ++ [.released key] }
      ⟨code, savedScope, target⟩ := by
  obtain ⟨next, step, saved⟩ := cell_leave boundary value runtimeScope (framesOf annotations) target
  exact ⟨⟨rfl, code, runtimeScope, .returned value, pushed_mapped (.boundary boundary older)⟩,
    next, step, ⟨rfl, code, savedScope, .returned saved, pushed_mapped older⟩⟩

#print axioms handler_leave_mapped
#print axioms cell_leave_mapped

/-- A noninteger initializer is rejected, not represented as progress. -/
theorem cell_rejects_unit (graph : CoreSyntax.Graph) (base : CoreMachine.State)
    (site identity body : Nat) (handle : CoreSyntax.Binder) (environment : MEnv) (tail : List CoreMachine.Frame) :
    CoreMachine.next graph { base with control := .returned .unit, frames := .resourceInitializer site identity handle body environment :: tail } =
      .rejected .nonInteger := rfl

namespace Exported
open CoreExportedFixture
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private def rawBody : Code := (CoreTranslation.translateFuel graph 56 [] 47).toOption.getD .unit
private def suffix : Code := .bind 4 (.resourceRef (.bound 0)) rawBody
private def resourceCode : Code := .resource 0 (.integer 0) suffix
private def called : MEnv := .binding 0 .unit (.functionTemplate 13 0 49 .empty)
private def plain : PlainData := ⟨.resource 0 suffix, .none, .integer, .integer, [], rfl⟩
private def initializer : CoreMachine.Frame := .resourceInitializer 48 0 ⟨4, .reference (.bound 0)⟩ 47 called
private def node : CoreSyntax.Node :=
  ⟨47, .integer, [], some ⟨1, 1, 98, 548⟩, .resource 0 ⟨4, .reference (.bound 0)⟩ 1 47⟩
private def base : CoreMachine.State := { control := .evaluate 48 called, nextActivation := 7 }
private def focused (annotations : List MappedFrame) : CoreMachine.State :=
  { base with control := .evaluate 1 called, frames := initializer :: framesOf annotations, observations := [.entered 48] }
private def returned (annotations : List MappedFrame) : CoreMachine.State :=
  { base with control := .returned (.integer 0), frames := initializer :: framesOf annotations, observations := [.entered 48, .entered 1] }
private def acquired (annotations : List MappedFrame) : CoreMachine.State :=
  { base with control := .evaluate 47 (.binding 4 (.handle 7) (.resource 0 7 called)), frames := .resourceBoundary 48 7 0 :: framesOf annotations, nextActivation := 8, observations := [.entered 48, .entered 1, .acquired 48 7] }
private def middle (target : Stack) : Configuration :=
  ⟨.bind 4 (.resourceRef (.activation 7)) (rawBody.instantiate (Instantiation.Environment.empty.bind 0 7)),
    .none, .push (.cell 7 0 .none .integer) target⟩
private def result (target : Stack) : Configuration :=
  ⟨(rawBody.instantiate (Instantiation.Environment.empty.bind 0 7)).subst 4 (.resourceRef (.activation 7)),
    .none, .push (.cell 7 0 .none .integer) target⟩

private theorem current : EnvCloses graph [] [] called resourceCode resourceCode := by
  apply EnvCloses.binding ValueRel.unit
  rw [ScopedTyping.subst_absent resourceCode 0 .unit (by decide)]
  exact .templateUnused (by decide) .empty

private theorem bodyReady : ClosedExcept 4 rawBody := by
  have supported : rawBody.dependencies.all (fun dep => match dep with | .variable name => name == 4 | _ => true) = true := by decide
  intro name member
  have accepted := List.all_eq_true.mp supported (.variable name) member
  simpa using accepted

/-- The exported resource48's already-value initializer still performs actual
Core entry and integer evaluation. Its identical target then acquires exact
key7 and completes the generated handle bind, retaining arbitrary older maps.
This prefix enters body47 toward handler41; no suffix execution is assumed. -/
theorem acquisition_prefix (older : PushedWithMaps graph [] annotations target) :
    CoreStrictPotential.SilentMapped graph [] [] annotations (([], initializer) :: annotations)
      { base with frames := framesOf annotations } (focused annotations) ⟨resourceCode, .none, target⟩ ∧
    CoreAdministrativeTransport.TransportMapped graph [] [] (([], initializer) :: annotations) (([], initializer) :: annotations)
      (focused annotations) (returned annotations) ⟨resourceCode, .none, target⟩ ∧
    CoreMachine.next graph (returned annotations) = .stepped (acquired annotations) ∧
    RawStep ⟨resourceCode, .none, target⟩ (middle target) [.resource 7] [] ∧
    RawStep (middle target) (result target) [] [] ∧
    ComponentMapped graph [] (([], .resourceBoundary 48 7 0) :: annotations) (acquired annotations) (result target) := by
  have ordered := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl
  have entry := resource_entry_same_target (base := base) (owners := []) (fuel := 56)
    (site := 48) (node := node) (identity := 0) (handle := ⟨4, .reference (.bound 0)⟩) (initializer := 1) (body := 47)
    (rawInitializer := .integer 0) (rawBody := rawBody) (initializerCode := .integer 0) (suffix := suffix)
    ordered rfl rfl rfl rfl current
    (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := 0)).closed plain rfl older
  obtain ⟨init, carrier⟩ := resource_components current
  have frame : InitializerRel graph [] [] initializer plain :=
    .resource (site := 48) (node := node) (fuel := 56) rfl rfl rfl carrier rfl
  have stack := prepend_initializer frame
    (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := 0)).closed
    (pushed_mapped older) Execution.Scope.none
  obtain ⟨witness, translated⟩ := CoreAdministrativeSteps.integer_evaluate
    (base := { base with observations := [.entered 48] }) (graph := graph) (owners := [])
    (index := 1) (node := ⟨0, .integer, [], some ⟨1, 1, 119, 120⟩, .integer 0⟩)
    rfl rfl init (initializer :: framesOf annotations)
  have transport := CoreAdministrativeTransport.value_entry_mapped witness rfl rfl stack
  obtain ⟨before, next, enter, bind, after⟩ := cell_acquire_mapped
    (base := returned annotations) (graph := graph) (savedOwners := []) (codeOwners := [])
    (site := 48) (node := node) (identity := 0) (handle := ⟨4, .reference (.bound 0)⟩)
    (initializer := 1) (body := 47) (fuel := 56) (rawBody := rawBody) (bodyCode := rawBody)
    (payload := 0) rfl rfl rfl current (by change resourceCode.freeNames = []; decide) bodyReady plain rfl older Execution.Scope.none Ty.integer
  exact ⟨entry, transport, next, enter, bind, after⟩

end Exported
#print axioms Exported.acquisition_prefix

#print axioms handler_enter
#print axioms cell_acquire
#print axioms cell_rejects_unit
end Ash.OneShot.CoreEffectEntry
