import CoreStrictPotential
import CoreCleanupEntry

/-! Exact first-user-request capture components. Static annotations, allocation
freshness and whole-state validity are separate obligations. No error outcome
is a transition, and saved captures are recursively related. -/
namespace Ash.OneShot.CoreCaptureEntry
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreEffectFrames
  CoreCleanupFrames CoreRequestFrames CoreStrictStack CoreStrictPotential Instantiation

private theorem freeze_injective (same : freezeEffect left = freezeEffect right) : left = right := by
  exact effect_realization_unique (same ▸ frozen_effect_realizes Instantiation.Environment.empty left)
    (frozen_effect_realizes Instantiation.Environment.empty right)

/-- Union of existing exact pushed-frame carriers, excluding owner boundaries.
This does not introduce a second expression or environment interpretation. -/
inductive PushCarrier (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap) (heap : Heap) :
    CoreMachine.Frame → ExecFrame → Prop where
  | ordinary (related : PlainFrameRel graph owners heap core plain) : PushCarrier graph owners heap core (.plain plain)
  | initializer (related : InitializerRel graph owners heap core plain) : PushCarrier graph owners heap core (.plain plain)
  | request (related : RequestRel graph owners heap core plain) : PushCarrier graph owners heap core (.plain plain)
  | resume (related : CoreResumeFrames.ResumeRel graph owners heap core plain) : PushCarrier graph owners heap core (.plain plain)
  | cleanup (related : CleanupRel graph owners heap core data) : PushCarrier graph owners heap core (.armed data)
  | boundary (related : BoundaryRel graph owners heap core frame) : PushCarrier graph owners heap core frame

theorem PushCarrier.prepend (related : PushCarrier graph owners heap core frame)
    (tail : PushedWithMaps graph heap annotations target) :
    PushedWithMaps graph heap ((owners, core) :: annotations) (.push frame target) := by
  cases related with
  | ordinary related => exact .cons related tail
  | initializer related => exact .initializer related tail
  | request related => exact .request related tail
  | resume related => exact .resume related tail
  | cleanup related => exact .cleanup related tail
  | boundary related => exact .boundary related tail

set_option linter.unusedSimpArgs false in
/-- A target miss certifies the actual Core nearest-selector miss. In
particular a cell boundary is never passed for its matching cell effect. -/
theorem PushCarrier.selector_miss (related : PushCarrier graph owners heap core frame)
    (miss : frame.erase.target ≠ some requested)
    (next : CoreMachine.findInterpreter graph (freezeEffect requested) outside =
      .ok (.handler inside site environment occurrence tail)) :
    CoreMachine.findInterpreter graph (freezeEffect requested) (core :: outside) =
      .ok (.handler (core :: inside) site environment occurrence tail) := by
  cases related with
  | ordinary related =>
      rename_i plain
      change FrameRel graph owners heap core plain.context at related
      generalize contextEq : plain.context = context at related
      cases related <;> simp [CoreMachine.findInterpreter, next, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | initializer related => cases related; simp [CoreMachine.findInterpreter, next, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | request related => cases related; simp [CoreMachine.findInterpreter, next, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | resume related => cases related; simp [CoreMachine.findInterpreter, next, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | cleanup related => cases related; simp [CoreMachine.findInterpreter, next, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | boundary related =>
      cases related with
      | @handler site node handlerId effect body clauses fuel rawBody rawClauses saved data known kind translated header =>
          have actual := handle_effect_at header _ _ _ _ _ _ rfl rfl
          have different : freezeEffect requested ≠ freezeEffect data.effectInst := by
            intro same
            apply miss
            simp only [ExecFrame.erase, HandlerData.erase, Frame.target]
            exact congrArg some (freeze_injective same).symm
          simp only [CoreMachine.findInterpreter, known, kind, actual]
          simp [different, next, Bind.bind, Except.bind, Pure.pure, Except.pure]
      | @cell site node identity handle initializer body key payload scope answer known kind =>
          have different : freezeEffect requested ≠ Effect.cell (.activation key) := by
            intro same
            apply miss
            simp only [ExecFrame.erase, Frame.target]
            exact congrArg some (freeze_injective same).symm
          simp [CoreMachine.findInterpreter, different, next, Bind.bind, Except.bind, Pure.pure, Except.pure]

set_option linter.unusedSimpArgs false in
private theorem handler_selector_hit
    (related : BoundaryRel graph owners heap core targetFrame) :
    ∀ site environment occurrence data,
      core = .handlerBoundary site environment occurrence → targetFrame = .handler data →
      data.effectInst = requested →
      CoreMachine.findInterpreter graph (freezeEffect requested) (.handlerBoundary site environment occurrence :: outside) =
        .ok (.handler [] site environment occurrence outside) := by
  cases related with
  | handler known kind translated header =>
      intro site environment occurrence data sourceEq targetEq same
      cases targetEq
      have parts : _ := CoreMachine.Frame.handlerBoundary.inj sourceEq
      rcases parts with ⟨rfl, rfl, rfl⟩
      have actual := handle_effect_at header _ _ _ _ _ _ rfl rfl
      simp [CoreMachine.findInterpreter, known, kind, actual, same, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | cell known kind => intro site environment occurrence data sourceEq; cases sourceEq

/-- Structural simultaneous cut. Each saved and outside segment remains
recursively related; dormant captures are preserved but not searched. -/
inductive MappedHandlerCut (graph : CoreSyntax.Graph) (heap : Heap) (requested : Instance) :
    List MappedFrame → Stack → List MappedFrame → CoreTranslation.OwnerMap → Nat → CoreMachine.Environment →
      HandlerData → List MappedFrame → Stack → Stack → Prop where
  | hit (header : BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data))
      (same : data.effectInst = requested)
      (outside : PushedWithMaps graph heap outsideMaps outsideTarget) :
      MappedHandlerCut graph heap requested ((owners, .handlerBoundary site environment data.activation) :: outsideMaps)
        (.push (.handler data) outsideTarget) [] owners site environment data outsideMaps
        (.push (.handler data) .nil) outsideTarget
  | push (frame : PushCarrier graph owners heap core targetFrame)
      (miss : targetFrame.erase.target ≠ some requested)
      (next : MappedHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
      MappedHandlerCut graph heap requested ((owners, core) :: whole) (.push targetFrame target)
        ((owners, core) :: inside) savedOwners site environment data outside (.push targetFrame cap) tail
  | live (header : OwnerHeader graph owners heap handler owner occurrence oldData)
      (saved : PushedWithMaps graph heap savedMaps savedTarget)
      (next : MappedHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
      MappedHandlerCut graph heap requested
        ((owners, .clauseBoundary handler owner occurrence ticket (some (framesOf savedMaps))) :: whole)
        (.live ticket result oldData.answer savedTarget oldData.scope target)
        ((owners, .clauseBoundary handler owner occurrence ticket (some (framesOf savedMaps))) :: inside)
        savedOwners site environment data outside (.live ticket result oldData.answer savedTarget oldData.scope cap) tail
  | spent (header : OwnerHeader graph owners heap handler owner occurrence oldData)
      (next : MappedHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
      MappedHandlerCut graph heap requested
        ((owners, .clauseBoundary handler owner occurrence ticket none) :: whole)
        (.spent ticket oldData.answer oldData.scope target)
        ((owners, .clauseBoundary handler owner occurrence ticket none) :: inside)
        savedOwners site environment data outside (.spent ticket oldData.answer oldData.scope cap) tail

set_option linter.unusedSimpArgs false in
theorem MappedHandlerCut.realizes
    (cut : MappedHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
    CoreMachine.findInterpreter graph (freezeEffect requested) (framesOf whole) =
      .ok (.handler (framesOf inside) site environment data.activation (framesOf outside)) ∧
    HandlerCut requested target cap tail data ∧
    PushedWithMaps graph heap whole target ∧
    PushedWithMaps graph heap (inside ++ [(savedOwners, .handlerBoundary site environment data.activation)]) cap ∧
    PushedWithMaps graph heap outside tail := by
  induction cut with
  | hit header same outside =>
      exact ⟨handler_selector_hit header _ _ _ _ rfl rfl same, .hit _ _ same,
        .boundary header outside, .boundary header .nil, outside⟩
  | push frame miss next ih =>
      rcases ih with ⟨core, target, whole, cap, outside⟩
      exact ⟨by simpa only [framesOf_cons] using PushCarrier.selector_miss frame miss core,
        .push _ _ _ _ _ miss target, frame.prepend whole, frame.prepend cap, outside⟩
  | live header saved next ih =>
      rcases ih with ⟨core, target, whole, cap, outside⟩
      exact ⟨by simp [framesOf_cons, CoreMachine.findInterpreter, core, Bind.bind, Except.bind, Pure.pure, Except.pure], .live _ _ _ _ _ _ _ _ _ target,
        .live header saved whole, .live header saved cap, outside⟩
  | spent header next ih =>
      rcases ih with ⟨core, target, whole, cap, outside⟩
      exact ⟨by simp [framesOf_cons, CoreMachine.findInterpreter, core, Bind.bind, Except.bind, Pure.pure, Except.pure], .spent _ _ _ _ _ _ _ target,
        .spent header whole, .spent header cap, outside⟩

/-- A non-value request operand uses the actual positive focus rule. Its saved
effect carrier and child interpretation are projected from one current close. -/
theorem request_focus_mapped {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .request effect operation operand)
    (translated : CoreTranslation.translateFuel graph fuel owners operand = .ok raw)
    (current : EnvCloses graph owners base.heap environment (.perform effect operation raw)
      (.perform (freezeEffect requested) operation code))
    (notValue : ¬ code.IsValue) (plain : PlainData)
    (context : plain.context = .perform (freezeEffect requested) operation)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      { base with control := .evaluate site environment, frames := framesOf annotations }
      ⟨.perform (freezeEffect requested) operation code,plain.scope,target⟩ ∧
    CoreMachine.next graph { base with control := .evaluate site environment, frames := framesOf annotations } =
      .stepped { base with control := .evaluate operand environment, frames := .request effect operation environment :: framesOf annotations, observations := base.observations ++ [.entered site] } ∧
    RawStep ⟨.perform (freezeEffect requested) operation code,plain.scope,target⟩
      ⟨code,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.request effect operation environment) :: annotations)
      { base with control := .evaluate operand environment, frames := .request effect operation environment :: framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨code,plain.scope,.push (.plain plain) target⟩ := by
  have siteTranslation : CoreTranslation.translateFuel graph (fuel + 1) owners site = .ok (.perform effect operation raw) := by
    rw [CoreTranslation.request_equation graph owners fuel site node effect operation operand known kind, translated]; rfl
  have carrier := perform_header_at current _ _ _ _ _ rfl rfl
  have child := (perform_components current).2
  have frame : RequestRel graph owners base.heap (.request effect operation environment) plain := .operand carrier context
  have focus : Focus (.perform (freezeEffect requested) operation code) code plain.context := by
    rw [context]; exact .perform notValue
  exact ⟨⟨rfl,_,plain.scope,.evaluate siteTranslation current,pushed_mapped older⟩,
    (request_entry_decreases (base := base) ordered known kind (framesOf annotations)).1,
    .focus plain focus target, ⟨rfl,_,plain.scope,.evaluate translated child,pushed_mapped (.request frame older)⟩⟩

#print axioms request_focus_mapped

theorem MappedHandlerCut.header
    (cut : MappedHandlerCut graph heap requested whole target inside owners site environment data outside cap tail) :
    BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data) := by
  induction cut with
  | hit header same outside => exact header
  | push frame miss next ih | live header saved next ih | spent header next ih => exact ih

/-- Successful capture constructs the clause environment and the live owner
from existing current witnesses. Readiness is a current selected-clause static
obligation; it is not validity of a desired successor. -/
theorem capture_mapped {graph : CoreSyntax.Graph} {base : CoreMachine.State}
    (cut : MappedHandlerCut graph base.heap requested whole target inside savedOwners site environment data outside cap tail)
    (known : graph.node site = some node)
    (kind : node.kind = .handler handler handled handlerBody clauses)
    (selected : clauses.find? (fun clause => clause.operation == operation) = some clause)
    (operand : ValueRel graph operandOwners base.heap value operandCode)
    (requestCarrier : EnvCloses graph operandOwners base.heap requestEnvironment
      (.perform effect operation .unit) (.perform (freezeEffect requested) operation .unit))
    (plain : PlainData) (context : plain.context = .perform (freezeEffect requested) operation)
    (ready : ∀ parameter binder body, ClauseAt operation data.clauses parameter binder body → ClosedExcept parameter body)
    (operationResult : Ty) (runtimeScope : Scope) :
    ∃ fuel argument rawBody body,
      clause.argument = .binder argument ∧
      ClauseAt operation data.clauses argument.id (CoreTranslation.ticket graph clause.owner) body ∧
      CoreTranslation.translateFuel graph fuel
        (⟨handler, clause.owner, CoreTranslation.ticket graph clause.owner⟩ :: savedOwners) clause.body = .ok rawBody ∧
      ComponentMapped graph operandOwners ((operandOwners, .request effect operation requestEnvironment) :: whole)
        { base with control := .returned value, frames := .request effect operation requestEnvironment :: framesOf whole }
        ⟨.perform (freezeEffect requested) operation operandCode, plain.scope, target⟩ ∧
      CoreMachine.next graph
        { base with control := .returned value, frames := .request effect operation requestEnvironment :: framesOf whole } =
        .stepped { base with control := .evaluate clause.body (.binding argument.id value environment), frames := .clauseBoundary handler clause.owner data.activation base.nextOwner (some (framesOf inside ++ [.handlerBoundary site environment data.activation])) :: framesOf outside, nextOwner := base.nextOwner + 1, observations := base.observations ++ [.captured data.activation base.nextOwner] } ∧
      RawStep ⟨.perform (freezeEffect requested) operation operandCode, plain.scope, target⟩
        ⟨body.subst argument.id operandCode, .ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner,
          .live base.nextOwner operationResult data.answer cap data.scope tail⟩ [.ticket base.nextOwner] [] ∧
      ComponentMapped graph (⟨handler, clause.owner, CoreTranslation.ticket graph clause.owner⟩ :: savedOwners)
        ((savedOwners, .clauseBoundary handler clause.owner data.activation base.nextOwner
          (some (framesOf (inside ++ [(savedOwners, .handlerBoundary site environment data.activation)])))) :: outside)
        { base with control := .evaluate clause.body (.binding argument.id value environment), frames := .clauseBoundary handler clause.owner data.activation base.nextOwner (some (framesOf inside ++ [.handlerBoundary site environment data.activation])) :: framesOf outside, nextOwner := base.nextOwner + 1, observations := base.observations ++ [.captured data.activation base.nextOwner] }
        ⟨body.subst argument.id operandCode, .ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner,
          .live base.nextOwner operationResult data.answer cap data.scope tail⟩ := by
  obtain ⟨selector, targetCut, currentStack, capturedStack, outsideStack⟩ := cut.realizes
  have header := cut.header
  generalize coreEq : CoreMachine.Frame.handlerBoundary site environment data.activation = core at header
  generalize targetEq : ExecFrame.handler data = targetFrame at header
  cases header with
  | @handler savedSite savedNode handlerId rawEffect bodyIndex rawDeclarations handlerFuel rawHandlerBody rawClauses savedEnv savedData found shape translated closing =>
    have dataEq : data = savedData := ExecFrame.handler.inj targetEq
    cases dataEq
    have fields := CoreMachine.Frame.handlerBoundary.inj coreEq
    rcases fields with ⟨rfl,rfl,_⟩
    have nodeEq : node = savedNode := Option.some.inj (known.symm.trans found)
    cases nodeEq
    have kindEq : CoreSyntax.Kind.handler handler handled handlerBody clauses =
        .handler handlerId rawEffect bodyIndex rawDeclarations := kind.symm.trans shape
    cases kindEq
    obtain ⟨fuel, argument, rawBody, pattern, bodyTranslation, rawSelection⟩ :=
      handler_selected_translation found shape translated selected
    obtain ⟨body, selection, masked⟩ := selected_clause_at closing _ _ _ _ _ _ _ _ rfl rfl rawSelection
    have clauseEnvironment := (masked.owner_transport
      (⟨handler, clause.owner, CoreTranslation.ticket graph clause.owner⟩ :: savedOwners)).beta_argument
      (operand.owner_transport _)
    have member : clause ∈ clauses := List.mem_of_find?_eq_some selected
    have operationEq : clause.operation = operation := by simpa using List.find?_some selected
    have ownerHeader : OwnerHeader graph savedOwners base.heap handler clause.owner data.activation data :=
      .selected found shape member rfl (.handler found shape translated closing) rfl (operationEq ▸ selection)
    have requestFrame : RequestRel graph operandOwners base.heap (.request effect operation requestEnvironment) plain :=
      .operand requestCarrier context
    have beforeStack := prepend_request requestFrame operand.closed (pushed_mapped currentStack) runtimeScope
    simp only [context, Context.plug] at beforeStack
    have instantiated := (perform_components requestCarrier).1
    have coreNext : CoreMachine.next graph
        { base with control := .returned value, frames := .request effect operation requestEnvironment :: framesOf whole } =
        .stepped { base with control := .evaluate clause.body (.binding argument.id value environment), frames := .clauseBoundary handler clause.owner data.activation base.nextOwner (some (framesOf inside ++ [.handlerBoundary site environment data.activation])) :: framesOf outside, nextOwner := base.nextOwner + 1, observations := base.observations ++ [.captured data.activation base.nextOwner] } := by
      simp only [CoreMachine.next, CoreMachine.request, instantiated]
      cases node with
      | mk original type effects source nodeKind =>
        cases shape
        cases requested <;> simp only [freezeEffect] at selector ⊢
        all_goals simp only [selector, found, selected, pattern]
    refine ⟨fuel, argument, rawBody, body, pattern, selection, bodyTranslation,
      ⟨rfl, operandCode, runtimeScope, .returned operand, beforeStack⟩, coreNext,
      .capture _ _ _ _ _ _ _ _ _ _ _ _ _ targetCut selection operand.closed (ready _ _ _ selection), ?_⟩
    refine ⟨?_, _, _, .evaluate bodyTranslation clauseEnvironment,
      pushed_mapped (.live ownerHeader capturedStack outsideStack)⟩
    simp [framesOf, List.map_append]
  | cell found shape => cases coreEq

namespace Exported
open CoreExportedFixture CoreInitialPrefix CoreHandlerPrefix CoreCleanupEntry CoreOrdinaryCompletion CoreAdministrativeTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0,.unit,[],none,.unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl
private theorem translation_unique
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok rawCode)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok otherRaw) : rawCode = otherRaw := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index rawCode (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index otherRaw (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

private theorem cleanup_head_pushed
    (related : OrdinaryWithMaps graph heap ((owners,.cleanupBoundary action saved identity) :: rest)
      code scope result resultScope target) :
    code = result ∧ scope = resultScope ∧
      PushedWithMaps graph heap ((owners,.cleanupBoundary action saved identity) :: rest) target := by
  obtain ⟨flatPrefix,suffix,split,flat,pushed⟩ := related
  cases flat with
  | nil => exact ⟨rfl,rfl,split.symm ▸ pushed⟩
  | @cons frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .cleanupBoundary action saved identity := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same
      cases frame
  | @initializer frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .cleanupBoundary action saved identity := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same
      cases frame
  | @request frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .cleanupBoundary action saved identity := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same
      cases frame
  | @resume frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .cleanupBoundary action saved identity := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same
      cases frame

private theorem current_guarded : EnvCloses graph [] [] callbackEnv (raw 24) guardedCode ∧
    PushedWithMaps graph [] r24.annotations guardedTarget.stack := by
  obtain ⟨shape,code,scope,control,stack⟩ := reached_guarded_related
  change OrdinaryWithMaps graph []
    (([],.cleanupBoundary 27 callbackEnv 0) :: q20.annotations)
    code scope guardedCode .none guardedTarget.stack at stack
  obtain ⟨rfl,rfl,pushed⟩ := cleanup_head_pushed stack
  cases control with
  | evaluate translated saved =>
      have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 24 = .ok (raw 24))
      cases same
      exact ⟨saved,pushed⟩

def suffix : Code := (close2 (raw 23)).subst 8 callbackCode
def bindPlain : PlainData := ⟨.bind 7 suffix,.none,.unit,.unit,[],by decide⟩
def performPlain : PlainData := ⟨.perform (.user 0 []) 0,.none,.boolean,.unit,[],rfl⟩
def s25 : CoreMachine.State := { s24 with control := .evaluate 15 callbackEnv, frames := .bind 7 23 callbackEnv :: s24.frames, observations := s24.observations ++ [.entered 24] }
def s26 : CoreMachine.State := { s25 with control := .evaluate 14 callbackEnv, frames := .request (.user 0 []) 0 callbackEnv :: s25.frames, observations := s25.observations ++ [.entered 15] }
def s27 : CoreMachine.State := { s26 with control := .returned (.boolean true), observations := s26.observations ++ [.entered 14] }
def requestTarget : Configuration := ⟨.perform (.user 0 []) 0 (.boolean true),.none,.push (.plain bindPlain) guardedTarget.stack⟩
def t25 : Point := ⟨s25,requestTarget,[],([], .bind 7 23 callbackEnv) :: r24.annotations⟩
def t26 : Point := ⟨s26,requestTarget,[],([], .request (.user 0 []) 0 callbackEnv) :: t25.annotations⟩
def t27 : Point := ⟨s27,requestTarget,[],t26.annotations⟩

private theorem suffixReady : ClosedExcept 7 suffix := by
  have bound : suffix.dependencies.all (fun dep => match dep with | .variable n => n == 7 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp bound (.variable n) member

private theorem focus_bind : Link graph r24 t25 ∧
    EnvCloses graph [] [] callbackEnv (raw 15) (.perform (.user 0 []) 0 (.boolean true)) ∧
    PushedWithMaps graph [] t25.annotations requestTarget.stack := by
  have whole : EnvCloses graph [] [] callbackEnv
      (.bind 7 (raw 15) (raw 23)) (.bind 7 (.perform (.user 0 []) 0 (.boolean true)) suffix) := current_guarded.1
  obtain ⟨operand, suffixSaved⟩ := bind_components whole
  have frame : PlainFrameRel graph [] [] (.bind 7 23 callbackEnv) bindPlain :=
    .bind (rfl : CoreTranslation.translateFuel graph 56 [] 23 = .ok (raw 23)) suffixSaved suffixReady
  have after : Related graph t25 := ⟨rfl,_,.none,.evaluate (fuel := 56) rfl operand,
    pushed_mapped (.cons frame current_guarded.2)⟩
  have focus : RawStep guardedTarget requestTarget [] [] := .focus bindPlain (.bind (by simp [Code.subst, Code.instantiate, Code.IsValue])) guardedTarget.stack
  exact ⟨.positive reached_guarded_related rfl (.one focus) after,operand,.cons frame current_guarded.2⟩

private theorem requestTraversal : SilentMapped graph [] [] t25.annotations t26.annotations s25 s26 requestTarget := by
  exact (request_entry_same_target_mapped (base := s25) (environment := callbackEnv)
    (requested := .user 0 []) (code := .boolean true) (annotations := t25.annotations) ordered
    (rfl : graph.node 15 = some (node 15)) rfl (rfl : CoreTranslation.translateFuel graph 56 [] 14 = .ok (.boolean true))
    focus_bind.2.1 (ValueRel.boolean (graph := graph) (owners := []) (heap := []) (value := true)).closed
    performPlain rfl focus_bind.2.2)

private theorem request_entry : Link graph t25 t26 := .traversal requestTraversal

private theorem operandReturn : Link graph t26 t27 := by
  have saved := (perform_components focus_bind.2.1).2
  obtain ⟨witness, translated⟩ := CoreAdministrativeSteps.boolean_evaluate (base := s26)
    (rfl : graph.node 14 = some (node 14)) rfl saved s26.frames
  have carrier : EnvCloses graph [] [] callbackEnv (.perform (.user 0 []) 0 .unit) (.perform (.user 0 []) 0 .unit) :=
    perform_header_at focus_bind.2.1 _ _ _ _ _ rfl rfl
  have frame : RequestRel graph [] [] (.request (.user 0 []) 0 callbackEnv) performPlain :=
    .operand (requested := .user 0 []) carrier rfl
  have stack := prepend_request frame (ValueRel.boolean (graph := graph) (owners := []) (heap := []) (value := true)).closed
    (pushed_mapped focus_bind.2.2) .none
  exact .value (value_entry_mapped witness rfl rfl stack)

private theorem pushed_head
    (related : PushedWithMaps graph heap ((owners, core) :: rest) (.push frame target)) :
    PushCarrier graph owners heap core frame ∧ PushedWithMaps graph heap rest target := by
  cases related with
  | cons relation tail => exact ⟨.ordinary relation,tail⟩
  | initializer relation tail => exact ⟨.initializer relation,tail⟩
  | request relation tail => exact ⟨.request relation,tail⟩
  | resume relation tail => exact ⟨.resume relation,tail⟩
  | cleanup relation tail => exact ⟨.cleanup relation,tail⟩
  | boundary relation tail => exact ⟨.boundary relation,tail⟩

private theorem selected_cut :
    MappedHandlerCut graph [] (.user 0 []) t25.annotations requestTarget.stack
      [([],.bind 7 23 callbackEnv),([],.cleanupBoundary 27 callbackEnv 0)] [] 41 methodsEnv handlerData
      [([],.bind 12 44 methodsEnv),([],.resourceBoundary 48 0 0)]
      (.push (.plain bindPlain) (.push (.armed actionData) (.push (.handler handlerData) .nil)))
      (.push (.plain handlerPlain) cell) := by
  obtain ⟨bindFrame,rest⟩ := pushed_head focus_bind.2.2
  obtain ⟨cleanupFrame,rest⟩ := pushed_head rest
  change PushedWithMaps graph []
    [([],.handlerBoundary 41 methodsEnv 0),([],.bind 12 44 methodsEnv),([],.resourceBoundary 48 0 0)]
    (.push (.handler handlerData) (.push (.plain handlerPlain) cell)) at rest
  obtain ⟨handlerFrame,rest⟩ := pushed_head rest
  cases handlerFrame with
  | boundary header =>
    exact .push bindFrame (by simp [ExecFrame.erase,PlainData.erase,Frame.target])
      (.push cleanupFrame (by simp [ExecFrame.erase,ActionData.erase,Frame.target]) (.hit (site := 41) (environment := methodsEnv) (data := handlerData) (owners := []) header rfl rest))

private theorem clause_unique {clauses : Clauses}
    (first : ClauseAt operation clauses parameter binder body)
    (second : ClauseAt operation clauses otherParameter otherBinder otherBody) :
    parameter = otherParameter ∧ binder = otherBinder ∧ body = otherBody := by
  induction first with
  | hit => cases second with
    | hit => exact ⟨rfl,rfl,rfl⟩
    | pass different next => exact False.elim (different rfl)
  | pass different next ih => cases second with
    | hit => exact False.elim (different rfl)
    | pass otherDifferent otherNext => exact ih otherNext

def firstClauseBody : Code := match handlerData.clauses with
  | .cons _ _ _ body _ => body
  | .nil => .unit
private theorem firstSelection : ClauseAt 0 handlerData.clauses 9 (CoreTranslation.ticket graph 0) firstClauseBody := .hit
private theorem firstReady : ClosedExcept 9 firstClauseBody := by
  have bound : firstClauseBody.dependencies.all (fun dep => match dep with | .variable n => n == 9 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp bound (.variable n) member

def clauseMaps : CoreTranslation.OwnerMap := [⟨0,0,CoreTranslation.ticket graph 0⟩]
def capturedMaps : List MappedFrame :=
  [([],.bind 7 23 callbackEnv),([],.cleanupBoundary 27 callbackEnv 0),([],.handlerBoundary 41 methodsEnv 0)]
def outsideMaps : List MappedFrame := [([],.bind 12 44 methodsEnv),([],.resourceBoundary 48 0 0)]
def capturedTarget : Stack := .push (.plain bindPlain) (.push (.armed actionData) (.push (.handler handlerData) .nil))
def clauseTarget : Configuration := ⟨firstClauseBody.subst 9 (.boolean true),.ticket (CoreTranslation.ticket graph 0) 0,
  .live 0 .unit .unit capturedTarget .none (.push (.plain handlerPlain) cell)⟩
def s28 : CoreMachine.State := { s27 with control := .evaluate 40 (.binding 9 (.boolean true) methodsEnv), frames := .clauseBoundary 0 0 0 0 (some (framesOf capturedMaps)) :: framesOf outsideMaps, nextOwner := 1, observations := s27.observations ++ [.captured 0 0] }
def t28 : Point := ⟨s28,clauseTarget,clauseMaps,([], .clauseBoundary 0 0 0 0 (some (framesOf capturedMaps))) :: outsideMaps⟩

/-- Exact saved annotation witnesses from the same selected cut used by
capture. framesOf is not inverted to guess captured owner maps. -/
theorem first_capture_parts : OwnerHeader graph [] [] 0 0 0 handlerData ∧
    PushedWithMaps graph [] capturedMaps capturedTarget ∧
    PushedWithMaps graph [] outsideMaps (.push (.plain handlerPlain) cell) := by
  obtain ⟨_,_,_,captured,outside⟩ := selected_cut.realizes
  have boundary := selected_cut.header
  have header : OwnerHeader graph [] [] 0 0 0 handlerData :=
    .selected (clause := ⟨0,.binder ⟨9,.boolean⟩,0,40⟩)
      (rfl : graph.node 41 = some (node 41)) rfl (List.mem_cons_self) rfl boundary rfl firstSelection
  exact ⟨header,captured,outside⟩

#print axioms first_capture_parts

private theorem capture : Link graph t27 t28 ∧ RawStep requestTarget clauseTarget [.ticket 0] [] := by
  have requestCarrier := perform_header_at focus_bind.2.1 _ _ _ _ _ rfl rfl
  obtain ⟨fuel,argument,rawBody,body,pattern,selection,translated,before,next,step,after⟩ :=
    capture_mapped (base := s27) selected_cut (rfl : graph.node 41 = some (node 41)) rfl
      (clause := ⟨0,.binder ⟨9,.boolean⟩,0,40⟩) rfl .boolean requestCarrier performPlain rfl
      (by intro parameter binder body selected
          obtain ⟨rfl,rfl,rfl⟩ := clause_unique selected firstSelection
          exact firstReady) .unit .none
  have argumentEq : argument = ⟨9,.boolean⟩ := (CoreSyntax.Pattern.binder.inj pattern).symm
  cases argumentEq
  obtain ⟨_,_,rfl⟩ := clause_unique selection firstSelection
  exact ⟨.positive operandReturn.endpoints.2 next (.one step) after,step⟩

theorem cleanup_to_first_clause : Chain graph r24 [t25,t26,t27,t28] t28 :=
  .next focus_bind.1 (.next request_entry (.next operandReturn (.last capture.1)))

theorem exported_capture_prefix : Chain graph p0
    [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20,r21,r22,r23,r24,t25,t26,t27,t28] t28 :=
  chain_append exported_cleanup_prefix cleanup_to_first_clause

theorem reached_first_clause_related : Related graph t28 := exported_capture_prefix.endpoints.2

theorem exported_capture_steps : CoreAllocationHistory.Steps graph 28 (CoreMachine.initial graph) s28 :=
  exported_capture_prefix.core_steps

theorem exported_capture_history : CoreAllocationHistory.History s28 :=
  CoreAllocationHistory.initial_steps_history graph exported_capture_steps

theorem reached_first_clause_control : t28.state.control = .evaluate 40 (.binding 9 (.boolean true) methodsEnv) ∧
    t28.state.frames = .clauseBoundary 0 0 0 0 (some (framesOf capturedMaps)) :: framesOf outsideMaps ∧
    t28.state.nextOwner = 1 := ⟨rfl,rfl,rfl⟩

private theorem rawTrace_append (first : RawTrace before middle created discharged)
    (second : RawTrace middle after laterCreated laterDischarged) :
    RawTrace before after (created ++ laterCreated) (laterDischarged ++ discharged) := by
  induction first with
  | refl => simpa using second
  | next step rest ih => simpa [List.append_assoc] using RawTrace.next step (ih second)

/-- Silent request operand traversal creates nothing; the genuine capture link
creates exactly ticket0, retaining the already-created resource and cleanup. -/
theorem cleanup_to_capture_ledger : RawTrace guardedTarget clauseTarget [.ticket 0] [] := by
  have focus : RawStep guardedTarget requestTarget [] [] :=
    .focus bindPlain (.bind (by simp [Code.subst,Code.instantiate,Code.IsValue])) guardedTarget.stack
  exact .next focus (.next capture.2 (.refl _))

theorem exported_capture_ledger : RawTrace rootTarget clauseTarget [.resource 0,.cleanup 0,.ticket 0] [] :=
  rawTrace_append exported_cleanup_ledger cleanup_to_capture_ledger

/-- The pending second request remains behind the captured bind and its real
saved cleanup; registration/capture has not evaluated the delayed action. -/
theorem retained_pending_request_and_callback :
    capturedMaps = [([],.bind 7 23 callbackEnv),([],.cleanupBoundary 27 callbackEnv 0),([],.handlerBoundary 41 methodsEnv 0)] ∧
    (node 23).kind = .bind ⟨6,.unit⟩ 17 22 ∧
    (node 17).kind = .request (.user 0 []) 0 16 := ⟨rfl,rfl,rfl⟩

/-- A matching active cell cannot be silently skipped to claim a user-handler
cut. This is a concrete nearest-selector negative case. -/
theorem matching_cell_blocks_handler :
    CoreMachine.findInterpreter graph (.cell (.activation 0))
      [.resourceBoundary 48 0 0,.handlerBoundary 41 methodsEnv 0] =
      .ok (.cell ⟨[],48,0,0,[.handlerBoundary 41 methodsEnv 0]⟩) := rfl

/-- The request-specific silent witness still rejects an unchanged source. -/
theorem request_unchanged_rejected :
    ¬ SilentMapped graph [] [] t25.annotations t25.annotations s25 s25 requestTarget := by
  intro witness
  exact unchanged_potential_rejected graph s25 witness.decreasing

#print axioms cleanup_to_capture_ledger
#print axioms exported_capture_ledger
#print axioms retained_pending_request_and_callback
#print axioms matching_cell_blocks_handler
#print axioms request_unchanged_rejected
#print axioms cleanup_to_first_clause
#print axioms exported_capture_prefix
#print axioms reached_first_clause_related
#print axioms exported_capture_steps
#print axioms exported_capture_history
#print axioms reached_first_clause_control



end Exported

#print axioms capture_mapped
#print axioms PushCarrier.selector_miss
#print axioms MappedHandlerCut.realizes
end Ash.OneShot.CoreCaptureEntry
