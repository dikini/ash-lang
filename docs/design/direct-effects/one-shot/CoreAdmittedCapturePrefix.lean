import CoreAdmittedCleanupPrefix
import CoreCaptureEntry
import SourceScheduledCapture

/-! The admitted exported prefix keeps source-selected data through the first
request. Capture footprint rows are explicit annotations; they are not claimed
to describe the dynamic work of the corresponding runtime request. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCapturePrefix
open ScopedExpressions ScopedExecution ProtectionContracts
open InstallationSupport InstallationSupport.Preservation CoreInitialExample
open CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential
open CoreOrdinaryCompletion CoreInitialPrefix CoreExportedFixture
open CoreHandlerPrefix (raw close2 methodsEnv)
open CoreCleanupEntry (callbackCode guardedCode callbackEnv)
open CoreCaptureEntry CoreRequestFrames CoreAdministrativeTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def outerMaps : List MappedFrame :=
  [([], .cleanupBoundary 27 callbackEnv 0), ([], .handlerBoundary 41 methodsEnv 0),
   ([], .bind 12 44 methodsEnv), ([], .resourceBoundary 48 0 0)]
private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0, .unit, [], none, .unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl

private theorem translation_unique {owners : CoreTranslation.OwnerMap} {rawCode otherRaw : Code}
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok rawCode)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok otherRaw) : rawCode = otherRaw := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index rawCode (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index otherRaw (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

private theorem cleanup_head_pushed {owners : CoreTranslation.OwnerMap}
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


private theorem currentGuarded (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (related : Related graph (CoreAdmittedCleanupPrefix.r24 answer plain handler action)) :
    EnvCloses graph [] [] callbackEnv (raw 24) guardedCode ∧
    PushedWithMaps graph [] outerMaps (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action).stack := by
  obtain ⟨_shape, code, scope, control, stack⟩ := related
  change OrdinaryWithMaps graph [] outerMaps code scope guardedCode .none
    (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action).stack at stack
  obtain ⟨rfl, rfl, pushed⟩ := cleanup_head_pushed stack
  cases control with
  | evaluate translated saved =>
    have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 24 = .ok (raw 24))
    cases same
    exact ⟨saved, pushed⟩

def suffix : Code := (close2 (raw 23)).subst 8 callbackCode

def requestTarget (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (focus : PlainData) : Configuration :=
  ⟨.perform (.user 0 []) 0 (.boolean true), .none,
    .push (.plain focus) (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action).stack⟩

def t25 (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData) (focus : PlainData) : Point :=
  ⟨CoreCaptureEntry.Exported.s25, requestTarget answer plain handler action focus, [],
    ([], .bind 7 23 callbackEnv) :: outerMaps⟩
def t26 (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData) (focus : PlainData) : Point :=
  ⟨CoreCaptureEntry.Exported.s26, requestTarget answer plain handler action focus, [],
    ([], .request (.user 0 []) 0 callbackEnv) :: (t25 answer plain handler action focus).annotations⟩
def t27 (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData) (focus : PlainData) : Point :=
  ⟨CoreCaptureEntry.Exported.s27, requestTarget answer plain handler action focus, [],
    (t26 answer plain handler action focus).annotations⟩

private theorem suffixReady : ClosedExcept 7 suffix := by
  have bound : suffix.dependencies.all (fun dep => match dep with | .variable n => n == 7 | _ => true) = true := by decide
  intro n member
  simpa using List.all_eq_true.mp bound (.variable n) member

/-- Focus uses the frame selected by source preservation, with its actual
context and scope. The remaining annotations stay arbitrary. -/
theorem focusMapped (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (focus : PlainData) (context : focus.context = .bind 7 suffix) (scope : focus.scope = .none)
    (related : Related graph (CoreAdmittedCleanupPrefix.r24 answer plain handler action)) :
    Link graph (CoreAdmittedCleanupPrefix.r24 answer plain handler action) (t25 answer plain handler action focus) ∧
    EnvCloses graph [] [] callbackEnv (raw 15) (.perform (.user 0 []) 0 (.boolean true)) ∧
    PushedWithMaps graph [] (t25 answer plain handler action focus).annotations
      (requestTarget answer plain handler action focus).stack := by
  obtain ⟨current, pushed⟩ := currentGuarded answer plain handler action related
  have whole : EnvCloses graph [] [] callbackEnv
      (.bind 7 (raw 15) (raw 23)) (.bind 7 (.perform (.user 0 []) 0 (.boolean true)) suffix) := current
  obtain ⟨operand, suffixSaved⟩ := bind_components whole
  have frame : PlainFrameRel graph [] [] (.bind 7 23 callbackEnv) focus := by
    change FrameRel graph [] [] (.bind 7 23 callbackEnv) focus.context
    rw [context]
    exact .bind (rfl : CoreTranslation.translateFuel graph 56 [] 23 = .ok (raw 23)) suffixSaved suffixReady
  have after : Related graph (t25 answer plain handler action focus) := by
    refine ⟨rfl, _, .none, .evaluate (fuel := 56) rfl operand, ?_⟩
    exact pushed_mapped (.cons frame pushed)
  have step : RawStep (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action)
      (requestTarget answer plain handler action focus) [] [] := by
    have position : Focus (.bind 7 (.perform (.user 0 []) 0 (.boolean true)) suffix)
        (.perform (.user 0 []) 0 (.boolean true)) (.bind 7 suffix) := .bind (by simp [Code.IsValue])
    have focused := RawStep.focus focus (context.symm ▸ position)
      (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action).stack
    change RawStep
      ⟨.bind 7 (.perform (.user 0 []) 0 (.boolean true)) suffix, .none,
        (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action).stack⟩
      ⟨.perform (.user 0 []) 0 (.boolean true), .none,
        .push (.plain focus) (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action).stack⟩ [] []
    simpa only [scope] using focused
  exact ⟨.positive related rfl (.one step) after, operand, .cons frame pushed⟩

/-- Request entry and operand evaluation are named Core steps that keep the
same selected target configuration. -/
theorem operandPrefix (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (focus : PlainData) (context : focus.context = .bind 7 suffix) (scope : focus.scope = .none)
    (related : Related graph (CoreAdmittedCleanupPrefix.r24 answer plain handler action)) :
    Chain graph (t25 answer plain handler action focus)
      [t26 answer plain handler action focus, t27 answer plain handler action focus]
      (t27 answer plain handler action focus) := by
  have focused := focusMapped answer plain handler action focus context scope related
  let temporary : PlainData := ⟨.perform (.user 0 []) 0, .none, .boolean, .unit, [], rfl⟩
  have traversal : SilentMapped graph [] [] (t25 answer plain handler action focus).annotations
      (t26 answer plain handler action focus).annotations CoreCaptureEntry.Exported.s25
      CoreCaptureEntry.Exported.s26 (requestTarget answer plain handler action focus) :=
    request_entry_same_target_mapped (base := CoreCaptureEntry.Exported.s25) (environment := callbackEnv)
      (requested := .user 0 []) (code := .boolean true)
      (annotations := (t25 answer plain handler action focus).annotations) ordered
      (rfl : graph.node 15 = some (node 15)) rfl
      (rfl : CoreTranslation.translateFuel graph 56 [] 14 = .ok (.boolean true))
      focused.2.1 (ValueRel.boolean (graph := graph) (owners := []) (heap := []) (value := true)).closed
      temporary rfl focused.2.2
  have saved := (perform_components focused.2.1).2
  obtain ⟨witness, _translated⟩ := CoreAdministrativeSteps.boolean_evaluate
    (base := CoreCaptureEntry.Exported.s26) (rfl : graph.node 14 = some (node 14)) rfl saved
    CoreCaptureEntry.Exported.s26.frames
  have carrier : EnvCloses graph [] [] callbackEnv (.perform (.user 0 []) 0 .unit)
      (.perform (.user 0 []) 0 .unit) := perform_header_at focused.2.1 _ _ _ _ _ rfl rfl
  have frame : RequestRel graph [] [] (.request (.user 0 []) 0 callbackEnv) temporary :=
    .operand (requested := .user 0 []) carrier rfl
  have stack := prepend_request frame
    (ValueRel.boolean (graph := graph) (owners := []) (heap := []) (value := true)).closed
    (pushed_mapped focused.2.2) .none
  exact .next (.traversal traversal) (.last (.value (value_entry_mapped witness rfl rfl stack)))

private theorem pushedHead
    (related : PushedWithMaps graph heap ((map, core) :: rest) (.push frame target)) :
    PushCarrier graph map heap core frame ∧ PushedWithMaps graph heap rest target := by
  cases related with
  | cons relation tail => exact ⟨.ordinary relation, tail⟩
  | initializer relation tail => exact ⟨.initializer relation, tail⟩
  | request relation tail => exact ⟨.request relation, tail⟩
  | resume relation tail => exact ⟨.resume relation, tail⟩
  | cleanup relation tail => exact ⟨.cleanup relation, tail⟩
  | boundary relation tail => exact ⟨.boundary relation, tail⟩

def capturedTarget (handler : HandlerData) (action : ActionData) (focus : PlainData) : Stack :=
  .push (.plain focus) (.push (.armed action) (.push (.handler handler) .nil))

def outsideTarget (answer : Ty) (plain : PlainData) : Stack :=
  .push (.plain plain) (.push (.cell 0 0 .none answer) .nil)

/-- The physical capture cut follows the actual saved maps and all source-
selected frame data. -/
theorem selectedCut (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (focus : PlainData) (context : focus.context = .bind 7 suffix) (scope : focus.scope = .none)
    (effect : handler.effectInst = .user 0 []) (identity : handler.activation = 0)
    (related : Related graph (CoreAdmittedCleanupPrefix.r24 answer plain handler action)) :
    MappedHandlerCut graph [] (.user 0 []) (t25 answer plain handler action focus).annotations
      (requestTarget answer plain handler action focus).stack
      [([], .bind 7 23 callbackEnv), ([], .cleanupBoundary 27 callbackEnv 0)] [] 41 methodsEnv handler
      [([], .bind 12 44 methodsEnv), ([], .resourceBoundary 48 0 0)]
      (capturedTarget handler action focus) (outsideTarget answer plain) := by
  obtain ⟨bindFrame, rest⟩ := pushedHead (focusMapped answer plain handler action focus context scope related).2.2
  obtain ⟨cleanupFrame, rest⟩ := pushedHead rest
  change PushedWithMaps graph []
    [([], .handlerBoundary 41 methodsEnv 0), ([], .bind 12 44 methodsEnv), ([], .resourceBoundary 48 0 0)]
    (.push (.handler handler) (outsideTarget answer plain)) at rest
  obtain ⟨handlerFrame, rest⟩ := pushedHead rest
  cases handlerFrame with
  | boundary header =>
    have header' : CoreEffectFrames.BoundaryRel graph [] []
        (.handlerBoundary 41 methodsEnv handler.activation) (.handler handler) := by
      simpa only [identity] using header
    have selected := MappedHandlerCut.hit (site := 41) (environment := methodsEnv)
      (data := handler) (owners := []) header' effect rest
    rw [identity] at selected
    exact .push bindFrame (by simp [ExecFrame.erase, PlainData.erase, Frame.target])
      (.push cleanupFrame (by simp [ExecFrame.erase, ActionData.erase, Frame.target]) selected)

private theorem physicalUnique
    (first : HandlerCut requested whole cap tail handler)
    (second : HandlerCut requested whole otherCap otherTail otherHandler) :
    cap = otherCap ∧ tail = otherTail ∧ handler = otherHandler := by
  induction first generalizing otherCap otherTail otherHandler with
  | hit selected rest effect =>
    cases second with
    | hit => exact ⟨rfl, rfl, rfl⟩
    | push frame rest cap tail handler miss cut =>
      simp [ExecFrame.erase, HandlerData.erase, Frame.target, effect] at miss
  | push frame rest cap tail handler miss cut ih =>
    cases second with
    | hit selected rest effect =>
      simp [ExecFrame.erase, HandlerData.erase, Frame.target, effect] at miss
    | push frame rest otherCap otherTail otherHandler otherMiss other =>
      obtain ⟨rfl, rfl, rfl⟩ := ih other
      exact ⟨rfl, rfl, rfl⟩
  | live owner input answer saved caller rest cap tail handler cut ih =>
    cases second with
    | live owner input answer saved caller rest otherCap otherTail otherHandler other =>
      obtain ⟨rfl, rfl, rfl⟩ := ih other
      exact ⟨rfl, rfl, rfl⟩
  | spent owner answer caller rest cap tail handler cut ih =>
    cases second with
    | spent owner answer caller rest otherCap otherTail otherHandler other =>
      obtain ⟨rfl, rfl, rfl⟩ := ih other
      exact ⟨rfl, rfl, rfl⟩

def firstClauseBody : Code := match CoreHandlerPrefix.clauses with
  | .cons _ _ _ body _ => body
  | .nil => .unit
private theorem firstSelection : ClauseAt 0 CoreHandlerPrefix.clauses 9 (CoreTranslation.ticket graph 0) firstClauseBody := .hit
private theorem firstReady : ClosedExcept 9 firstClauseBody := by
  have bound : firstClauseBody.dependencies.all (fun dep => match dep with | .variable n => n == 9 | _ => true) = true := by decide
  intro n member
  simpa using List.all_eq_true.mp bound (.variable n) member

private theorem clauseUnique
    (first : ClauseAt operation clauses parameter binder body)
    (second : ClauseAt operation clauses otherParameter otherBinder otherBody) :
    parameter = otherParameter ∧ binder = otherBinder ∧ body = otherBody := by
  induction first with
  | hit => cases second with
    | hit => exact ⟨rfl, rfl, rfl⟩
    | pass different next => exact False.elim (different rfl)
  | pass different next ih => cases second with
    | hit => exact False.elim (different rfl)
    | pass otherDifferent otherNext => exact ih otherNext

def clauseTarget (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (focus : PlainData) (operationResult : Ty) : Configuration :=
  ⟨firstClauseBody.subst 9 (.boolean true), .ticket (CoreTranslation.ticket graph 0) 0,
    .live 0 operationResult handler.answer (capturedTarget handler action focus) handler.scope (outsideTarget answer plain)⟩

def t28 (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (focus : PlainData) (operationResult : Ty) : Point :=
  ⟨CoreCaptureEntry.Exported.s28, clauseTarget answer plain handler action focus operationResult,
    CoreCaptureEntry.Exported.clauseMaps,
    ([], .clauseBoundary 0 0 0 0 (some (framesOf CoreCaptureEntry.Exported.capturedMaps))) ::
      CoreCaptureEntry.Exported.outsideMaps⟩

/-- The operation-result annotation remains the one selected by source
preservation; no fixed Unit result or fixed handler answer is assumed. -/
theorem captureMapped (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (focus : PlainData) (operationResult : Ty)
    (context : focus.context = .bind 7 suffix) (scope : focus.scope = .none)
    (effect : handler.effectInst = .user 0 []) (identity : handler.activation = 0)
    (arms : handler.clauses = CoreHandlerPrefix.clauses)
    (related : Related graph (CoreAdmittedCleanupPrefix.r24 answer plain handler action)) :
    Link graph (t27 answer plain handler action focus) (t28 answer plain handler action focus operationResult) ∧
    RawStep (requestTarget answer plain handler action focus)
      (clauseTarget answer plain handler action focus operationResult) [.ticket 0] [] := by
  have focused := focusMapped answer plain handler action focus context scope related
  have cut := selectedCut answer plain handler action focus context scope effect identity related
  have requestCarrier := perform_header_at focused.2.1 _ _ _ _ _ rfl rfl
  let temporary : PlainData := ⟨.perform (.user 0 []) 0, .none, .boolean, .unit, [], rfl⟩
  obtain ⟨fuel, argument, rawBody, body, pattern, selection, _translated, _before, next, step, after⟩ :=
    capture_mapped (base := CoreCaptureEntry.Exported.s27) cut
      (rfl : graph.node 41 = some (node 41)) rfl
      (clause := ⟨0, .binder ⟨9, .boolean⟩, 0, 40⟩) rfl .boolean requestCarrier temporary rfl
      (by intro parameter binder body selected
          rw [arms] at selected
          obtain ⟨rfl, rfl, rfl⟩ := clauseUnique selected firstSelection
          exact firstReady) operationResult .none
  have argumentEq : argument = ⟨9, .boolean⟩ := (CoreSyntax.Pattern.binder.inj pattern).symm
  cases argumentEq
  rw [arms] at selection
  obtain ⟨_, _, rfl⟩ := clauseUnique selection firstSelection
  rw [identity] at next after
  exact ⟨.positive (operandPrefix answer plain handler action focus context scope related).endpoints.2
    next (.one step) after, step⟩

def extensionPoints (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (focus : PlainData) (operationResult : Ty) : List Point :=
  [t25 answer plain handler action focus, t26 answer plain handler action focus,
   t27 answer plain handler action focus, t28 answer plain handler action focus operationResult]
def priorPoints (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData) : List Point :=
  CoreAdmittedCleanupPrefix.priorPoints answer plain handler ++
    CoreAdmittedCleanupPrefix.extensionPoints answer plain handler action

/-- The actual first capture is admitted from the same exported root. Resume
and close rows are chosen bookkeeping annotations, while the operation result,
selected clause and capabilities come from current source preservation. -/
theorem admittedCapturePrefix (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
      (focus : PlainData) (allocated : SourcePlannedTyping.Contract) (final : Snapshot operations),
      allocated.resumeRow = resumeRow ∧ allocated.closeRow = closeRow ∧
      focus.context = .bind 7 suffix ∧ focus.scope = .none ∧
      handler.activation = 0 ∧ handler.clauses = CoreHandlerPrefix.clauses ∧
      Chain graph p0
        (priorPoints answer plain handler action ++
          extensionPoints answer plain handler action focus (ScopedPorts.embedPort allocated.input.erase.erase.port))
        (t28 answer plain handler action focus (ScopedPorts.embedPort allocated.input.erase.erase.port)) ∧
      RawTrace (CoreAdmittedPrefix.initial tables families required).run.execution 13 final.run.execution ∧
      CoreAdmittedPrefix.Admitted final ∧
      (∀ point ∈ p0 :: (priorPoints answer plain handler action ++
          extensionPoints answer plain handler action focus (ScopedPorts.embedPort allocated.input.erase.erase.port)),
        Related graph point ∧ ∃ snapshot : Snapshot operations,
          CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = .eval point.target) ∧
      final.world = [0] ∧ final.history = [0] ∧
      final.run.execution.issued = [.resource 0, .cleanup 0, .ticket 0] ∧
      final.run.execution.completed = [] ∧
      final.run.tickets 0 = some firstClauseBody.requiredActions ∧
      final.run.execution.machine = .eval
        (t28 answer plain handler action focus (ScopedPorts.embedPort allocated.input.erase.erase.port)).target := by
  obtain ⟨answer, plain, handler, action, base, handlerIdentity, plainContext, plainScope,
    handlerScope, handlerEffect, handlerArms, actionIdentity, actionEq, actionScope,
    _opened, earlier, trace, baseValid, allEarlier, world, history, issued, completed, machine⟩ :=
    CoreAdmittedCleanupPrefix.admittedCleanupPrefix tables families required
  have baseRelated := earlier.endpoints.2
  let ready := CoreAdmittedHandlerPrefix.reconfigure base
    (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action)
  have readyEq : ready = base := by
    dsimp only [ready, CoreAdmittedHandlerPrefix.reconfigure]
    change base.run.execution.machine = .eval
      (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action) at machine
    rw [← machine]
  have readyValid : CoreAdmittedPrefix.Admitted ready := by rw [readyEq]; exact baseValid
  have position : Focus guardedCode (.perform (.user 0 []) 0 (.boolean true)) (.bind 7 suffix) := by
    change Focus (.bind 7 (.perform (.user 0 []) 0 (.boolean true)) suffix)
      (.perform (.user 0 []) 0 (.boolean true)) (.bind 7 suffix)
    exact .bind (by simp [Code.IsValue])
  let request : Allocating.Request ready :=
    .focus (whole := guardedCode) (runtimeScope := .none)
      (stack := (CoreAdmittedCleanupPrefix.guardedTarget answer plain handler action).stack)
      (issued := base.run.execution.issued) (completed := base.run.execution.completed)
      (actions := base.run.tickets) rfl position
  obtain ⟨afterFocus, focusEvent, realization, focusedValid⟩ := request.preserve readyValid
  dsimp [request] at realization
  cases realization with
  | focus focus context scope =>
    let pending := CoreAdmittedHandlerPrefix.reconfigure base (requestTarget answer plain handler action focus)
    have pendingValid : CoreAdmittedPrefix.Admitted pending := focusedValid
    have actualFocusEvent : LexicalUnwind.Event base.run.execution pending.run.execution := by
      change LexicalUnwind.Event base.run.execution
        ⟨.eval (requestTarget answer plain handler action focus), base.run.execution.issued,
          base.run.execution.completed⟩
      simpa only [readyEq, requestTarget] using focusEvent
    have cut := selectedCut answer plain handler action focus context scope handlerEffect handlerIdentity baseRelated
    have physical := cut.realizes.2.1
    have state := pendingValid.unpack
    obtain ⟨allocated, inputRows, answerRows, captureScope, savedRequirements, rights, next,
      selectedHandler, selectedCaptured, selectedTail, parameter, binder, code,
      resumeEq, closeEq, selectedPhysical, located, closed, rightsEq, expressionEq, scopeEq,
      stackEq, captureEvent, nextState⟩ := state.capture_successor_metadata physical
        (ValueRel.boolean (graph := graph) (owners := []) (heap := []) (value := true)).closed 0
        (by change (base.run.execution.issued ++ [Owner.ticket 0]).Nodup; rw [issued]; decide) resumeRow closeRow
    have sameCut := physicalUnique selectedPhysical physical
    rw [sameCut.2.2] at located
    rw [sameCut.1, sameCut.2.1, sameCut.2.2] at stackEq
    rw [handlerArms] at located
    obtain ⟨rfl, rfl, rfl⟩ := clauseUnique located firstSelection
    let final := Snapshot.ofState nextState
    have finalValid : CoreAdmittedPrefix.Admitted final := valid_ofState nextState
    have nextEq : next = clauseTarget answer plain handler action focus
        (ScopedPorts.embedPort allocated.input.erase.erase.port) := by
      cases next with
      | mk expression runtimeScope stack =>
        change expression = _ at expressionEq
        change runtimeScope = _ at scopeEq
        change stack = _ at stackEq
        cases expressionEq
        cases scopeEq
        cases stackEq
        rfl
    have linked := captureMapped answer plain handler action focus
      (ScopedPorts.embedPort allocated.input.erase.erase.port) context scope handlerEffect handlerIdentity handlerArms baseRelated
    have suffixChain : Chain graph (CoreAdmittedCleanupPrefix.r24 answer plain handler action)
        (extensionPoints answer plain handler action focus (ScopedPorts.embedPort allocated.input.erase.erase.port))
        (t28 answer plain handler action focus (ScopedPorts.embedPort allocated.input.erase.erase.port)) :=
      .next (focusMapped answer plain handler action focus context scope baseRelated).1
        (CoreHandlerPrefix.chain_append (operandPrefix answer plain handler action focus context scope baseRelated)
          (.last linked.1))
    have chain := CoreHandlerPrefix.chain_append earlier suffixChain
    have finalMachine : final.run.execution.machine = .eval
        (t28 answer plain handler action focus (ScopedPorts.embedPort allocated.input.erase.erase.port)).target := by
      change LexicalUnwind.Machine.eval next = _
      rw [nextEq]
      rfl
    have extensionValid : ∀ point ∈ extensionPoints answer plain handler action focus
        (ScopedPorts.embedPort allocated.input.erase.erase.port), ∃ snapshot : Snapshot operations,
          CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = .eval point.target := by
      intro point member
      simp only [extensionPoints, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact ⟨pending, pendingValid, rfl⟩
      · exact ⟨pending, pendingValid, rfl⟩
      · exact ⟨pending, pendingValid, rfl⟩
      · exact ⟨final, finalValid, finalMachine⟩
    refine ⟨answer, plain, handler, action, focus, allocated, final, resumeEq, closeEq,
      context, scope, handlerIdentity, handlerArms, chain,
      .step (.step trace actualFocusEvent) captureEvent, finalValid, ?_, world, history, ?_, completed, ?_, finalMachine⟩
    · intro point member
      rcases List.mem_cons.mp member with equal | later
      · subst point
        exact allEarlier p0 List.mem_cons_self
      · refine ⟨chain.every_point_related point later, ?_⟩
        rcases List.mem_append.mp later with prior | extension
        · exact (allEarlier point (List.mem_cons_of_mem _ prior)).2
        · exact extensionValid point extension
    · change base.run.execution.issued ++ [.ticket 0] = _
      rw [issued]
      rfl
    · change (base.run.tickets.insert 0 rights) 0 = _
      rw [rightsEq]
      rfl

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCapturePrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCapturePrefix.focusMapped

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCapturePrefix.operandPrefix

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCapturePrefix.captureMapped

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCapturePrefix.admittedCapturePrefix
