import CoreAdmittedResumePrefix
import CoreSecondCapture

/-! The same admitted restored continuation reaches its second user capture.
Saved owner maps stay authenticated; physical frame equality does not select
new lexical owner maps. Both captures' footprint rows remain explicit chosen
annotations. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedSecondCapturePrefix
open ScopedExpressions ScopedExecution ProtectionContracts
open InstallationSupport InstallationSupport.Preservation CoreInitialExample
open CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential
open CoreOrdinaryCompletion CoreAdministrativeTransport CoreInitialPrefix CoreExportedFixture
open CoreEffectFrames CoreRequestFrames CoreResumeFrames CoreCaptureEntry
open CoreHandlerPrefix (raw methodsEnv)
open CoreCleanupEntry (callbackEnv)
open CoreCaptureEntry.Exported (clauseMaps capturedMaps outsideMaps)
open CoreResumeEntry.Exported (clauseEnv ticketScope postWriteCode)
open CoreSecondCapture (nextEnv secondCode setterCode)
open CoreAdmittedResumePrefix (Data)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

structure Maps where
  bindOwner : CoreTranslation.OwnerMap
  cleanupOwner : CoreTranslation.OwnerMap
  handlerOwner : CoreTranslation.OwnerMap

def savedMaps (m : Maps) : List MappedFrame :=
  [(m.bindOwner, .bind 7 23 callbackEnv), (m.cleanupOwner, .cleanupBoundary 27 callbackEnv 0),
   (m.handlerOwner, .handlerBoundary 41 methodsEnv 0)]
def outside (_post : PlainData) : List MappedFrame :=
  [(clauseMaps, .bind 10 37 clauseEnv), ([], .clauseBoundary 0 0 0 0 none)] ++ outsideMaps

def tailTarget (d : Data) (post : PlainData) : Stack :=
  .push (.armed d.action) (.push (.handler d.handler)
    (.push (.plain post) (.spent 0 d.handler.answer d.handler.scope
      (CoreAdmittedCapturePrefix.outsideTarget d.answer d.plain))))
def tailMaps (m : Maps) : List MappedFrame :=
  [(m.cleanupOwner, .cleanupBoundary 27 callbackEnv 0), (m.handlerOwner, .handlerBoundary 41 methodsEnv 0)] ++
    [(clauseMaps, .bind 10 37 clauseEnv), ([], .clauseBoundary 0 0 0 0 none)] ++ outsideMaps

def p35 (d : Data) (post : PlainData) (m : Maps) : Point := CoreAdmittedResumePrefix.p35 d post (savedMaps m)
def bindTarget (d : Data) (post : PlainData) : Configuration :=
  ⟨.bind 7 .unit CoreAdmittedCapturePrefix.suffix, .none, tailTarget d post⟩
def secondTarget (d : Data) (post : PlainData) : Configuration := ⟨secondCode, .none, tailTarget d post⟩
def p36 (d : Data) (post : PlainData) (m : Maps) : Point :=
  ⟨CoreSecondCapture.s36, secondTarget d post, m.bindOwner, tailMaps m⟩

private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0, .unit, [], none, .unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl

/-- Split the actual current annotations, retaining each saved owner map. -/
theorem splitSaved (saved : List MappedFrame) (framesEq : framesOf saved = framesOf capturedMaps) :
    ∃ m : Maps, saved = savedMaps m := by
  rcases saved with _ | ⟨⟨alpha, first⟩, rest⟩
  · cases framesEq
  rcases rest with _ | ⟨⟨beta, second⟩, rest⟩
  · cases framesEq
  rcases rest with _ | ⟨⟨gamma, third⟩, rest⟩
  · cases framesEq
  cases rest with
  | nil =>
    simp only [framesOf, capturedMaps, List.map_cons, List.map_nil, List.cons.injEq] at framesEq
    obtain ⟨rfl, rfl, rfl, _⟩ := framesEq
    exact ⟨⟨alpha, beta, gamma⟩, rfl⟩
  | cons fourth more =>
    have same := congrArg (fun frames => frames.length) framesEq
    simp [framesOf, capturedMaps] at same

private theorem translation_unique {owners : CoreTranslation.OwnerMap} {code other : Code}
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok code)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok other) : code = other := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index code (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index other (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

private theorem plug_not_unit (context : ScopedExecution.Context) (code : Code) : context.plug code ≠ .unit := by
  cases context <;> simp [Context.plug]

/-- No nonempty flattened prefix can produce Unit. -/
private theorem flat_unit {annotations : List MappedFrame} (flat : FlattenedWithMaps graph heap annotations code scope result resultScope) :
    result = .unit → annotations = [] ∧ code = .unit ∧ scope = resultScope := by
  induction flat with
  | nil => intro same; exact ⟨rfl,same,rfl⟩
  | cons frame ready tail ih =>
      intro same
      exact False.elim (plug_not_unit _ _ (ih same).2.1)
  | initializer frame ready tail ih =>
      intro same
      exact False.elim (plug_not_unit _ _ (ih same).2.1)
  | request frame ready tail ih =>
      intro same
      exact False.elim (plug_not_unit _ _ (ih same).2.1)
  | resume frame ready tail ih =>
      intro same
      exact False.elim (plug_not_unit _ _ (ih same).2.1)


private theorem restoredPushed (d : Data) (post : PlainData) (m : Maps)
    (related : Related graph (p35 d post m)) :
    PushedWithMaps graph [] ((savedMaps m) ++ outside post)
      (CoreAdmittedResumePrefix.restoredTarget d post).stack := by
  obtain ⟨_shape, code, scope, control, stack⟩ := related
  obtain ⟨pre, tail, split, flat, pushed⟩ := stack
  obtain ⟨rfl, _, _⟩ := flat_unit flat rfl
  have same : tail = savedMaps m ++ outside post := by simpa only [p35, CoreAdmittedResumePrefix.p35, outside, List.append_assoc, List.nil_append, List.cons_append] using split.symm
  subst tail
  exact pushed

private theorem bindParts (d : Data) (post : PlainData) (m : Maps)
    (context : d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix)
    (related : Related graph (p35 d post m)) :
    EnvCloses graph m.bindOwner [] callbackEnv (.lambda 7 (raw 23)) (.lambda 7 CoreAdmittedCapturePrefix.suffix) ∧
    ClosedExcept 7 CoreAdmittedCapturePrefix.suffix ∧ PushedWithMaps graph [] (tailMaps m) (tailTarget d post) := by
  have pushed := restoredPushed d post m related
  change PushedWithMaps graph [] ((m.bindOwner, .bind 7 23 callbackEnv) :: tailMaps m)
    (.push (.plain d.focus) (tailTarget d post)) at pushed
  cases pushed with
  | cons relation tail =>
    change FrameRel graph m.bindOwner [] (.bind 7 23 callbackEnv) d.focus.context at relation
    rw [context] at relation
    cases relation with
    | bind translated saved ready =>
      have equal := translation_unique translated
        (rfl : CoreTranslation.translateFuel graph 56 m.bindOwner 23 = .ok (raw 23))
      cases equal
      exact ⟨saved, ready, tail⟩
  | initializer relation tail => cases relation
  | boundary relation tail => cases relation
  | request relation tail => cases relation
  | resume relation tail => cases relation

/-- The first restored value plugs and binds under the same selected frame.
Two target steps match the single actual Core return-bind transition. -/
theorem returnBind (d : Data) (post : PlainData) (m : Maps)
    (context : d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix) (scope : d.focus.scope = .none)
    (related : Related graph (p35 d post m)) :
    Link graph (p35 d post m) (p36 d post m) ∧
    RawStep (CoreAdmittedResumePrefix.restoredTarget d post) (bindTarget d post) [] [] ∧
    RawStep (bindTarget d post) (secondTarget d post) [] [] := by
  have parts := bindParts d post m context related
  obtain ⟨_before, next, plug, bind, after⟩ := bind_return_mapped (base := CoreResumeEntry.Exported.s35)
    (rfl : CoreTranslation.translateFuel graph 56 m.bindOwner 23 = .ok (raw 23)) parts.1 parts.2.1
    (ValueRel.unit (owners := clauseMaps)) d.focus context parts.2.2 ticketScope
  rw [scope] at plug bind after
  exact ⟨.positive related next (.next plug (.one bind)) after, plug, bind⟩

def falseTarget (d : Data) (post second : PlainData) : Configuration :=
  ⟨.perform (.user 0 []) 0 (.boolean false), .none, .push (.plain second) (tailTarget d post)⟩
def p37 (d : Data) (post second : PlainData) (m : Maps) : Point :=
  ⟨CoreSecondCapture.s37, falseTarget d post second, m.bindOwner,
    (m.bindOwner, .bind 6 22 nextEnv) :: tailMaps m⟩
def p38 (d : Data) (post second : PlainData) (m : Maps) : Point :=
  ⟨CoreSecondCapture.s38, falseTarget d post second, m.bindOwner,
    (m.bindOwner, .request (.user 0 []) 0 nextEnv) :: (p37 d post second m).annotations⟩
def p39 (d : Data) (post second : PlainData) (m : Maps) : Point :=
  ⟨CoreSecondCapture.s39, falseTarget d post second, m.bindOwner, (p38 d post second m).annotations⟩

private theorem secondParts (d : Data) (post : PlainData) (m : Maps)
    (context : d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix)
    (related : Related graph (p35 d post m)) :
    EnvCloses graph m.bindOwner [] nextEnv (raw 17) (.perform (.user 0 []) 0 (.boolean false)) ∧
    EnvCloses graph m.bindOwner [] nextEnv (.lambda 6 (raw 22)) (.lambda 6 setterCode) := by
  have current := (bindParts d post m context related).1.beta_argument (ValueRel.unit (owners := m.bindOwner))
  change EnvCloses graph m.bindOwner [] nextEnv (.bind 6 (raw 17) (raw 22))
    (.bind 6 (.perform (.user 0 []) 0 (.boolean false)) setterCode) at current
  exact bind_components current
private theorem setterReady : ClosedExcept 6 setterCode := by
  have bound : setterCode.dependencies.all (fun dep => match dep with | .variable n => n == 6 | _ => true) = true := by decide
  intro n member
  simpa using List.all_eq_true.mp bound (.variable n) member
private theorem secondFrame (d : Data) (post second : PlainData) (m : Maps)
    (focusContext : d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix)
    (context : second.context = .bind 6 setterCode) (related : Related graph (p35 d post m)) :
    PlainFrameRel graph m.bindOwner [] (.bind 6 22 nextEnv) second := by
  change FrameRel graph m.bindOwner [] (.bind 6 22 nextEnv) second.context
  rw [context]
  exact .bind (rfl : CoreTranslation.translateFuel graph 56 m.bindOwner 22 = .ok (raw 22))
    (secondParts d post m focusContext related).2 setterReady
private theorem falseStack (d : Data) (post second : PlainData) (m : Maps)
    (focusContext : d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix)
    (context : second.context = .bind 6 setterCode) (related : Related graph (p35 d post m)) :
    PushedWithMaps graph [] (p37 d post second m).annotations (falseTarget d post second).stack :=
  .cons (secondFrame d post second m focusContext context related) (bindParts d post m focusContext related).2.2

theorem focusMapped (d : Data) (post second : PlainData) (m : Maps)
    (focusContext : d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix) (focusScope : d.focus.scope = .none)
    (context : second.context = .bind 6 setterCode) (scope : second.scope = .none)
    (related : Related graph (p35 d post m)) :
    Link graph (p36 d post m) (p37 d post second m) ∧ RawStep (secondTarget d post) (falseTarget d post second) [] [] := by
  have after : Related graph (p37 d post second m) :=
    ⟨rfl, _, .none, .evaluate (fuel := 56) rfl (secondParts d post m focusContext related).1,
      pushed_mapped (falseStack d post second m focusContext context related)⟩
  have position : Focus secondCode (.perform (.user 0 []) 0 (.boolean false)) (.bind 6 setterCode) := by
    change Focus (.bind 6 (.perform (.user 0 []) 0 (.boolean false)) setterCode)
      (.perform (.user 0 []) 0 (.boolean false)) (.bind 6 setterCode)
    exact .bind (by simp [Code.IsValue])
  have step : RawStep (secondTarget d post) (falseTarget d post second) [] [] := by
    simpa only [scope, secondTarget, falseTarget] using RawStep.focus second (context.symm ▸ position) (tailTarget d post)
  exact ⟨.positive (returnBind d post m focusContext focusScope related).1.endpoints.2 rfl (.one step) after, step⟩

theorem operandPrefix (d : Data) (post second : PlainData) (m : Maps)
    (focusContext : d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix)
    (context : second.context = .bind 6 setterCode) (related : Related graph (p35 d post m)) :
    Chain graph (p37 d post second m) [p38 d post second m, p39 d post second m] (p39 d post second m) := by
  have parts := secondParts d post m focusContext related
  have pushed := falseStack d post second m focusContext context related
  let temporary : PlainData := ⟨.perform (.user 0 []) 0, .none, .boolean, .unit, [], rfl⟩
  have traversal : SilentMapped graph m.bindOwner m.bindOwner (p37 d post second m).annotations
      (p38 d post second m).annotations CoreSecondCapture.s37 CoreSecondCapture.s38 (falseTarget d post second) :=
    request_entry_same_target_mapped (base := CoreSecondCapture.s37) (environment := nextEnv)
      (requested := .user 0 []) (code := .boolean false) (annotations := (p37 d post second m).annotations) ordered
      (rfl : graph.node 17 = some (node 17)) rfl
      (rfl : CoreTranslation.translateFuel graph 56 m.bindOwner 16 = .ok (.boolean false))
      parts.1 (ValueRel.boolean (graph := graph) (owners := m.bindOwner) (heap := []) (value := false)).closed
      temporary rfl pushed
  obtain ⟨witness, _translated⟩ := CoreAdministrativeSteps.boolean_evaluate (base := CoreSecondCapture.s38)
    (rfl : graph.node 16 = some (node 16)) rfl (perform_components parts.1).2 CoreSecondCapture.s38.frames
  have frame : RequestRel graph m.bindOwner [] (.request (.user 0 []) 0 nextEnv) temporary :=
    .operand (requested := .user 0 []) (perform_header_at parts.1 _ _ _ _ _ rfl rfl) rfl
  have stack := prepend_request frame
    (ValueRel.boolean (graph := graph) (owners := m.bindOwner) (heap := []) (value := false)).closed
    (pushed_mapped pushed) .none
  exact .next (.traversal traversal) (.last (.value (value_entry_mapped witness rfl rfl stack)))

private theorem pushedHead {owners : CoreTranslation.OwnerMap}
    (related : PushedWithMaps graph heap ((owners, core) :: rest) (.push frame target)) :
    PushCarrier graph owners heap core frame ∧ PushedWithMaps graph heap rest target := by
  cases related with
  | cons relation tail => exact ⟨.ordinary relation, tail⟩
  | initializer relation tail => exact ⟨.initializer relation, tail⟩
  | request relation tail => exact ⟨.request relation, tail⟩
  | resume relation tail => exact ⟨.resume relation, tail⟩
  | cleanup relation tail => exact ⟨.cleanup relation, tail⟩
  | boundary relation tail => exact ⟨.boundary relation, tail⟩

private theorem headerEffect {owners : CoreTranslation.OwnerMap}
    (header : BoundaryRel graph owners [] (.handlerBoundary 41 methodsEnv 0) (.handler data)) :
    data.effectInst = .user 0 [] := by
  generalize coreEq : CoreMachine.Frame.handlerBoundary 41 methodsEnv 0 = core at header
  generalize targetEq : ExecFrame.handler data = target at header
  cases header with
  | handler known kind translated closing =>
    have dataEq := ExecFrame.handler.inj targetEq
    cases dataEq
    obtain ⟨siteEq, environmentEq, identityEq⟩ := CoreMachine.Frame.handlerBoundary.inj coreEq
    cases siteEq
    cases environmentEq
    have nodeEq := Option.some.inj (known.symm.trans (rfl : graph.node 41 = some (node 41)))
    cases nodeEq
    cases kind
    have effect := handle_effect_at closing _ _ _ _ _ _ rfl rfl
    have frozen : Instantiation.freezeEffect data.effectInst = .user 0 [] := effect.symm
    exact freeze_effect_injective frozen
  | cell known kind => cases coreEq

def inside (m : Maps) : List MappedFrame :=
  [(m.bindOwner, .bind 6 22 nextEnv), (m.cleanupOwner, .cleanupBoundary 27 callbackEnv 0)]
def captured (m : Maps) : List MappedFrame := inside m ++ [(m.handlerOwner, .handlerBoundary 41 methodsEnv 0)]
def capturedTarget (d : Data) (second : PlainData) : Stack :=
  .push (.plain second) (.push (.armed d.action) (.push (.handler d.handler) .nil))
def outsideTarget (d : Data) (post : PlainData) : Stack :=
  .push (.plain post) (.spent 0 d.handler.answer d.handler.scope (CoreAdmittedCapturePrefix.outsideTarget d.answer d.plain))

theorem selectedCut (d : Data) (post second : PlainData) (m : Maps)
    (focusContext : d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix)
    (context : second.context = .bind 6 setterCode) (identity : d.handler.activation = 0)
    (related : Related graph (p35 d post m)) :
    MappedHandlerCut graph [] (.user 0 []) (p37 d post second m).annotations (falseTarget d post second).stack
      (inside m) m.handlerOwner 41 methodsEnv d.handler (outside post) (capturedTarget d second) (outsideTarget d post) := by
  obtain ⟨bindFrame, rest⟩ := pushedHead (falseStack d post second m focusContext context related)
  obtain ⟨cleanupFrame, rest⟩ := pushedHead rest
  obtain ⟨handlerFrame, rest⟩ := pushedHead rest
  cases handlerFrame with
  | boundary header =>
    have effect := headerEffect header
    have header' : BoundaryRel graph m.handlerOwner []
        (.handlerBoundary 41 methodsEnv d.handler.activation) (.handler d.handler) := by simpa only [identity] using header
    have selected := MappedHandlerCut.hit (site := 41) (environment := methodsEnv) (owners := m.handlerOwner) header' effect rest
    rw [identity] at selected
    exact .push bindFrame (by simp [ExecFrame.erase, PlainData.erase, Frame.target])
      (.push cleanupFrame (by simp [ExecFrame.erase, ActionData.erase, Frame.target]) selected)

private theorem firstSelection : ClauseAt 0 CoreHandlerPrefix.clauses 9 (CoreTranslation.ticket graph 0)
    CoreAdmittedCapturePrefix.firstClauseBody := .hit
private theorem firstReady : ClosedExcept 9 CoreAdmittedCapturePrefix.firstClauseBody := by
  have bound : CoreAdmittedCapturePrefix.firstClauseBody.dependencies.all
      (fun dep => match dep with | .variable n => n == 9 | _ => true) = true := by decide
  intro n member
  simpa using List.all_eq_true.mp bound (.variable n) member

def clauseTarget (d : Data) (post second : PlainData) (input : Ty) : Configuration :=
  ⟨CoreAdmittedCapturePrefix.firstClauseBody.subst 9 (.boolean false), .ticket (CoreTranslation.ticket graph 0) 1,
    .live 1 input d.handler.answer (capturedTarget d second) d.handler.scope (outsideTarget d post)⟩
def p40 (d : Data) (post second : PlainData) (m : Maps) (input : Ty) : Point :=
  ⟨CoreSecondCapture.s40, clauseTarget d post second input,
    ⟨0, 0, CoreTranslation.ticket graph 0⟩ :: m.handlerOwner,
    (m.handlerOwner, .clauseBoundary 0 0 0 1 (some (framesOf (captured m)))) :: outside post⟩

/-- Capture retains the same source-selected handler, action, post frame and
spent owner zero. The new operation-result port is an explicit source choice. -/
theorem captureMapped (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (focusContext : d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix)
    (context : second.context = .bind 6 setterCode) (identity : d.handler.activation = 0)
    (arms : d.handler.clauses = CoreHandlerPrefix.clauses) (related : Related graph (p35 d post m)) :
    Link graph (p39 d post second m) (p40 d post second m input) ∧
    RawStep (falseTarget d post second) (clauseTarget d post second input) [.ticket 1] [] := by
  have parts := secondParts d post m focusContext related
  have cut := selectedCut d post second m focusContext context identity related
  let temporary : PlainData := ⟨.perform (.user 0 []) 0, .none, .boolean, .unit, [], rfl⟩
  obtain ⟨fuel, argument, rawBody, body, pattern, selected, _translated, _before, next, step, after⟩ :=
    capture_mapped (base := CoreSecondCapture.s39) cut (rfl : graph.node 41 = some (node 41)) rfl
      (clause := ⟨0, .binder ⟨9, .boolean⟩, 0, 40⟩) rfl .boolean
      (perform_header_at parts.1 _ _ _ _ _ rfl rfl) temporary rfl
      (by intro parameter binder body selected
          rw [arms] at selected
          obtain ⟨rfl, rfl, rfl⟩ := CaptureAnnotations.clause_selection_unique selected firstSelection
          exact firstReady) input .none
  have argumentEq : argument = ⟨9, .boolean⟩ := (CoreSyntax.Pattern.binder.inj pattern).symm
  cases argumentEq
  rw [arms] at selected
  obtain ⟨_, _, rfl⟩ := CaptureAnnotations.clause_selection_unique selected firstSelection
  rw [identity] at next after
  exact ⟨.positive (operandPrefix d post second m focusContext context related).endpoints.2 next (.one step) after, step⟩

def priorPoints (d : Data) (post : PlainData) (m : Maps) : List Point :=
  CoreAdmittedResumePrefix.priorPoints d ++ CoreAdmittedResumePrefix.extensionPoints d post (savedMaps m)
def extensionPoints (d : Data) (post second : PlainData) (m : Maps) (input : Ty) : List Point :=
  [p36 d post m, p37 d post second m, p38 d post second m, p39 d post second m, p40 d post second m input]

/-- Both capture epochs belong to the same admitted exported execution. The
second capture saves the armed cleanup and handler while retaining the
post-resume frame and spent owner zero outside its cut. -/
theorem admittedSecondCapturePrefix (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (firstResumeRow : Footprint) (firstCloseRow : Option Footprint)
    (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ (d : Data) (post : PlainData) (m : Maps) (second : PlainData)
      (firstAllocated allocated : SourcePlannedTyping.Contract) (previous bound final : Snapshot operations),
      firstAllocated.resumeRow = firstResumeRow ∧ firstAllocated.closeRow = firstCloseRow ∧
      allocated.resumeRow = resumeRow ∧ allocated.closeRow = closeRow ∧
      d.input = ScopedPorts.embedPort firstAllocated.input.erase.erase.port ∧
      d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix ∧ d.focus.scope = .none ∧
      d.handler.activation = 0 ∧ d.handler.clauses = CoreHandlerPrefix.clauses ∧
      post.context = .bind 10 postWriteCode ∧ post.scope = ticketScope ∧
      second.context = .bind 6 setterCode ∧ second.scope = .none ∧
      CoreAdmittedPrefix.Admitted previous ∧ previous.run.execution.machine = .eval (p35 d post m).target ∧
      CoreAdmittedPrefix.Admitted bound ∧ bound.run.execution.machine = .eval (bindTarget d post) ∧
      Chain graph p0
        (priorPoints d post m ++ extensionPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port))
        (p40 d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port)) ∧
      RawTrace (CoreAdmittedPrefix.initial tables families required).run.execution 20 final.run.execution ∧
      CoreAdmittedPrefix.Admitted final ∧
      (∀ point ∈ p0 :: (priorPoints d post m ++
          extensionPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port)),
        Related graph point ∧ ∃ snapshot : Snapshot operations,
          CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = .eval point.target) ∧
      final.world = [0] ∧ final.history = [0] ∧
      final.run.execution.issued = [.resource 0, .cleanup 0, .ticket 0, .ticket 1] ∧
      final.run.execution.completed = [.ticket 0] ∧
      final.run.tickets 1 = some CoreAdmittedCapturePrefix.firstClauseBody.requiredActions ∧
      final.run.execution.machine = .eval
        (p40 d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port)).target := by
  obtain ⟨d, firstAllocated, captured, post, saved, previous,
    firstResumeEq, firstCloseEq, inputEq, focusContext, focusScope, handlerIdentity, handlerArms,
    postContext, postScope, framesEq, _capturedValid, _capturedMachine, earlier, trace,
    previousValid, allEarlier, world, history, issued, completed, _resumes, _disposals,
    _annotatedStore, _tickets, machine⟩ :=
    CoreAdmittedResumePrefix.admittedResumePrefix_metadata tables families required firstResumeRow firstCloseRow
  obtain ⟨m, savedEq⟩ := splitSaved saved framesEq
  subst saved
  have current : Related graph (p35 d post m) := earlier.endpoints.2
  have bindReturn := returnBind d post m focusContext focusScope current
  let ready := CoreAdmittedHandlerPrefix.reconfigure previous (CoreAdmittedResumePrefix.restoredTarget d post)
  let bound := CoreAdmittedHandlerPrefix.reconfigure previous (bindTarget d post)
  let following := CoreAdmittedHandlerPrefix.reconfigure previous (secondTarget d post)
  have readyEq : ready = previous := by
    dsimp only [ready, CoreAdmittedHandlerPrefix.reconfigure]
    change previous.run.execution.machine = .eval (CoreAdmittedResumePrefix.restoredTarget d post) at machine
    rw [← machine]
  have readyValid : CoreAdmittedPrefix.Admitted ready := by rw [readyEq]; exact previousValid
  have plugStep : Stable.Step operations ready bound := by
    have selected := Stable.Step.plug (snapshot := previous) (plain := d.focus) (value := .unit)
      (runtimeScope := ticketScope) (tail := tailTarget d post)
      (issued := previous.run.execution.issued) (completed := previous.run.execution.completed)
      (actions := previous.run.tickets) (ValueRel.unit (graph := graph) (owners := clauseMaps) (heap := [])).closed
    rw [focusContext, focusScope] at selected
    exact selected
  obtain ⟨plugEvent, boundValid⟩ := plugStep.preserve readyValid
  have actualPlugEvent : LexicalUnwind.Event previous.run.execution bound.run.execution := by
    simpa only [readyEq] using plugEvent
  have isReady : RecursiveExpressions.Ready (bindTarget d post).expression := .bind trivial
  have bindStep : Stable.Step operations bound following :=
    .computation (snapshot := previous) (issued := previous.run.execution.issued)
      (completed := previous.run.execution.completed) (actions := previous.run.tickets) isReady bindReturn.2.2
  obtain ⟨bindEvent, followingValid⟩ := bindStep.preserve boundValid
  have position : Focus secondCode (.perform (.user 0 []) 0 (.boolean false)) (.bind 6 setterCode) := by
    change Focus (.bind 6 (.perform (.user 0 []) 0 (.boolean false)) setterCode)
      (.perform (.user 0 []) 0 (.boolean false)) (.bind 6 setterCode)
    exact .bind (by simp [Code.IsValue])
  let focusRequest : Allocating.Request following :=
    .focus (whole := secondCode) (runtimeScope := .none) (stack := tailTarget d post)
      (issued := previous.run.execution.issued) (completed := previous.run.execution.completed)
      (actions := previous.run.tickets) rfl position
  obtain ⟨afterFocus, focusEvent, realization, focusedValid⟩ := focusRequest.preserve followingValid
  dsimp [focusRequest] at realization
  cases realization with
  | focus second context scope =>
    let pending := CoreAdmittedHandlerPrefix.reconfigure previous (falseTarget d post second)
    have pendingValid : CoreAdmittedPrefix.Admitted pending := focusedValid
    have actualFocusEvent : LexicalUnwind.Event following.run.execution pending.run.execution := by
      change LexicalUnwind.Event following.run.execution
        ⟨.eval (falseTarget d post second), previous.run.execution.issued, previous.run.execution.completed⟩
      simpa only [falseTarget] using focusEvent
    have cut := selectedCut d post second m focusContext context handlerIdentity current
    have physical := cut.realizes.2.1
    have state := pendingValid.unpack
    obtain ⟨allocated, inputRows, answerRows, captureScope, savedRequirements, rights, next,
      selectedHandler, selectedCaptured, selectedTail, parameter, binder, code,
      resumeEq, closeEq, selectedPhysical, located, _closed, rightsEq, expressionEq, scopeEq,
      stackEq, captureEvent, nextState⟩ := state.capture_successor_metadata physical
        (ValueRel.boolean (graph := graph) (owners := m.bindOwner) (heap := []) (value := false)).closed 1
        (by change (previous.run.execution.issued ++ [Owner.ticket 1]).Nodup; rw [issued]; decide) resumeRow closeRow
    have sameCut := CoreAdmittedCapturePrefix.physicalUnique selectedPhysical physical
    rw [sameCut.2.2, handlerArms] at located
    rw [sameCut.1, sameCut.2.1, sameCut.2.2] at stackEq
    obtain ⟨rfl, rfl, rfl⟩ := CaptureAnnotations.clause_selection_unique located firstSelection
    let final := Snapshot.ofState nextState
    have finalValid : CoreAdmittedPrefix.Admitted final := valid_ofState nextState
    have nextEq : next = clauseTarget d post second (ScopedPorts.embedPort allocated.input.erase.erase.port) := by
      cases next with
      | mk expression runtimeScope stack =>
        change expression = _ at expressionEq
        change runtimeScope = _ at scopeEq
        change stack = _ at stackEq
        cases expressionEq
        cases scopeEq
        cases stackEq
        rfl
    have linked := captureMapped d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port)
      focusContext context handlerIdentity handlerArms current
    have suffixChain : Chain graph (p35 d post m)
        (extensionPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port))
        (p40 d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port)) :=
      .next bindReturn.1 (.next (focusMapped d post second m focusContext focusScope context scope current).1
        (CoreHandlerPrefix.chain_append (operandPrefix d post second m focusContext context current) (.last linked.1)))
    have chain := CoreHandlerPrefix.chain_append earlier suffixChain
    have finalMachine : final.run.execution.machine = .eval
        (p40 d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port)).target := by
      change LexicalUnwind.Machine.eval next = _
      rw [nextEq]
      rfl
    have extensionValid : ∀ point ∈ extensionPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port),
        ∃ snapshot : Snapshot operations, CoreAdmittedPrefix.Admitted snapshot ∧
          snapshot.run.execution.machine = .eval point.target := by
      intro point member
      simp only [extensionPoints, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact ⟨following, followingValid, rfl⟩
      · exact ⟨pending, pendingValid, rfl⟩
      · exact ⟨pending, pendingValid, rfl⟩
      · exact ⟨pending, pendingValid, rfl⟩
      · exact ⟨final, finalValid, finalMachine⟩
    refine ⟨d, post, m, second, firstAllocated, allocated, previous, bound, final,
      firstResumeEq, firstCloseEq, resumeEq, closeEq, inputEq,
      focusContext, focusScope, handlerIdentity, handlerArms, postContext, postScope,
      context, scope, previousValid, machine,
      boundValid, rfl, chain, .step (.step (.step (.step trace actualPlugEvent) bindEvent) actualFocusEvent) captureEvent,
      finalValid, ?_, world, history, ?_, completed, ?_, finalMachine⟩
    · intro point member
      rcases List.mem_cons.mp member with equal | later
      · subst point
        exact allEarlier p0 List.mem_cons_self
      · refine ⟨chain.every_point_related point later, ?_⟩
        rcases List.mem_append.mp later with prior | extension
        · exact (allEarlier point (List.mem_cons_of_mem _ prior)).2
        · exact extensionValid point extension
    · change previous.run.execution.issued ++ [.ticket 1] = _
      rw [issued]
      rfl
    · change (previous.run.tickets.insert 1 rights) 1 = _
      rw [rightsEq]
      rfl

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedSecondCapturePrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedSecondCapturePrefix.splitSaved
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedSecondCapturePrefix.returnBind

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedSecondCapturePrefix.focusMapped
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedSecondCapturePrefix.operandPrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedSecondCapturePrefix.selectedCut

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedSecondCapturePrefix.captureMapped

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedSecondCapturePrefix.admittedSecondCapturePrefix
