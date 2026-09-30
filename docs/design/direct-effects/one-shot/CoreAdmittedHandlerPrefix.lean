import CoreAdmittedPrefix
import CoreHandlerPrefix
import CoreReadyBindings

/-! Admission and actual Core linkage through handler41 installation. The cell
answer and the handler-result frame remain selected by source preservation. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedHandlerPrefix
open ScopedExpressions ScopedExecution ProtectionContracts
open InstallationSupport InstallationSupport.Preservation CoreInitialExample
open CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential
open CoreAdministrativeTransport CoreOrdinaryCompletion CoreEffectEntry CoreEffectFrames
open CoreInitialPrefix CoreExportedFixture
open CoreHandlerPrefix (raw close0 close1 close2 getter setter getterEnv methodsEnv)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cell (answer : Ty) : Stack := .push (.cell 0 0 .none answer) .nil
private def cellMaps : List MappedFrame := [([], .resourceBoundary 48 0 0)]
private theorem cellTail (answer : Ty) : PushedWithMaps graph [] cellMaps (cell answer) :=
  .boundary (.cell (node := ⟨47, .integer, [], some ⟨1,1,98,548⟩,
    .resource 0 ⟨4, .reference (.bound 0)⟩ 1 47⟩) rfl rfl) .nil
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl
private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0,.unit,[],none,.unit⟩

/-- A value-ready Core lambda bind retains the chosen resource boundary. Its
administrative Core frames leave the admitted target unchanged until the bind. -/
private theorem lambda_binding {base : CoreMachine.State} {answer : Ty} {site initializer body parameter fnBody binder : Nat}
    {environment : MEnv} {initializerCode suffix : Code} {parameterType : CoreSyntax.ValueType}
    (known : graph.node site = some (node site))
    (kind : (node site).kind = .bind ⟨binder, (node initializer).type⟩ initializer body)
    (fnKnown : graph.node initializer = some (node initializer))
    (fnKind : (node initializer).kind = .function ⟨parameter, parameterType⟩ fnBody)
    (it : CoreTranslation.translateFuel graph 56 [] initializer = .ok (raw initializer))
    (bt : CoreTranslation.translateFuel graph 56 [] body = .ok (raw body))
    (ft : CoreTranslation.translateFuel graph 55 [] fnBody = .ok (raw fnBody))
    (fnRaw : raw initializer = .lambda parameter (raw fnBody))
    (certificate : CallableCertificate graph parameter fnBody (raw fnBody))
    (current : EnvCloses graph [] base.heap environment
      (.bind binder (raw initializer) (raw body)) (.bind binder initializerCode suffix))
    (closed : ClosedValue initializerCode) (ready : ClosedExcept binder suffix)
    (plain : PlainData) (context : plain.context = .bind binder suffix) (plainScope : plain.scope = .none)
    (tail : PushedWithMaps graph base.heap cellMaps (cell answer)) :
    let entered := { base with control := .evaluate initializer environment, frames := .bind binder body environment :: framesOf cellMaps, observations := base.observations ++ [.entered site]}
    let returned := { entered with control := .returned (.closure parameter fnBody environment), observations := entered.observations ++ [.entered initializer]}
    let completed := { returned with control := .evaluate body (.binding binder (.closure parameter fnBody environment) environment), frames := framesOf cellMaps}
    let before := CoreInitialPrefix.point { base with control := .evaluate site environment, frames := framesOf cellMaps}
      ⟨.bind binder initializerCode suffix,.none,cell answer⟩
    let middle := CoreInitialPrefix.point entered ⟨.bind binder initializerCode suffix,.none,cell answer⟩
    let lastValue := CoreInitialPrefix.point returned ⟨.bind binder initializerCode suffix,.none,cell answer⟩
    let after := CoreInitialPrefix.point completed ⟨suffix.subst binder initializerCode,.none,cell answer⟩
    Chain graph before [middle,lastValue,after] after ∧
    EnvCloses graph [] base.heap (.binding binder (.closure parameter fnBody environment) environment)
      (raw body) (suffix.subst binder initializerCode) ∧
    RawStep before.target after.target [] [] := by
  have result := CoreReadyBindings.lambda_binding_mapped
    (base := base) (owners := []) (annotations := cellMaps) (target := cell answer)
    (binder := ⟨binder, (node initializer).type⟩) (parameter := ⟨parameter, parameterType⟩)
    ordered known kind fnKnown fnKind it bt ft fnRaw certificate current closed ready plain context tail
  rw [plainScope] at result
  exact result


def methodsTarget (answer : Ty) : Configuration := ⟨close1 (raw 46), .none, cell answer⟩
def continuationTarget (answer : Ty) : Configuration := ⟨close2 (raw 45), .none, cell answer⟩
def focusedTarget (answer : Ty) (plain : PlainData) : Configuration :=
  ⟨close2 (raw 41), .none, .push (.plain plain) (cell answer)⟩
def bodyTarget (answer : Ty) (plain : PlainData) (handler : HandlerData) : Configuration :=
  ⟨close2 (raw 29), .none, .push (.handler handler) (.push (.plain plain) (cell answer))⟩

def q13 (answer : Ty) : Point := point CoreHandlerPrefix.s13 (CoreAdmittedPrefix.bodyTarget answer)
def q14 (answer : Ty) : Point := point CoreHandlerPrefix.s14 (CoreAdmittedPrefix.bodyTarget answer)
def q15 (answer : Ty) : Point := point CoreHandlerPrefix.s15 (methodsTarget answer)
def q16 (answer : Ty) : Point := point CoreHandlerPrefix.s16 (methodsTarget answer)
def q17 (answer : Ty) : Point := point CoreHandlerPrefix.s17 (methodsTarget answer)
def q18 (answer : Ty) : Point := point CoreHandlerPrefix.s18 (continuationTarget answer)
def q19 (answer : Ty) (plain : PlainData) : Point := point CoreHandlerPrefix.s19 (focusedTarget answer plain)
def q20 (answer : Ty) (plain : PlainData) (handler : HandlerData) : Point :=
  point CoreHandlerPrefix.s20 (bodyTarget answer plain handler)

private theorem current47 : EnvCloses graph [] [] CoreHandlerPrefix.acquired (raw 47) (close0 (raw 47)) :=
  .binding .handle (.resource (.binding .unit (.templateUnused (by decide) .empty)))
private theorem getterClosed : ClosedValue getter := by
  change ClosedValue (.lambda 1 (.perform (.cell (.activation 0)) 0 (.variable 1)))
  simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Syntax.without,Instantiation.Effect.freeNames,Instantiation.ResourceName.freeNames]
private theorem setterClosed : ClosedValue setter := by
  change ClosedValue (.lambda 2 (.perform (.cell (.activation 0)) 1 (.variable 2)))
  simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Syntax.without,Instantiation.Effect.freeNames,Instantiation.ResourceName.freeNames]
private theorem getterReady : ClosedExcept 11 (close0 (raw 46)) := by
  have only : (close0 (raw 46)).dependencies.all (fun dep => match dep with | .variable n => n == 11 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp only (.variable n) member
private theorem setterReady : ClosedExcept 3 (close1 (raw 45)) := by
  have only : (close1 (raw 45)).dependencies.all (fun dep => match dep with | .variable n => n == 3 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp only (.variable n) member
private theorem getterCertificate : CallableCertificate graph 1 3 (raw 3) :=
  CoreCallableChecks.checkFunction_certificate (site := 4) (checked := ⟨1,3,raw 3⟩) rfl
private theorem setterCertificate : CallableCertificate graph 2 6 (raw 6) :=
  CoreCallableChecks.checkFunction_certificate (site := 7) (checked := ⟨2,6,raw 6⟩) rfl

private theorem getterPrefix (answer : Ty) :
    Chain graph (CoreAdmittedPrefix.endpoint answer) [q13 answer, q14 answer, q15 answer] (q15 answer) ∧
    EnvCloses graph [] [] getterEnv (raw 46) (close1 (raw 46)) ∧
    RawStep (CoreAdmittedPrefix.bodyTarget answer) (methodsTarget answer) [] [] := by
  exact lambda_binding (base := s12) (site := 47) (initializer := 4) (body := 46)
    (parameter := 1) (parameterType := .reference (.bound 0)) (fnBody := 3) (binder := 11)
    (environment := CoreHandlerPrefix.acquired) (initializerCode := getter) (suffix := close0 (raw 46))
    rfl rfl rfl rfl rfl rfl rfl rfl getterCertificate current47 getterClosed getterReady
    ⟨.bind 11 (close0 (raw 46)),.none,.unit,.integer,[],rfl⟩ rfl rfl (cellTail answer)

private theorem setterPrefix (answer : Ty) :
    Chain graph (q15 answer) [q16 answer, q17 answer, q18 answer] (q18 answer) ∧
    EnvCloses graph [] [] methodsEnv (raw 45) (close2 (raw 45)) ∧
    RawStep (methodsTarget answer) (continuationTarget answer) [] [] := by
  exact lambda_binding (base := CoreHandlerPrefix.s15) (site := 46) (initializer := 7) (body := 45)
    (parameter := 2) (parameterType := .product (.reference (.bound 0)) .integer) (fnBody := 6) (binder := 3)
    (environment := getterEnv) (initializerCode := setter) (suffix := close1 (raw 45))
    rfl rfl rfl rfl rfl rfl rfl rfl setterCertificate (getterPrefix answer).2.1 setterClosed setterReady
    ⟨.bind 3 (close1 (raw 45)),.none,.unit,.integer,[],rfl⟩ rfl rfl (cellTail answer)

private theorem continuationReady : ClosedExcept 12 (close2 (raw 44)) := by
  have absent : (close2 (raw 44)).dependencies.all (fun dep => match dep with | .variable n => n == 12 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp absent (.variable n) member
private theorem continuationSaved (answer : Ty) : EnvCloses graph [] [] methodsEnv
    (.lambda 12 (raw 44)) (.lambda 12 (close2 (raw 44))) :=
  (bind_components (setterPrefix answer).2.1).2
private theorem handlerSaved (answer : Ty) : EnvCloses graph [] [] methodsEnv (raw 41) (close2 (raw 41)) :=
  (bind_components (setterPrefix answer).2.1).1

private theorem continuationShape : close2 (raw 45) =
    .bind 12 (close2 (raw 41)) (close2 (raw 44)) := by rfl
private theorem handlerShape : close2 (raw 41) =
    .handle (Instantiation.freezeEffect (.user 0 [])) (close2 (raw 29)) CoreHandlerPrefix.clauses := by rfl
private theorem beforeShape :
    { CoreHandlerPrefix.s19 with
      control := .evaluate 41 methodsEnv
      frames := framesOf (([], .bind 12 44 methodsEnv) :: cellMaps) } = CoreHandlerPrefix.s19 := by rfl
private theorem afterShape :
    { CoreHandlerPrefix.s19 with
      control := .evaluate 29 methodsEnv
      frames := .handlerBoundary 41 methodsEnv 0 :: framesOf (([], .bind 12 44 methodsEnv) :: cellMaps)
      nextHandler := CoreHandlerPrefix.s19.nextHandler + 1
      observations := CoreHandlerPrefix.s19.observations ++ [.entered 41, .handlerEntered 41 0] } = CoreHandlerPrefix.s20 := by rfl
private theorem beforeMaps : uniformFrames [] CoreHandlerPrefix.s19.frames =
    (([], .bind 12 44 methodsEnv) :: cellMaps) := by rfl
private theorem afterMaps : uniformFrames [] CoreHandlerPrefix.s20.frames =
    (([], .handlerBoundary 41 methodsEnv 0) :: ([], .bind 12 44 methodsEnv) :: cellMaps) := by rfl

/-- Only the context and scope of the source-selected ordinary frame matter to
this Core administrative relation; its selected ports are retained unchanged. -/
theorem focusMapped (answer : Ty) (plain : PlainData)
    (context : plain.context = .bind 12 (close2 (raw 44))) (scope : plain.scope = .none) :
    Link graph (q18 answer) (q19 answer plain) := by
  have frame : PlainFrameRel graph [] [] (.bind 12 44 methodsEnv) plain := by
    change FrameRel graph [] [] _ plain.context
    rw [context]
    exact FrameRel.bind (fuel := 56) rfl (continuationSaved answer) continuationReady
  have focus : RawStep (continuationTarget answer) (focusedTarget answer plain) [] [] := by
    have position : Focus (.bind 12 (close2 (raw 41)) (close2 (raw 44))) (close2 (raw 41)) plain.context := by
      rw [context]
      exact .bind (by change ¬ Code.IsValue (.handle _ _ _); simp [Code.IsValue])
    have step := RawStep.focus plain position (cell answer)
    simpa only [context, scope, continuationTarget, focusedTarget, continuationShape] using step
  have successor : Related graph (q19 answer plain) :=
    ⟨rfl, close2 (raw 41), .none, .evaluate (fuel := 56) rfl (handlerSaved answer),
      pushed_mapped (.cons frame (cellTail answer))⟩
  exact .positive (setterPrefix answer).1.endpoints.2 rfl (.one focus) successor


/-- Core's actual occurrence is supplied by the static endpoint, while all
other handler data remains exactly what source installation selected. -/
theorem handlerMapped (answer : Ty) (plain : PlainData) (handler : HandlerData)
    (context : plain.context = .bind 12 (close2 (raw 44))) (_plainScope : plain.scope = .none)
    (activation : handler.activation = 0) (scope : handler.scope = .none)
    (effect : handler.effectInst = .user 0 []) (arms : handler.clauses = CoreHandlerPrefix.clauses) :
    Link graph (q19 answer plain) (q20 answer plain handler) := by
  have frame : PlainFrameRel graph [] [] (.bind 12 44 methodsEnv) plain := by
    change FrameRel graph [] [] _ plain.context
    rw [context]
    exact FrameRel.bind (fuel := 56) rfl (continuationSaved answer) continuationReady
  have current : EnvCloses graph [] [] methodsEnv
      (.handle (.user 0 []) (raw 29) (match raw 41 with | .handle _ _ cs => cs | _ => .nil))
      (.handle (Instantiation.freezeEffect handler.effectInst) (close2 (raw 29)) handler.clauses) := by
    rw [effect, arms]
    exact handlerSaved answer
  obtain ⟨before, next, step, after⟩ := handler_enter_mapped
    (base := CoreHandlerPrefix.s19) (graph := graph) (owners := []) (site := 41) (node := node 41)
    (handlerId := 0) (effect := .user 0 []) (body := 29)
    (clauses := [⟨0,.binder ⟨9,.boolean⟩,0,40⟩]) (fuel := 56) (bodyFuel := 56)
    (rawBody := raw 29) (rawClauses := match raw 41 with | .handle _ _ cs => cs | _ => .nil)
    (bodyCode := close2 (raw 29)) (data := handler) (environment := methodsEnv)
    (annotations := ([], .bind 12 44 methodsEnv) :: cellMaps) (target := .push (.plain plain) (cell answer))
    rfl rfl rfl rfl current activation (.cons frame (cellTail answer))
  have currentRelated : Related graph (q19 answer plain) := by
    rw [beforeShape, ← beforeMaps] at before
    simpa only [scope, effect, arms, ← handlerShape, q19, point, Related, focusedTarget] using before
  have actualNext : CoreMachine.next graph CoreHandlerPrefix.s19 = .stepped CoreHandlerPrefix.s20 := by
    rw [activation, beforeShape, afterShape] at next
    exact next
  have rawStep : RawStep (focusedTarget answer plain) (bodyTarget answer plain handler) [] [] := by
    simpa only [scope, effect, arms, ← handlerShape, focusedTarget, bodyTarget] using step
  have related : Related graph (q20 answer plain handler) := by
    rw [activation, scope, afterShape, ← afterMaps] at after
    exact after
  exact .positive currentRelated actualNext (.one rawStep) related


def reconfigure (snapshot : Snapshot operations) (target : Configuration) : Snapshot operations :=
  { snapshot with run := ⟨⟨.eval target, snapshot.run.execution.issued, snapshot.run.execution.completed⟩,
      snapshot.run.tickets⟩ }

def extensionPoints (answer : Ty) (plain : PlainData) (handler : HandlerData) : List Point :=
  [q13 answer, q14 answer, q15 answer, q16 answer, q17 answer, q18 answer, q19 answer plain, q20 answer plain handler]

/-- The same admitted resource prefix advances through both cell methods and
the actual handler-result context. Installation uses Core's occurrence zero,
whose freshness follows from this prefix's empty history. -/
theorem admittedHandlerPrefix (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) :
    ∃ (answer : Ty) (plain : PlainData) (handler : HandlerData) (final : Snapshot operations),
      handler.activation = 0 ∧ plain.context = .bind 12 (close2 (raw 44)) ∧ plain.scope = .none ∧
      handler.scope = .none ∧ handler.effectInst = .user 0 [] ∧ handler.clauses = CoreHandlerPrefix.clauses ∧
      CoreAdmittedPrefix.Admitted (CoreAdmittedPrefix.acquired (CoreAdmittedPrefix.initial tables families required) answer) ∧
      Chain graph p0 (CoreAdmittedPrefix.points answer ++ extensionPoints answer plain handler) (q20 answer plain handler) ∧
      RawTrace (CoreAdmittedPrefix.initial tables families required).run.execution 9 final.run.execution ∧
      CoreAdmittedPrefix.Admitted final ∧
      (∀ point ∈ p0 :: (CoreAdmittedPrefix.points answer ++ extensionPoints answer plain handler),
        Related graph point ∧ ∃ snapshot : Snapshot operations,
          CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = .eval point.target) ∧
      final.world = [0] ∧ final.history = [0] ∧ final.run.execution.issued = [.resource 0] ∧
      final.run.execution.completed = [] ∧ final.run.execution.machine = .eval (q20 answer plain handler).target := by
  obtain ⟨answer, priorChain, trace, openedValid, baseValid, allPrefix, _world, _history, _issued, _completed, _machine⟩ :=
    CoreAdmittedPrefix.admittedCorePrefix tables families required
  let base := CoreAdmittedPrefix.finished (CoreAdmittedPrefix.initial tables families required) answer
  let methods := reconfigure base (methodsTarget answer)
  let continuation := reconfigure base (continuationTarget answer)
  have getterIsReady : RecursiveExpressions.Ready (CoreAdmittedPrefix.bodyTarget answer).expression := by
    change RecursiveExpressions.Ready (.bind 11 getter (close0 (raw 46)))
    exact .bind getterClosed.1
  have getterStep : Stable.Step operations base methods :=
    .computation (snapshot := base) (issued := [.resource 0]) (completed := [])
      (actions := InitialAdmission.actions) getterIsReady (getterPrefix answer).2.2
  obtain ⟨getterEvent, methodsValid⟩ := getterStep.preserve baseValid
  have setterIsReady : RecursiveExpressions.Ready (methodsTarget answer).expression := by
    change RecursiveExpressions.Ready (.bind 3 setter (close1 (raw 45)))
    exact .bind setterClosed.1
  have setterStep : Stable.Step operations methods continuation :=
    .computation (snapshot := base) (issued := [.resource 0]) (completed := [])
      (actions := InitialAdmission.actions) setterIsReady (setterPrefix answer).2.2
  obtain ⟨setterEvent, continuationValid⟩ := setterStep.preserve methodsValid
  let request : Allocating.Request continuation :=
    .focus (whole := .bind 12 (close2 (raw 41)) (close2 (raw 44)))
      (child := close2 (raw 41)) (evaluationContext := .bind 12 (close2 (raw 44))) rfl
      (.bind (by change ¬ Code.IsValue (.handle _ _ _); simp [Code.IsValue]))
  obtain ⟨focused, focusEvent, realization, focusedValid⟩ := request.preserve continuationValid
  dsimp [request] at realization
  cases realization with
  | focus plain context plainScope =>
    have focusedAdmission : CoreAdmittedPrefix.Admitted (reconfigure base (focusedTarget answer plain)) := by
      simpa only [plainScope, CoreAdmittedPrefix.Admitted, continuation, reconfigure, focusedTarget] using focusedValid
    have focusActual : LexicalUnwind.Event continuation.run.execution
        (reconfigure base (focusedTarget answer plain)).run.execution := by
      simpa only [plainScope, reconfigure, focusedTarget] using focusEvent
    have installed : InstallationState operations policy base.contracts base.tables base.families base.required []
        base.annotations base.world [] base.history base.resumes base.disposals base.annotatedStore []
        ports base.owners InitialAdmission.emptyRows (.value .integer) (.value .integer)
        ⟨⟨.eval ⟨.handle (Instantiation.freezeEffect (.user 0 [])) (close2 (raw 29)) CoreHandlerPrefix.clauses,
          .none, .push (.plain plain) (cell answer)⟩, [.resource 0], []⟩, InitialAdmission.actions⟩ := focusedAdmission
    obtain ⟨handler, nextTables, nextFamilies, nextRequired, identity, _fresh, scope, effect, arms, _agree, event, nextState⟩ :=
      installed.install_handler_at 0 (by change (0 : Nat) ∉ ([] : List Nat); simp)
    let final := Snapshot.ofState nextState
    have finalValid : CoreAdmittedPrefix.Admitted final := valid_ofState nextState
    have handlerEvent : LexicalUnwind.Event (reconfigure base (focusedTarget answer plain)).run.execution final.run.execution := event
    have suffix : Chain graph (CoreAdmittedPrefix.endpoint answer) (extensionPoints answer plain handler)
        (q20 answer plain handler) :=
      CoreHandlerPrefix.chain_append (getterPrefix answer).1
        (CoreHandlerPrefix.chain_append (setterPrefix answer).1
          (.next (focusMapped answer plain context plainScope)
            (.last (handlerMapped answer plain handler context plainScope identity scope effect arms))))
    have chain := CoreHandlerPrefix.chain_append priorChain suffix
    have suffixAdmitted : ∀ point ∈ extensionPoints answer plain handler,
        ∃ snapshot : Snapshot operations, CoreAdmittedPrefix.Admitted snapshot ∧
          snapshot.run.execution.machine = .eval point.target := by
      intro point member
      simp only [extensionPoints, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨base, baseValid, rfl⟩
      · exact ⟨base, baseValid, rfl⟩
      · exact ⟨methods, methodsValid, rfl⟩
      · exact ⟨methods, methodsValid, rfl⟩
      · exact ⟨methods, methodsValid, rfl⟩
      · exact ⟨continuation, continuationValid, rfl⟩
      · exact ⟨reconfigure base (focusedTarget answer plain), focusedAdmission, rfl⟩
      · exact ⟨final, finalValid, rfl⟩
    refine ⟨answer, plain, handler, final, identity, context, plainScope, scope, effect, arms, openedValid, chain,
      .step (.step (.step (.step trace getterEvent) setterEvent) focusActual) handlerEvent, finalValid, ?_, rfl, ?_, rfl, rfl, rfl⟩
    · intro point member
      rcases List.mem_cons.mp member with equal | later
      · subst point; exact allPrefix p0 (List.mem_cons_self)
      · refine ⟨chain.every_point_related point later, ?_⟩
        rcases List.mem_append.mp later with earlier | extension
        · exact (allPrefix point (List.mem_cons_of_mem _ earlier)).2
        · exact suffixAdmitted point extension
    · change [] ++ [handler.activation] = [0]
      rw [identity]
      rfl

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedHandlerPrefix

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedHandlerPrefix.focusMapped
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedHandlerPrefix.handlerMapped
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedHandlerPrefix.admittedHandlerPrefix
