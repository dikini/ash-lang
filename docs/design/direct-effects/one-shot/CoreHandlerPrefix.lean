import CoreInitialPrefix

/-! Exact extension of the retained initial prefix through the generated cell
methods and handler installation. Scopes and PlainData remain supplied metadata;
this does not authenticate M4 admission or execute the cleanup body. -/
namespace Ash.OneShot.CoreHandlerPrefix
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreStrictPotential CoreAdministrativeTransport CoreOrdinaryCompletion CoreEffectEntry CoreEffectFrames
open CoreInitialPrefix CoreExportedFixture
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def raw (index : Nat) : Code := (CoreTranslation.translateFuel graph 56 [] index).toOption.getD .unit
def acquired : MEnv := .binding 4 (.handle 0) (.resource 0 0 CoreInitialPrefix.called)
def close0 (code : Code) : Code :=
  ((code.subst 4 (.resourceRef (.activation 0))).instantiate (Instantiation.Environment.empty.bind 0 0)).subst 0 .unit
def getter : Code := close0 (raw 4)
def getterEnv : MEnv := .binding 11 (.closure 1 3 acquired) acquired
def close1 (code : Code) : Code := close0 (code.subst 11 getter)
def setter : Code := close1 (raw 7)
def methodsEnv : MEnv := .binding 3 (.closure 2 6 getterEnv) getterEnv
def close2 (code : Code) : Code := close1 (code.subst 3 setter)
def cell : Stack := .push (.cell 0 0 .none .integer) .nil
private def cellMaps : List MappedFrame := [([], .resourceBoundary 48 0 0)]
private theorem cellTail : PushedWithMaps graph [] cellMaps cell :=
  .boundary (.cell (node := ⟨47, .integer, [], some ⟨1,1,98,548⟩,
    .resource 0 ⟨4, .reference (.bound 0)⟩ 1 47⟩) rfl rfl) .nil
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl
private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0,.unit,[],none,.unit⟩

/-- Three actual transitions for a ready function initializer. The saved body
is derived from the same current bind interpretation. -/
private theorem lambda_binding { base : CoreMachine.State} {site initializer body parameter fnBody binder : Nat}
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
    (tail : PushedWithMaps graph base.heap cellMaps cell) :
    let entered := { base with control := .evaluate initializer environment, frames := .bind binder body environment :: framesOf cellMaps, observations := base.observations ++ [.entered site]}
    let returned := { entered with control := .returned (.closure parameter fnBody environment), observations := entered.observations ++ [.entered initializer]}
    let completed := { returned with control := .evaluate body (.binding binder (.closure parameter fnBody environment) environment), frames := framesOf cellMaps}
    let before := CoreInitialPrefix.point { base with control := .evaluate site environment, frames := framesOf cellMaps}
      ⟨.bind binder initializerCode suffix,.none,cell⟩
    let middle := CoreInitialPrefix.point entered ⟨.bind binder initializerCode suffix,.none,cell⟩
    let lastValue := CoreInitialPrefix.point returned ⟨.bind binder initializerCode suffix,.none,cell⟩
    let after := CoreInitialPrefix.point completed ⟨suffix.subst binder initializerCode,.none,cell⟩
    Chain graph before [middle,lastValue,after] after ∧
    EnvCloses graph [] base.heap (.binding binder (.closure parameter fnBody environment) environment)
      (raw body) (suffix.subst binder initializerCode) ∧
    RawStep before.target after.target [] [] := by
  dsimp only
  obtain ⟨initSaved, bodySaved⟩ := bind_components current
  have entry := bind_entry_same_target ordered known kind it bt current closed ready plain context tail
  rw [fnRaw] at initSaved
  obtain ⟨valueWitness, translated⟩ := CoreAdministrativeSteps.lambda_evaluate
    (base := { base with observations := base.observations ++ [.entered site] })
    fnKnown fnKind ft certificate initSaved closed (.bind binder body environment :: framesOf cellMaps)
  have frame : PlainFrameRel graph [] base.heap (.bind binder body environment) plain :=
    by
      change FrameRel graph [] base.heap _ plain.context
      rw [context]; exact .bind bt bodySaved ready
  have stack := prepend_mapped frame closed (pushed_mapped tail) Execution.Scope.none
  simp only [context, Context.plug] at stack
  have transport := value_entry_mapped valueWitness rfl rfl stack
  obtain ⟨value, equal, related⟩ := valueWitness.returned
  have valueEqual : value = .closure parameter fnBody environment := by
    exact CoreMachine.Control.returned.inj equal.symm
  cases valueEqual
  obtain ⟨beforeReturn, next, plug, bind, afterReturn⟩ := bind_return_mapped
    (base := { base with observations := base.observations ++ [.entered site] ++ [.entered initializer] })
    bt bodySaved ready related plain context tail Execution.Scope.none
  rw [plainScope] at entry transport bind afterReturn
  exact ⟨.next (.traversal entry) (.next (.value transport)
    (.last (.positive transport.successor next (.one bind) afterReturn))), bodySaved.beta_argument related, bind⟩


def s13 : CoreMachine.State := { s12 with control := .evaluate 4 acquired, frames := .bind 11 46 acquired :: framesOf cellMaps, observations := s12.observations ++ [.entered 47] }
def s14 : CoreMachine.State := { s13 with control := .returned (.closure 1 3 acquired), observations := s13.observations ++ [.entered 4] }
def s15 : CoreMachine.State := { s14 with control := .evaluate 46 getterEnv, frames := framesOf cellMaps }
def s16 : CoreMachine.State := { s15 with control := .evaluate 7 getterEnv, frames := .bind 3 45 getterEnv :: framesOf cellMaps, observations := s15.observations ++ [.entered 46] }
def s17 : CoreMachine.State := { s16 with control := .returned (.closure 2 6 getterEnv), observations := s16.observations ++ [.entered 7] }
def s18 : CoreMachine.State := { s17 with control := .evaluate 45 methodsEnv, frames := framesOf cellMaps }
def s19 : CoreMachine.State := { s18 with control := .evaluate 41 methodsEnv, frames := .bind 12 44 methodsEnv :: framesOf cellMaps, observations := s18.observations ++ [.entered 45] }
def s20 : CoreMachine.State := { s19 with control := .evaluate 29 methodsEnv, frames := .handlerBoundary 41 methodsEnv 0 :: s19.frames, nextHandler := 1, observations := s19.observations ++ [.entered 41, .handlerEntered 41 0] }
def methodsTarget : Configuration := ⟨close1 (raw 46),.none,cell⟩
def continuationTarget : Configuration := ⟨close2 (raw 45),.none,cell⟩
def handlerPlain : PlainData := ⟨.bind 12 (close2 (raw 44)),.none,.unit,.integer,[],rfl⟩
def handlerTarget : Configuration := ⟨close2 (raw 41),.none,.push (.plain handlerPlain) cell⟩
def q13 : Point := point s13 cellTarget
def q14 : Point := point s14 cellTarget
def q15 : Point := point s15 methodsTarget
def q16 : Point := point s16 methodsTarget
def q17 : Point := point s17 methodsTarget
def q18 : Point := point s18 continuationTarget
def q19 : Point := point s19 handlerTarget

private theorem current47 : EnvCloses graph [] [] acquired (raw 47) (close0 (raw 47)) :=
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

private theorem getter_prefix : Chain graph p12 [q13,q14,q15] q15 ∧
    EnvCloses graph [] [] getterEnv (raw 46) (close1 (raw 46)) ∧
    RawStep cellTarget methodsTarget [] [] := by
  have result := lambda_binding (base := s12) (site := 47) (initializer := 4) (body := 46)
    (parameter := 1) (parameterType := .reference (.bound 0)) (fnBody := 3) (binder := 11)
    (environment := acquired) (initializerCode := getter) (suffix := close0 (raw 46))
    rfl rfl rfl rfl rfl rfl rfl rfl getterCertificate current47 getterClosed getterReady
    ⟨.bind 11 (close0 (raw 46)),.none,.unit,.integer,[],rfl⟩ rfl rfl cellTail
  exact result
private theorem setter_prefix : Chain graph q15 [q16,q17,q18] q18 ∧
    EnvCloses graph [] [] methodsEnv (raw 45) (close2 (raw 45)) ∧
    RawStep methodsTarget continuationTarget [] [] := by
  have result := lambda_binding (base := s15) (site := 46) (initializer := 7) (body := 45)
    (parameter := 2) (parameterType := .product (.reference (.bound 0)) .integer) (fnBody := 6) (binder := 3)
    (environment := getterEnv) (initializerCode := setter) (suffix := close1 (raw 45))
    rfl rfl rfl rfl rfl rfl rfl rfl setterCertificate getter_prefix.2.1 setterClosed setterReady
    ⟨.bind 3 (close1 (raw 45)),.none,.unit,.integer,[],rfl⟩ rfl rfl cellTail
  exact result

private theorem continuationReady : ClosedExcept 12 (close2 (raw 44)) := by
  have absent : (close2 (raw 44)).dependencies.all (fun dep => match dep with | .variable n => n == 12 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp absent (.variable n) member
private theorem continuationSaved : EnvCloses graph [] [] methodsEnv
    (.lambda 12 (raw 44)) (.lambda 12 (close2 (raw 44))) :=
  (bind_components setter_prefix.2.1).2
private theorem handlerSaved : EnvCloses graph [] [] methodsEnv (raw 41) (close2 (raw 41)) :=
  (bind_components setter_prefix.2.1).1
private theorem continuationFrame : PlainFrameRel graph [] [] (.bind 12 44 methodsEnv) handlerPlain :=
  FrameRel.bind (fuel := 56) rfl continuationSaved continuationReady
private theorem focus_step : RawStep continuationTarget handlerTarget [] [] :=
  RawStep.focus handlerPlain (Focus.bind (by change ¬ Code.IsValue (.handle _ _ _); simp [Code.IsValue])) cell
private theorem focus_handler : Link graph q18 q19 := by
  have next : CoreMachine.next graph s18 = .stepped s19 := rfl
  have focus := focus_step
  have successor : Related graph q19 := by
    exact ⟨rfl, close2 (raw 41), .none, .evaluate (fuel := 56) rfl handlerSaved,
      pushed_mapped (.cons continuationFrame cellTail)⟩
  exact .positive setter_prefix.1.endpoints.2 next (.one focus) successor

def clauses : Clauses := match close2 (raw 41) with | .handle _ _ cs => cs | _ => .nil
def handlerData : HandlerData :=
  ⟨0,.user 0 [],clauses,.none,.unit,by decide⟩
def bodyTarget : Configuration :=
  ⟨close2 (raw 29),.none,.push (.handler handlerData) (.push (.plain handlerPlain) cell)⟩
def q20 : Point := point s20 bodyTarget
private theorem enter_handler : Link graph q19 q20 := by
  obtain ⟨before, next, step, after⟩ := handler_enter_mapped
    (base := s19) (graph := graph) (owners := []) (site := 41) (node := node 41)
    (handlerId := 0) (effect := .user 0 []) (body := 29)
    (clauses := [⟨0,.binder ⟨9,.boolean⟩,0,40⟩]) (fuel := 56) (bodyFuel := 56)
    (rawBody := raw 29) (rawClauses := match raw 41 with | .handle _ _ cs => cs | _ => .nil)
    (bodyCode := close2 (raw 29)) (data := handlerData) (environment := methodsEnv)
    (annotations := ([], .bind 12 44 methodsEnv) :: cellMaps) (target := .push (.plain handlerPlain) cell)
    rfl rfl rfl rfl handlerSaved rfl (.cons continuationFrame cellTail)
  exact .positive before next (.one step) after

/-- Concatenate the existing indexed linked executions without a second
simulation or unrestricted silent-step rule. -/
theorem chain_append (first : Chain graph before left middle) (second : Chain graph middle right after) :
    Chain graph before (left ++ right) after := by
  induction first with
  | last link => exact .next link second
  | next link rest ih => exact .next link (ih second)

/-- Getter, setter, ordinary continuation focus, and handler installation. -/
theorem acquired_to_handler : Chain graph p12 [q13,q14,q15,q16,q17,q18,q19,q20] q20 :=
  chain_append getter_prefix.1 (chain_append setter_prefix.1 (.next focus_handler (.last enter_handler)))

/-- The fixed exported graph starts at actual CoreMachine.initial. All twenty
actual Core transitions retain related intermediate target configurations. -/
theorem exported_handler_prefix : Chain graph p0
    [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20] q20 :=
  chain_append exported_initial_prefix acquired_to_handler

theorem reached_handler_body_related : Related graph q20 := exported_handler_prefix.endpoints.2

theorem exported_handler_steps : CoreAllocationHistory.Steps graph 20 (CoreMachine.initial graph) s20 :=
  exported_handler_prefix.core_steps

theorem exported_handler_history : CoreAllocationHistory.History s20 :=
  CoreAllocationHistory.initial_steps_history graph exported_handler_steps

theorem reached_handler_body : q20.state.control = .evaluate 29 methodsEnv ∧
    q20.state.nextActivation = 1 ∧ q20.state.nextHandler = 1 ∧
    q20.state.frames = [.handlerBoundary 41 methodsEnv 0, .bind 12 44 methodsEnv, .resourceBoundary 48 0 0] :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- Raw resource accounting of the same fixed target prefix. Handler installation
and ordinary steps do not create resource/ticket ledger entries. -/
private theorem rawTrace_append (first : RawTrace before middle created discharged)
    (second : RawTrace middle after laterCreated laterDischarged) :
    RawTrace before after (created ++ laterCreated) (laterDischarged ++ discharged) := by
  induction first with
  | refl => simpa using second
  | next step rest ih => simpa [List.append_assoc] using RawTrace.next step (ih second)

theorem acquired_to_handler_ledger : RawTrace cellTarget bodyTarget [] [] := by
  have enter : RawStep handlerTarget bodyTarget [] [] :=
    RawStep.enterHandler handlerData (close2 (raw 29)) (.push (.plain handlerPlain) cell)
  exact .next getter_prefix.2.2 (.next setter_prefix.2.2 (.next focus_step (.next enter (.refl _))))

theorem exported_handler_ledger : RawTrace rootTarget bodyTarget [.resource 0] [] :=
  rawTrace_append exported_target_ledger acquired_to_handler_ledger

#print axioms acquired_to_handler_ledger
#print axioms exported_handler_ledger
#print axioms acquired_to_handler
#print axioms exported_handler_prefix
#print axioms reached_handler_body_related
#print axioms exported_handler_steps
#print axioms exported_handler_history
#print axioms reached_handler_body
end Ash.OneShot.CoreHandlerPrefix
