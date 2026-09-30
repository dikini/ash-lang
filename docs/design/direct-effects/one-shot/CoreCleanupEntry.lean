import CoreHandlerPrefix
import CoreCleanupFrames

/-! Actual cleanup registration preserves delayed execution. Its callback/body
interpretations come from one current lexical derivation. This does not assert
M4 validity, metadata authentication, cleanup freshness or request simulation. -/
namespace Ash.OneShot.CoreCleanupEntry
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreCleanupFrames CoreInitialPrefix CoreHandlerPrefix CoreExportedFixture
open CoreStrictPotential CoreAdministrativeTransport CoreOrdinaryCompletion

private theorem lambda_is_closure {graph : CoreSyntax.Graph} (related : ValueRel graph owners heap value (.lambda parameter body)) :
    ∃ parameter body saved, value = .closure parameter body saved := by
  cases related with
  | closure => exact ⟨_,_,_,rfl⟩

/-- Registration never evaluates the saved action. It emits one cleanup
creation and saves the exact delayed Core action/environment at the old key. -/
theorem cleanup_enter_mapped {graph : CoreSyntax.Graph} { base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .cleanup callback action body)
    (shape : CoreTranslation.checkCleanup graph site callback action = .ok ())
    (translated : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment (.cleanup (.variable callback.id) rawBody)
      (.cleanup data.action bodyCode))
    (callable : data.action = .lambda parameter lambdaBody)
    (identity : data.identity = base.nextCleanup)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations { base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.cleanup data.action bodyCode,data.scope,target⟩ ∧
    CoreMachine.next graph { base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped { base with control := .evaluate body environment, frames := .cleanupBoundary action environment data.identity :: framesOf annotations, nextCleanup := base.nextCleanup + 1, observations := base.observations ++ [.entered site,.cleanupArmed data.identity]} ∧
    RawStep ⟨.cleanup data.action bodyCode,data.scope,target⟩
      ⟨bodyCode,data.scope,.push (.armed data) target⟩ [.cleanup data.identity] [] ∧
    ComponentMapped graph owners ((owners,.cleanupBoundary action environment data.identity) :: annotations)
      { base with control := .evaluate body environment, frames := .cleanupBoundary action environment data.identity :: framesOf annotations, nextCleanup := base.nextCleanup + 1, observations := base.observations ++ [.entered site,.cleanupArmed data.identity]}
      ⟨bodyCode,data.scope,.push (.armed data) target⟩ := by
  obtain ⟨callbackSaved,bodySaved⟩ := cleanup_components current
  obtain ⟨value,lookup,related⟩ := callbackSaved.lookup data.closed
  have closureRelated := related
  rw [callable] at closureRelated
  obtain ⟨parameter,functionBody,captured,rfl⟩ := lambda_is_closure closureRelated
  have delayed := checked_action_translation (owners := owners) shape
  have boundary : CleanupRel graph owners base.heap (.cleanupBoundary action environment data.identity) data :=
    .armed known kind shape delayed (app_unit callbackSaved) lookup related
  have whole : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.cleanup (.variable callback.id) rawBody) := by
    rw [CoreTranslation.cleanup_equation _ _ _ _ _ _ _ _ known kind shape,translated]; rfl
  refine ⟨⟨rfl,_,data.scope,.evaluate whole current,pushed_mapped older⟩,?_,
    .enterCleanup data bodyCode target,⟨rfl,_,data.scope,.evaluate translated bodySaved,pushed_mapped (.cleanup boundary older)⟩⟩
  simp [CoreMachine.next,known,kind,lookup,identity,List.append_assoc]

/-- A handler boundary cannot be a value-ready flattened ordinary frame. Thus
its current code/scope and the complete pushed stack can be recovered. -/
private theorem handler_head_pushed {graph : CoreSyntax.Graph}
    (related : OrdinaryWithMaps graph heap ((owners,.handlerBoundary site saved activation) :: rest)
      code scope result resultScope target) :
    code = result ∧ scope = resultScope ∧
      PushedWithMaps graph heap ((owners,.handlerBoundary site saved activation) :: rest) target := by
  obtain ⟨flatPrefix,suffix,split,flat,pushed⟩ := related
  cases flat with
  | nil => exact ⟨rfl,rfl,split.symm ▸ pushed⟩
  | @cons frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .handlerBoundary site saved activation := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same
      cases frame
  | @initializer frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .handlerBoundary site saved activation := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same
      cases frame
  | @request frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .handlerBoundary site saved activation := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same
      cases frame
  | @resume frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .handlerBoundary site saved activation := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same
      cases frame

private theorem translation_unique {rawCode otherRaw : Code}
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok rawCode)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok otherRaw) : rawCode = otherRaw := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index rawCode (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index otherRaw (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)


set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def outerMaps : List MappedFrame := q20.annotations
private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0,.unit,[],none,.unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl

/-- Recover current body interpretation and saved boundaries from the frozen
reached endpoint, rather than assuming a new related starting configuration. -/
private theorem current_body : EnvCloses graph [] [] methodsEnv (raw 29) (close2 (raw 29)) ∧
    PushedWithMaps graph [] outerMaps bodyTarget.stack := by
  obtain ⟨shape,code,scope,control,stack⟩ := reached_handler_body_related
  change OrdinaryWithMaps graph []
    (([],.handlerBoundary 41 methodsEnv 0) :: [([],.bind 12 44 methodsEnv),([],.resourceBoundary 48 0 0)])
    code scope (close2 (raw 29)) .none bodyTarget.stack at stack
  obtain ⟨rfl,rfl,pushed⟩ := handler_head_pushed stack
  cases control with
  | evaluate translated saved =>
      have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 29 = .ok (raw 29))
      cases same
      exact ⟨saved,pushed⟩

private theorem callback_binding { base : CoreMachine.State} {site initializer body parameter fnBody binder : Nat}
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
    (tail : PushedWithMaps graph base.heap outerMaps bodyTarget.stack) :
    let entered := { base with control := .evaluate initializer environment, frames := .bind binder body environment :: framesOf outerMaps, observations := base.observations ++ [.entered site]}
    let returned := { entered with control := .returned (.closure parameter fnBody environment), observations := entered.observations ++ [.entered initializer]}
    let completed := { returned with control := .evaluate body (.binding binder (.closure parameter fnBody environment) environment), frames := framesOf outerMaps}
    let before := CoreInitialPrefix.point { base with control := .evaluate site environment, frames := framesOf outerMaps}
      ⟨.bind binder initializerCode suffix,.none,bodyTarget.stack⟩
    let middle := CoreInitialPrefix.point entered ⟨.bind binder initializerCode suffix,.none,bodyTarget.stack⟩
    let lastValue := CoreInitialPrefix.point returned ⟨.bind binder initializerCode suffix,.none,bodyTarget.stack⟩
    let after := CoreInitialPrefix.point completed ⟨suffix.subst binder initializerCode,.none,bodyTarget.stack⟩
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
    fnKnown fnKind ft certificate initSaved closed (.bind binder body environment :: framesOf outerMaps)
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


def callbackCode : Code := close2 (raw 13)
def callbackEnv : MEnv := .binding 8 (.closure 5 12 methodsEnv) methodsEnv
def cleanupCode : Code := (close2 (raw 28)).subst 8 callbackCode
def guardedCode : Code := (close2 (raw 24)).subst 8 callbackCode
private theorem callbackClosed : ClosedValue callbackCode := by
  refine ⟨trivial,(by change callbackCode.freeNames = []; decide),?_⟩
  have bound : callbackCode.dependencies.all (fun dep => match dep with | .variable _ | .ticket _ => false | _ => true) = true := by decide
  intro dependency member
  have valid := List.all_eq_true.mp bound dependency member
  cases dependency <;> simp_all
private theorem suffixReady : ClosedExcept 8 (close2 (raw 28)) := by
  have bound : (close2 (raw 28)).dependencies.all (fun dep => match dep with | .variable n => n == 8 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp bound (.variable n) member
private theorem callbackCertificate : CallableCertificate graph 5 12 (raw 12) :=
  CoreCallableChecks.checkFunction_certificate (site := 13) (checked := ⟨5,12,raw 12⟩) rfl

def s21 : CoreMachine.State := { s20 with control := .evaluate 13 methodsEnv, frames := .bind 8 28 methodsEnv :: s20.frames, observations := s20.observations ++ [.entered 29]}
def s22 : CoreMachine.State := { s21 with control := .returned (.closure 5 12 methodsEnv), observations := s21.observations ++ [.entered 13]}
def s23 : CoreMachine.State := { s22 with control := .evaluate 28 callbackEnv, frames := s20.frames}
def cleanupTarget : Configuration := ⟨cleanupCode,.none,bodyTarget.stack⟩
def r21 : Point := point s21 bodyTarget
def r22 : Point := point s22 bodyTarget
def r23 : Point := point s23 cleanupTarget

private theorem callback_prefix : Chain graph q20 [r21,r22,r23] r23 ∧
    EnvCloses graph [] [] callbackEnv (raw 28) cleanupCode ∧ RawStep bodyTarget cleanupTarget [] [] := by
  exact callback_binding (base := s20) (site := 29) (initializer := 13) (body := 28)
    (parameter := 5) (parameterType := .unit) (fnBody := 12) (binder := 8)
    (environment := methodsEnv) (initializerCode := callbackCode) (suffix := close2 (raw 28))
    rfl rfl rfl rfl rfl rfl rfl rfl callbackCertificate current_body.1 callbackClosed suffixReady
    ⟨.bind 8 (close2 (raw 28)),.none,.unit,.unit,[],rfl⟩ rfl rfl current_body.2


def actionData : ActionData := ⟨0,callbackCode,callbackClosed,.none,.unit,[.cell 0]⟩
def s24 : CoreMachine.State := { s23 with control := .evaluate 24 callbackEnv, frames := .cleanupBoundary 27 callbackEnv 0 :: s23.frames, nextCleanup := 1, observations := s23.observations ++ [.entered 28,.cleanupArmed 0]}
def guardedTarget : Configuration := ⟨guardedCode,.none,.push (.armed actionData) bodyTarget.stack⟩
def r24 : Point := point s24 guardedTarget
private theorem register : Link graph r23 r24 := by
  obtain ⟨before,next,step,after⟩ := cleanup_enter_mapped
    (base := s23) (graph := graph) (owners := []) (site := 28) (node := node 28)
    (callback := ⟨8,.function .unit .unit [.cell (.bound 0)]⟩) (action := 27) (body := 24)
    (fuel := 56) (rawBody := raw 24) (bodyCode := guardedCode) (environment := callbackEnv)
    (data := actionData) (parameter := 5) (lambdaBody := close2 (raw 12))
    (annotations := outerMaps) (target := bodyTarget.stack)
    rfl rfl rfl rfl callback_prefix.2.1 rfl rfl current_body.2
  exact .positive before next (.one step) after

/-- Four actual steps after handler entry: focus callback binding, return the
closure, complete the binding, and register cleanup without evaluating action27. -/
theorem handler_to_cleanup : Chain graph q20 [r21,r22,r23,r24] r24 :=
  chain_append callback_prefix.1 (.last register)

theorem exported_cleanup_prefix : Chain graph p0
    [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20,r21,r22,r23,r24] r24 :=
  chain_append exported_handler_prefix handler_to_cleanup

theorem reached_guarded_related : Related graph r24 := exported_cleanup_prefix.endpoints.2

theorem exported_cleanup_steps : CoreAllocationHistory.Steps graph 24 (CoreMachine.initial graph) s24 :=
  exported_cleanup_prefix.core_steps

theorem exported_cleanup_history : CoreAllocationHistory.History s24 :=
  CoreAllocationHistory.initial_steps_history graph exported_cleanup_steps

/-- The action remains saved, not evaluated: current control is guarded24 and
the newly armed boundary retains exact action27, environment and key0. -/
theorem reached_guarded_control : r24.state.control = .evaluate 24 callbackEnv ∧
    r24.state.frames = .cleanupBoundary 27 callbackEnv 0 :: s20.frames ∧
    r24.state.nextCleanup = 1 := ⟨rfl,rfl,rfl⟩

private theorem rawTrace_append (first : RawTrace before middle created discharged)
    (second : RawTrace middle after laterCreated laterDischarged) :
    RawTrace before after (created ++ laterCreated) (laterDischarged ++ discharged) := by
  induction first with
  | refl => simpa using second
  | next step rest ih => simpa [List.append_assoc] using RawTrace.next step (ih second)

theorem handler_to_cleanup_ledger : RawTrace bodyTarget guardedTarget [.cleanup 0] [] := by
  have step : RawStep cleanupTarget guardedTarget [.cleanup 0] [] :=
    RawStep.enterCleanup actionData guardedCode bodyTarget.stack
  exact .next callback_prefix.2.2 (.next step (.refl _))

theorem exported_cleanup_ledger : RawTrace rootTarget guardedTarget [.resource 0,.cleanup 0] [] :=
  rawTrace_append exported_handler_ledger handler_to_cleanup_ledger

theorem delayed_action_not_entered : CoreMachine.Observation.entered 27 ∉ s24.observations := by decide

/-- A missing callback is a rejection, never registration progress. -/
theorem missing_callback_not_step (after : CoreMachine.State) :
    ¬ CoreMachine.Step graph { s23 with control := .evaluate 28 .empty} after :=
  CoreMachine.rejected_not_step graph _ .cleanupCallback rfl after

#print axioms delayed_action_not_entered
#print axioms missing_callback_not_step
#print axioms cleanup_enter_mapped
#print axioms handler_to_cleanup
#print axioms exported_cleanup_prefix
#print axioms reached_guarded_related
#print axioms exported_cleanup_steps
#print axioms exported_cleanup_history
#print axioms reached_guarded_control
#print axioms handler_to_cleanup_ledger
#print axioms exported_cleanup_ledger
end Ash.OneShot.CoreCleanupEntry
