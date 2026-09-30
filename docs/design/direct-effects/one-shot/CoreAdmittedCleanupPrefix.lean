import CoreAdmittedHandlerPrefix
import CoreReadyBindings
import CoreCleanupEntry

/-! Source-preserved callback binding and cleanup registration at the actual
exported Core states. Registration retains the selected action data and saves
its delayed callback without executing it. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCleanupPrefix
open ScopedExpressions ScopedExecution ProtectionContracts
open InstallationSupport InstallationSupport.Preservation CoreInitialExample
open CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential
open CoreOrdinaryCompletion CoreInitialPrefix CoreExportedFixture
open CoreHandlerPrefix (raw close2 methodsEnv)
open CoreCleanupEntry (callbackCode cleanupCode guardedCode callbackEnv)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def outerMaps : List MappedFrame :=
  [([], .handlerBoundary 41 methodsEnv 0), ([], .bind 12 44 methodsEnv), ([], .resourceBoundary 48 0 0)]
private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0, .unit, [], none, .unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl

def cleanupTarget (answer : Ty) (plain : PlainData) (handler : HandlerData) : Configuration :=
  ⟨cleanupCode, .none, (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler).stack⟩
def guardedTarget (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData) : Configuration :=
  ⟨guardedCode, .none, .push (.armed action) (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler).stack⟩

def r21 (answer : Ty) (plain : PlainData) (handler : HandlerData) : Point :=
  point CoreCleanupEntry.s21 (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler)
def r22 (answer : Ty) (plain : PlainData) (handler : HandlerData) : Point :=
  point CoreCleanupEntry.s22 (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler)
def r23 (answer : Ty) (plain : PlainData) (handler : HandlerData) : Point :=
  point CoreCleanupEntry.s23 (cleanupTarget answer plain handler)
def r24 (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData) : Point :=
  point CoreCleanupEntry.s24 (guardedTarget answer plain handler action)

private theorem translation_unique {owners : CoreTranslation.OwnerMap} {rawCode otherRaw : Code}
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok rawCode)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok otherRaw) : rawCode = otherRaw := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index rawCode (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index otherRaw (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

/-- Project current lexical code and pushed boundaries from the actual reached
handler point; a future interpretation is not an input. -/
private theorem currentBody (answer : Ty) (plain : PlainData) (handler : HandlerData)
    (related : Related graph (CoreAdmittedHandlerPrefix.q20 answer plain handler)) :
    EnvCloses graph [] [] methodsEnv (raw 29) (close2 (raw 29)) ∧
    PushedWithMaps graph [] outerMaps (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler).stack := by
  obtain ⟨_shape, code, scope, control, stack⟩ := related
  change OrdinaryWithMaps graph []
    (([], .handlerBoundary 41 methodsEnv 0) :: [([], .bind 12 44 methodsEnv), ([], .resourceBoundary 48 0 0)])
    code scope (close2 (raw 29)) .none (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler).stack at stack
  obtain ⟨rfl, rfl, pushed⟩ := CoreReadyBindings.handler_head_pushed stack
  cases control with
  | evaluate translated saved =>
    have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 29 = .ok (raw 29))
    cases same
    exact ⟨saved, pushed⟩

private theorem callbackClosed : ClosedValue callbackCode := by
  refine ⟨trivial, (by change callbackCode.freeNames = []; decide), ?_⟩
  have bound : callbackCode.dependencies.all (fun dep => match dep with | .variable _ | .ticket _ => false | _ => true) = true := by decide
  intro dependency member
  have valid := List.all_eq_true.mp bound dependency member
  cases dependency <;> simp_all
private theorem suffixReady : ClosedExcept 8 (close2 (raw 28)) := by
  have bound : (close2 (raw 28)).dependencies.all (fun dep => match dep with | .variable n => n == 8 | _ => true) = true := by decide
  intro n member
  simpa using List.all_eq_true.mp bound (.variable n) member
private theorem callbackCertificate : CallableCertificate graph 5 12 (raw 12) :=
  CoreCallableChecks.checkFunction_certificate (site := 13) (checked := ⟨5, 12, raw 12⟩) rfl

/-- The arbitrary selected handler/plain/cell tail is passed directly to the
shared lambda-bind composition. -/
theorem callbackPrefix (answer : Ty) (plain : PlainData) (handler : HandlerData)
    (related : Related graph (CoreAdmittedHandlerPrefix.q20 answer plain handler)) :
    Chain graph (CoreAdmittedHandlerPrefix.q20 answer plain handler)
      [r21 answer plain handler, r22 answer plain handler, r23 answer plain handler] (r23 answer plain handler) ∧
    EnvCloses graph [] [] callbackEnv (raw 28) cleanupCode ∧
    RawStep (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler) (cleanupTarget answer plain handler) [] [] := by
  obtain ⟨current, pushed⟩ := currentBody answer plain handler related
  exact CoreReadyBindings.lambda_binding_mapped
    (base := CoreHandlerPrefix.s20) (owners := []) (annotations := outerMaps)
    (target := (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler).stack)
    (site := 29) (initializer := 13) (body := 28)
    (binder := ⟨8, (node 13).type⟩) (parameter := ⟨5, .unit⟩)
    (fnBody := 12) (fuel := 56) (fnFuel := 55)
    (environment := methodsEnv) (rawInitializer := raw 13) (rawBody := raw 28) (rawFunction := raw 12)
    (initializerCode := callbackCode) (suffix := close2 (raw 28))
    ordered rfl rfl rfl rfl rfl rfl rfl rfl callbackCertificate current callbackClosed suffixReady
    ⟨.bind 8 (close2 (raw 28)), .none, .unit, .unit, [], rfl⟩ rfl pushed


private theorem beforeShape :
    { CoreCleanupEntry.s23 with
      control := .evaluate 28 callbackEnv
      frames := framesOf outerMaps } = CoreCleanupEntry.s23 := by rfl
private theorem afterShape :
    { CoreCleanupEntry.s23 with
      control := .evaluate 24 callbackEnv
      frames := .cleanupBoundary 27 callbackEnv 0 :: framesOf outerMaps
      nextCleanup := CoreCleanupEntry.s23.nextCleanup + 1
      observations := CoreCleanupEntry.s23.observations ++ [.entered 28, .cleanupArmed 0] } = CoreCleanupEntry.s24 := by rfl
private theorem beforeMaps : uniformFrames [] CoreCleanupEntry.s23.frames = outerMaps := by rfl
private theorem afterMaps : uniformFrames [] CoreCleanupEntry.s24.frames =
    ([], .cleanupBoundary 27 callbackEnv 0) :: outerMaps := by rfl
private theorem cleanupShape : cleanupCode = .cleanup callbackCode guardedCode := by rfl

/-- Registration uses precisely the action chosen by source preservation,
including its saved ports/effects. Only its proved identity/action/scope
projections synchronize the actual Core registration. -/
theorem registerMapped (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData)
    (related : Related graph (CoreAdmittedHandlerPrefix.q20 answer plain handler))
    (identity : action.identity = 0) (actionEq : action.action = callbackCode) (scope : action.scope = .none) :
    Link graph (r23 answer plain handler) (r24 answer plain handler action) := by
  obtain ⟨_current, pushed⟩ := currentBody answer plain handler related
  have current : EnvCloses graph [] [] callbackEnv (.cleanup (.variable 8) (raw 24)) (.cleanup action.action guardedCode) := by
    rw [actionEq]
    exact (callbackPrefix answer plain handler related).2.1
  obtain ⟨before, next, step, after⟩ := CoreCleanupEntry.cleanup_enter_mapped
    (base := CoreCleanupEntry.s23) (graph := graph) (owners := []) (site := 28) (node := node 28)
    (callback := ⟨8, .function .unit .unit [.cell (.bound 0)]⟩) (action := 27) (body := 24)
    (fuel := 56) (rawBody := raw 24) (bodyCode := guardedCode) (environment := callbackEnv)
    (data := action) (parameter := 5) (lambdaBody := close2 (raw 12))
    (annotations := outerMaps) (target := (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler).stack)
    rfl rfl rfl rfl current (by rw [actionEq]; rfl) identity pushed
  have currentRelated : Related graph (r23 answer plain handler) := by
    rw [beforeShape, ← beforeMaps] at before
    simpa only [scope, actionEq, ← cleanupShape, r23, point, Related, cleanupTarget] using before
  have actualNext : CoreMachine.next graph CoreCleanupEntry.s23 = .stepped CoreCleanupEntry.s24 := by
    rw [identity, beforeShape, afterShape] at next
    exact next
  have rawStep : RawStep (cleanupTarget answer plain handler) (guardedTarget answer plain handler action) [.cleanup 0] [] := by
    simpa only [identity, scope, actionEq, ← cleanupShape, cleanupTarget, guardedTarget] using step
  have successor : Related graph (r24 answer plain handler action) := by
    rw [identity, scope, afterShape, ← afterMaps] at after
    exact after
  exact .positive currentRelated actualNext (.one rawStep) successor


def extensionPoints (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData) : List Point :=
  [r21 answer plain handler, r22 answer plain handler, r23 answer plain handler, r24 answer plain handler action]

def priorPoints (answer : Ty) (plain : PlainData) (handler : HandlerData) : List Point :=
  CoreAdmittedPrefix.points answer ++ CoreAdmittedHandlerPrefix.extensionPoints answer plain handler

/-- The same actual prefix registers cleanup zero without running the callback.
All chosen data and every intermediate target's admission survive the linkage
from the exported root through actual s24. -/
theorem admittedCleanupPrefix (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) :
    ∃ (answer : Ty) (plain : PlainData) (handler : HandlerData) (action : ActionData) (final : Snapshot operations),
      handler.activation = 0 ∧ plain.context = .bind 12 (close2 (raw 44)) ∧ plain.scope = .none ∧
      handler.scope = .none ∧ handler.effectInst = .user 0 [] ∧ handler.clauses = CoreHandlerPrefix.clauses ∧
      action.identity = 0 ∧ action.action = callbackCode ∧ action.scope = .none ∧
      CoreAdmittedPrefix.Admitted (CoreAdmittedPrefix.acquired (CoreAdmittedPrefix.initial tables families required) answer) ∧
      Chain graph p0 (priorPoints answer plain handler ++ extensionPoints answer plain handler action)
        (r24 answer plain handler action) ∧
      RawTrace (CoreAdmittedPrefix.initial tables families required).run.execution 11 final.run.execution ∧
      CoreAdmittedPrefix.Admitted final ∧
      (∀ point ∈ p0 :: (priorPoints answer plain handler ++ extensionPoints answer plain handler action),
        Related graph point ∧ ∃ snapshot : Snapshot operations,
          CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = .eval point.target) ∧
      final.world = [0] ∧ final.history = [0] ∧ final.run.execution.issued = [.resource 0, .cleanup 0] ∧
      final.run.execution.completed = [] ∧ final.run.execution.machine = .eval (r24 answer plain handler action).target := by
  obtain ⟨answer, plain, handler, base, handlerIdentity, plainContext, plainScope, handlerScope, handlerEffect,
    handlerArms, openedValid, earlier, trace, baseValid, allEarlier, world, history, issued, completed, machine⟩ :=
    CoreAdmittedHandlerPrefix.admittedHandlerPrefix tables families required
  have baseRelated : Related graph (CoreAdmittedHandlerPrefix.q20 answer plain handler) := earlier.endpoints.2
  let ready := CoreAdmittedHandlerPrefix.reconfigure base (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler)
  let pending := CoreAdmittedHandlerPrefix.reconfigure base (cleanupTarget answer plain handler)
  have readyEq : ready = base := by
    dsimp only [ready, CoreAdmittedHandlerPrefix.reconfigure]
    change base.run.execution.machine = .eval (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler) at machine
    rw [← machine]
  have readyValid : CoreAdmittedPrefix.Admitted ready := by rw [readyEq]; exact baseValid
  have isReady : RecursiveExpressions.Ready (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler).expression := by
    change RecursiveExpressions.Ready (.bind 8 callbackCode (close2 (raw 28)))
    exact .bind callbackClosed.1
  have bindStep : Stable.Step operations ready pending :=
    .computation (snapshot := base) (issued := base.run.execution.issued) (completed := base.run.execution.completed)
      (actions := base.run.tickets) isReady (callbackPrefix answer plain handler baseRelated).2.2
  obtain ⟨bindEvent, pendingValid⟩ := bindStep.preserve readyValid
  have actualBindEvent : LexicalUnwind.Event base.run.execution pending.run.execution := by
    simpa only [readyEq] using bindEvent
  let request : Allocating.Request pending :=
    .registerCleanup (callback := callbackCode) (body := guardedCode)
      (runtimeScope := .none) (stack := (CoreAdmittedHandlerPrefix.bodyTarget answer plain handler).stack)
      (issued := base.run.execution.issued) (completed := base.run.execution.completed)
      (actions := base.run.tickets) (identity := 0) rfl callbackClosed.1
      (by change (base.run.execution.issued ++ [Owner.cleanup 0]).Nodup; rw [issued]; decide)
  obtain ⟨after, registerEvent, realization, afterValid⟩ := request.preserve pendingValid
  dsimp [request] at realization
  cases realization with
  | registerCleanup action identity actionEq scope =>
    let final : Snapshot operations :=
      { pending with run := ⟨⟨.eval (guardedTarget answer plain handler action),
        base.run.execution.issued ++ [.cleanup 0], base.run.execution.completed⟩, base.run.tickets⟩ }
    have valid : CoreAdmittedPrefix.Admitted final := afterValid
    have linked := registerMapped answer plain handler action baseRelated identity actionEq scope
    have suffix : Chain graph (CoreAdmittedHandlerPrefix.q20 answer plain handler)
        (extensionPoints answer plain handler action) (r24 answer plain handler action) :=
      CoreHandlerPrefix.chain_append (callbackPrefix answer plain handler baseRelated).1 (.last linked)
    have chain := CoreHandlerPrefix.chain_append earlier suffix
    have suffixAdmitted : ∀ point ∈ extensionPoints answer plain handler action,
        ∃ snapshot : Snapshot operations, CoreAdmittedPrefix.Admitted snapshot ∧
          snapshot.run.execution.machine = .eval point.target := by
      intro point member
      simp only [extensionPoints, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact ⟨base, baseValid, machine⟩
      · exact ⟨base, baseValid, machine⟩
      · exact ⟨pending, pendingValid, rfl⟩
      · refine ⟨final, valid, ?_⟩
        rfl
    refine ⟨answer, plain, handler, action, final, handlerIdentity, plainContext, plainScope, handlerScope,
      handlerEffect, handlerArms, identity, actionEq, scope, openedValid, chain,
      .step (.step trace actualBindEvent) registerEvent, valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro point member
      rcases List.mem_cons.mp member with equal | later
      · subst point; exact allEarlier p0 List.mem_cons_self
      · refine ⟨chain.every_point_related point later, ?_⟩
        rcases List.mem_append.mp later with prior | extension
        · exact (allEarlier point (List.mem_cons_of_mem _ prior)).2
        · exact suffixAdmitted point extension
    · exact world
    · exact history
    · change base.run.execution.issued ++ [.cleanup 0] = [.resource 0, .cleanup 0]
      rw [issued]
      rfl
    · exact completed
    · rfl

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCleanupPrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCleanupPrefix.callbackPrefix

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCleanupPrefix.registerMapped

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCleanupPrefix.admittedCleanupPrefix
