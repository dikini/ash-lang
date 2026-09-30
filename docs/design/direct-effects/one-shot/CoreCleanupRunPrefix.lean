import CoreDiscardPrefix

/-! Exact continuation of the same initial chain through cleanup start and
callback beta. Projected physical frames and retained lexical scopes remain
explicit. The endpoint precedes the callback's cell write and its completion. -/
namespace Ash.OneShot.CoreCleanupRunPrefix
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential
  CoreCleanupFrames CoreCleanupRunFrames CoreAdministrativeTransport CoreInitialPrefix CoreHandlerPrefix
  CoreCleanupEntry CoreCaptureEntry.Exported CoreResumeEntry.Exported CoreSecondCapture CoreDiscardPrefix CoreExportedFixture
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

/-- Extract the delayed carrier and retained handler from the SAME captured
stack interpretation, without independently asserting callback closure data. -/
private theorem saved_cleanup : CleanupRel graph [] [] (.cleanupBoundary 27 callbackEnv 0) actionData ∧
    PushedWithMaps graph [] [([],.handlerBoundary 41 methodsEnv 0)] (.push (.handler handlerData) .nil) := by
  have captured := second_capture_parts.1
  cases captured with
  | cons pending rest =>
      cases rest with
      | cleanup delayed retained => exact ⟨delayed,retained⟩
      | boundary frame tail => cases frame
  | initializer frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame
  | boundary frame tail => cases frame

private theorem action_parts :
    EnvCloses graph [] [] callbackEnv (.app (.variable 8) .unit) (.app callbackCode .unit) ∧
    ValueRel graph [] [] (.closure 5 12 methodsEnv) callbackCode := by
  have delayed := saved_cleanup.1
  generalize coreEq : CoreMachine.Frame.cleanupBoundary 27 callbackEnv 0 = core at delayed
  generalize dataEq : actionData = data at delayed
  cases delayed with
  | armed known kind shape translated saved lookup value =>
      cases dataEq
      obtain ⟨rfl,rfl,_⟩ := CoreMachine.Frame.cleanupBoundary.inj coreEq
      have same := translation_unique translated
        (rfl : CoreTranslation.translateFuel graph 3 [] 27 = .ok (.app (.variable 8) .unit))
      have binderEq := Code.variable.inj (Code.app.inj same).1
      rw [binderEq] at saved lookup
      have valueEq := Option.some.inj (lookup.symm.trans (rfl : callbackEnv.lookup 8 = some (.closure 5 12 methodsEnv)))
      cases valueEq
      exact ⟨saved,value⟩

def physicalTail : List CoreMachine.Frame := .cleanupCompletion 0 .unit :: .closeCompletion 0 :: framesOf closingTailMaps
def lexicalTail : Stack := .push (.unwinding actionData) (.push (.handler handlerData)
  (.push (.closing 0 falseScope) (.spent 1 .unit .none secondTail)))
private theorem runningTail : RunningTail graph [] physicalTail lexicalTail :=
  .projected (data := actionData) (pending := .bind 6 22 nextEnv) (action := 27) (environment := callbackEnv)
    (closing := []) (closeIdentity := 0) (closeScope := falseScope)
    second_capture_parts.1 saved_cleanup.1 saved_cleanup.2
    (.spent first_capture_parts.1 second_capture_parts.2) closing_projection

def callbackTarget : Configuration := ⟨.app callbackCode .unit,.none,.nil⟩
def bodyTarget : Configuration := ⟨(close2 (raw 12)).subst 5 .unit,.none,.nil⟩
def functionPlain : PlainData := ⟨.appFunction .unit,.none,.function .unit .unit [.cell 0] [],.unit,[],rfl⟩
def argumentPlain : PlainData := ⟨.appArgument callbackCode,.none,.unit,.unit,[],by decide⟩
def s46 : CoreMachine.State := { s45 with control := .evaluate 27 callbackEnv, frames := physicalTail, observations := s45.observations ++ [.cleanupStarted 0] }
def s47 : CoreMachine.State := { s46 with control := .evaluate 25 callbackEnv, frames := .applyFunction 26 callbackEnv :: physicalTail, observations := s46.observations ++ [.entered 27] }
def s48 : CoreMachine.State := { s47 with control := .returned (.closure 5 12 methodsEnv), observations := s47.observations ++ [.entered 25] }
def s49 : CoreMachine.State := { s48 with control := .evaluate 26 callbackEnv, frames := .applyArgument (.closure 5 12 methodsEnv) :: physicalTail }
def s50 : CoreMachine.State := { s49 with control := .returned .unit, observations := s49.observations ++ [.entered 26] }
def s51 : CoreMachine.State := { s50 with control := .evaluate 12 (.binding 5 .unit methodsEnv), frames := physicalTail }
def w46 : CoreUnwindRelation.Point := ⟨s46,.eval (attach callbackTarget lexicalTail),[],[]⟩
def w47 : CoreUnwindRelation.Point := ⟨s47,.eval (attach callbackTarget lexicalTail),[],[([],.applyFunction 26 callbackEnv)]⟩
def w48 : CoreUnwindRelation.Point := ⟨s48,.eval (attach callbackTarget lexicalTail),[],w47.annotations⟩
def w49 : CoreUnwindRelation.Point := ⟨s49,.eval (attach callbackTarget lexicalTail),[],[([],.applyArgument (.closure 5 12 methodsEnv))]⟩
def w50 : CoreUnwindRelation.Point := ⟨s50,.eval (attach callbackTarget lexicalTail),[],w49.annotations⟩
def w51 : CoreUnwindRelation.Point := ⟨s51,.eval (attach bodyTarget lexicalTail),[],[]⟩

private theorem action_component : ComponentMapped graph [] [] (isolate s46 []) callbackTarget :=
  ⟨rfl,_,.none,.evaluate (fuel := 3) rfl action_parts.1,pushed_mapped .nil⟩
private theorem start : CoreUnwindRelation.Link graph v45 w46 ∧
    CoreUnwindRelation.Positive (.unwind falseScope unwindStack) (.eval (attach callbackTarget lexicalTail)) [] [] := by
  have started : CoreUnwindRelation.Related graph w46 := .runningCleanup runningTail action_component rfl
  have target : CoreUnwindRelation.Positive (.unwind falseScope unwindStack)
      (.eval (attach callbackTarget lexicalTail)) [] [] :=
    .next (.advance (.plain)) (.one .startCleanup)
  exact ⟨.positive reached_unwind_related rfl target started,target⟩

private theorem appTraversal : SilentMapped graph [] [] [] w47.annotations
    (isolate s46 []) (isolate s47 w47.annotations) callbackTarget :=
  application_entry_same_target_mapped (base := isolate s46 []) (environment := callbackEnv) ordered
    (rfl : graph.node 27 = some (node 27)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 25 = .ok (.variable 8))
    (rfl : CoreTranslation.translateFuel graph 2 [] 26 = .ok .unit)
    action_parts.1 action_parts.2.closed functionPlain rfl .nil

private theorem returnFunction : TransportMapped graph [] [] w47.annotations w48.annotations
    (isolate s47 w47.annotations) (isolate s48 w48.annotations) callbackTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s47 w47.annotations)
    (rfl : graph.node 25 = some (node 25)) rfl action_parts.1.app_components.1 action_parts.2.closed
    (framesOf w47.annotations)
  have valueEq := Option.some.inj (lookup.symm.trans (rfl : callbackEnv.lookup 8 = some (.closure 5 12 methodsEnv)))
  cases valueEq
  have frame : PlainFrameRel graph [] [] (.applyFunction 26 callbackEnv) functionPlain :=
    .applyFunction (rfl : CoreTranslation.translateFuel graph 2 [] 26 = .ok .unit) action_parts.1.app_components.2
  have stack := prepend_mapped frame action_parts.2.closed (pushed_mapped .nil) .none
  exact value_entry_mapped witness rfl rfl stack

private theorem argumentTraversal : SilentMapped graph [] [] w48.annotations w49.annotations
    (isolate s48 w48.annotations) (isolate s49 w49.annotations) callbackTarget :=
  application_argument_same_target_mapped (base := isolate s48 w48.annotations)
    (rfl : CoreTranslation.translateFuel graph 2 [] 26 = .ok .unit) action_parts.1.app_components.2
    action_parts.2 (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed
    functionPlain argumentPlain rfl rfl rfl .nil .none

private theorem returnUnit : TransportMapped graph [] [] w49.annotations w50.annotations
    (isolate s49 w49.annotations) (isolate s50 w50.annotations) callbackTarget := by
  obtain ⟨witness,_⟩ := CoreAdministrativeSteps.unit_evaluate (base := isolate s49 w49.annotations)
    (rfl : graph.node 26 = some (node 26)) rfl action_parts.1.app_components.2 (framesOf w49.annotations)
  have frame : PlainFrameRel graph [] [] (.applyArgument (.closure 5 12 methodsEnv)) argumentPlain :=
    .applyArgument action_parts.2
  have stack := prepend_mapped frame (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed
    (pushed_mapped .nil) .none
  exact value_entry_mapped witness rfl rfl stack

private theorem beta : CoreUnwindRelation.Link graph w50 w51 ∧ RawStep callbackTarget bodyTarget [] [] := by
  obtain ⟨before,next,step,after⟩ := beta_complete_mapped (base := isolate s50 w50.annotations)
    (show ValueRel graph [] [] (.closure 5 12 methodsEnv) (.lambda 5 (close2 (raw 12))) from action_parts.2)
    ValueRel.unit argumentPlain rfl .nil .none []
  have related : CoreUnwindRelation.Related graph w51 := .runningCleanup runningTail after rfl
  have current : CoreUnwindRelation.Related graph w50 := .runningCleanup runningTail before rfl
  have actualStep : RawStep (attach callbackTarget lexicalTail) (attach bodyTarget lexicalTail) [] [] :=
    .beta 5 (close2 (raw 12)) .unit .none lexicalTail (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed action_parts.2.closed
  exact ⟨.positive current rfl (CoreUnwindRelation.ordinary_step actualStep trivial) related,step⟩

private theorem link47 : CoreUnwindRelation.Link graph w46 w47 :=
  .runningAdministration runningTail (.traversal appTraversal rfl) rfl rfl rfl
private theorem link48 : CoreUnwindRelation.Link graph w47 w48 :=
  .runningAdministration runningTail (.value returnFunction rfl) rfl rfl rfl
private theorem link49 : CoreUnwindRelation.Link graph w48 w49 :=
  .runningAdministration runningTail (.traversal argumentTraversal rfl) rfl rfl rfl
private theorem link50 : CoreUnwindRelation.Link graph w49 w50 :=
  .runningAdministration runningTail (.value returnUnit rfl) rfl rfl rfl

theorem discard_to_callback_body : CoreUnwindRelation.Chain graph v45 [w46,w47,w48,w49,w50,w51] w51 :=
  .next start.1 (.next link47 (.next link48 (.next link49 (.next link50 (.last beta.1)))))

/-- All inherited points and the six callback-entry points share one current
lexical-machine chain from the actual Core initial state. -/
theorem exported_cleanup_run_prefix : CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift p0)
    ((([p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20,r21,r22,r23,r24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35,u36,u37,u38,u39,u40].map CoreUnwindRelation.lift) ++
      [CoreUnwindRelation.lift v41,CoreUnwindRelation.lift v42,CoreUnwindRelation.lift v43,v44,v45]) ++
      [w46,w47,w48,w49,w50,w51]) w51 :=
  CoreUnwindRelation.chain_append exported_lexical_unwind_prefix discard_to_callback_body

theorem reached_callback_body_related : CoreUnwindRelation.Related graph w51 := exported_cleanup_run_prefix.endpoints.2

theorem exported_cleanup_run_steps : CoreAllocationHistory.Steps graph 51 (CoreMachine.initial graph) s51 :=
  exported_cleanup_run_prefix.core_steps

theorem exported_cleanup_run_history : CoreAllocationHistory.History s51 :=
  CoreAllocationHistory.initial_steps_history graph exported_cleanup_run_steps

private theorem actual_beta : RawStep (attach callbackTarget lexicalTail) (attach bodyTarget lexicalTail) [] [] :=
  .beta 5 (close2 (raw 12)) .unit .none lexicalTail
    (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed action_parts.2.closed

theorem cleanup_run_ledger : CoreUnwindRelation.Trace (.unwind falseScope unwindStack)
    (.eval (attach bodyTarget lexicalTail)) [] [] :=
  start.2.trace.append (.next (.evaluate actual_beta trivial) (.refl _))

theorem exported_cleanup_run_ledger : CoreUnwindRelation.Trace (.eval rootTarget)
    (.eval (attach bodyTarget lexicalTail)) [.resource 0,.cleanup 0,.ticket 0,.ticket 1,.close 0] [.ticket 1,.ticket 0] :=
  exported_lexical_discard_ledger.append cleanup_run_ledger

/-- Callable entry restores its captured lexical environment and empty current
owner map. Cleanup/closing and all caller scopes remain pending below it. -/
theorem callback_body_spines_exact :
    s51.control = .evaluate 12 (.binding 5 .unit methodsEnv) ∧
    s51.frames = [.cleanupCompletion 0 .unit,.closeCompletion 0,.clauseBoundary 0 0 0 1 none,
      .bind 10 37 clauseEnv,.clauseBoundary 0 0 0 0 none,.bind 12 44 methodsEnv,.resourceBoundary 48 0 0] ∧
    w51.owners = [] ∧
    w51.machine = .eval ⟨(close2 (raw 12)).subst 5 .unit,.none,
      .push (.unwinding actionData) (.push (.handler handlerData)
        (.push (.closing 0 falseScope) (.spent 1 .unit .none secondTail)))⟩ := ⟨rfl,rfl,rfl,rfl⟩

theorem cleanup_started_once : s51.observations.count (.cleanupStarted 0) = 1 ∧
    s51.observations.contains (.cleanupFinished 0) = false ∧
    s51.observations.contains (.closeFinished 0) = false := ⟨by decide,by decide,by decide⟩

/-- Restricted dispatch agrees for this callback's actual cell request. The
retained target-only user handler is not an all-effect correspondence claim. -/
theorem running_callback_cell_dispatch : actionData.requests = [.cell 0] ∧
    lexicalTail.erase.resolve (.cell 0) = some (.builtin 0) ∧
    CoreMachine.findInterpreter graph (.cell (.activation 0)) s51.frames =
      .ok (.cell ⟨[.cleanupCompletion 0 .unit,.closeCompletion 0,.clauseBoundary 0 0 0 1 none,
        .bind 10 37 clauseEnv,.clauseBoundary 0 0 0 0 none,.bind 12 44 methodsEnv],48,0,0,[]⟩) := ⟨rfl,rfl,rfl⟩

theorem running_unchanged_rejected :
    ¬ Administrative graph [] [] [] [] s46 s46 callbackTarget := by
  intro witness
  exact Nat.lt_irrefl _ witness.components.2.2.2

#print axioms discard_to_callback_body
#print axioms exported_cleanup_run_prefix
#print axioms reached_callback_body_related
#print axioms exported_cleanup_run_steps
#print axioms exported_cleanup_run_history
#print axioms cleanup_run_ledger
#print axioms exported_cleanup_run_ledger
#print axioms callback_body_spines_exact
#print axioms cleanup_started_once
#print axioms running_callback_cell_dispatch
#print axioms running_unchanged_rejected
end Ash.OneShot.CoreCleanupRunPrefix
