import CoreAdmittedDiscardPrefix
import CoreCleanupFinishPrefix
import CoreFinalPrefix
import CoreValueUniqueness

/-! Completion of the same admitted discard, retaining its source-selected
ports and scope annotations. Callback Code is obtained from finite closing
evidence, not by identifying selectable annotations with a fixture. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCompletionPrefix
open ScopedExpressions ScopedExecution ProtectionContracts
open InstallationSupport InstallationSupport.Preservation CoreInitialExample
open CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential CoreCleanupFrames CoreCleanupRunFrames
open CoreOrdinaryCompletion CoreAdministrativeTransport CoreInitialPrefix CoreExportedFixture
open CoreEffectFrames CoreRequestFrames CoreResumeFrames CoreCaptureEntry CoreResumeEntry CoreCellWriteFrames
open CoreHandlerPrefix (raw methodsEnv close2)
open CoreCleanupEntry (callbackEnv callbackCode)
open CoreCaptureEntry.Exported (outsideMaps)
open CoreAdmittedResumePrefix (Data)
open CoreAdmittedSecondCapturePrefix (Maps captured capturedTarget outside outsideTarget clauseTarget p40)
open CoreDiscardPrefix (falseEnv falseScope s45)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0,.unit,[],none,.unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl
private theorem translation_unique {owners : CoreTranslation.OwnerMap}
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok code)
    (second : CoreTranslation.translateFuel graph other owners index = .ok otherCode) : code = otherCode := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel other) owners index code (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph other (max fuel other) owners index otherCode (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

private theorem currentPushed (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (related : CoreInitialPrefix.Related graph (p40 d post second m input)) :
    PushedWithMaps graph [] (p40 d post second m input).annotations (clauseTarget d post second input).stack := by
  obtain ⟨_,code,scope,control,stack⟩ := related
  change OrdinaryWithMaps graph []
    ((m.handlerOwner,.clauseBoundary 0 0 0 1 (some (framesOf (captured m)))) :: outside post)
    code scope (clauseTarget d post second input).expression falseScope (clauseTarget d post second input).stack at stack
  exact (CoreAdmittedResumePrefix.owner_head_pushed stack).2.2

private theorem ownerParts (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (related : CoreInitialPrefix.Related graph (p40 d post second m input)) :
    ∃ saved : List MappedFrame, ∃ data : HandlerData,
      framesOf saved = framesOf (captured m) ∧
      CoreRequestFrames.OwnerHeader graph m.handlerOwner [] 0 0 0 data ∧
      data.answer = d.handler.answer ∧ data.scope = d.handler.scope ∧
      PushedWithMaps graph [] saved (capturedTarget d second) ∧
      PushedWithMaps graph [] (outside post) (outsideTarget d post) := by
  have pushed := currentPushed d post second m input related
  change PushedWithMaps graph []
    ((m.handlerOwner, .clauseBoundary 0 0 0 1 (some (framesOf (captured m)))) :: outside post)
    (.live 1 input d.handler.answer (capturedTarget d second)
      d.handler.scope (outsideTarget d post)) at pushed
  generalize mappingsEq :
    ((m.handlerOwner, CoreMachine.Frame.clauseBoundary 0 0 0 1 (some (framesOf (captured m)))) :: outside post) = mappings at pushed
  generalize stackEq :
    Stack.live 1 input d.handler.answer (capturedTarget d second)
      d.handler.scope (outsideTarget d post) = target at pushed
  cases pushed with
  | live header captured outside =>
    obtain ⟨ticketEq, inputEq, answerEq, capturedEq, scopeEq, tailEq⟩ := Stack.live.inj stackEq
    obtain ⟨headEq, outsideEq⟩ := List.cons.inj mappingsEq
    obtain ⟨ownerEq, frameEq⟩ := Prod.mk.inj headEq
    obtain ⟨handlerEq, ownerIdEq, occurrenceEq, ticketFrameEq, framesEq⟩ := CoreMachine.Frame.clauseBoundary.inj frameEq
    cases ownerEq
    cases handlerEq
    cases ownerIdEq
    cases occurrenceEq
    cases capturedEq
    cases tailEq
    cases outsideEq
    exact ⟨_, _, (Option.some.inj framesEq).symm, header, answerEq.symm, scopeEq.symm, captured, outside⟩
  | nil => cases stackEq
  | cons | initializer | boundary | cleanup | request | resume | spent => cases stackEq



private theorem splitCaptured (saved : List MappedFrame) (framesEq : framesOf saved = framesOf (captured m)) :
    ∃ n : Maps,saved = captured n := by
  rcases saved with _ | ⟨⟨alpha,first⟩,rest⟩
  · cases framesEq
  rcases rest with _ | ⟨⟨beta,second⟩,rest⟩
  · cases framesEq
  rcases rest with _ | ⟨⟨gamma,third⟩,rest⟩
  · cases framesEq
  cases rest with
  | nil =>
    simp [framesOf,captured,CoreAdmittedSecondCapturePrefix.inside] at framesEq
    obtain ⟨rfl,rfl,rfl,_⟩ := framesEq
    exact ⟨⟨alpha,beta,gamma⟩,rfl⟩
  | cons fourth more =>
    have same := congrArg (fun frames => frames.length) framesEq
    simp [framesOf,captured,CoreAdmittedSecondCapturePrefix.inside] at same

private theorem delayedParts (d : Data) (second : PlainData) (n : Maps)
    (pushed : PushedWithMaps graph [] (captured n) (capturedTarget d second)) :
    CleanupRel graph n.cleanupOwner [] (.cleanupBoundary 27 callbackEnv 0) d.action ∧
      PushedWithMaps graph [] [(n.handlerOwner,.handlerBoundary 41 methodsEnv 0)] (.push (.handler d.handler) .nil) := by
  change PushedWithMaps graph []
    ((n.bindOwner,.bind 6 22 CoreSecondCapture.nextEnv) ::
      (n.cleanupOwner,.cleanupBoundary 27 callbackEnv 0) :: [(n.handlerOwner,.handlerBoundary 41 methodsEnv 0)])
    (.push (.plain second) (.push (.armed d.action) (.push (.handler d.handler) .nil))) at pushed
  cases pushed with
  | cons pending rest =>
    cases rest with
    | cleanup delayed retained => exact ⟨delayed,retained⟩
    | boundary frame tail => cases frame
  | initializer frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame
  | boundary frame tail => cases frame

private theorem canonicalActionParts : EnvCloses graph [] [] callbackEnv (.app (.variable 8) .unit) (.app callbackCode .unit) ∧
    ValueRel graph [] [] (.closure 5 12 methodsEnv) callbackCode := by
  have captured := CoreSecondCapture.second_capture_parts.1
  cases captured with
  | cons pending rest =>
    cases rest with
    | cleanup delayed retained =>
      generalize coreEq : CoreMachine.Frame.cleanupBoundary 27 callbackEnv 0 = core at delayed
      generalize dataEq : CoreCleanupEntry.actionData = action at delayed
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
    | boundary frame tail => cases frame
  | initializer frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame
  | boundary frame tail => cases frame

/-- Extract actual callback Code while retaining all selectable annotations. -/
theorem callbackParts (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (related : CoreInitialPrefix.Related graph (p40 d post second m input)) :
    ∃ n : Maps, d.action.identity = 0 ∧ d.action.action = callbackCode ∧
      PushedWithMaps graph [] (captured n) (capturedTarget d second) ∧
      CleanupRel graph n.cleanupOwner [] (.cleanupBoundary 27 callbackEnv 0) d.action ∧
      PushedWithMaps graph [] [(n.handlerOwner,.handlerBoundary 41 methodsEnv 0)] (.push (.handler d.handler) .nil) ∧
      PushedWithMaps graph [] ((m.handlerOwner,.clauseBoundary 0 0 0 1 none) :: outside post)
        (.spent 1 d.handler.answer d.handler.scope (outsideTarget d post)) ∧
      EnvCloses graph [] [] callbackEnv (.app (.variable 8) .unit) (.app callbackCode .unit) := by
  obtain ⟨saved,data,framesEq,header,answerEq,scopeEq,capturedPushed,outsidePushed⟩ := ownerParts d post second m input related
  obtain ⟨n,savedEq⟩ := splitCaptured saved framesEq
  subst saved
  obtain ⟨delayed,retained⟩ := delayedParts d second n capturedPushed
  have spent := PushedWithMaps.spent (ticket := 1) header outsidePushed
  rw [answerEq,scopeEq] at spent
  have delayedCopy := delayed
  generalize coreEq : CoreMachine.Frame.cleanupBoundary 27 callbackEnv 0 = core at delayedCopy
  generalize dataEq : d.action = action at delayedCopy
  cases delayedCopy with
  | armed known kind shape translated saved lookup value =>
    cases dataEq
    obtain ⟨rfl,rfl,identityEq⟩ := CoreMachine.Frame.cleanupBoundary.inj coreEq
    have same := translation_unique translated
      (rfl : CoreTranslation.translateFuel graph 3 n.cleanupOwner 27 = .ok (.app (.variable 8) .unit))
    have binderEq := Code.variable.inj (Code.app.inj same).1
    rw [binderEq] at saved lookup
    have valueEq := Option.some.inj (lookup.symm.trans (rfl : callbackEnv.lookup 8 = some (.closure 5 12 methodsEnv)))
    cases valueEq
    have callbackEq := ValueRel.unique (value.owner_transport []) canonicalActionParts.2
    rw [callbackEq] at saved
    exact ⟨n,identityEq.symm,callbackEq,capturedPushed,(identityEq ▸ delayed),retained,spent,saved.owner_transport []⟩

/-- Current cut evidence extracted by callbackParts; no successor or admission
judgment is an input. -/
private structure Evidence (d : Data) (post second : PlainData) (m n : Maps) : Prop where
  identity : d.action.identity = 0
  action : d.action.action = callbackCode
  captured : PushedWithMaps graph [] (CoreAdmittedSecondCapturePrefix.captured n) (capturedTarget d second)
  delayed : CleanupRel graph n.cleanupOwner [] (.cleanupBoundary 27 callbackEnv 0) d.action
  retained : PushedWithMaps graph [] [(n.handlerOwner,.handlerBoundary 41 methodsEnv 0)] (.push (.handler d.handler) .nil)
  outside : PushedWithMaps graph [] ((m.handlerOwner,.clauseBoundary 0 0 0 1 none) :: outside post)
    (.spent 1 d.handler.answer d.handler.scope (outsideTarget d post))

def lexicalTail (d : Data) (post : PlainData) : Stack :=
  .push (.unwinding d.action) (.push (.handler d.handler)
    (.push (.closing 0 falseScope) (.spent 1 d.handler.answer d.handler.scope (outsideTarget d post))))

private theorem runningTail (evidence : Evidence d post second m n) :
    RunningTail graph [] CoreCleanupRunPrefix.physicalTail (lexicalTail d post) := by
  have projection : CoreMachine.closeFuel
      (CoreMachine.framesMass (.bind 6 22 CoreSecondCapture.nextEnv :: .cleanupBoundary 27 callbackEnv d.action.identity ::
        framesOf [(n.handlerOwner,.handlerBoundary 41 methodsEnv 0)]) + 1)
      (.bind 6 22 CoreSecondCapture.nextEnv :: .cleanupBoundary 27 callbackEnv d.action.identity ::
        framesOf [(n.handlerOwner,.handlerBoundary 41 methodsEnv 0)]) =
      .ok ([.cleanupBoundary 27 callbackEnv d.action.identity],[]) := by rw [evidence.identity]; rfl
  have capturedCopy : PushedWithMaps graph []
      [(n.bindOwner,.bind 6 22 CoreSecondCapture.nextEnv),
        (n.cleanupOwner,.cleanupBoundary 27 callbackEnv d.action.identity),
        (n.handlerOwner,.handlerBoundary 41 methodsEnv 0)] (capturedTarget d second) := by
    rw [evidence.identity]
    exact evidence.captured
  have selected := RunningTail.projected (closeIdentity := 0) (closeScope := falseScope)
    capturedCopy (evidence.identity.symm ▸ evidence.delayed) evidence.retained evidence.outside projection
  rw [evidence.identity] at selected
  exact selected

open CoreCleanupRunPrefix (s46 s47 s48 s49 s50 s51 physicalTail callbackTarget bodyTarget functionPlain argumentPlain)
def w46 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s46,.eval (attach callbackTarget (lexicalTail d post)),[],[]⟩
def w47 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s47,(w46 d post).machine,[],[([],.applyFunction 26 callbackEnv)]⟩
def w48 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s48,(w46 d post).machine,[],(w47 d post).annotations⟩
def w49 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s49,(w46 d post).machine,[],[([],.applyArgument (.closure 5 12 methodsEnv))]⟩
def w50 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s50,(w46 d post).machine,[],(w49 d post).annotations⟩
def w51 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s51,.eval (attach bodyTarget (lexicalTail d post)),[],[]⟩

private theorem action_component : ComponentMapped graph [] [] (isolate s46 []) callbackTarget :=
  ⟨rfl,_,.none,.evaluate (fuel := 3) rfl canonicalActionParts.1,pushed_mapped .nil⟩

section Entry
variable {d : Data} {post second : PlainData} {m n : Maps}
variable (evidence : Evidence d post second m n)
variable (current : CoreUnwindRelation.Related graph (CoreAdmittedDiscardPrefix.p45 d post second m))
include evidence
include current in
private theorem start : CoreUnwindRelation.Link graph (CoreAdmittedDiscardPrefix.p45 d post second m) (w46 d post) := by
  have started : CoreUnwindRelation.Related graph (w46 d post) := .runningCleanup (runningTail evidence) action_component rfl
  have target : CoreUnwindRelation.Positive (CoreAdmittedDiscardPrefix.p45 d post second m).machine (w46 d post).machine [] [] := by
    change CoreUnwindRelation.Positive (.unwind falseScope (CoreAdmittedDiscardPrefix.unwindStack d post second))
      (.eval ⟨.app callbackCode .unit,.none,lexicalTail d post⟩) [] []
    rw [← evidence.action]
    exact .next (.advance .plain) (.one .startCleanup)
  exact .positive current rfl target started

omit evidence in
private theorem appTraversal : SilentMapped graph [] [] [] (w47 d post).annotations
    (isolate s46 []) (isolate s47 (w47 d post).annotations) callbackTarget :=
  application_entry_same_target_mapped (base := isolate s46 []) (environment := callbackEnv) ordered
    (rfl : graph.node 27 = some (node 27)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 25 = .ok (.variable 8))
    (rfl : CoreTranslation.translateFuel graph 2 [] 26 = .ok .unit)
    canonicalActionParts.1 canonicalActionParts.2.closed functionPlain rfl .nil

omit evidence in
private theorem returnFunction : TransportMapped graph [] [] (w47 d post).annotations (w48 d post).annotations
    (isolate s47 (w47 d post).annotations) (isolate s48 (w48 d post).annotations) callbackTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s47 (w47 d post).annotations)
    (rfl : graph.node 25 = some (node 25)) rfl canonicalActionParts.1.app_components.1 canonicalActionParts.2.closed
    (framesOf (w47 d post).annotations)
  have valueEq := Option.some.inj (lookup.symm.trans (rfl : callbackEnv.lookup 8 = some (.closure 5 12 methodsEnv)))
  cases valueEq
  have frame : PlainFrameRel graph [] [] (.applyFunction 26 callbackEnv) functionPlain :=
    .applyFunction (rfl : CoreTranslation.translateFuel graph 2 [] 26 = .ok .unit) canonicalActionParts.1.app_components.2
  have stack := prepend_mapped frame canonicalActionParts.2.closed (pushed_mapped .nil) .none
  exact value_entry_mapped witness rfl rfl stack

omit evidence in
private theorem argumentTraversal : SilentMapped graph [] [] (w48 d post).annotations (w49 d post).annotations
    (isolate s48 (w48 d post).annotations) (isolate s49 (w49 d post).annotations) callbackTarget :=
  application_argument_same_target_mapped (base := isolate s48 (w48 d post).annotations)
    (rfl : CoreTranslation.translateFuel graph 2 [] 26 = .ok .unit) canonicalActionParts.1.app_components.2
    canonicalActionParts.2 (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed
    functionPlain argumentPlain rfl rfl rfl .nil .none

omit evidence in
private theorem returnUnit : TransportMapped graph [] [] (w49 d post).annotations (w50 d post).annotations
    (isolate s49 (w49 d post).annotations) (isolate s50 (w50 d post).annotations) callbackTarget := by
  obtain ⟨witness,_⟩ := CoreAdministrativeSteps.unit_evaluate (base := isolate s49 (w49 d post).annotations)
    (rfl : graph.node 26 = some (node 26)) rfl canonicalActionParts.1.app_components.2 (framesOf (w49 d post).annotations)
  have frame : PlainFrameRel graph [] [] (.applyArgument (.closure 5 12 methodsEnv)) argumentPlain :=
    .applyArgument canonicalActionParts.2
  have stack := prepend_mapped frame (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed
    (pushed_mapped .nil) .none
  exact value_entry_mapped witness rfl rfl stack

private theorem beta : CoreUnwindRelation.Link graph (w50 d post) (w51 d post) ∧ RawStep callbackTarget bodyTarget [] [] := by
  obtain ⟨before,next,step,after⟩ := beta_complete_mapped (base := isolate s50 (w50 d post).annotations)
    (show ValueRel graph [] [] (.closure 5 12 methodsEnv) (.lambda 5 (close2 (raw 12))) from canonicalActionParts.2)
    ValueRel.unit argumentPlain rfl .nil .none []
  have related : CoreUnwindRelation.Related graph (w51 d post) := .runningCleanup (runningTail evidence) after rfl
  have current : CoreUnwindRelation.Related graph (w50 d post) := .runningCleanup (runningTail evidence) before rfl
  have actualStep : RawStep (attach callbackTarget (lexicalTail d post)) (attach bodyTarget (lexicalTail d post)) [] [] :=
    .beta 5 (close2 (raw 12)) .unit .none (lexicalTail d post) (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed canonicalActionParts.2.closed
  exact ⟨.positive current rfl (CoreUnwindRelation.ordinary_step actualStep trivial) related,step⟩

private theorem link47 : CoreUnwindRelation.Link graph (w46 d post) (w47 d post) :=
  .runningAdministration (runningTail evidence) (.traversal (appTraversal (d := d) (post := post)) rfl) rfl rfl rfl
private theorem link48 : CoreUnwindRelation.Link graph (w47 d post) (w48 d post) :=
  .runningAdministration (runningTail evidence) (.value (returnFunction (d := d) (post := post)) rfl) rfl rfl rfl
private theorem link49 : CoreUnwindRelation.Link graph (w48 d post) (w49 d post) :=
  .runningAdministration (runningTail evidence) (.traversal (argumentTraversal (d := d) (post := post)) rfl) rfl rfl rfl
private theorem link50 : CoreUnwindRelation.Link graph (w49 d post) (w50 d post) :=
  .runningAdministration (runningTail evidence) (.value (returnUnit (d := d) (post := post)) rfl) rfl rfl rfl

include current in
private theorem discard_to_callback_body : CoreUnwindRelation.Chain graph (CoreAdmittedDiscardPrefix.p45 d post second m) [(w46 d post),(w47 d post),(w48 d post),(w49 d post),(w50 d post),(w51 d post)] (w51 d post) :=
  .next (start evidence current) (.next (link47 evidence) (.next (link48 evidence) (.next (link49 evidence) (.next (link50 evidence) (.last (beta evidence).1)))))


end Entry

open CoreCleanupWritePrefix (pairCode callTarget writeTarget bodyEnv setterValue setterEnv allocated
  s52 s53 s54 s55 s56 s57 s58 s59 s60 s61 s62 maps52 maps54 maps55 maps57 maps61)
private abbrev writeFunctionPlain := CoreCleanupWritePrefix.functionPlain
private abbrev writeArgumentPlain := CoreCleanupWritePrefix.argumentPlain
private abbrev writeLeftPlain := CoreCleanupWritePrefix.leftPlain
private abbrev writeRightPlain := CoreCleanupWritePrefix.rightPlain
private abbrev writeRequestPlain := CoreCleanupWritePrefix.requestPlain

private theorem bodySaved : EnvCloses graph [] [] bodyEnv
    (.app (.variable 3) (.pair (.variable 4) (.integer 7))) callTarget.expression := by
  obtain ⟨fuel,rawBody,translated,saved,_⟩ := canonicalActionParts.2.closure_view
  have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 12 = .ok (raw 12))
  cases same
  exact saved.beta_argument ValueRel.unit

private theorem setter_related : ValueRel graph [] [] setterValue CoreHandlerPrefix.setter := by
  obtain ⟨value,lookup,related⟩ := bodySaved.app_components.1.lookup (by
    change ClosedValue (.lambda 2 (.perform (.cell (.activation 0)) 1 (.variable 2)))
    simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies,Syntax.without,Instantiation.Effect.freeNames])
  have equal := Option.some.inj (lookup.symm.trans (rfl : bodyEnv.lookup 3 = some setterValue))
  cases equal
  exact related
private theorem pair_closed : ClosedValue pairCode := by
  simp [pairCode,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies]
private theorem handle_saved : EnvCloses graph [] [] bodyEnv (.variable 4) (.resourceRef (.activation 0)) :=
  (pair_components bodySaved.app_components.2).1
private theorem integer_saved : EnvCloses graph [] [] bodyEnv (.integer 7) (.integer 7) :=
  (pair_components bodySaved.app_components.2).2


def w52 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s52,.eval (attach callTarget (lexicalTail d post)),[],maps52⟩
def w53 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s53,(w52 d post).machine,[],maps52⟩
def w54 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s54,(w52 d post).machine,[],maps54⟩
def w55 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s55,(w52 d post).machine,[],maps55⟩
def w56 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s56,(w52 d post).machine,[],maps55⟩
def w57 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s57,(w52 d post).machine,[],maps57⟩
def w58 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s58,(w52 d post).machine,[],maps57⟩
def w59 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s59,(w52 d post).machine,[],maps54⟩
def w60 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s60,.eval (attach writeTarget (lexicalTail d post)),[],[]⟩
def w61 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s61,(w60 d post).machine,[],maps61⟩
def w62 (d : Data) (post : PlainData) : CoreUnwindRelation.Point := ⟨s62,(w60 d post).machine,[],maps61⟩

section Write
variable {d : Data} {post second : PlainData} {m n : Maps}
variable (evidence : Evidence d post second m n)
private theorem app52 : SilentMapped graph [] [] [] maps52 (isolate s51 []) (isolate s52 maps52) callTarget :=
  application_entry_same_target_mapped (base := isolate s51 []) ordered
    (rfl : graph.node 12 = some (node 12)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 8 = .ok (.variable 3))
    (rfl : CoreTranslation.translateFuel graph 2 [] 11 = .ok (.pair (.variable 4) (.integer 7)))
    bodySaved setter_related.closed writeFunctionPlain rfl .nil
private theorem value53 : TransportMapped graph [] [] maps52 maps52 (isolate s52 maps52) (isolate s53 maps52) callTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s52 maps52)
    (rfl : graph.node 8 = some (node 8)) rfl bodySaved.app_components.1 setter_related.closed (framesOf maps52)
  have equal := Option.some.inj (lookup.symm.trans (rfl : bodyEnv.lookup 3 = some setterValue))
  cases equal
  have frame : PlainFrameRel graph [] [] (.applyFunction 11 bodyEnv) writeFunctionPlain :=
    .applyFunction (rfl : CoreTranslation.translateFuel graph 2 [] 11 = .ok (.pair (.variable 4) (.integer 7))) bodySaved.app_components.2
  exact value_entry_mapped witness rfl rfl (prepend_mapped frame setter_related.closed (pushed_mapped .nil) .none)
private theorem app54 : SilentMapped graph [] [] maps52 maps54 (isolate s53 maps52) (isolate s54 maps54) callTarget :=
  application_argument_same_target_mapped (base := isolate s53 maps52)
    (rfl : CoreTranslation.translateFuel graph 2 [] 11 = .ok (.pair (.variable 4) (.integer 7)))
    bodySaved.app_components.2 setter_related pair_closed writeFunctionPlain writeArgumentPlain rfl rfl rfl .nil .none
private theorem argument_stack : OrdinaryWithMaps graph [] maps54 pairCode .none callTarget.expression .none .nil :=
  prepend_mapped (plain := writeArgumentPlain) (.applyArgument setter_related) pair_closed (pushed_mapped .nil) .none
private theorem left_frame : PlainFrameRel graph [] [] (.tupleLeft 10 bodyEnv) writeLeftPlain :=
  .tupleLeft (rfl : CoreTranslation.translateFuel graph 2 [] 10 = .ok (.integer 7)) integer_saved
private theorem right_frame : PlainFrameRel graph [] [] (.tupleRight (.handle 0)) writeRightPlain := .tupleRight ValueRel.handle
private theorem tuple55 : SilentMapped graph [] [] maps54 maps55 (isolate s54 maps54) (isolate s55 maps55) callTarget := by
  exact ⟨rfl,(tuple_entry_decreases (base := isolate s54 maps54) ordered (rfl : graph.node 11 = some (node 11)) rfl (framesOf maps54)).2,
    rfl,⟨rfl,pairCode,.none,.evaluate (rfl : CoreTranslation.translateFuel graph 3 [] 11 = .ok (.pair (.variable 4) (.integer 7))) bodySaved.app_components.2,argument_stack⟩,
    ⟨rfl,_,.none,.evaluate (rfl : CoreTranslation.translateFuel graph 2 [] 9 = .ok (.variable 4)) handle_saved,
      prepend_mapped left_frame (ValueRel.handle (graph := graph) (owners := []) (heap := [])).closed argument_stack .none⟩⟩
private theorem value56 : TransportMapped graph [] [] maps55 maps55 (isolate s55 maps55) (isolate s56 maps55) callTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s55 maps55)
    (rfl : graph.node 9 = some (node 9)) rfl handle_saved (ValueRel.handle (graph := graph) (owners := []) (heap := [])).closed (framesOf maps55)
  have equal := Option.some.inj (lookup.symm.trans (rfl : bodyEnv.lookup 4 = some (.handle 0)))
  cases equal
  exact value_entry_mapped witness rfl rfl
    (prepend_mapped left_frame (ValueRel.handle (graph := graph) (owners := []) (heap := [])).closed argument_stack .none)
private theorem tuple57 : SilentMapped graph [] [] maps55 maps57 (isolate s56 maps55) (isolate s57 maps57) callTarget := by
  exact ⟨rfl,(tuple_right_decreases (graph := graph) (isolate s56 maps55) (framesOf maps54)).2,rfl,
    value56.successor,
    ⟨rfl,_,.none,.evaluate (rfl : CoreTranslation.translateFuel graph 2 [] 10 = .ok (.integer 7)) integer_saved,
      prepend_mapped right_frame (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := 7)).closed argument_stack .none⟩⟩
private theorem value58 : TransportMapped graph [] [] maps57 maps57 (isolate s57 maps57) (isolate s58 maps57) callTarget := by
  obtain ⟨witness,_⟩ := CoreAdministrativeSteps.integer_evaluate (base := isolate s57 maps57)
    (rfl : graph.node 10 = some (node 10)) rfl integer_saved (framesOf maps57)
  exact value_entry_mapped witness rfl rfl
    (prepend_mapped right_frame (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := 7)).closed argument_stack .none)
private theorem allocate59 : TransportMapped graph [] [] maps57 maps54 (isolate s58 maps57) (isolate s59 maps54) callTarget :=
  tuple_allocation_mapped (base := isolate s58 maps57) ValueRel.handle ValueRel.integer writeRightPlain rfl argument_stack .none []
private theorem allocation_extension : HeapExtends s58.heap s59.heap :=
  (CoreAdministrativeSteps.tuple_allocate (base := isolate s58 maps57)
    (ValueRel.handle (graph := graph) (owners := []) (heap := [])) (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := 7)) (framesOf maps54)).2.1
private theorem location_related : ValueRel graph [] allocated (.location 0) pairCode := .location rfl .handle .integer
include evidence in
private theorem beta60 : CoreUnwindRelation.Link graph (w59 d post) (w60 d post) ∧ RawStep (attach callTarget (lexicalTail d post)) (attach writeTarget (lexicalTail d post)) [] [] := by
  have function := setter_related.heap_weaken allocation_extension
  obtain ⟨before,next,step,after⟩ := beta_complete_mapped (base := isolate s59 maps54)
    (show ValueRel graph [] allocated setterValue (.lambda 2 (.perform (.cell (.activation 0)) 1 (.variable 2))) from function)
    location_related writeArgumentPlain rfl .nil .none []
  have carrier := (runningTail evidence).heap_weaken allocation_extension
  have current : CoreUnwindRelation.Related graph (w59 d post) := .runningCleanup carrier before rfl
  have successor : CoreUnwindRelation.Related graph (w60 d post) := .runningCleanup carrier after rfl
  have rawStep : RawStep (attach callTarget (lexicalTail d post)) (attach writeTarget (lexicalTail d post)) [] [] :=
    .beta 2 (.perform (.cell (.activation 0)) 1 (.variable 2)) pairCode .none (lexicalTail d post) location_related.closed function.closed
  exact ⟨.positive current rfl (CoreUnwindRelation.ordinary_step rawStep trivial) successor,rawStep⟩
private theorem setter_body : EnvCloses graph [] allocated setterEnv (.perform (.cell (.bound 0)) 1 (.variable 2)) writeTarget.expression := by
  obtain ⟨fuel,rawBody,translated,saved,_⟩ := setter_related.closure_view
  have equal := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 6 = .ok (.perform (.cell (.bound 0)) 1 (.variable 2)))
  cases equal
  exact (saved.heap_weaken allocation_extension).beta_argument location_related
private theorem request61 : SilentMapped graph [] [] [] maps61 (isolate s60 []) (isolate s61 maps61) writeTarget :=
  request_entry_same_target_mapped (requested := .cell 0) (base := isolate s60 []) ordered (rfl : graph.node 6 = some (node 6)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 5 = .ok (.variable 2)) setter_body pair_closed writeRequestPlain rfl .nil
private theorem value62 : TransportMapped graph [] [] maps61 maps61 (isolate s61 maps61) (isolate s62 maps61) writeTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s61 maps61)
    (rfl : graph.node 5 = some (node 5)) rfl (perform_components setter_body).2 pair_closed (framesOf maps61)
  have equal := Option.some.inj (lookup.symm.trans (rfl : setterEnv.lookup 2 = some (.location 0)))
  cases equal
  have frame : CoreRequestFrames.RequestRel graph [] allocated (.request (.cell (.bound 0)) 1 setterEnv) writeRequestPlain :=
    .operand (requested := .cell 0) (perform_header_at setter_body _ _ _ (.cell (.activation 0)) pairCode rfl rfl) rfl
  exact value_entry_mapped witness rfl rfl (prepend_request frame pair_closed (pushed_mapped .nil) .none)

include evidence in
private theorem carrier7 : RunningTail graph allocated physicalTail (lexicalTail d post) := (runningTail evidence).heap_weaken allocation_extension
include evidence in
private theorem link52 : CoreUnwindRelation.Link graph (w51 d post) (w52 d post) :=
  .runningAdministration (runningTail evidence) (.traversal app52 rfl) rfl rfl rfl
include evidence in
private theorem link53 : CoreUnwindRelation.Link graph (w52 d post) (w53 d post) :=
  .runningAdministration (runningTail evidence) (.value value53 rfl) rfl rfl rfl
include evidence in
private theorem link54 : CoreUnwindRelation.Link graph (w53 d post) (w54 d post) :=
  .runningAdministration (runningTail evidence) (.traversal app54 rfl) rfl rfl rfl
include evidence in
private theorem link55 : CoreUnwindRelation.Link graph (w54 d post) (w55 d post) :=
  .runningAdministration (runningTail evidence) (.traversal tuple55 rfl) rfl rfl rfl
include evidence in
private theorem link56 : CoreUnwindRelation.Link graph (w55 d post) (w56 d post) :=
  .runningAdministration (runningTail evidence) (.value value56 rfl) rfl rfl rfl
include evidence in
private theorem link57 : CoreUnwindRelation.Link graph (w56 d post) (w57 d post) :=
  .runningAdministration (runningTail evidence) (.traversal tuple57 rfl) rfl rfl rfl
include evidence in
private theorem link58 : CoreUnwindRelation.Link graph (w57 d post) (w58 d post) :=
  .runningAdministration (runningTail evidence) (.value value58 rfl) rfl rfl rfl
include evidence in
private theorem link59 : CoreUnwindRelation.Link graph (w58 d post) (w59 d post) :=
  .runningAdministration (runningTail evidence) (.allocation allocate59 allocation_extension) rfl rfl rfl
include evidence in
private theorem link61 : CoreUnwindRelation.Link graph (w60 d post) (w61 d post) :=
  .runningAdministration (carrier7 evidence) (.traversal request61 rfl) rfl rfl rfl
include evidence in
private theorem link62 : CoreUnwindRelation.Link graph (w61 d post) (w62 d post) :=
  .runningAdministration (carrier7 evidence) (.value value62 rfl) rfl rfl rfl


end Write

def outsideAt (d : Data) (post : PlainData) (payload : Int) : Stack :=
  .push (.plain post) (.spent 0 d.handler.answer d.handler.scope
    (.push (.plain d.plain) (.push (.cell 0 payload .none d.answer) .nil)))
def mapsAt (payload : Int) : List MappedFrame :=
  [(CoreCaptureEntry.Exported.clauseMaps,.bind 10 37 CoreResumeEntry.Exported.clauseEnv),
    ([],.clauseBoundary 0 0 0 0 none),([], .bind 12 44 methodsEnv),([], .resourceBoundary 48 0 payload)]
def closeMapsAt (m : Maps) (payload : Int) : List MappedFrame :=
  (m.handlerOwner,.clauseBoundary 0 0 0 1 none) :: mapsAt payload
def spentAt (d : Data) (post : PlainData) (payload : Int) : Stack :=
  .spent 1 d.handler.answer d.handler.scope (outsideAt d post payload)
def lexicalAt (d : Data) (post : PlainData) (payload : Int) : Stack :=
  .push (.unwinding d.action) (.push (.handler d.handler) (.push (.closing 0 falseScope) (spentAt d post payload)))
def physicalAt (m : Maps) (payload : Int) : List CoreMachine.Frame :=
  .cleanupCompletion 0 .unit :: .closeCompletion 0 :: framesOf (closeMapsAt m payload)
open CoreCleanupWritePrefix (s63)
open CoreCleanupFinishPrefix (s64 s65 s66 s67)
def w63 (d : Data) (post : PlainData) : CoreUnwindRelation.Point :=
  ⟨s63,.eval ⟨.unit,.none,lexicalAt d post 7⟩,[],[]⟩
def w64 (d : Data) (post : PlainData) (m : Maps) : CoreUnwindRelation.Point :=
  ⟨s64,.unwind d.action.scope (.push (.closing 0 falseScope) (spentAt d post 7)),[],closeMapsAt m 7⟩
def w65 (d : Data) (post : PlainData) (m : Maps) : CoreUnwindRelation.Point :=
  ⟨s65,.eval ⟨.unit,falseScope,spentAt d post 7⟩,[],closeMapsAt m 7⟩
def w66 (d : Data) (post : PlainData) : CoreUnwindRelation.Point :=
  ⟨s66,.eval ⟨.unit,d.handler.scope,outsideAt d post 7⟩,[],mapsAt 7⟩
def ordinaryAt (d : Data) (payload : Int) : Stack :=
  .spent 0 d.handler.answer d.handler.scope (.push (.plain d.plain) (.push (.cell 0 payload .none d.answer) .nil))
def postBindTarget (d : Data) : Configuration :=
  ⟨.bind 10 .unit CoreResumeEntry.Exported.postWriteCode,CoreResumeEntry.Exported.ticketScope,ordinaryAt d 7⟩
def postTarget (d : Data) : Configuration :=
  ⟨CoreResumeEntry.Exported.postWriteCode.subst 10 .unit,CoreResumeEntry.Exported.ticketScope,ordinaryAt d 7⟩
def remainingMaps : List MappedFrame :=
  [([],.clauseBoundary 0 0 0 0 none),([],.bind 12 44 methodsEnv),([],.resourceBoundary 48 0 7)]
def w67 (d : Data) : CoreUnwindRelation.Point :=
  ⟨s67,.eval (postTarget d),CoreCaptureEntry.Exported.clauseMaps,remainingMaps⟩

private theorem outsideWrite (evidence : Evidence d post second m n) :
    WriteCut graph [] 0 0 7 ((m.handlerOwner,.clauseBoundary 0 0 0 1 none) :: outside post)
      (.spent 1 d.handler.answer d.handler.scope (outsideTarget d post)) (closeMapsAt m 7) (spentAt d post 7) := by
  have selected := evidence.outside
  generalize firstEq : Stack.spent 1 d.handler.answer d.handler.scope (outsideTarget d post) = target at selected
  cases selected with
  | spent firstHeader rest =>
    obtain ⟨_,firstAnswer,firstScope,firstTail⟩ := Stack.spent.inj firstEq
    rw [← firstTail] at rest
    rw [← firstAnswer,← firstScope,← firstTail]
    change PushedWithMaps graph [] (outside post) (.push (.plain post) (.spent 0 d.handler.answer d.handler.scope
      (.push (.plain d.plain) (.push (.cell 0 0 .none d.answer) .nil)))) at rest
    cases rest with
    | cons postFrame next =>
      generalize nextEq : Stack.spent 0 d.handler.answer d.handler.scope
        (.push (.plain d.plain) (.push (.cell 0 0 .none d.answer) .nil)) = target at next
      cases next with
      | spent secondHeader next =>
        obtain ⟨_,secondAnswer,secondScope,secondTail⟩ := Stack.spent.inj nextEq
        rw [← secondTail] at next
        cases next with
        | cons caller next =>
          cases next with
          | boundary boundary next =>
            cases boundary with
            | cell known kind =>
              have update := WriteCut.spent (ticket := 0) secondHeader
                (WriteCut.push (.ordinary caller) (by simp [ExecFrame.erase,PlainData.erase,Frame.target])
                  (WriteCut.hit (owners := []) (scope := .none) (answer := d.answer)
                    (identity := 0) (old := 0) (new := 7) known kind next))
              rw [← secondAnswer,← secondScope] at update
              have full := WriteCut.spent (ticket := 1) firstHeader (WriteCut.push (.ordinary postFrame) (by simp [ExecFrame.erase,PlainData.erase,Frame.target]) update)
              rw [← firstAnswer,← firstScope] at full
              exact full
        | initializer frame tail => cases frame
        | boundary frame tail => cases frame
        | request frame tail => cases frame
        | resume frame tail => cases frame
      | cons frame tail => cases frame
      | initializer frame tail => cases frame
      | boundary frame tail => cases frame
      | cleanup frame tail => cases frame
      | request frame tail => cases frame
      | resume frame tail => cases frame
    | initializer frame tail => cases frame
    | boundary frame tail => cases frame
    | request frame tail => cases frame
    | resume frame tail => cases frame
  | cons frame tail => cases frame
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | cleanup frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

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

private theorem retainedEffect (evidence : Evidence d post second m n) : d.handler.effectInst = .user 0 [] := by
  have retained := evidence.retained
  cases retained with
  | boundary frame tail => exact headerEffect frame

private theorem updatedTail (evidence : Evidence d post second m n) :
    RunningTail graph allocated (physicalAt m 7) (lexicalAt d post 7) ∧
      CellUpdate 0 0 7 (lexicalTail d post) (lexicalAt d post 7) := by
  have projection : CoreMachine.closeFuel
      (CoreMachine.framesMass (.bind 6 22 CoreSecondCapture.nextEnv :: .cleanupBoundary 27 callbackEnv d.action.identity ::
        framesOf [(n.handlerOwner,.handlerBoundary 41 methodsEnv 0)]) + 1)
      (.bind 6 22 CoreSecondCapture.nextEnv :: .cleanupBoundary 27 callbackEnv d.action.identity ::
        framesOf [(n.handlerOwner,.handlerBoundary 41 methodsEnv 0)]) =
      .ok ([.cleanupBoundary 27 callbackEnv d.action.identity],[]) := by rw [evidence.identity]; rfl
  have capturedCopy : PushedWithMaps graph allocated
      [(n.bindOwner,.bind 6 22 CoreSecondCapture.nextEnv),
        (n.cleanupOwner,.cleanupBoundary 27 callbackEnv d.action.identity),
        (n.handlerOwner,.handlerBoundary 41 methodsEnv 0)] (capturedTarget d second) := by
    rw [evidence.identity]
    exact evidence.captured.heap_weaken allocation_extension
  have result := running_write (data := d.action) (pending := .bind 6 22 CoreSecondCapture.nextEnv)
    (action := 27) (environment := callbackEnv) (closing := []) (closeIdentity := 0) (closeScope := falseScope)
    capturedCopy ((evidence.identity.symm ▸ evidence.delayed).heap_weaken allocation_extension)
    (evidence.retained.heap_weaken allocation_extension)
    ((outsideWrite evidence).heap_weaken allocation_extension) projection (by
      intro tail changed update
      exact .push (by simp [ExecFrame.erase,HandlerData.erase,Frame.target,retainedEffect evidence]) update)
  rw [evidence.identity] at result
  exact result

private theorem write63 (evidence : Evidence d post second m n) :
    CoreUnwindRelation.Link graph (w62 d post) (w63 d post) ∧
      RawStep (attach writeTarget (lexicalTail d post)) ⟨.unit,.none,lexicalAt d post 7⟩ [] [] := by
  have successor : CoreUnwindRelation.Related graph (w63 d post) :=
    .runningCleanup (target := ⟨.unit,.none,.nil⟩) (updatedTail evidence).1
      ⟨rfl,.unit,.none,.returned .unit,pushed_mapped .nil⟩ rfl
  have rawStep : RawStep (attach writeTarget (lexicalTail d post)) ⟨.unit,.none,lexicalAt d post 7⟩ [] [] :=
    .writeCell 0 0 7 .none (lexicalTail d post) (lexicalAt d post 7) (updatedTail evidence).2
  exact ⟨.positive (.runningCleanup (carrier7 evidence) value62.successor rfl) rfl
    (CoreUnwindRelation.ordinary_step rawStep trivial) successor,rawStep⟩

private theorem callback_to_cell_write (evidence : Evidence d post second m n) :
    CoreUnwindRelation.Chain graph (w51 d post)
      [w52 d post,w53 d post,w54 d post,w55 d post,w56 d post,w57 d post,w58 d post,w59 d post,
        w60 d post,w61 d post,w62 d post,w63 d post] (w63 d post) :=
  .next (link52 evidence) (.next (link53 evidence) (.next (link54 evidence) (.next (link55 evidence)
    (.next (link56 evidence) (.next (link57 evidence) (.next (link58 evidence) (.next (link59 evidence)
      (.next (beta60 evidence).1 (.next (link61 evidence) (.next (link62 evidence) (.last (write63 evidence).1)))))))))))

private theorem outside7 (evidence : Evidence d post second m n) :
    PushedWithMaps graph allocated (mapsAt 7) (outsideAt d post 7) := by
  have selected := (outsideWrite evidence).components.2.1.heap_weaken allocation_extension
  generalize targetEq : spentAt d post 7 = target at selected
  cases selected with
  | spent header tail => exact (Stack.spent.inj targetEq).2.2.2.symm ▸ tail
  | cons frame tail => cases frame
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | cleanup frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

private theorem postParts (evidence : Evidence d post second m n)
    (context : post.context = .bind 10 CoreResumeEntry.Exported.postWriteCode) :
    ∃ fuel rawSuffix,CoreTranslation.translateFuel graph fuel CoreCaptureEntry.Exported.clauseMaps 37 = .ok rawSuffix ∧
      EnvCloses graph CoreCaptureEntry.Exported.clauseMaps allocated CoreResumeEntry.Exported.clauseEnv
        (.lambda 10 rawSuffix) (.lambda 10 CoreResumeEntry.Exported.postWriteCode) ∧
      ClosedExcept 10 CoreResumeEntry.Exported.postWriteCode ∧ PushedWithMaps graph allocated remainingMaps (ordinaryAt d 7) := by
  have tail := outside7 evidence
  cases tail with
  | cons frame tail =>
    change FrameRel graph CoreCaptureEntry.Exported.clauseMaps allocated (.bind 10 37 CoreResumeEntry.Exported.clauseEnv) post.context at frame
    rw [context] at frame
    cases frame with
    | bind translated saved ready => exact ⟨_,_,translated,saved,ready,tail⟩
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

private theorem cleanup_to_caller (evidence : Evidence d post second m n)
    (context : post.context = .bind 10 CoreResumeEntry.Exported.postWriteCode)
    (scope : post.scope = CoreResumeEntry.Exported.ticketScope) :
    CoreUnwindRelation.Chain graph (w63 d post) [w64 d post m,w65 d post m,w66 d post,w67 d] (w67 d) := by
  have spent := (outsideWrite evidence).components.2.1.heap_weaken allocation_extension
  have wait : CoreUnwindRelation.Related graph (w64 d post m) := .awaitingClose rfl rfl spent
  have finish : CoreUnwindRelation.Link graph (w63 d post) (w64 d post m) :=
    .positive (write63 evidence).1.endpoints.2 rfl (.next .finishCleanup (.one (.advance .handler))) wait
  have close : CoreUnwindRelation.Link graph (w64 d post m) (w65 d post m) :=
    .positive wait rfl (.one .finishClose) (.eval ⟨rfl,.unit,falseScope,.returned .unit,pushed_mapped spent⟩)
  have outside := outside7 evidence
  have returned : CoreUnwindRelation.Link graph (w65 d post m) (w66 d post) :=
    .positive close.endpoints.2 rfl (CoreUnwindRelation.ordinary_step (.leaveClause 1 d.handler.answer .unit
      (ValueRel.unit (graph := graph) (owners := []) (heap := allocated)).closed falseScope d.handler.scope
      (outsideAt d post 7)) trivial) (.eval ⟨rfl,.unit,d.handler.scope,.returned .unit,pushed_mapped outside⟩)
  obtain ⟨fuel,rawSuffix,translated,saved,ready,tail⟩ := postParts evidence context
  have frame : PlainFrameRel graph CoreCaptureEntry.Exported.clauseMaps allocated
      (.bind 10 37 CoreResumeEntry.Exported.clauseEnv) post := by
    change FrameRel graph CoreCaptureEntry.Exported.clauseMaps allocated _ post.context
    rw [context]
    exact .bind translated saved ready
  obtain ⟨before,next,plug,bind,after⟩ := bind_return_mapped (base := s66) translated saved ready
    (ValueRel.unit (graph := graph) (owners := CoreCaptureEntry.Exported.clauseMaps) (heap := allocated))
    post context tail d.handler.scope
  rw [scope] at plug bind after
  have linked : CoreUnwindRelation.Link graph (w66 d post) (w67 d) :=
    .positive returned.endpoints.2 next (.next (.evaluate plug trivial) (.one (.evaluate bind trivial))) (.eval after)
  exact .next finish (.next close (.next returned (.last linked)))


private theorem ordinary40 (related : CoreUnwindRelation.Related graph
    (CoreUnwindRelation.lift (p40 d post second m input))) : CoreInitialPrefix.Related graph (p40 d post second m input) := by
  generalize pointEq : CoreUnwindRelation.lift (p40 d post second m input) = point at related
  cases related with
  | eval component =>
    obtain ⟨stateEq,machineEq,ownersEq,mapsEq⟩ := CoreUnwindRelation.Point.mk.inj pointEq
    cases stateEq; cases ownersEq; cases mapsEq
    have targetEq := LexicalUnwind.Machine.eval.inj machineEq
    cases targetEq
    exact component
  | discard carrier control frames pushed =>
    obtain ⟨stateEq,machineEq,ownersEq,mapsEq⟩ := CoreUnwindRelation.Point.mk.inj pointEq
    have expressionEq := congrArg Configuration.expression (LexicalUnwind.Machine.eval.inj machineEq)
    cases expressionEq
  | projected captured outside projection nonempty control frames counter =>
    have machineEq := (CoreUnwindRelation.Point.mk.inj pointEq).2.1
    cases machineEq
  | awaitingClose control frames tail =>
    have machineEq := (CoreUnwindRelation.Point.mk.inj pointEq).2.1
    cases machineEq
  | resourceProjected cursor outside control frames =>
    have machineEq := (CoreUnwindRelation.Point.mk.inj pointEq).2.1
    cases machineEq
  | retainedProjected cursor outside control frames =>
    have machineEq := (CoreUnwindRelation.Point.mk.inj pointEq).2.1
    cases machineEq
  | runningCleanup carrier component frames =>
    rename_i physical lexical target
    obtain ⟨stateEq,machineEq,ownersEq,mapsEq⟩ := CoreUnwindRelation.Point.mk.inj pointEq
    cases stateEq; cases ownersEq; cases mapsEq
    have actual : (p40 d post second m input).state.frames = framesOf (p40 d post second m input).annotations := rfl
    rw [actual] at frames
    have lengths := congrArg List.length frames
    simp only [List.length_append] at lengths
    rename_i physical lexical
    have empty : physical = [] := by
      cases physical with
      | nil => rfl
      | cons head tail => simp only [List.length_cons] at lengths; omega
    exact False.elim (carrier.nonempty empty)

private def move (snapshot : Snapshot operations) (machine : LexicalUnwind.Machine) (completed : List Owner) : Snapshot operations :=
  {snapshot with run := ⟨⟨machine,snapshot.run.execution.issued,completed⟩,snapshot.run.tickets⟩}

def extensionPoints (d : Data) (post : PlainData) (m : Maps) : List CoreUnwindRelation.Point :=
  [w46 d post,w47 d post,w48 d post,w49 d post,w50 d post,w51 d post,w52 d post,w53 d post,w54 d post,
    w55 d post,w56 d post,w57 d post,w58 d post,w59 d post,w60 d post,w61 d post,w62 d post,w63 d post,
    w64 d post m,w65 d post m,w66 d post,w67 d]

private theorem everyPoint (chain : CoreUnwindRelation.Chain graph before points after) :
    ∀ point ∈ before :: points,CoreUnwindRelation.Related graph point := by
  induction chain with
  | last link =>
    intro point member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact link.endpoints.1
    · exact link.endpoints.2
  | next link rest ih =>
    intro point member
    rcases List.mem_cons.mp member with rfl | later
    · exact link.endpoints.1
    · exact ih point later

def earlierPoints (d : Data) (post second : PlainData) (m : Maps) (input : Ty) : List CoreUnwindRelation.Point :=
  CoreAdmittedDiscardPrefix.priorPoints d post second m input ++ CoreAdmittedDiscardPrefix.extensionPoints d post second m input

/-- The same admitted discard runs its actual callback, writes seven, completes
cleanup and close, and restores the post-resume caller. Every selected annotation
is retained until its existing source transition removes that boundary. -/
theorem admittedCleanupCompletion (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (firstResumeRow : Footprint) (firstCloseRow : Option Footprint)
    (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ (d : Data) (post : PlainData) (m : Maps) (second : PlainData)
      (firstAllocated allocated : SourcePlannedTyping.Contract)
      (discarded afterCleanup plugged final : Snapshot operations),
      firstAllocated.resumeRow = firstResumeRow ∧ firstAllocated.closeRow = firstCloseRow ∧
      allocated.resumeRow = resumeRow ∧ allocated.closeRow = closeRow ∧
      d.action.identity = 0 ∧ d.action.action = callbackCode ∧
      post.context = .bind 10 CoreResumeEntry.Exported.postWriteCode ∧ post.scope = CoreResumeEntry.Exported.ticketScope ∧
      CoreAdmittedPrefix.Admitted discarded ∧ discarded.run.execution.machine = (CoreAdmittedDiscardPrefix.p45 d post second m).machine ∧
      CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift p0)
        (earlierPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port) ++ extensionPoints d post m) (w67 d) ∧
      CoreAllocationHistory.Steps graph 67 (CoreMachine.initial graph) s67 ∧
      RawTrace (CoreAdmittedPrefix.initial tables families required).run.execution 33 final.run.execution ∧
      CoreAdmittedPrefix.Admitted final ∧
      (∀ point ∈ CoreUnwindRelation.lift p0 ::
          (earlierPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port) ++ extensionPoints d post m),
        CoreUnwindRelation.Related graph point ∧ ∃ snapshot : Snapshot operations,
          CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = point.machine) ∧
      CoreAdmittedPrefix.Admitted afterCleanup ∧ afterCleanup.run.execution.machine =
        .unwind d.action.scope (.push (.handler d.handler) (.push (.closing 0 falseScope) (spentAt d post 7))) ∧
      CoreAdmittedPrefix.Admitted plugged ∧ plugged.run.execution.machine = .eval (postBindTarget d) ∧
      final.world = [0] ∧ final.history = [0] ∧
      final.run.execution.issued = [.resource 0,.cleanup 0,.ticket 0,.ticket 1,.close 0] ∧
      final.run.execution.completed = [.close 0,.cleanup 0,.ticket 1,.ticket 0] ∧
      final.resumes = discarded.resumes ∧ final.disposals = discarded.disposals ∧ final.annotatedStore = discarded.annotatedStore ∧
      final.run.tickets = discarded.run.tickets ∧ final.run.execution.machine = (w67 d).machine := by
  obtain ⟨d,post,m,second,firstAllocated,allocated,captured,selected,discarded,
    firstResumeEq,firstCloseEq,resumeEq,closeEq,_inputEq,_focusContext,_focusScope,_handlerIdentity,_handlerArms,
    postContext,postScope,_secondContext,_secondScope,_capturedValid,_capturedMachine,_selectedValid,_selectedMachine,
    earlier,_coreSteps,trace,discardedValid,allEarlier,world,history,issued,completed,_resumes,_disposals,_store,_tickets,machine⟩ :=
    CoreAdmittedDiscardPrefix.admittedDiscardPrefix tables families required firstResumeRow firstCloseRow resumeRow closeRow
  let input := ScopedPorts.embedPort allocated.input.erase.erase.port
  have current40 : CoreInitialPrefix.Related graph (p40 d post second m input) := by
    apply ordinary40
    apply (allEarlier _ ?_).1
    simp [input,CoreAdmittedDiscardPrefix.priorPoints,CoreAdmittedSecondCapturePrefix.extensionPoints,
      List.mem_append,CoreAdmittedDiscardPrefix.extensionPoints]
  obtain ⟨n,identity,action,capturedPushed,delayed,retained,outsidePushed,_saved⟩ := callbackParts d post second m input current40
  let evidence : Evidence d post second m n := ⟨identity,action,capturedPushed,delayed,retained,outsidePushed⟩
  have current := earlier.endpoints.2
  have suffixChain : CoreUnwindRelation.Chain graph (CoreAdmittedDiscardPrefix.p45 d post second m)
      (extensionPoints d post m) (w67 d) :=
    CoreUnwindRelation.chain_append (discard_to_callback_body evidence current)
      (CoreUnwindRelation.chain_append (callback_to_cell_write evidence) (cleanup_to_caller evidence postContext postScope))
  have chain : CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift p0)
      (earlierPoints d post second m input ++ extensionPoints d post m) (w67 d) :=
    CoreUnwindRelation.chain_append earlier suffixChain
  let ready := move discarded (CoreAdmittedDiscardPrefix.p45 d post second m).machine discarded.run.execution.completed
  have readyEq : ready = discarded := by
    dsimp only [ready,move]
    rw [← machine]
  have readyValid : CoreAdmittedPrefix.Admitted ready := by rw [readyEq]; exact discardedValid
  let cleared := move discarded (.unwind falseScope (.push (.armed d.action)
    (.push (.handler d.handler) (.push (.closing 0 falseScope) (spentAt d post 0))))) discarded.run.execution.completed
  have clearStep : Stable.Step operations ready cleared := .advance .plain
  obtain ⟨clearEvent,clearedValid⟩ := clearStep.preserve readyValid
  have actualClear : LexicalUnwind.Event discarded.run.execution cleared.run.execution := by simpa only [readyEq] using clearEvent
  let running := move discarded (w46 d post).machine discarded.run.execution.completed
  have startStep : Stable.Step operations cleared running := by
    have step := Stable.Step.start_unwind_cleanup (snapshot := discarded) (runtimeScope := falseScope)
      (action := d.action) (tail := .push (.handler d.handler) (.push (.closing 0 falseScope) (spentAt d post 0)))
      (issued := discarded.run.execution.issued) (completed := discarded.run.execution.completed) (actions := discarded.run.tickets)
    rw [action] at step
    exact step
  obtain ⟨startEvent,runningValid⟩ := startStep.preserve clearedValid
  let body := move discarded (w51 d post).machine discarded.run.execution.completed
  have callbackBeta : Stable.Step operations running body :=
    .computation (snapshot := discarded) (issued := discarded.run.execution.issued) (completed := discarded.run.execution.completed)
      (actions := discarded.run.tickets) (.app trivial)
      (.beta 5 (close2 (raw 12)) .unit .none (lexicalTail d post)
        (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed canonicalActionParts.2.closed)
  obtain ⟨callbackEvent,bodyValid⟩ := callbackBeta.preserve runningValid
  let writing := move discarded (w60 d post).machine discarded.run.execution.completed
  have setterBeta : Stable.Step operations body writing :=
    .computation (snapshot := discarded) (issued := discarded.run.execution.issued) (completed := discarded.run.execution.completed)
      (actions := discarded.run.tickets) (.app pair_closed.1)
      (.beta 2 (.perform (.cell (.activation 0)) 1 (.variable 2)) pairCode .none (lexicalTail d post) pair_closed setter_related.closed)
  obtain ⟨setterEvent,writingValid⟩ := setterBeta.preserve bodyValid
  let written := move discarded (w63 d post).machine discarded.run.execution.completed
  have writeStep : Stable.Step operations writing written := .write_cell rfl (updatedTail evidence).2
  obtain ⟨writeEvent,writtenValid⟩ := writeStep.preserve writingValid
  let completedCleanup := .cleanup 0 :: discarded.run.execution.completed
  let afterCleanup := move discarded (.unwind d.action.scope
    (.push (.handler d.handler) (.push (.closing 0 falseScope) (spentAt d post 7)))) completedCleanup
  have cleanupStep : Stable.Step operations written afterCleanup := by
    have step := Stable.Step.finish_unwind_cleanup (snapshot := discarded) (runtimeScope := Execution.Scope.none)
      (action := d.action) (tail := .push (.handler d.handler) (.push (.closing 0 falseScope) (spentAt d post 7)))
      (issued := discarded.run.execution.issued) (completed := discarded.run.execution.completed) (actions := discarded.run.tickets)
    rw [identity] at step
    exact step
  obtain ⟨cleanupEvent,afterCleanupValid⟩ := cleanupStep.preserve writtenValid
  let waiting := move discarded (w64 d post m).machine completedCleanup
  have advanceStep : Stable.Step operations afterCleanup waiting := .advance .handler
  obtain ⟨advanceEvent,waitingValid⟩ := advanceStep.preserve afterCleanupValid
  let completedClose := .close 0 :: completedCleanup
  let closed := move discarded (w65 d post m).machine completedClose
  have closeStep : Stable.Step operations waiting closed := .finish_unwind_close
  obtain ⟨closeEvent,closedValid⟩ := closeStep.preserve waitingValid
  let returned := move discarded (w66 d post).machine completedClose
  have returnStep : Stable.Step operations closed returned := .leave_clause
    (ValueRel.unit (graph := graph) (owners := []) (heap := CoreCleanupWritePrefix.allocated)).closed
  obtain ⟨returnEvent,returnedValid⟩ := returnStep.preserve closedValid
  let plugged := move discarded (.eval (postBindTarget d)) completedClose
  have plugStep : Stable.Step operations returned plugged := by
    have step := Stable.Step.plug (snapshot := discarded) (runtimeScope := d.handler.scope)
      (plain := post) (tail := ordinaryAt d 7) (issued := discarded.run.execution.issued)
      (completed := completedClose) (actions := discarded.run.tickets)
      (ValueRel.unit (graph := graph) (owners := []) (heap := CoreCleanupWritePrefix.allocated)).closed
    rw [postContext,postScope] at step
    exact step
  obtain ⟨plugEvent,pluggedValid⟩ := plugStep.preserve returnedValid
  obtain ⟨_,_,_,_,postReady,_⟩ := postParts evidence postContext
  let final := move discarded (w67 d).machine completedClose
  have bindStep : Stable.Step operations plugged final :=
    .computation (snapshot := discarded) (issued := discarded.run.execution.issued) (completed := completedClose)
      (actions := discarded.run.tickets) (.bind trivial)
      (.bind 10 .unit CoreResumeEntry.Exported.postWriteCode CoreResumeEntry.Exported.ticketScope (ordinaryAt d 7)
        (ValueRel.unit (graph := graph) (owners := []) (heap := CoreCleanupWritePrefix.allocated)).closed postReady)
  obtain ⟨bindEvent,finalValid⟩ := bindStep.preserve pluggedValid
  have coreSteps : CoreAllocationHistory.Steps graph 67 (CoreMachine.initial graph) s67 := by
    have steps := chain.core_steps
    have length : (earlierPoints d post second m input ++ extensionPoints d post m).length = 67 := rfl
    rw [length] at steps
    exact steps
  have extensionValid : ∀ point ∈ extensionPoints d post m,
      ∃ snapshot : Snapshot operations,CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = point.machine := by
    intro point member
    simp only [extensionPoints,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact ⟨running,runningValid,rfl⟩
      | exact ⟨body,bodyValid,rfl⟩
      | exact ⟨writing,writingValid,rfl⟩
      | exact ⟨written,writtenValid,rfl⟩
      | exact ⟨waiting,waitingValid,rfl⟩
      | exact ⟨closed,closedValid,rfl⟩
      | exact ⟨returned,returnedValid,rfl⟩
      | exact ⟨final,finalValid,rfl⟩
  refine ⟨d,post,m,second,firstAllocated,allocated,discarded,afterCleanup,plugged,final,
    firstResumeEq,firstCloseEq,resumeEq,closeEq,identity,action,postContext,postScope,discardedValid,machine,
    chain,coreSteps,.step (.step (.step (.step (.step (.step (.step (.step (.step (.step (.step trace actualClear)
      startEvent) callbackEvent) setterEvent) writeEvent) cleanupEvent) advanceEvent) closeEvent) returnEvent) plugEvent) bindEvent,
    finalValid,?_,afterCleanupValid,rfl,pluggedValid,rfl,world,history,issued,?_,rfl,rfl,rfl,rfl,rfl⟩
  · intro point member
    refine ⟨everyPoint chain point member,?_⟩
    rcases List.mem_cons.mp member with equal | later
    · subst point
      exact (allEarlier _ List.mem_cons_self).2
    · rcases List.mem_append.mp later with prior | extension
      · exact (allEarlier point (List.mem_cons_of_mem _ prior)).2
      · exact extensionValid point extension
  · change .close 0 :: .cleanup 0 :: discarded.run.execution.completed = _
    rw [completed]


private theorem ordinary67 (related : CoreUnwindRelation.Related graph (w67 d)) :
    ComponentMapped graph CoreCaptureEntry.Exported.clauseMaps remainingMaps s67 (postTarget d) := by
  generalize pointEq : w67 d = point at related
  cases related with
  | eval component =>
    obtain ⟨stateEq,machineEq,ownersEq,mapsEq⟩ := CoreUnwindRelation.Point.mk.inj pointEq
    cases stateEq; cases ownersEq; cases mapsEq
    have targetEq := LexicalUnwind.Machine.eval.inj machineEq
    cases targetEq
    exact component
  | discard carrier control frames pushed =>
    obtain ⟨stateEq,machineEq,ownersEq,mapsEq⟩ := CoreUnwindRelation.Point.mk.inj pointEq
    cases stateEq
    cases control
  | projected captured outside projection nonempty control frames counter =>
    have machineEq := (CoreUnwindRelation.Point.mk.inj pointEq).2.1
    cases machineEq
  | awaitingClose control frames tail =>
    have machineEq := (CoreUnwindRelation.Point.mk.inj pointEq).2.1
    cases machineEq
  | resourceProjected cursor outside control frames =>
    have machineEq := (CoreUnwindRelation.Point.mk.inj pointEq).2.1
    cases machineEq
  | retainedProjected cursor outside control frames =>
    have machineEq := (CoreUnwindRelation.Point.mk.inj pointEq).2.1
    cases machineEq
  | runningCleanup carrier component frames =>
    rename_i physical lexical target
    obtain ⟨stateEq,machineEq,ownersEq,mapsEq⟩ := CoreUnwindRelation.Point.mk.inj pointEq
    cases stateEq; cases ownersEq; cases mapsEq
    have actual : s67.frames = framesOf remainingMaps := rfl
    rw [actual] at frames
    have lengths := congrArg List.length frames
    simp only [List.length_append] at lengths
    rename_i physical lexical
    have empty : physical = [] := by
      cases physical with
      | nil => rfl
      | cons head tail => simp only [List.length_cons] at lengths; omega
    exact False.elim (carrier.nonempty empty)

private theorem canonicalGetterSaved : EnvCloses graph [] [] methodsEnv
    (.lambda 12 (raw 44)) (.lambda 12 (close2 (raw 44))) := by
  obtain ⟨_,code,scope,control,stack⟩ := CoreHandlerPrefix.reached_handler_body_related
  have tail := (CoreReadyBindings.handler_head_pushed stack).2.2
  cases tail with
  | boundary boundary tail =>
    cases tail with
    | cons frame tail =>
      change FrameRel graph [] [] (.bind 12 44 methodsEnv) (.bind 12 (close2 (raw 44))) at frame
      cases frame with
      | bind translated saved ready =>
        have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 44 = .ok (raw 44))
        cases same
        exact saved
    | initializer frame tail => cases frame
    | boundary frame tail => cases frame
    | request frame tail => cases frame
    | resume frame tail => cases frame

private theorem plainContextOfTail (pushed : PushedWithMaps graph CoreCleanupWritePrefix.allocated
    CoreCleanupFinishPrefix.outsideMaps7 (ordinaryAt d 7)) : d.plain.context = .bind 12 (close2 (raw 44)) := by
  have selected := pushed
  generalize targetEq : ordinaryAt d 7 = target at selected
  cases selected with
  | spent header rest =>
    rw [← (Stack.spent.inj targetEq).2.2.2] at rest
    cases rest with
    | cons frame tail =>
      change FrameRel graph [] CoreCleanupWritePrefix.allocated (.bind 12 44 methodsEnv) d.plain.context at frame
      generalize contextEq : d.plain.context = context at frame
      cases frame with
      | bind translated selected ready =>
        have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 44 = .ok (raw 44))
        cases same
        have extension : HeapExtends [] CoreCleanupWritePrefix.allocated := by
          intro index cell known
          simp at known
        have sameCode := selected.unique (canonicalGetterSaved.heap_weaken extension)
        have bodyEq := (Code.lambda.inj sameCode).2
        exact congrArg (Context.bind 12) bodyEq
    | initializer frame tail => cases frame
    | boundary frame tail => cases frame
    | request frame tail => cases frame
    | resume frame tail => cases frame
  | cons frame tail => cases frame
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | cleanup frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

private theorem finalInputs (related : CoreUnwindRelation.Related graph (w67 d)) :
    PushedWithMaps graph CoreCleanupWritePrefix.allocated CoreCleanupFinishPrefix.outsideMaps7 (ordinaryAt d 7) ∧
    EnvCloses graph CoreCaptureEntry.Exported.clauseMaps CoreCleanupWritePrefix.allocated CoreFinalPrefix.bodyEnv
      (.app (.variable 3) (.pair (.variable 4) (.integer 11))) (postTarget d).expression ∧
    d.plain.context = .bind 12 (close2 (raw 44)) := by
  obtain ⟨frames,code,scope,control,stack⟩ := ordinary67 related
  obtain ⟨codeEq,scopeEq,pushed⟩ := CoreAdmittedResumePrefix.owner_head_pushed stack
  cases codeEq; cases scopeEq
  cases control with
  | evaluate translated saved =>
    have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 3 CoreCaptureEntry.Exported.clauseMaps 37 = .ok (.app (.variable 3) (.pair (.variable 4) (.integer 11))))
    cases same
    refine ⟨pushed,saved,?_⟩
    exact plainContextOfTail pushed

namespace Finale
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open CoreFinalPrefix (s68 s69 s70 s71 s72 s73 s74 s75 s76 s77 s78 s79 s80 s81 s82 s83 s84 s85 s86 s87 s88 s89 s90
  setterValue setterEnv allocated11 getterCaller getterBodyEnv maps68 maps70 maps71 maps73 maps77
  maps82 maps84 maps87 getterMaps11 callerMaps11 cellMaps11)
open CoreHandlerPrefix (getter acquired)
open CoreCleanupWritePrefix (allocated)
open CoreCaptureEntry.Exported (clauseMaps)
open CoreResumeEntry.Exported (ticketScope)
open CoreCleanupFinishPrefix (outsideMaps7)
def cellTail (d : Data) : Stack := .push (.cell 0 11 .none d.answer) .nil
def getterTail (d : Data) : Stack := .push (.plain d.plain) (cellTail d)
section
variable (d : Data)
variable (tail7 : PushedWithMaps graph allocated outsideMaps7 (ordinaryAt d 7))
variable (postSaved : EnvCloses graph clauseMaps allocated CoreFinalPrefix.bodyEnv (.app (.variable 3) (.pair (.variable 4) (.integer 11))) (postTarget d).expression)
variable (plainContext : d.plain.context = .bind 12 (close2 (raw 44)))
include tail7 postSaved plainContext
def pairCode : Code := .pair (.resourceRef (.activation 0)) (.integer 11)
def callTarget (d : Data) : Configuration := ⟨.app CoreHandlerPrefix.setter pairCode,ticketScope,(ordinaryAt d 7)⟩
def writeTarget (d : Data) : Configuration := ⟨.perform (.cell (.activation 0)) 1 pairCode,.none,(ordinaryAt d 7)⟩
private theorem current_parts : PushedWithMaps graph allocated outsideMaps7 (ordinaryAt d 7) ∧
    EnvCloses graph clauseMaps allocated CoreFinalPrefix.bodyEnv (.app (.variable 3) (.pair (.variable 4) (.integer 11))) (callTarget d).expression := ⟨tail7,postSaved⟩
private theorem setter_related : ValueRel graph clauseMaps allocated CoreFinalPrefix.setterValue CoreHandlerPrefix.setter := by
  obtain ⟨value,lookup,related⟩ := (current_parts d tail7 postSaved plainContext).2.app_components.1.lookup (by
    change ClosedValue (.lambda 2 (.perform (.cell (.activation 0)) 1 (.variable 2)))
    simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.Effect.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies,Syntax.without])
  have equal := Option.some.inj (lookup.symm.trans (rfl : CoreFinalPrefix.bodyEnv.lookup 3 = some CoreFinalPrefix.setterValue))
  cases equal
  exact related
private theorem pair_closed : ClosedValue pairCode := by
  simp [pairCode,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies]
private theorem handle_saved : EnvCloses graph clauseMaps allocated CoreFinalPrefix.bodyEnv (.variable 4) (.resourceRef (.activation 0)) :=
  (pair_components (current_parts d tail7 postSaved plainContext).2.app_components.2).1
private theorem integer_saved : EnvCloses graph clauseMaps allocated CoreFinalPrefix.bodyEnv (.integer 11) (.integer 11) :=
  (pair_components (current_parts d tail7 postSaved plainContext).2.app_components.2).2

def functionPlain (d : Data) : PlainData := ⟨.appFunction pairCode,ticketScope,.function (.product (.reference 0) .integer) .unit [.cell 0] [],.unit,[],rfl⟩
def argumentPlain (d : Data) : PlainData := ⟨.appArgument CoreHandlerPrefix.setter,ticketScope,.product (.reference 0) .integer,.unit,[],by decide⟩
def leftPlain (d : Data) : PlainData := ⟨.pairLeft (.integer 11),ticketScope,.reference 0,.product (.reference 0) .integer,[],rfl⟩
def rightPlain (d : Data) : PlainData := ⟨.pairRight (.resourceRef (.activation 0)),ticketScope,.integer,.product (.reference 0) .integer,[],by decide⟩
def requestPlain (d : Data) : PlainData := ⟨.perform (.cell (.activation 0)) 1,.none,.product (.reference 0) .integer,.unit,[],rfl⟩
def w68 (d : Data) : CoreUnwindRelation.Point := ⟨s68,.eval (callTarget d),clauseMaps,maps68⟩
def w69 (d : Data) : CoreUnwindRelation.Point := ⟨s69,(w68 d).machine,clauseMaps,maps68⟩
def w70 (d : Data) : CoreUnwindRelation.Point := ⟨s70,(w68 d).machine,clauseMaps,maps70⟩
def w71 (d : Data) : CoreUnwindRelation.Point := ⟨s71,(w68 d).machine,clauseMaps,maps71⟩
def w72 (d : Data) : CoreUnwindRelation.Point := ⟨s72,(w68 d).machine,clauseMaps,maps71⟩
def w73 (d : Data) : CoreUnwindRelation.Point := ⟨s73,(w68 d).machine,clauseMaps,maps73⟩
def w74 (d : Data) : CoreUnwindRelation.Point := ⟨s74,(w68 d).machine,clauseMaps,maps73⟩
def w75 (d : Data) : CoreUnwindRelation.Point := ⟨s75,(w68 d).machine,clauseMaps,maps70⟩
def w76 (d : Data) : CoreUnwindRelation.Point := ⟨s76,.eval (writeTarget d),[],outsideMaps7⟩
def w77 (d : Data) : CoreUnwindRelation.Point := ⟨s77,(w76 d).machine,[],maps77⟩
def w78 (d : Data) : CoreUnwindRelation.Point := ⟨s78,(w76 d).machine,[],maps77⟩

private theorem app68 : SilentMapped graph clauseMaps clauseMaps outsideMaps7 maps68 (isolate s67 outsideMaps7) (isolate s68 maps68) (callTarget d) :=
  application_entry_same_target_mapped (base := isolate s67 outsideMaps7) ordered
    (rfl : graph.node 37 = some (node 37)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 33 = .ok (.variable 3))
    (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 36 = .ok (.pair (.variable 4) (.integer 11)))
    (current_parts d tail7 postSaved plainContext).2 (setter_related d tail7 postSaved plainContext).closed (functionPlain d) rfl (current_parts d tail7 postSaved plainContext).1
private theorem value69 : TransportMapped graph clauseMaps clauseMaps maps68 maps68 (isolate s68 maps68) (isolate s69 maps68) (callTarget d) := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s68 maps68)
    (rfl : graph.node 33 = some (node 33)) rfl (current_parts d tail7 postSaved plainContext).2.app_components.1 (setter_related d tail7 postSaved plainContext).closed (framesOf maps68)
  have equal := Option.some.inj (lookup.symm.trans (rfl : CoreFinalPrefix.bodyEnv.lookup 3 = some CoreFinalPrefix.setterValue))
  cases equal
  have frame : PlainFrameRel graph clauseMaps allocated (.applyFunction 36 CoreFinalPrefix.bodyEnv) (functionPlain d) :=
    .applyFunction (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 36 = .ok (.pair (.variable 4) (.integer 11))) (current_parts d tail7 postSaved plainContext).2.app_components.2
  exact value_entry_mapped witness rfl rfl (prepend_mapped frame (setter_related d tail7 postSaved plainContext).closed (pushed_mapped (current_parts d tail7 postSaved plainContext).1) .none)
private theorem app70 : SilentMapped graph clauseMaps clauseMaps maps68 maps70 (isolate s69 maps68) (isolate s70 maps70) (callTarget d) :=
  application_argument_same_target_mapped (base := isolate s69 maps68)
    (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 36 = .ok (.pair (.variable 4) (.integer 11)))
    (current_parts d tail7 postSaved plainContext).2.app_components.2 (setter_related d tail7 postSaved plainContext) (pair_closed d tail7 postSaved plainContext) (functionPlain d) (argumentPlain d) rfl rfl rfl (current_parts d tail7 postSaved plainContext).1 .none
private theorem argument_stack : OrdinaryWithMaps graph allocated maps70 pairCode ticketScope (callTarget d).expression ticketScope (ordinaryAt d 7) :=
  prepend_mapped (plain := (argumentPlain d)) (.applyArgument (setter_related d tail7 postSaved plainContext)) (pair_closed d tail7 postSaved plainContext) (pushed_mapped (current_parts d tail7 postSaved plainContext).1) ticketScope
private theorem left_frame : PlainFrameRel graph clauseMaps allocated (.tupleLeft 35 CoreFinalPrefix.bodyEnv) (leftPlain d) :=
  .tupleLeft (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 35 = .ok (.integer 11)) (integer_saved d tail7 postSaved plainContext)
private theorem right_frame : PlainFrameRel graph clauseMaps allocated (.tupleRight (.handle 0)) (rightPlain d) := .tupleRight ValueRel.handle
private theorem tuple71 : SilentMapped graph clauseMaps clauseMaps maps70 maps71 (isolate s70 maps70) (isolate s71 maps71) (callTarget d) := by
  exact ⟨rfl,(tuple_entry_decreases (base := isolate s70 maps70) ordered (rfl : graph.node 36 = some (node 36)) rfl (framesOf maps70)).2,
    rfl,⟨rfl,pairCode,ticketScope,.evaluate (rfl : CoreTranslation.translateFuel graph 3 clauseMaps 36 = .ok (.pair (.variable 4) (.integer 11))) (current_parts d tail7 postSaved plainContext).2.app_components.2,(argument_stack d tail7 postSaved plainContext)⟩,
    ⟨rfl,_,.none,.evaluate (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 34 = .ok (.variable 4)) (handle_saved d tail7 postSaved plainContext),
      prepend_mapped (left_frame d tail7 postSaved plainContext) (ValueRel.handle (graph := graph) (owners := clauseMaps) (heap := allocated)).closed (argument_stack d tail7 postSaved plainContext) .none⟩⟩
private theorem value72 : TransportMapped graph clauseMaps clauseMaps maps71 maps71 (isolate s71 maps71) (isolate s72 maps71) (callTarget d) := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s71 maps71)
    (rfl : graph.node 34 = some (node 34)) rfl (handle_saved d tail7 postSaved plainContext) (ValueRel.handle (graph := graph) (owners := clauseMaps) (heap := allocated)).closed (framesOf maps71)
  have equal := Option.some.inj (lookup.symm.trans (rfl : CoreFinalPrefix.bodyEnv.lookup 4 = some (.handle 0)))
  cases equal
  exact value_entry_mapped witness rfl rfl
    (prepend_mapped (left_frame d tail7 postSaved plainContext) (ValueRel.handle (graph := graph) (owners := clauseMaps) (heap := allocated)).closed (argument_stack d tail7 postSaved plainContext) .none)
private theorem tuple73 : SilentMapped graph clauseMaps clauseMaps maps71 maps73 (isolate s72 maps71) (isolate s73 maps73) (callTarget d) := by
  exact ⟨rfl,(tuple_right_decreases (graph := graph) (isolate s72 maps71) (framesOf maps70)).2,rfl,
    (value72 d tail7 postSaved plainContext).successor,
    ⟨rfl,_,.none,.evaluate (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 35 = .ok (.integer 11)) (integer_saved d tail7 postSaved plainContext),
      prepend_mapped (right_frame d tail7 postSaved plainContext) (ValueRel.integer (graph := graph) (owners := clauseMaps) (heap := allocated) (value := 11)).closed (argument_stack d tail7 postSaved plainContext) .none⟩⟩
private theorem value74 : TransportMapped graph clauseMaps clauseMaps maps73 maps73 (isolate s73 maps73) (isolate s74 maps73) (callTarget d) := by
  obtain ⟨witness,_⟩ := CoreAdministrativeSteps.integer_evaluate (base := isolate s73 maps73)
    (rfl : graph.node 35 = some (node 35)) rfl (integer_saved d tail7 postSaved plainContext) (framesOf maps73)
  exact value_entry_mapped witness rfl rfl
    (prepend_mapped (right_frame d tail7 postSaved plainContext) (ValueRel.integer (graph := graph) (owners := clauseMaps) (heap := allocated) (value := 11)).closed (argument_stack d tail7 postSaved plainContext) .none)
private theorem allocate75 : TransportMapped graph clauseMaps clauseMaps maps73 maps70 (isolate s74 maps73) (isolate s75 maps70) (callTarget d) :=
  tuple_allocation_mapped (base := isolate s74 maps73) ValueRel.handle ValueRel.integer (rightPlain d) rfl (argument_stack d tail7 postSaved plainContext) .none clauseMaps
private theorem allocation_extension : HeapExtends s74.heap s75.heap :=
  (CoreAdministrativeSteps.tuple_allocate (base := isolate s74 maps73)
    (ValueRel.handle (graph := graph) (owners := clauseMaps) (heap := allocated)) (ValueRel.integer (graph := graph) (owners := clauseMaps) (heap := allocated) (value := 11)) (framesOf maps70)).2.1
private theorem location_related : ValueRel graph [] allocated11 (.location 1) pairCode := .location rfl .handle .integer
private theorem beta76 : CoreUnwindRelation.Link graph (w75 d) (w76 d) ∧ RawStep (callTarget d) (writeTarget d) [] [] := by
  have function := (setter_related d tail7 postSaved plainContext).heap_weaken (allocation_extension d tail7 postSaved plainContext)
  obtain ⟨before,next,step,after⟩ := beta_complete_mapped (base := isolate s75 maps70)
    (show ValueRel graph clauseMaps allocated11 CoreFinalPrefix.setterValue (.lambda 2 (.perform (.cell (.activation 0)) 1 (.variable 2))) from function)
    ((location_related d tail7 postSaved plainContext).owner_transport clauseMaps) (argumentPlain d) rfl ((current_parts d tail7 postSaved plainContext).1.heap_weaken (allocation_extension d tail7 postSaved plainContext)) .none clauseMaps
  exact ⟨.positive (.eval before) next (CoreUnwindRelation.ordinary_step step trivial) (.eval after),step⟩
private theorem setter_body : EnvCloses graph [] allocated11 CoreFinalPrefix.setterEnv (.perform (.cell (.bound 0)) 1 (.variable 2)) (writeTarget d).expression := by
  obtain ⟨fuel,rawBody,translated,saved,_⟩ := (setter_related d tail7 postSaved plainContext).closure_view
  have equal := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 6 = .ok (.perform (.cell (.bound 0)) 1 (.variable 2)))
  cases equal
  exact (saved.heap_weaken (allocation_extension d tail7 postSaved plainContext)).beta_argument (location_related d tail7 postSaved plainContext)
private theorem request77 : SilentMapped graph [] [] outsideMaps7 maps77 (isolate s76 outsideMaps7) (isolate s77 maps77) (writeTarget d) :=
  request_entry_same_target_mapped (requested := .cell 0) (base := isolate s76 outsideMaps7) ordered (rfl : graph.node 6 = some (node 6)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 5 = .ok (.variable 2)) (setter_body d tail7 postSaved plainContext) (pair_closed d tail7 postSaved plainContext) (requestPlain d) rfl ((current_parts d tail7 postSaved plainContext).1.heap_weaken (allocation_extension d tail7 postSaved plainContext))
private theorem value78 : TransportMapped graph [] [] maps77 maps77 (isolate s77 maps77) (isolate s78 maps77) (writeTarget d) := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s77 maps77)
    (rfl : graph.node 5 = some (node 5)) rfl (perform_components (setter_body d tail7 postSaved plainContext)).2 (pair_closed d tail7 postSaved plainContext) (framesOf maps77)
  have equal := Option.some.inj (lookup.symm.trans (rfl : CoreFinalPrefix.setterEnv.lookup 2 = some (.location 1)))
  cases equal
  have frame : CoreRequestFrames.RequestRel graph [] allocated11 (.request (.cell (.bound 0)) 1 CoreFinalPrefix.setterEnv) (requestPlain d) :=
    .operand (requested := .cell 0) (perform_header_at (setter_body d tail7 postSaved plainContext) _ _ _ (.cell (.activation 0)) pairCode rfl rfl) rfl
  exact value_entry_mapped witness rfl rfl (prepend_request frame (pair_closed d tail7 postSaved plainContext) (pushed_mapped ((current_parts d tail7 postSaved plainContext).1.heap_weaken (allocation_extension d tail7 postSaved plainContext))) .none)


private theorem link68 : CoreUnwindRelation.Link graph (w67 d) (w68 d) := .traversal (app68 d tail7 postSaved plainContext)
private theorem link69 : CoreUnwindRelation.Link graph (w68 d) (w69 d) := .value (value69 d tail7 postSaved plainContext)
private theorem link70 : CoreUnwindRelation.Link graph (w69 d) (w70 d) := .traversal (app70 d tail7 postSaved plainContext)
private theorem link71 : CoreUnwindRelation.Link graph (w70 d) (w71 d) := .traversal (tuple71 d tail7 postSaved plainContext)
private theorem link72 : CoreUnwindRelation.Link graph (w71 d) (w72 d) := .value (value72 d tail7 postSaved plainContext)
private theorem link73 : CoreUnwindRelation.Link graph (w72 d) (w73 d) := .traversal (tuple73 d tail7 postSaved plainContext)
private theorem link74 : CoreUnwindRelation.Link graph (w73 d) (w74 d) := .value (value74 d tail7 postSaved plainContext)
private theorem link75 : CoreUnwindRelation.Link graph (w74 d) (w75 d) := .value (allocate75 d tail7 postSaved plainContext)
private theorem link77 : CoreUnwindRelation.Link graph (w76 d) (w77 d) := .traversal (request77 d tail7 postSaved plainContext)
private theorem link78 : CoreUnwindRelation.Link graph (w77 d) (w78 d) := .value (value78 d tail7 postSaved plainContext)

def getterCall (d : Data) : Configuration := ⟨.app getter (.resourceRef (.activation 0)),d.plain.scope,(cellTail d)⟩
def w79 (d : Data) : CoreUnwindRelation.Point := ⟨s79,.eval ⟨.unit,.none,(ordinaryAt d 11)⟩,[],callerMaps11⟩
def w80 (d : Data) : CoreUnwindRelation.Point := ⟨s80,.eval ⟨.unit,d.handler.scope,(getterTail d)⟩,[],getterMaps11⟩
def w81 (d : Data) : CoreUnwindRelation.Point := ⟨s81,.eval (getterCall d),[],cellMaps11⟩

private theorem caller_write : WriteCut graph allocated11 0 7 11 outsideMaps7 (ordinaryAt d 7) callerMaps11 (ordinaryAt d 11) := by
  have tail := (current_parts d tail7 postSaved plainContext).1.heap_weaken (allocation_extension d tail7 postSaved plainContext)
  generalize targetEq : ordinaryAt d 7 = target at tail
  cases tail with
  | spent header tail =>
    obtain ⟨_,answerEq,scopeEq,restEq⟩ := Stack.spent.inj targetEq
    rw [← restEq] at tail
    cases tail with
    | cons caller rest =>
      cases rest with
      | boundary boundary rest =>
        cases boundary with
        | cell known kind =>
          have cut := WriteCut.spent (ticket := 0) header
            (WriteCut.push (.ordinary caller) (by simp [ExecFrame.erase,PlainData.erase,Frame.target,plainContext])
              (WriteCut.hit (owners := []) (scope := .none) (answer := d.answer) (identity := 0) (old := 7) (new := 11) known kind rest))
          rw [← answerEq,← scopeEq] at cut
          rw [← targetEq]
          exact cut
    | initializer frame tail => cases frame
    | boundary frame tail => cases frame
    | request frame tail => cases frame
    | resume frame tail => cases frame
  | cons frame tail => cases frame
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | cleanup frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

theorem write11_target : RawStep (writeTarget d) ⟨.unit,.none,(ordinaryAt d 11)⟩ [] [] :=
  .writeCell 0 7 11 .none (ordinaryAt d 7) (ordinaryAt d 11) (caller_write d tail7 postSaved plainContext).components.2.2
private theorem write79 : CoreUnwindRelation.Link graph (w78 d) (w79 d) :=
  .positive (.eval (value78 d tail7 postSaved plainContext).successor) rfl (CoreUnwindRelation.ordinary_step (write11_target d tail7 postSaved plainContext) trivial)
    (.eval ⟨rfl,.unit,.none,.returned .unit,pushed_mapped (caller_write d tail7 postSaved plainContext).components.2.1⟩)
private theorem getter_tail : PushedWithMaps graph allocated11 getterMaps11 (getterTail d) := by
  have tail := (caller_write d tail7 postSaved plainContext).components.2.1
  generalize targetEq : (ordinaryAt d 11) = target at tail
  cases tail with
  | spent header tail =>
      change PushedWithMaps graph allocated11 getterMaps11 (Stack.push (.plain d.plain) (.push (.cell 0 11 .none d.answer) .nil))
      exact (Stack.spent.inj targetEq).2.2.2.symm ▸ tail
  | cons frame tail => cases frame
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | cleanup frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

theorem return_first_spent_target : RawStep ⟨.unit,.none,(ordinaryAt d 11)⟩ ⟨.unit,d.handler.scope,(getterTail d)⟩ [] [] :=
  .leaveClause 0 d.handler.answer .unit (ValueRel.unit (graph := graph) (owners := []) (heap := allocated11)).closed .none d.handler.scope (getterTail d)
private theorem return80 : CoreUnwindRelation.Link graph (w79 d) (w80 d) :=
  .positive (write79 d tail7 postSaved plainContext).endpoints.2 rfl (CoreUnwindRelation.ordinary_step (return_first_spent_target d tail7 postSaved plainContext) trivial)
    (.eval ⟨rfl,.unit,d.handler.scope,.returned .unit,pushed_mapped (getter_tail d tail7 postSaved plainContext)⟩)
private theorem getter_parts : ∃ fuel rawSuffix,
    CoreTranslation.translateFuel graph fuel [] 44 = .ok rawSuffix ∧
    EnvCloses graph [] allocated11 methodsEnv (.lambda 12 rawSuffix) (.lambda 12 (close2 (raw 44))) ∧
    ClosedExcept 12 (close2 (raw 44)) ∧ PushedWithMaps graph allocated11 cellMaps11 (cellTail d) := by
  have tail := (getter_tail d tail7 postSaved plainContext)
  cases tail with
  | cons frame tail =>
      change FrameRel graph [] allocated11 (.bind 12 44 methodsEnv) d.plain.context at frame
      rw [plainContext] at frame
      cases frame with
      | bind translated saved ready => exact ⟨_,_,translated,saved,ready,tail⟩
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

def getterBindTarget (d : Data) : Configuration := ⟨.bind 12 .unit (close2 (raw 44)),d.plain.scope,(cellTail d)⟩
theorem getter_bind_target : RawStep ⟨.unit,d.handler.scope,(getterTail d)⟩ (getterBindTarget d) [] [] ∧ RawStep (getterBindTarget d) (getterCall d) [] [] := by
  obtain ⟨fuel,rawSuffix,translated,saved,ready,tail⟩ := (getter_parts d tail7 postSaved plainContext)
  obtain ⟨_,_,plug,bind,_⟩ := bind_return_mapped (base := s80) translated saved ready
    (ValueRel.unit (graph := graph) (owners := []) (heap := allocated11)) d.plain plainContext tail d.handler.scope
  exact ⟨plug,bind⟩
private theorem bind81 : CoreUnwindRelation.Link graph (w80 d) (w81 d) := by
  obtain ⟨fuel,rawSuffix,translated,saved,ready,tail⟩ := (getter_parts d tail7 postSaved plainContext)
  obtain ⟨current,next,plug,bind,successor⟩ := bind_return_mapped (base := s80) translated saved ready
    (ValueRel.unit (graph := graph) (owners := []) (heap := allocated11)) d.plain plainContext tail d.handler.scope
  exact .positive (.eval current) next (.next (.evaluate plug trivial) (CoreUnwindRelation.ordinary_step bind trivial)) (.eval successor)
private theorem cell_tail : PushedWithMaps graph allocated11 cellMaps11 (cellTail d) := by
  obtain ⟨_,_,_,_,_,tail⟩ := (getter_parts d tail7 postSaved plainContext)
  exact tail
private theorem getter_current : EnvCloses graph [] allocated11 getterCaller (.app (.variable 11) (.variable 4)) (getterCall d).expression := by
  obtain ⟨fuel,rawSuffix,translated,saved,_,_⟩ := (getter_parts d tail7 postSaved plainContext)
  have equal := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 44 = .ok (.app (.variable 11) (.variable 4)))
  cases equal
  exact saved.beta_argument ValueRel.unit
private theorem getter_related : ValueRel graph [] allocated11 (.closure 1 3 acquired) getter := by
  obtain ⟨value,lookup,related⟩ := (getter_current d tail7 postSaved plainContext).app_components.1.lookup (by
    change ClosedValue (.lambda 1 (.perform (.cell (.activation 0)) 0 (.variable 1)))
    simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.Effect.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies,Syntax.without])
  have equal := Option.some.inj (lookup.symm.trans (rfl : getterCaller.lookup 11 = some (.closure 1 3 acquired)))
  cases equal
  exact related

def getterFunction (d : Data) : PlainData := ⟨.appFunction (.resourceRef (.activation 0)),d.plain.scope,.function (.reference 0) .integer [.cell 0] [],.integer,[],rfl⟩
def getterArgument (d : Data) : PlainData := ⟨.appArgument getter,d.plain.scope,.reference 0,.integer,[],rfl⟩
def readPlain (d : Data) : PlainData := ⟨.perform (.cell (.activation 0)) 0,.none,.reference 0,.integer,[],rfl⟩
def readTarget (d : Data) : Configuration := ⟨.perform (.cell (.activation 0)) 0 (.resourceRef (.activation 0)),.none,(cellTail d)⟩
def w82 (d : Data) : CoreUnwindRelation.Point := ⟨s82,.eval (getterCall d),[],maps82⟩
def w83 (d : Data) : CoreUnwindRelation.Point := ⟨s83,(w82 d).machine,[],maps82⟩
def w84 (d : Data) : CoreUnwindRelation.Point := ⟨s84,(w82 d).machine,[],maps84⟩
def w85 (d : Data) : CoreUnwindRelation.Point := ⟨s85,(w82 d).machine,[],maps84⟩
def w86 (d : Data) : CoreUnwindRelation.Point := ⟨s86,.eval (readTarget d),[],cellMaps11⟩
def w87 (d : Data) : CoreUnwindRelation.Point := ⟨s87,(w86 d).machine,[],maps87⟩
def w88 (d : Data) : CoreUnwindRelation.Point := ⟨s88,(w86 d).machine,[],maps87⟩
def w89 (d : Data) : CoreUnwindRelation.Point := ⟨s89,.eval ⟨.integer 11,.none,(cellTail d)⟩,[],cellMaps11⟩
def finalTarget : Configuration := ⟨.integer 11,.none,.nil⟩
def w90 (d : Data) : CoreUnwindRelation.Point := ⟨s90,.eval finalTarget,[],[]⟩

private theorem app82 : SilentMapped graph [] [] cellMaps11 maps82 s81 s82 (getterCall d) :=
  application_entry_same_target_mapped (base := s81) ordered (rfl : graph.node 44 = some (node 44)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 42 = .ok (.variable 11))
    (rfl : CoreTranslation.translateFuel graph 2 [] 43 = .ok (.variable 4)) (getter_current d tail7 postSaved plainContext) (getter_related d tail7 postSaved plainContext).closed (getterFunction d) rfl (cell_tail d tail7 postSaved plainContext)
private theorem value83 : TransportMapped graph [] [] maps82 maps82 s82 s83 (getterCall d) := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := s82)
    (rfl : graph.node 42 = some (node 42)) rfl (getter_current d tail7 postSaved plainContext).app_components.1 (getter_related d tail7 postSaved plainContext).closed (framesOf maps82)
  have equal := Option.some.inj (lookup.symm.trans (rfl : getterCaller.lookup 11 = some (.closure 1 3 acquired)))
  cases equal
  have frame : PlainFrameRel graph [] allocated11 (.applyFunction 43 getterCaller) (getterFunction d) :=
    .applyFunction (rfl : CoreTranslation.translateFuel graph 2 [] 43 = .ok (.variable 4)) (getter_current d tail7 postSaved plainContext).app_components.2
  exact value_entry_mapped witness rfl rfl (prepend_mapped frame (getter_related d tail7 postSaved plainContext).closed (pushed_mapped (cell_tail d tail7 postSaved plainContext)) d.plain.scope)
private theorem argument84 : SilentMapped graph [] [] maps82 maps84 s83 s84 (getterCall d) :=
  application_argument_same_target_mapped (base := s83)
    (rfl : CoreTranslation.translateFuel graph 2 [] 43 = .ok (.variable 4)) (getter_current d tail7 postSaved plainContext).app_components.2
    (getter_related d tail7 postSaved plainContext) (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed
    (getterFunction d) (getterArgument d) rfl rfl rfl (cell_tail d tail7 postSaved plainContext) d.plain.scope
private theorem value85 : TransportMapped graph [] [] maps84 maps84 s84 s85 (getterCall d) := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := s84)
    (rfl : graph.node 43 = some (node 43)) rfl (getter_current d tail7 postSaved plainContext).app_components.2 (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed (framesOf maps84)
  have equal := Option.some.inj (lookup.symm.trans (rfl : getterCaller.lookup 4 = some (.handle 0)))
  cases equal
  have frame : PlainFrameRel graph [] allocated11 (.applyArgument (.closure 1 3 acquired)) (getterArgument d) := .applyArgument (getter_related d tail7 postSaved plainContext)
  exact value_entry_mapped witness rfl rfl (prepend_mapped frame (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed (pushed_mapped (cell_tail d tail7 postSaved plainContext)) d.plain.scope)
private theorem beta86 : CoreUnwindRelation.Link graph (w85 d) (w86 d) ∧ RawStep (getterCall d) (readTarget d) [] [] := by
  obtain ⟨before,next,step,after⟩ := beta_complete_mapped (base := s85)
    (show ValueRel graph [] allocated11 (.closure 1 3 acquired) (.lambda 1 (.perform (.cell (.activation 0)) 0 (.variable 1))) from (getter_related d tail7 postSaved plainContext))
    (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)) (getterArgument d) rfl (cell_tail d tail7 postSaved plainContext) .none []
  exact ⟨.positive (.eval before) next (CoreUnwindRelation.ordinary_step step trivial) (.eval after),step⟩
private theorem getter_body : EnvCloses graph [] allocated11 getterBodyEnv (.perform (.cell (.bound 0)) 0 (.variable 1)) (readTarget d).expression := by
  obtain ⟨fuel,rawBody,translated,saved,_⟩ := (getter_related d tail7 postSaved plainContext).closure_view
  have equal := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 3 = .ok (.perform (.cell (.bound 0)) 0 (.variable 1)))
  cases equal
  exact saved.beta_argument ValueRel.handle
private theorem request87 : SilentMapped graph [] [] cellMaps11 maps87 s86 s87 (readTarget d) :=
  request_entry_same_target_mapped (requested := .cell 0) (base := s86) ordered (rfl : graph.node 3 = some (node 3)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 2 = .ok (.variable 1)) (getter_body d tail7 postSaved plainContext)
    (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed (readPlain d) rfl (cell_tail d tail7 postSaved plainContext)
private theorem value88 : TransportMapped graph [] [] maps87 maps87 s87 s88 (readTarget d) := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := s87)
    (rfl : graph.node 2 = some (node 2)) rfl (perform_components (getter_body d tail7 postSaved plainContext)).2
    (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed (framesOf maps87)
  have equal := Option.some.inj (lookup.symm.trans (rfl : getterBodyEnv.lookup 1 = some (.handle 0)))
  cases equal
  have frame : RequestRel graph [] allocated11 (.request (.cell (.bound 0)) 0 getterBodyEnv) (readPlain d) :=
    .operand (requested := .cell 0) (perform_header_at (getter_body d tail7 postSaved plainContext) _ _ _ (.cell (.activation 0)) (.resourceRef (.activation 0)) rfl rfl) rfl
  exact value_entry_mapped witness rfl rfl (prepend_request frame (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed (pushed_mapped (cell_tail d tail7 postSaved plainContext)) d.plain.scope)

theorem read11_target : RawStep (readTarget d) ⟨.integer 11,.none,(cellTail d)⟩ [] [] := .readCell 0 11 .none (cellTail d) (cellTail d) .hit
private theorem read89 : CoreUnwindRelation.Link graph (w88 d) (w89 d) :=
  .positive (.eval (value88 d tail7 postSaved plainContext).successor) rfl (CoreUnwindRelation.ordinary_step (read11_target d tail7 postSaved plainContext) trivial)
    (.eval ⟨rfl,.integer 11,.none,.returned .integer,pushed_mapped (cell_tail d tail7 postSaved plainContext)⟩)
theorem release_target : RawStep ⟨.integer 11,.none,(cellTail d)⟩ finalTarget [] [.resource 0] :=
  .leaveCell 0 11 d.answer .none .none (.integer 11) (ValueRel.integer (graph := graph) (owners := []) (heap := allocated11) (value := 11)).closed .nil
private theorem release90 : CoreUnwindRelation.Link graph (w89 d) (w90 d) :=
  .positive (read89 d tail7 postSaved plainContext).endpoints.2 rfl (CoreUnwindRelation.ordinary_step (release_target d tail7 postSaved plainContext) trivial)
    (.eval ⟨rfl,.integer 11,.none,.returned .integer,pushed_mapped .nil⟩)

private theorem link82 : CoreUnwindRelation.Link graph (w81 d) (w82 d) := .traversal (app82 d tail7 postSaved plainContext)
private theorem link83 : CoreUnwindRelation.Link graph (w82 d) (w83 d) := .value (value83 d tail7 postSaved plainContext)
private theorem link84 : CoreUnwindRelation.Link graph (w83 d) (w84 d) := .traversal (argument84 d tail7 postSaved plainContext)
private theorem link85 : CoreUnwindRelation.Link graph (w84 d) (w85 d) := .value (value85 d tail7 postSaved plainContext)
private theorem link87 : CoreUnwindRelation.Link graph (w86 d) (w87 d) := .traversal (request87 d tail7 postSaved plainContext)
private theorem link88 : CoreUnwindRelation.Link graph (w87 d) (w88 d) := .value (value88 d tail7 postSaved plainContext)

theorem post_beta_target : RawStep (callTarget d) (writeTarget d) [] [] := (beta76 d tail7 postSaved plainContext).2
theorem getter_beta_target : RawStep (getterCall d) (readTarget d) [] [] := (beta86 d tail7 postSaved plainContext).2

def finalPoints (d : Data) : List CoreUnwindRelation.Point := [(w68 d),(w69 d),(w70 d),(w71 d),(w72 d),(w73 d),(w74 d),(w75 d),(w76 d),(w77 d),(w78 d),(w79 d),(w80 d),(w81 d),(w82 d),(w83 d),(w84 d),(w85 d),(w86 d),(w87 d),(w88 d),(w89 d),(w90 d)]
theorem caller_to_final : CoreUnwindRelation.Chain graph (w67 d) (finalPoints d) (w90 d) :=
  .next (link68 d tail7 postSaved plainContext) (.next (link69 d tail7 postSaved plainContext) (.next (link70 d tail7 postSaved plainContext) (.next (link71 d tail7 postSaved plainContext) (.next (link72 d tail7 postSaved plainContext) (.next (link73 d tail7 postSaved plainContext) (.next (link74 d tail7 postSaved plainContext)
  (.next (link75 d tail7 postSaved plainContext) (.next (beta76 d tail7 postSaved plainContext).1 (.next (link77 d tail7 postSaved plainContext) (.next (link78 d tail7 postSaved plainContext) (.next (write79 d tail7 postSaved plainContext) (.next (return80 d tail7 postSaved plainContext) (.next (bind81 d tail7 postSaved plainContext)
  (.next (link82 d tail7 postSaved plainContext) (.next (link83 d tail7 postSaved plainContext) (.next (link84 d tail7 postSaved plainContext) (.next (link85 d tail7 postSaved plainContext) (.next (beta86 d tail7 postSaved plainContext).1 (.next (link87 d tail7 postSaved plainContext) (.next (link88 d tail7 postSaved plainContext)
  (.next (read89 d tail7 postSaved plainContext) (.last (release90 d tail7 postSaved plainContext)))))))))))))))))))))))


end
end Finale
/-- Complete the same admitted exported execution. The terminal result and empty
stack are obtained through current source preservation, not future validity. -/
theorem admittedFinalCompletion (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (firstResumeRow : Footprint) (firstCloseRow : Option Footprint)
    (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ (d : Data) (post : PlainData) (m : Maps) (second : PlainData)
      (firstAllocated allocated : SourcePlannedTyping.Contract) (at67 plugged final : Snapshot operations),
      firstAllocated.resumeRow = firstResumeRow ∧ firstAllocated.closeRow = firstCloseRow ∧
      allocated.resumeRow = resumeRow ∧ allocated.closeRow = closeRow ∧
      d.action.identity = 0 ∧ d.action.action = callbackCode ∧
      CoreAdmittedPrefix.Admitted at67 ∧ at67.run.execution.machine = (w67 d).machine ∧
      CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift p0)
        ((earlierPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port) ++ extensionPoints d post m) ++ Finale.finalPoints d) (Finale.w90 d) ∧
      CoreAllocationHistory.Steps graph 90 (CoreMachine.initial graph) CoreFinalPrefix.s90 ∧
      RawTrace (CoreAdmittedPrefix.initial tables families required).run.execution 41 final.run.execution ∧
      CoreAdmittedPrefix.Admitted final ∧
      (∀ point ∈ CoreUnwindRelation.lift p0 ::
          ((earlierPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port) ++ extensionPoints d post m) ++ Finale.finalPoints d),
        CoreUnwindRelation.Related graph point ∧ ∃ snapshot : Snapshot operations,
          CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = point.machine) ∧
      CoreAdmittedPrefix.Admitted plugged ∧ plugged.run.execution.machine = .eval (Finale.getterBindTarget d) ∧
      final.world = [0] ∧ final.history = [0] ∧
      final.run.execution.issued = [.resource 0,.cleanup 0,.ticket 0,.ticket 1,.close 0] ∧
      final.run.execution.completed = [.resource 0,.close 0,.cleanup 0,.ticket 1,.ticket 0] ∧
      final.resumes = at67.resumes ∧ final.disposals = at67.disposals ∧ final.annotatedStore = at67.annotatedStore ∧
      final.run.tickets = at67.run.tickets ∧ final.run.execution.machine = .eval ⟨.integer 11,.none,.nil⟩ := by
  obtain ⟨d,post,m,second,firstAllocated,allocated,discarded,afterCleanup,postPlugged,at67,
    firstResumeEq,firstCloseEq,resumeEq,closeEq,identity,action,postContext,postScope,discardedValid,discardedMachine,
    earlier,core67,trace,at67Valid,allEarlier,afterCleanupValid,afterCleanupMachine,postPluggedValid,postPluggedMachine,
    world,history,issued,completed,resumes,disposals,store,tickets,machine⟩ :=
    admittedCleanupCompletion tables families required firstResumeRow firstCloseRow resumeRow closeRow
  obtain ⟨tail7,postSaved,plainContext⟩ := finalInputs earlier.endpoints.2
  have suffix := Finale.caller_to_final d tail7 postSaved plainContext
  have chain := CoreUnwindRelation.chain_append earlier suffix
  let ready := move at67 (w67 d).machine at67.run.execution.completed
  have readyEq : ready = at67 := by dsimp only [ready,move]; rw [← machine]
  have readyValid : CoreAdmittedPrefix.Admitted ready := by rw [readyEq]; exact at67Valid
  let writing := move at67 (Finale.w76 d).machine at67.run.execution.completed
  have betaStep : Stable.Step operations ready writing :=
    .computation (snapshot := at67) (issued := at67.run.execution.issued) (completed := at67.run.execution.completed)
      (actions := at67.run.tickets) (.app (Finale.pair_closed d tail7 postSaved plainContext).1)
      (.beta 2 (.perform (.cell (.activation 0)) 1 (.variable 2)) Finale.pairCode CoreResumeEntry.Exported.ticketScope
        (ordinaryAt d 7) (Finale.pair_closed d tail7 postSaved plainContext)
        (Finale.setter_related d tail7 postSaved plainContext).closed)
  obtain ⟨betaEvent,writingValid⟩ := betaStep.preserve readyValid
  have actualBeta : LexicalUnwind.Event at67.run.execution writing.run.execution := by simpa only [readyEq] using betaEvent
  let written := move at67 (Finale.w79 d).machine at67.run.execution.completed
  have writeStep : Stable.Step operations writing written :=
    .write_cell rfl (Finale.caller_write d tail7 postSaved plainContext).components.2.2
  obtain ⟨writeEvent,writtenValid⟩ := writeStep.preserve writingValid
  let returned := move at67 (Finale.w80 d).machine at67.run.execution.completed
  have returnStep : Stable.Step operations written returned := .leave_clause
    (ValueRel.unit (graph := graph) (owners := []) (heap := CoreFinalPrefix.allocated11)).closed
  obtain ⟨returnEvent,returnedValid⟩ := returnStep.preserve writtenValid
  let plugged := move at67 (.eval (Finale.getterBindTarget d)) at67.run.execution.completed
  have plugStep : Stable.Step operations returned plugged := by
    have step := Stable.Step.plug (snapshot := at67) (runtimeScope := d.handler.scope)
      (plain := d.plain) (tail := Finale.cellTail d) (issued := at67.run.execution.issued)
      (completed := at67.run.execution.completed) (actions := at67.run.tickets)
      (ValueRel.unit (graph := graph) (owners := []) (heap := CoreFinalPrefix.allocated11)).closed
    rw [plainContext] at step
    exact step
  obtain ⟨plugEvent,pluggedValid⟩ := plugStep.preserve returnedValid
  obtain ⟨_,_,_,_,getterReady,_⟩ := Finale.getter_parts d tail7 postSaved plainContext
  let calling := move at67 (Finale.w81 d).machine at67.run.execution.completed
  have bindStep : Stable.Step operations plugged calling :=
    .computation (snapshot := at67) (issued := at67.run.execution.issued) (completed := at67.run.execution.completed)
      (actions := at67.run.tickets) (.bind trivial)
      (.bind 12 .unit (close2 (raw 44)) d.plain.scope (Finale.cellTail d)
        (ValueRel.unit (graph := graph) (owners := []) (heap := CoreFinalPrefix.allocated11)).closed getterReady)
  obtain ⟨bindEvent,callingValid⟩ := bindStep.preserve pluggedValid
  let reading := move at67 (Finale.w86 d).machine at67.run.execution.completed
  have getterBeta : Stable.Step operations calling reading :=
    .computation (snapshot := at67) (issued := at67.run.execution.issued) (completed := at67.run.execution.completed)
      (actions := at67.run.tickets) (.app trivial)
      (.beta 1 (.perform (.cell (.activation 0)) 0 (.variable 1)) (.resourceRef (.activation 0)) d.plain.scope
        (Finale.cellTail d) (ValueRel.handle (graph := graph) (owners := []) (heap := CoreFinalPrefix.allocated11) (key := 0)).closed
        (Finale.getter_related d tail7 postSaved plainContext).closed)
  obtain ⟨getterEvent,readingValid⟩ := getterBeta.preserve callingValid
  let read := move at67 (Finale.w89 d).machine at67.run.execution.completed
  have readStep : Stable.Step operations reading read := .read_cell rfl .hit
  obtain ⟨readEvent,readValid⟩ := readStep.preserve readingValid
  let final := move at67 (Finale.w90 d).machine (.resource 0 :: at67.run.execution.completed)
  have releaseStep : Stable.Step operations read final := .leave_resource
    (ValueRel.integer (graph := graph) (owners := []) (heap := CoreFinalPrefix.allocated11) (value := 11)).closed
  obtain ⟨releaseEvent,finalValid⟩ := releaseStep.preserve readValid
  have coreSteps : CoreAllocationHistory.Steps graph 90 (CoreMachine.initial graph) CoreFinalPrefix.s90 := by
    have steps := chain.core_steps
    have length : ((earlierPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port) ++ extensionPoints d post m) ++ Finale.finalPoints d).length = 90 := rfl
    rw [length] at steps
    exact steps
  have suffixValid : ∀ point ∈ Finale.finalPoints d,
      ∃ snapshot : Snapshot operations,CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = point.machine := by
    intro point member
    simp only [Finale.finalPoints,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact ⟨at67,at67Valid,machine⟩
      | exact ⟨writing,writingValid,rfl⟩
      | exact ⟨written,writtenValid,rfl⟩
      | exact ⟨returned,returnedValid,rfl⟩
      | exact ⟨calling,callingValid,rfl⟩
      | exact ⟨reading,readingValid,rfl⟩
      | exact ⟨read,readValid,rfl⟩
      | exact ⟨final,finalValid,rfl⟩
  refine ⟨d,post,m,second,firstAllocated,allocated,at67,plugged,final,
    firstResumeEq,firstCloseEq,resumeEq,closeEq,identity,action,at67Valid,machine,chain,coreSteps,
    .step (.step (.step (.step (.step (.step (.step (.step trace actualBeta) writeEvent) returnEvent) plugEvent) bindEvent) getterEvent) readEvent) releaseEvent,
    finalValid,?_,pluggedValid,rfl,world,history,issued,?_,rfl,rfl,rfl,rfl,rfl⟩
  · intro point member
    refine ⟨everyPoint chain point member,?_⟩
    rcases List.mem_cons.mp member with rfl | later
    · exact (allEarlier _ List.mem_cons_self).2
    · rcases List.mem_append.mp later with prior | extension
      · exact (allEarlier point (List.mem_cons_of_mem _ prior)).2
      · exact suffixValid point extension
  · change .resource 0 :: at67.run.execution.completed = _
    rw [completed]

#print axioms finalInputs
#print axioms Finale.caller_to_final

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCompletionPrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCompletionPrefix.callbackParts

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCompletionPrefix.admittedCleanupCompletion

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedCompletionPrefix.admittedFinalCompletion
