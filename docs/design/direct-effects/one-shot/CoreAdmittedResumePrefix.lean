import CoreAdmittedCapturePrefix
import CoreResumeEntry

/-! The admitted first clause and resume keep the capture-selected port and
frame data. Ordinary Core traversal uses current lexical evidence; source
preservation selects the post-resume frame and continuation successor. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedResumePrefix
open ScopedExpressions ScopedExecution ProtectionContracts
open InstallationSupport InstallationSupport.Preservation CoreInitialExample
open CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential
open CoreOrdinaryCompletion CoreInitialPrefix CoreExportedFixture CoreAdministrativeTransport
open CoreHandlerPrefix (raw close2 methodsEnv)
open CoreCaptureEntry.Exported (clauseMaps capturedMaps outsideMaps)
open CoreResumeEntry CoreResumeFrames
open CoreResumeEntry.Exported (ownedRaw clauseEnv ticketScope yesCode noCode postWriteCode resumeCode branchPlain resumePlain restoredMaps)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Current selected data; this record contains no invariant or future-state
certificate. -/
structure Data where
  answer : Ty
  plain : PlainData
  handler : HandlerData
  action : ActionData
  focus : PlainData
  input : Ty

private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0, .unit, [], none, .unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl

def startTarget (d : Data) : Configuration :=
  CoreAdmittedCapturePrefix.clauseTarget d.answer d.plain d.handler d.action d.focus d.input
def p28 (d : Data) : Point :=
  CoreAdmittedCapturePrefix.t28 d.answer d.plain d.handler d.action d.focus d.input

def selectedTarget (d : Data) : Configuration := ⟨yesCode, ticketScope, (startTarget d).stack⟩
def resumeTarget (d : Data) (post : PlainData) : Configuration :=
  ⟨resumeCode, ticketScope, .push (.plain post) (startTarget d).stack⟩
def restoredTarget (d : Data) (post : PlainData) : Configuration :=
  ⟨.unit, ticketScope, (CoreAdmittedCapturePrefix.capturedTarget d.handler d.action d.focus).append
    (.push (.plain post) (.spent 0 d.handler.answer d.handler.scope
      (CoreAdmittedCapturePrefix.outsideTarget d.answer d.plain)))⟩

def p29 (d : Data) : Point := ⟨CoreResumeEntry.Exported.s29, startTarget d, clauseMaps,
  (clauseMaps, .matchCases (CoreStrictSteps.booleanArms 38 39 false) clauseEnv) :: (p28 d).annotations⟩
def p30 (d : Data) : Point := ⟨CoreResumeEntry.Exported.s30, startTarget d, clauseMaps, (p29 d).annotations⟩
def p31 (d : Data) : Point := ⟨CoreResumeEntry.Exported.s31, selectedTarget d, clauseMaps, (p28 d).annotations⟩
def p32 (d : Data) (post : PlainData) : Point := ⟨CoreResumeEntry.Exported.s32, resumeTarget d post, clauseMaps,
  (clauseMaps, .bind 10 37 clauseEnv) :: (p28 d).annotations⟩
def p33 (d : Data) (post : PlainData) : Point := ⟨CoreResumeEntry.Exported.s33, resumeTarget d post, clauseMaps,
  (clauseMaps, .resume 0 0) :: (p32 d post).annotations⟩
def p34 (d : Data) (post : PlainData) : Point := ⟨CoreResumeEntry.Exported.s34, resumeTarget d post, clauseMaps, (p33 d post).annotations⟩
def p35 (d : Data) (post : PlainData) (saved : List MappedFrame) : Point :=
  ⟨CoreResumeEntry.Exported.s35, restoredTarget d post, clauseMaps,
    saved ++ [(clauseMaps, .bind 10 37 clauseEnv)] ++ ([], .clauseBoundary 0 0 0 0 none) :: outsideMaps⟩

private theorem translation_unique {owners : CoreTranslation.OwnerMap} {rawCode otherRaw : Code}
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok rawCode)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok otherRaw) : rawCode = otherRaw := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index rawCode (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index otherRaw (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

private theorem owner_head_pushed {owners : CoreTranslation.OwnerMap}
    (related : OrdinaryWithMaps graph heap ((owners,.clauseBoundary handler owner occurrence ticket capture) :: rest)
      code scope result resultScope target) :
    code = result ∧ scope = resultScope ∧
      PushedWithMaps graph heap ((owners,.clauseBoundary handler owner occurrence ticket capture) :: rest) target := by
  obtain ⟨flatPrefix,suffix,split,flat,pushed⟩ := related
  cases flat with
  | nil => exact ⟨rfl,rfl,split.symm ▸ pushed⟩
  | @cons frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .clauseBoundary handler owner occurrence ticket capture := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same; cases frame
  | @initializer frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .clauseBoundary handler owner occurrence ticket capture := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same; cases frame
  | @request frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .clauseBoundary handler owner occurrence ticket capture := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same; cases frame
  | @resume frameOwners core plain cores code scope result resultScope frame ready tail =>
      have same : core = .clauseBoundary handler owner occurrence ticket capture := by
        have head := congrArg (fun xs => xs.head?.map Prod.snd) split
        simpa using head.symm
      cases same; cases frame


private theorem currentClause (d : Data) (related : Related graph (p28 d)) :
    EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 40) (startTarget d).expression ∧
    PushedWithMaps graph [] (p28 d).annotations (startTarget d).stack := by
  obtain ⟨_shape, code, scope, control, stack⟩ := related
  change OrdinaryWithMaps graph []
    (([], .clauseBoundary 0 0 0 0 (some (framesOf capturedMaps))) :: outsideMaps)
    code scope (startTarget d).expression ticketScope (startTarget d).stack at stack
  obtain ⟨rfl, rfl, pushed⟩ := owner_head_pushed stack
  cases control with
  | evaluate translated saved =>
    have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 40 = .ok (ownedRaw 40))
    cases same
    exact ⟨saved, pushed⟩

private theorem branchParts (d : Data) (related : Related graph (p28 d)) :
    EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 30) (.boolean true) ∧
    EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 38) yesCode ∧
    EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 39) noCode :=
  branch_components (currentClause d related).1

/-- Branch selection follows the actual returned Core operand and preserves
all source-selected captured data. -/
theorem branchPrefix (d : Data) (related : Related graph (p28 d)) :
    Chain graph (p28 d) [p29 d, p30 d, p31 d] (p31 d) ∧
    RawStep (startTarget d) (selectedTarget d) [] [] := by
  have current := currentClause d related
  have parts := branchParts d related
  have traversal : SilentMapped graph clauseMaps clauseMaps (p28 d).annotations (p29 d).annotations
      CoreCaptureEntry.Exported.s28 CoreResumeEntry.Exported.s29 (startTarget d) :=
    boolean_entry_same_target (base := CoreCaptureEntry.Exported.s28) (environment := clauseEnv)
      (scrutineeCode := .boolean true) (yesCode := yesCode) (noCode := noCode)
      (annotations := (p28 d).annotations) ordered (rfl : graph.node 40 = some (node 40)) rfl
      (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 30 = .ok (ownedRaw 30))
      (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 38 = .ok (ownedRaw 38))
      (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 39 = .ok (ownedRaw 39))
      current.1 parts.1 parts.2.1 parts.2.2
      (ValueRel.boolean (graph := graph) (owners := clauseMaps) (heap := []) (value := true)).closed
      branchPlain rfl current.2
  obtain ⟨value, lookup, witness, _translated⟩ := CoreAdministrativeSteps.variable_evaluate
    (base := CoreResumeEntry.Exported.s29) (rfl : graph.node 30 = some (node 30)) rfl parts.1
    (ValueRel.boolean (graph := graph) (owners := clauseMaps) (heap := []) (value := true)).closed CoreResumeEntry.Exported.s29.frames
  have valueEq : value = .boolean true := Option.some.inj (lookup.symm.trans rfl)
  cases valueEq
  have frame : PlainFrameRel graph clauseMaps []
      (.matchCases (CoreStrictSteps.booleanArms 38 39 false) clauseEnv) branchPlain :=
    .booleanMatch (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 38 = .ok (ownedRaw 38))
      (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 39 = .ok (ownedRaw 39)) parts.2.1 parts.2.2
  have stack := prepend_mapped frame
    (ValueRel.boolean (graph := graph) (owners := clauseMaps) (heap := []) (value := true)).closed
    (pushed_mapped current.2) ticketScope
  have returned : Link graph (p29 d) (p30 d) := .value (value_entry_mapped witness rfl rfl stack)
  obtain ⟨_before, next, step, after⟩ := boolean_complete_mapped (base := CoreResumeEntry.Exported.s30)
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 38 = .ok (ownedRaw 38))
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 39 = .ok (ownedRaw 39)) parts.2.1 parts.2.2
    true false branchPlain rfl current.2 clauseMaps ticketScope
  exact ⟨.next (.traversal traversal) (.next returned (.last (.positive returned.endpoints.2 next (.one step) after))), step⟩

private theorem postReady : ClosedExcept 10 postWriteCode := by
  have bound : postWriteCode.dependencies.all (fun dep => match dep with | .variable n => n == 10 | _ => true) = true := by decide
  intro n member
  simpa using List.all_eq_true.mp bound (.variable n) member
private theorem bindParts (d : Data) (related : Related graph (p28 d)) :
    EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 32) resumeCode ∧
    EnvCloses graph clauseMaps [] clauseEnv (.lambda 10 (ownedRaw 37)) (.lambda 10 postWriteCode) :=
  bind_components (branchParts d related).2.1
private theorem postFrame (d : Data) (post : PlainData) (context : post.context = .bind 10 postWriteCode)
    (related : Related graph (p28 d)) : PlainFrameRel graph clauseMaps [] (.bind 10 37 clauseEnv) post := by
  change FrameRel graph clauseMaps [] (.bind 10 37 clauseEnv) post.context
  rw [context]
  exact .bind (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 37 = .ok (ownedRaw 37))
    (bindParts d related).2 postReady

/-- The suffix frame is the one selected by source focus, rather than a fixed
annotation copied from the raw resume example. -/
theorem focusMapped (d : Data) (post : PlainData) (context : post.context = .bind 10 postWriteCode)
    (scope : post.scope = ticketScope) (related : Related graph (p28 d)) :
    Link graph (p31 d) (p32 d post) ∧ RawStep (selectedTarget d) (resumeTarget d post) [] [] := by
  have frame := postFrame d post context related
  have current := currentClause d related
  have after : Related graph (p32 d post) := ⟨rfl, _, ticketScope, .evaluate (fuel := 56) rfl (bindParts d related).1,
    pushed_mapped (.cons frame current.2)⟩
  have position : Focus yesCode resumeCode (.bind 10 postWriteCode) := by
    change Focus (.bind 10 resumeCode postWriteCode) resumeCode (.bind 10 postWriteCode)
    exact .bind (by simp [resumeCode, Code.IsValue])
  have focused := RawStep.focus post (context.symm ▸ position) (startTarget d).stack
  have step : RawStep (selectedTarget d) (resumeTarget d post) [] [] := by
    simpa only [scope, selectedTarget, resumeTarget] using focused
  exact ⟨.positive (branchPrefix d related).1.endpoints.2 rfl (.one step) after, step⟩

/-- Operand traversal does not consume the owner before the ready Unit value
returns. -/
theorem operandPrefix (d : Data) (post : PlainData) (context : post.context = .bind 10 postWriteCode)
    (_scope : post.scope = ticketScope) (related : Related graph (p28 d)) :
    Chain graph (p32 d post) [p33 d post, p34 d post] (p34 d post) := by
  have parts := bindParts d related
  have pushed := PushedWithMaps.cons (postFrame d post context related) (currentClause d related).2
  have traversal : SilentMapped graph clauseMaps clauseMaps (p32 d post).annotations (p33 d post).annotations
      CoreResumeEntry.Exported.s32 CoreResumeEntry.Exported.s33 (resumeTarget d post) :=
    resume_entry_same_target_mapped (base := CoreResumeEntry.Exported.s32) (environment := clauseEnv)
      (annotations := (p32 d post).annotations) ordered (rfl : graph.node 32 = some (node 32)) rfl
      (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 32 = .ok (ownedRaw 32)) parts.1
      (ValueRel.unit (graph := graph) (owners := clauseMaps) (heap := [])).closed resumePlain rfl pushed
  have frame : ResumeRel graph clauseMaps [] (.resume 0 0) resumePlain :=
    .operand (rfl : graph.node 32 = some (node 32)) rfl
      (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 32 = .ok (ownedRaw 32)) rfl
      (resume_components parts.1).2.2 rfl
  obtain ⟨witness, _translated⟩ := CoreAdministrativeSteps.unit_evaluate
    (base := CoreResumeEntry.Exported.s33) (rfl : graph.node 31 = some (node 31)) rfl
    (resume_components parts.1).2.1 CoreResumeEntry.Exported.s33.frames
  have stack := prepend_resume frame (ValueRel.unit (graph := graph) (owners := clauseMaps) (heap := [])).closed
    (pushed_mapped pushed) ticketScope
  exact .next (.traversal traversal) (.last (.value (value_entry_mapped witness rfl rfl stack)))

/-- Physical saved frames do not determine saved owner maps. Keep the current
relation's authenticated maps and their exact physical-frame equality. -/
private theorem ownerParts (d : Data) (related : Related graph (p28 d)) :
    ∃ saved : List MappedFrame, ∃ data : HandlerData,
      framesOf saved = framesOf capturedMaps ∧
      CoreRequestFrames.OwnerHeader graph [] [] 0 0 0 data ∧
      data.answer = d.handler.answer ∧ data.scope = d.handler.scope ∧
      PushedWithMaps graph [] saved (CoreAdmittedCapturePrefix.capturedTarget d.handler d.action d.focus) ∧
      PushedWithMaps graph [] outsideMaps (CoreAdmittedCapturePrefix.outsideTarget d.answer d.plain) := by
  have pushed := (currentClause d related).2
  change PushedWithMaps graph []
    (([], .clauseBoundary 0 0 0 0 (some (framesOf capturedMaps))) :: outsideMaps)
    (.live 0 d.input d.handler.answer (CoreAdmittedCapturePrefix.capturedTarget d.handler d.action d.focus)
      d.handler.scope (CoreAdmittedCapturePrefix.outsideTarget d.answer d.plain)) at pushed
  generalize mappingsEq :
    (([], CoreMachine.Frame.clauseBoundary 0 0 0 0 (some (framesOf capturedMaps))) :: outsideMaps) = mappings at pushed
  generalize stackEq :
    Stack.live 0 d.input d.handler.answer (CoreAdmittedCapturePrefix.capturedTarget d.handler d.action d.focus)
      d.handler.scope (CoreAdmittedCapturePrefix.outsideTarget d.answer d.plain) = target at pushed
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

/-- Resume restores every captured boundary, the source-selected caller front,
and the spent marker before the unchanged outside spine. -/
theorem consumeMapped (d : Data) (post : PlainData) (context : post.context = .bind 10 postWriteCode)
    (scope : post.scope = ticketScope) (related : Related graph (p28 d)) :
    ∃ saved : List MappedFrame,
      framesOf saved = framesOf capturedMaps ∧
      Link graph (p34 d post) (p35 d post saved) ∧
      RawStep (resumeTarget d post) (restoredTarget d post) [] [.ticket 0] := by
  obtain ⟨saved, data, framesEq, header, answerEq, scopeEq, captured, outside⟩ := ownerParts d related
  have cut : MappedOwnerCut graph [] 0 0 (p32 d post).annotations (resumeTarget d post).stack
      [(clauseMaps, .bind 10 37 clauseEnv)] (.push (.plain post) .nil) [] 0 0 data d.input
      saved (CoreAdmittedCapturePrefix.capturedTarget d.handler d.action d.focus) outsideMaps
      (CoreAdmittedCapturePrefix.outsideTarget d.answer d.plain) := by
    have hit := MappedOwnerCut.hit (result := d.input) (ticket := 0) header captured outside
    rw [framesEq, answerEq, scopeEq] at hit
    exact .push (.ordinary (postFrame d post context related)) hit
  have frame : ResumeRel graph clauseMaps [] (.resume 0 0) resumePlain :=
    .operand (rfl : graph.node 32 = some (node 32)) rfl
      (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 32 = .ok (ownedRaw 32)) rfl
      (resume_components (bindParts d related).1).2.2 rfl
  obtain ⟨_before, next, step, after⟩ := resume_complete_mapped (base := CoreResumeEntry.Exported.s34)
    cut frame (rfl : resumePlain.context = .resume (CoreTranslation.ticket graph 0)) .unit rfl ticketScope
  rw [answerEq, scopeEq] at step after
  have nextShape :
      { CoreResumeEntry.Exported.s34 with
        control := .returned .unit
        frames := framesOf saved ++ framesOf [(clauseMaps, .bind 10 37 clauseEnv)] ++
          .clauseBoundary 0 0 0 0 none :: framesOf outsideMaps
        observations := CoreResumeEntry.Exported.s34.observations ++ [.resumed 0] } =
      CoreResumeEntry.Exported.s35 := by
    rw [framesEq]
    rfl
  rw [nextShape] at next after
  exact ⟨saved, framesEq, .positive (operandPrefix d post context scope related).endpoints.2
    next (.one step) after, step⟩

private theorem appendLiveNeNil (front : Stack) :
    front.append (.live owner input answer captured caller tail) ≠ .nil := by
  cases front <;> simp [Stack.append]

private theorem appendLiveNeOutside (d : Data) (front : Stack) :
    front.append (.live owner input answer captured caller tail) ≠
      CoreAdmittedCapturePrefix.outsideTarget d.answer d.plain := by
  intro same
  change front.append (.live owner input answer captured caller tail) =
    .push (.plain d.plain) (.push (.cell 0 0 .none d.answer) .nil) at same
  cases front with
  | nil => cases same
  | live | spent => cases same
  | push frame rest =>
    have restEq := (Stack.push.inj same).2
    cases rest with
    | nil => cases restEq
    | live | spent => cases restEq
    | push next suffix => exact appendLiveNeNil suffix (Stack.push.inj restEq).2

private theorem resumeStack (d : Data) (post : PlainData)
    {front captured tail : Stack} {input answer : Ty} {caller : Scope}
    (same : (resumeTarget d post).stack = front.append (.live 0 input answer captured caller tail)) :
    captured.append (front.append (.spent 0 answer caller tail)) = (restoredTarget d post).stack := by
  change .push (.plain post) (.live 0 d.input d.handler.answer
    (CoreAdmittedCapturePrefix.capturedTarget d.handler d.action d.focus) d.handler.scope
    (CoreAdmittedCapturePrefix.outsideTarget d.answer d.plain)) =
      front.append (.live 0 input answer captured caller tail) at same
  cases front with
  | nil => cases same
  | live | spent => cases same
  | push frame rest =>
    obtain ⟨frameEq, restEq⟩ := Stack.push.inj same
    cases frameEq
    cases rest with
    | nil =>
      obtain ⟨_ownerEq, inputEq, answerEq, capturedEq, callerEq, tailEq⟩ := Stack.live.inj restEq
      cases answerEq
      cases capturedEq
      cases callerEq
      cases tailEq
      rfl
    | push | spent => cases restEq
    | live owner q a saved scope next =>
      have impossible := (Stack.live.inj restEq).2.2.2.2.2
      exact False.elim (appendLiveNeOutside d next impossible.symm)

private theorem rawResume (d : Data) (post : PlainData)
    (step : RawStep (resumeTarget d post) next created discharged) :
    next = restoredTarget d post ∧ created = [] ∧ discharged = [.ticket 0] := by
  generalize beforeEq : resumeTarget d post = before at step
  cases step with
  | resume binder owner runtimeScope caller input answer front captured tail value closed resolve =>
    obtain ⟨expressionEq, runtimeEq, stackEq⟩ := Configuration.mk.inj beforeEq
    have fields := Code.resume.inj expressionEq
    obtain ⟨binderEq, valueEq⟩ := fields
    cases binderEq
    cases valueEq
    cases runtimeEq
    have ownerEq : owner = 0 := by
      simpa [ticketScope, Execution.Scope.resolve] using resolve.symm
    cases ownerEq
    have restored := resumeStack d post stackEq
    exact ⟨by rw [restored]; rfl, rfl, rfl⟩
  | focus plain position stack =>
    obtain ⟨expressionEq, runtimeEq, stackEq⟩ := Configuration.mk.inj beforeEq
    rw [← expressionEq] at position
    generalize contextEq : plain.context = evaluationContext at position
    cases position with
    | resume notValue => exact False.elim (notValue trivial)
  | plug plain value closed runtimeScope tail =>
    have expressionEq : resumeCode = value := congrArg Configuration.expression beforeEq
    have impossible : resumeCode.IsValue := by rw [expressionEq]; exact closed.1
    exact False.elim impossible
  | leaveHandler handler value closed runtimeScope tail =>
    have expressionEq : resumeCode = value := congrArg Configuration.expression beforeEq
    have impossible : resumeCode.IsValue := by rw [expressionEq]; exact closed.1
    exact False.elim impossible
  | leaveCell identity payload answer caller runtimeScope value closed tail =>
    have expressionEq : resumeCode = value := congrArg Configuration.expression beforeEq
    have impossible : resumeCode.IsValue := by rw [expressionEq]; exact closed.1
    exact False.elim impossible
  | startCleanup action value closed runtimeScope tail =>
    have expressionEq : resumeCode = value := congrArg Configuration.expression beforeEq
    have impossible : resumeCode.IsValue := by rw [expressionEq]; exact closed.1
    exact False.elim impossible
  | leaveClause ticket answer value closed runtimeScope caller tail =>
    have expressionEq : resumeCode = value := congrArg Configuration.expression beforeEq
    have impossible : resumeCode.IsValue := by rw [expressionEq]; exact closed.1
    exact False.elim impossible
  | bind | beta | ifTrue | ifFalse | enterHandler | enterCell | readCell | writeCell | enterCleanup |
      finishCleanup | capture | discard | finishClose | retire => cases beforeEq

/-- The current lexical event determines the consumed owner and full successor
stack; its existence alone is not used as a validity transport. -/
private theorem eventResume (d : Data) (post : PlainData)
    (event : LexicalUnwind.Event
      ⟨.eval (resumeTarget d post), issued, completed⟩ after) :
    after.machine = .eval (restoredTarget d post) ∧ after.issued = issued ∧
      after.completed = .ticket 0 :: completed := by
  cases event with
  | step transition fresh =>
    cases transition with
    | evaluate step allowed =>
      obtain ⟨rfl, rfl, rfl⟩ := rawResume d post step
      exact ⟨rfl, by simp, rfl⟩

def priorPoints (d : Data) : List Point :=
  CoreAdmittedCapturePrefix.priorPoints d.answer d.plain d.handler d.action ++
    CoreAdmittedCapturePrefix.extensionPoints d.answer d.plain d.handler d.action d.focus d.input
def extensionPoints (d : Data) (post : PlainData) (saved : List MappedFrame) : List Point :=
  [p29 d, p30 d, p31 d, p32 d post, p33 d post, p34 d post, p35 d post saved]

/-- Admission and simulation of the same actual Core execution through its
first resume. The continuation's full capture is restored, ticket zero is
consumed, and all current source-selected ports and action data are retained. -/
theorem admittedResumePrefix (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ (d : Data) (allocated : SourcePlannedTyping.Contract) (captured : Snapshot operations)
      (post : PlainData) (saved : List MappedFrame) (final : Snapshot operations),
      allocated.resumeRow = resumeRow ∧ allocated.closeRow = closeRow ∧
      d.input = ScopedPorts.embedPort allocated.input.erase.erase.port ∧
      post.context = .bind 10 postWriteCode ∧ post.scope = ticketScope ∧
      framesOf saved = framesOf capturedMaps ∧
      CoreAdmittedPrefix.Admitted captured ∧ captured.run.execution.machine = .eval (p28 d).target ∧
      Chain graph p0 (priorPoints d ++ extensionPoints d post saved) (p35 d post saved) ∧
      RawTrace (CoreAdmittedPrefix.initial tables families required).run.execution 16 final.run.execution ∧
      CoreAdmittedPrefix.Admitted final ∧
      (∀ point ∈ p0 :: (priorPoints d ++ extensionPoints d post saved),
        Related graph point ∧ ∃ snapshot : Snapshot operations,
          CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = .eval point.target) ∧
      final.world = [0] ∧ final.history = [0] ∧
      final.run.execution.issued = [.resource 0, .cleanup 0, .ticket 0] ∧
      final.run.execution.completed = [.ticket 0] ∧
      final.resumes = RecursiveTransport.removeOwner 0 captured.resumes ∧
      final.disposals = RecursiveTransport.removeOwner 0 captured.disposals ∧
      final.annotatedStore = RecursiveTransport.removeOwner 0 captured.annotatedStore ∧
      final.run.tickets = captured.run.tickets ∧
      final.run.execution.machine = .eval (p35 d post saved).target := by
  obtain ⟨answer, plain, handler, action, focus, allocated, captured,
    resumeEq, closeEq, _focusContext, _focusScope, _handlerIdentity, _handlerArms,
    earlier, trace, capturedValid, allEarlier, world, history, issued, completed, _rights, machine⟩ :=
    CoreAdmittedCapturePrefix.admittedCapturePrefix tables families required resumeRow closeRow
  let d : Data := ⟨answer, plain, handler, action, focus, ScopedPorts.embedPort allocated.input.erase.erase.port⟩
  have current : Related graph (p28 d) := earlier.endpoints.2
  let ready := CoreAdmittedHandlerPrefix.reconfigure captured (startTarget d)
  let selected := CoreAdmittedHandlerPrefix.reconfigure captured (selectedTarget d)
  have readyEq : ready = captured := by
    dsimp only [ready, CoreAdmittedHandlerPrefix.reconfigure]
    change captured.run.execution.machine = .eval (startTarget d) at machine
    rw [← machine]
  have readyValid : CoreAdmittedPrefix.Admitted ready := by rw [readyEq]; exact capturedValid
  have isReady : RecursiveExpressions.Ready (startTarget d).expression := by
    change RecursiveExpressions.Ready (.branch (.boolean true) yesCode noCode)
    exact .branch
  have branchStep : Stable.Step operations ready selected :=
    .computation (snapshot := captured) (issued := captured.run.execution.issued)
      (completed := captured.run.execution.completed) (actions := captured.run.tickets)
      isReady (branchPrefix d current).2
  obtain ⟨branchEvent, selectedValid⟩ := branchStep.preserve readyValid
  have actualBranchEvent : LexicalUnwind.Event captured.run.execution selected.run.execution := by
    simpa only [readyEq] using branchEvent
  have position : Focus yesCode resumeCode (.bind 10 postWriteCode) := by
    change Focus (.bind 10 resumeCode postWriteCode) resumeCode (.bind 10 postWriteCode)
    exact .bind (by simp [resumeCode, Code.IsValue])
  let focusRequest : Allocating.Request selected :=
    .focus (whole := yesCode) (runtimeScope := ticketScope) (stack := (startTarget d).stack)
      (issued := captured.run.execution.issued) (completed := captured.run.execution.completed)
      (actions := captured.run.tickets) rfl position
  obtain ⟨afterFocus, focusEvent, realization, focusedValid⟩ := focusRequest.preserve selectedValid
  dsimp [focusRequest] at realization
  cases realization with
  | focus post context scope =>
    let pending := CoreAdmittedHandlerPrefix.reconfigure captured (resumeTarget d post)
    have pendingValid : CoreAdmittedPrefix.Admitted pending := focusedValid
    have actualFocusEvent : LexicalUnwind.Event selected.run.execution pending.run.execution := by
      change LexicalUnwind.Event selected.run.execution
        ⟨.eval (resumeTarget d post), captured.run.execution.issued, captured.run.execution.completed⟩
      simpa only [resumeTarget] using focusEvent
    let resumeRequest : Allocating.Request pending :=
      .resume (binder := CoreTranslation.ticket graph 0) (operand := .unit)
        (runtimeScope := ticketScope) (stack := (resumeTarget d post).stack)
        (issued := captured.run.execution.issued) (completed := captured.run.execution.completed)
        (actions := captured.run.tickets) rfl
        (ValueRel.unit (graph := graph) (owners := clauseMaps) (heap := [])).closed
    obtain ⟨afterResume, resumeEvent, resumed, resumedValid⟩ := resumeRequest.preserve pendingValid
    dsimp [resumeRequest] at resumed
    cases resumed with
    | resume owner nextStack =>
      have determined := eventResume d post resumeEvent
      have ownerEq : owner = 0 := Owner.ticket.inj (List.cons.inj determined.2.2).1
      cases ownerEq
      have stackEq : nextStack = (restoredTarget d post).stack :=
        congrArg Configuration.stack (LexicalUnwind.Machine.eval.inj determined.1)
      cases stackEq
      let final : Snapshot operations :=
        { captured with
          resumes := RecursiveTransport.removeOwner 0 captured.resumes
          disposals := RecursiveTransport.removeOwner 0 captured.disposals
          annotatedStore := RecursiveTransport.removeOwner 0 captured.annotatedStore
          run := ⟨⟨.eval (restoredTarget d post), captured.run.execution.issued,
            .ticket 0 :: captured.run.execution.completed⟩, captured.run.tickets⟩ }
      have finalValid : CoreAdmittedPrefix.Admitted final := resumedValid
      obtain ⟨saved, framesEq, linked, _raw⟩ := consumeMapped d post context scope current
      have suffixChain : Chain graph (p28 d) (extensionPoints d post saved) (p35 d post saved) :=
        CoreHandlerPrefix.chain_append (branchPrefix d current).1
          (.next (focusMapped d post context scope current).1
            (CoreHandlerPrefix.chain_append (operandPrefix d post context scope current) (.last linked)))
      have chain := CoreHandlerPrefix.chain_append earlier suffixChain
      have extensionValid : ∀ point ∈ extensionPoints d post saved,
          ∃ snapshot : Snapshot operations, CoreAdmittedPrefix.Admitted snapshot ∧
            snapshot.run.execution.machine = .eval point.target := by
        intro point member
        simp only [extensionPoints, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨captured, capturedValid, machine⟩
        · exact ⟨captured, capturedValid, machine⟩
        · exact ⟨selected, selectedValid, rfl⟩
        · exact ⟨pending, pendingValid, rfl⟩
        · exact ⟨pending, pendingValid, rfl⟩
        · exact ⟨pending, pendingValid, rfl⟩
        · exact ⟨final, finalValid, rfl⟩
      refine ⟨d, allocated, captured, post, saved, final, resumeEq, closeEq, rfl,
        context, scope, framesEq, capturedValid, machine, chain,
        .step (.step (.step trace actualBranchEvent) actualFocusEvent) resumeEvent,
        finalValid, ?_, world, history, issued, ?_, rfl, rfl, rfl, rfl, rfl⟩
      · intro point member
        rcases List.mem_cons.mp member with equal | later
        · subst point
          exact allEarlier p0 List.mem_cons_self
        · refine ⟨chain.every_point_related point later, ?_⟩
          rcases List.mem_append.mp later with prior | extension
          · exact (allEarlier point (List.mem_cons_of_mem _ prior)).2
          · exact extensionValid point extension
      · change .ticket 0 :: captured.run.execution.completed = _
        rw [completed]

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedResumePrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedResumePrefix.branchPrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedResumePrefix.focusMapped
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedResumePrefix.operandPrefix

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedResumePrefix.consumeMapped

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedResumePrefix.admittedResumePrefix
