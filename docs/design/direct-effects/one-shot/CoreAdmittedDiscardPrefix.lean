import CoreAdmittedSecondCapturePrefix
import CoreDiscardPrefix

/-! The same admitted second capture enters lexical discard. Captured owner
maps remain authenticated by the current relation; Core projects the retained
lexical capture to its cleanup vector. The endpoint precedes callback execution. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedDiscardPrefix
open ScopedExpressions ScopedExecution ProtectionContracts
open InstallationSupport InstallationSupport.Preservation CoreInitialExample
open CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential
open CoreOrdinaryCompletion CoreAdministrativeTransport CoreInitialPrefix CoreExportedFixture
open CoreEffectFrames CoreRequestFrames CoreResumeFrames CoreCaptureEntry CoreResumeEntry
open CoreHandlerPrefix (raw methodsEnv)
open CoreCleanupEntry (callbackEnv)
open CoreCaptureEntry.Exported (outsideMaps)
open CoreAdmittedResumePrefix (Data)
open CoreAdmittedSecondCapturePrefix (Maps captured capturedTarget outside outsideTarget clauseTarget p40)
open CoreDiscardPrefix (falseEnv falseScope s41 s42 s43 s44 s45)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0,.unit,[],none,.unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl

def owners (m : Maps) : CoreTranslation.OwnerMap := ⟨0,0,CoreTranslation.ticket graph 0⟩ :: m.handlerOwner
def startTarget (d : Data) (post second : PlainData) (input : Ty) : Configuration := clauseTarget d post second input
def discardTarget (d : Data) (post second : PlainData) (input : Ty) : Configuration :=
  ⟨.discard (CoreTranslation.ticket graph 0),falseScope,(startTarget d post second input).stack⟩
def p41 (d : Data) (post second : PlainData) (m : Maps) (input : Ty) : CoreInitialPrefix.Point :=
  ⟨s41,startTarget d post second input,owners m,
    (owners m,.matchCases (CoreStrictSteps.booleanArms 38 39 false) falseEnv) :: (p40 d post second m input).annotations⟩
def p42 (d : Data) (post second : PlainData) (m : Maps) (input : Ty) : CoreInitialPrefix.Point :=
  ⟨s42,startTarget d post second input,owners m,(p41 d post second m input).annotations⟩
def p43 (d : Data) (post second : PlainData) (m : Maps) (input : Ty) : CoreInitialPrefix.Point :=
  ⟨s43,discardTarget d post second input,owners m,(p40 d post second m input).annotations⟩
def p44 (d : Data) (post second : PlainData) (m : Maps) (input : Ty) : CoreUnwindRelation.Point :=
  ⟨s44,.eval (discardTarget d post second input),owners m,(p40 d post second m input).annotations⟩
def unwindStack (d : Data) (post second : PlainData) : Stack :=
  (capturedTarget d second).append (.push (.closing 0 falseScope)
    (.spent 1 d.handler.answer d.handler.scope (outsideTarget d post)))
def p45 (d : Data) (post second : PlainData) (m : Maps) : CoreUnwindRelation.Point :=
  ⟨s45,.unwind falseScope (unwindStack d post second),owners m,
    (m.handlerOwner,.clauseBoundary 0 0 0 1 none) :: outside post⟩

private theorem translation_unique {owners : CoreTranslation.OwnerMap} {rawCode otherRaw : Code}
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok rawCode)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok otherRaw) : rawCode = otherRaw := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index rawCode (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index otherRaw (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

private theorem currentClause (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (related : CoreInitialPrefix.Related graph (p40 d post second m input)) :
    EnvCloses graph (owners m) [] falseEnv
      ((CoreTranslation.translateFuel graph 56 (owners m) 40).toOption.getD .unit)
      (startTarget d post second input).expression ∧
    PushedWithMaps graph [] (p40 d post second m input).annotations (startTarget d post second input).stack := by
  obtain ⟨_shape,code,scope,control,stack⟩ := related
  change OrdinaryWithMaps graph []
    ((m.handlerOwner,.clauseBoundary 0 0 0 1 (some (framesOf (captured m)) )) :: outside post)
    code scope (startTarget d post second input).expression falseScope (startTarget d post second input).stack at stack
  obtain ⟨rfl,rfl,pushed⟩ := CoreAdmittedResumePrefix.owner_head_pushed stack
  cases control with
  | evaluate translated saved =>
    have same := translation_unique translated
      (rfl : CoreTranslation.translateFuel graph 56 (owners m) 40 = .ok
        (.branch (.variable 9) (.bind 10 (.resume (CoreTranslation.ticket graph 0) .unit)
          (.app (.variable 3) (.pair (.variable 4) (.integer 11)))) (.discard (CoreTranslation.ticket graph 0))))
    cases same
    exact ⟨saved,pushed⟩

def rawYes : Code := .bind 10 (.resume (CoreTranslation.ticket graph 0) .unit) (.app (.variable 3) (.pair (.variable 4) (.integer 11)))
def yesCode : Code := CoreDiscardPrefix.falseYes
def noCode : Code := .discard (CoreTranslation.ticket graph 0)
def branchPlain : PlainData := ⟨.branch yesCode noCode,falseScope,.boolean,.unit,
  (falseScope.translate (.branch yesCode noCode : ScopedExecution.Context).dependencies).getD [],by decide⟩
private theorem branchParts (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (related : CoreInitialPrefix.Related graph (p40 d post second m input)) :
    EnvCloses graph (owners m) [] falseEnv (.variable 9) (.boolean false) ∧
    EnvCloses graph (owners m) [] falseEnv rawYes yesCode ∧
    EnvCloses graph (owners m) [] falseEnv noCode noCode :=
  branch_components (currentClause d post second m input related).1

/-- Finite branch traversal retains the same current source-selected capture. -/
theorem branchPrefix (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (related : CoreInitialPrefix.Related graph (p40 d post second m input)) :
    CoreInitialPrefix.Chain graph (p40 d post second m input)
      [p41 d post second m input,p42 d post second m input,p43 d post second m input]
      (p43 d post second m input) ∧
    RawStep (startTarget d post second input) (discardTarget d post second input) [] [] := by
  have current := currentClause d post second m input related
  have parts := branchParts d post second m input related
  have traversal : SilentMapped graph (owners m) (owners m) (p40 d post second m input).annotations
      (p41 d post second m input).annotations CoreSecondCapture.s40 s41 (startTarget d post second input) :=
    boolean_entry_same_target (base := CoreSecondCapture.s40) (environment := falseEnv)
    (scrutineeCode := .boolean false) (yesCode := yesCode) (noCode := noCode)
    (annotations := (p40 d post second m input).annotations) ordered
    (rfl : graph.node 40 = some (node 40)) rfl
    (rfl : CoreTranslation.translateFuel graph 56 (owners m) 30 = .ok (.variable 9))
    (rfl : CoreTranslation.translateFuel graph 56 (owners m) 38 = .ok rawYes)
    (rfl : CoreTranslation.translateFuel graph 56 (owners m) 39 = .ok noCode)
    current.1 parts.1 parts.2.1 parts.2.2
    (ValueRel.boolean (graph := graph) (owners := owners m) (heap := []) (value := false)).closed branchPlain rfl current.2
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := s41)
    (rfl : graph.node 30 = some (node 30)) rfl parts.1
    (ValueRel.boolean (graph := graph) (owners := owners m) (heap := []) (value := false)).closed s41.frames
  have valueEq : value = .boolean false := Option.some.inj (lookup.symm.trans rfl)
  cases valueEq
  have frame : PlainFrameRel graph (owners m) []
      (.matchCases (CoreStrictSteps.booleanArms 38 39 false) falseEnv) branchPlain :=
    .booleanMatch (rfl : CoreTranslation.translateFuel graph 56 (owners m) 38 = .ok rawYes)
      (rfl : CoreTranslation.translateFuel graph 56 (owners m) 39 = .ok noCode) parts.2.1 parts.2.2
  have stack := prepend_mapped frame
    (ValueRel.boolean (graph := graph) (owners := owners m) (heap := []) (value := false)).closed
    (pushed_mapped current.2) falseScope
  have condition := value_entry_mapped witness rfl rfl stack
  obtain ⟨before,next,step,after⟩ := boolean_complete_mapped (base := s42)
    (rfl : CoreTranslation.translateFuel graph 56 (owners m) 38 = .ok rawYes)
    (rfl : CoreTranslation.translateFuel graph 56 (owners m) 39 = .ok noCode) parts.2.1 parts.2.2
    false false branchPlain rfl current.2 (owners m) falseScope
  exact ⟨.next (.traversal traversal) (.next (.value condition)
    (.last (.positive condition.successor next (.one step) after))),step⟩

private theorem ownerParts (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (related : CoreInitialPrefix.Related graph (p40 d post second m input)) :
    ∃ saved : List MappedFrame, ∃ data : HandlerData,
      framesOf saved = framesOf (captured m) ∧
      CoreRequestFrames.OwnerHeader graph m.handlerOwner [] 0 0 0 data ∧
      data.answer = d.handler.answer ∧ data.scope = d.handler.scope ∧
      PushedWithMaps graph [] saved (capturedTarget d second) ∧
      PushedWithMaps graph [] (outside post) (outsideTarget d post) := by
  have pushed := (currentClause d post second m input related).2
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


private theorem carrier (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (related : CoreInitialPrefix.Related graph (p40 d post second m input)) :
    CoreUnwindRelation.DiscardCarrier graph (owners m) [] falseEnv 0 0 (CoreTranslation.ticket graph 0) :=
  .site (rfl : graph.node 39 = some (node 39)) rfl rfl (branchParts d post second m input related).2.2

private theorem entry_decreases : potential graph s44 < potential graph s43 := by
  have cost := cost_recurrence ordered (rfl : graph.node 39 = some (node 39))
  simp only [CoreSyntax.Kind.children,List.map_nil,List.sum_nil] at cost
  simp only [potential,s44,s43]
  omega

/-- Current source-selected ports and authenticated saved maps survive discard.
Only the physical close vector drops non-cleanup captured frames. -/
theorem discardMapped (d : Data) (post second : PlainData) (m : Maps) (input : Ty)
    (related : CoreInitialPrefix.Related graph (p40 d post second m input)) :
    CoreUnwindRelation.Link graph (CoreUnwindRelation.lift (p43 d post second m input)) (p44 d post second m input) ∧
    CoreUnwindRelation.Link graph (p44 d post second m input) (p45 d post second m) ∧
    LexicalUnwind.Transition (.eval (discardTarget d post second input))
      (.unwind falseScope (unwindStack d post second)) [.close 0] [.ticket 1] := by
  obtain ⟨saved,data,framesEq,header,answerEq,scopeEq,savedPushed,outsidePushed⟩ := ownerParts d post second m input related
  have cut : MappedOwnerCut graph [] 0 0 (p40 d post second m input).annotations
      (discardTarget d post second input).stack [] .nil m.handlerOwner 0 1 data input
      saved (capturedTarget d second) (outside post) (outsideTarget d post) := by
    have hit := MappedOwnerCut.hit (result := input) (ticket := 1) header savedPushed outsidePushed
    rw [framesEq,answerEq,scopeEq] at hit
    exact hit
  have closeProjection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf saved) + 1)
      (framesOf saved) = .ok ([.cleanupBoundary 27 callbackEnv 0],[]) := by
    rw [framesEq]
    rfl
  obtain ⟨after,before,next,step,afterRelated⟩ := CoreUnwindRelation.discard_projected (base := s44)
    cut (carrier d post second m input related)
    (rfl : falseScope.resolve (CoreTranslation.ticket graph 0) = some 1)
    (rfl : ProtectionContexts.protectedMode (capturedTarget d second).erase = false) closeProjection rfl
  have same : after = s45 := CoreMachine.Outcome.stepped.inj (next.symm.trans rfl)
  cases same
  rw [answerEq,scopeEq] at step afterRelated
  have selected := branchPrefix d post second m input related
  have selectedRelated := selected.1.endpoints.2
  exact ⟨.discardEntry (.eval selectedRelated) before rfl rfl
    ⟨39,falseEnv,0,0,rfl,rfl⟩ entry_decreases,
    .positive before next (.one step) afterRelated,step⟩


private theorem appendLiveNeOutside (d : Data) (post : PlainData) (front : Stack) {input answer : Ty} {captured tail : Stack} {caller : Scope} :
    front.append (.live 1 input answer captured caller tail) ≠ outsideTarget d post := by
  intro same
  have member : 1 ∈ ScopedExecution.ownedTickets (front.append (.live 1 input answer captured caller tail)) := by
    rw [ScopedExecution.owned_tickets_append]
    simp [ScopedExecution.ownedTickets]
  rw [same] at member
  simp [outsideTarget,CoreAdmittedCapturePrefix.outsideTarget,ScopedExecution.ownedTickets] at member

private theorem discardStack (d : Data) (post second : PlainData) (input : Ty)
    {front captured tail : Stack} {q answer : Ty} {caller : Scope}
    (same : (discardTarget d post second input).stack = front.append (.live 1 q answer captured caller tail)) :
    captured.append (.push (.closing 0 falseScope) (front.append (.spent 1 answer caller tail))) =
      unwindStack d post second := by
  change .live 1 input d.handler.answer (capturedTarget d second) d.handler.scope (outsideTarget d post) =
    front.append (.live 1 q answer captured caller tail) at same
  cases front with
  | nil =>
    obtain ⟨_,_,answerEq,capturedEq,callerEq,tailEq⟩ := Stack.live.inj same
    cases answerEq; cases capturedEq; cases callerEq; cases tailEq
    rfl
  | push | spent => cases same
  | live owner q' a saved scope next =>
    exact False.elim (appendLiveNeOutside d post next ((Stack.live.inj same).2.2.2.2.2).symm)

/-- Event inversion selects owner one and the exact retained lexical unwind.
The issued equality comes from the current discard request's chosen identity. -/
private theorem eventDiscard (d : Data) (post second : PlainData) (input : Ty)
    (event : LexicalUnwind.Event ⟨.eval (discardTarget d post second input),issued,completed⟩ after)
    (identity : after.issued = issued ++ [.close 0]) :
    after.machine = .unwind falseScope (unwindStack d post second) ∧
      after.completed = .ticket 1 :: completed := by
  cases event with
  | step transition fresh =>
    generalize machineEq : LexicalUnwind.Machine.eval (discardTarget d post second input) = machine at transition
    cases transition with
    | discard binder owner close scope caller q answer front captured tail resolve unprotected =>
      obtain ⟨expressionEq,scopeEq,stackEq⟩ := Configuration.mk.inj (LexicalUnwind.Machine.eval.inj machineEq)
      have binderEq := Code.discard.inj expressionEq
      cases binderEq; cases scopeEq
      have ownerEq : owner = 1 := by simpa [falseScope,Execution.Scope.resolve] using resolve.symm
      cases ownerEq
      have closeEq : close = 0 := by
        have same := List.append_cancel_left identity
        exact Owner.close.inj (List.cons.inj same).1
      cases closeEq
      have same := discardStack d post second input stackEq
      exact ⟨by rw [same],rfl⟩
    | evaluate step allowed =>
      have codeEq := congrArg Configuration.expression (LexicalUnwind.Machine.eval.inj machineEq)
      rw [← codeEq] at allowed
      exact False.elim allowed
    | finishCleanup | retireValue | closeValue => cases machineEq
    | advance | startCleanup | finishClose => cases machineEq

private theorem everyPoint (chain : CoreUnwindRelation.Chain graph before points after) :
    ∀ point ∈ before :: points, CoreUnwindRelation.Related graph point := by
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


def priorPoints (d : Data) (post second : PlainData) (m : Maps) (input : Ty) : List CoreUnwindRelation.Point :=
  (CoreAdmittedSecondCapturePrefix.priorPoints d post m ++
    CoreAdmittedSecondCapturePrefix.extensionPoints d post second m input).map CoreUnwindRelation.lift

def extensionPoints (d : Data) (post second : PlainData) (m : Maps) (input : Ty) : List CoreUnwindRelation.Point :=
  [CoreUnwindRelation.lift (p41 d post second m input),CoreUnwindRelation.lift (p42 d post second m input),
    CoreUnwindRelation.lift (p43 d post second m input),p44 d post second m input,p45 d post second m]

/-- The actual admitted exported execution reaches the same physical s45.
Source-selected ports, frames and action are retained; the current source
request allocates close zero and consumes ticket one without executing cleanup. -/
theorem admittedDiscardPrefix (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (firstResumeRow : Footprint) (firstCloseRow : Option Footprint)
    (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ (d : Data) (post : PlainData) (m : Maps) (second : PlainData)
      (firstAllocated allocated : SourcePlannedTyping.Contract) (captured selected final : Snapshot operations),
      firstAllocated.resumeRow = firstResumeRow ∧ firstAllocated.closeRow = firstCloseRow ∧
      allocated.resumeRow = resumeRow ∧ allocated.closeRow = closeRow ∧
      d.input = ScopedPorts.embedPort firstAllocated.input.erase.erase.port ∧
      d.focus.context = .bind 7 CoreAdmittedCapturePrefix.suffix ∧ d.focus.scope = .none ∧
      d.handler.activation = 0 ∧ d.handler.clauses = CoreHandlerPrefix.clauses ∧
      post.context = .bind 10 CoreResumeEntry.Exported.postWriteCode ∧ post.scope = CoreResumeEntry.Exported.ticketScope ∧
      second.context = .bind 6 CoreSecondCapture.setterCode ∧ second.scope = .none ∧
      CoreAdmittedPrefix.Admitted captured ∧ captured.run.execution.machine = .eval
        (p40 d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port)).target ∧
      CoreAdmittedPrefix.Admitted selected ∧ selected.run.execution.machine = .eval
        (discardTarget d post second (ScopedPorts.embedPort allocated.input.erase.erase.port)) ∧
      CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift p0)
        (priorPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port) ++
          extensionPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port)) (p45 d post second m) ∧
      CoreAllocationHistory.Steps graph 45 (CoreMachine.initial graph) s45 ∧
      RawTrace (CoreAdmittedPrefix.initial tables families required).run.execution 22 final.run.execution ∧
      CoreAdmittedPrefix.Admitted final ∧
      (∀ point ∈ CoreUnwindRelation.lift p0 ::
          (priorPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port) ++
            extensionPoints d post second m (ScopedPorts.embedPort allocated.input.erase.erase.port)),
        CoreUnwindRelation.Related graph point ∧ ∃ snapshot : Snapshot operations,
          CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = point.machine) ∧
      final.world = [0] ∧ final.history = [0] ∧
      final.run.execution.issued = [.resource 0,.cleanup 0,.ticket 0,.ticket 1,.close 0] ∧
      final.run.execution.completed = [.ticket 1,.ticket 0] ∧
      final.resumes = RecursiveTransport.removeOwner 1 captured.resumes ∧
      final.disposals = RecursiveTransport.removeOwner 1 captured.disposals ∧
      final.annotatedStore = RecursiveTransport.removeOwner 1 captured.annotatedStore ∧
      final.run.tickets = captured.run.tickets ∧
      final.run.execution.machine = (p45 d post second m).machine := by
  obtain ⟨d,post,m,second,firstAllocated,allocated,previous,bound,captured,
    firstResumeEq,firstCloseEq,resumeEq,closeEq,inputEq,focusContext,focusScope,handlerIdentity,handlerArms,
    postContext,postScope,secondContext,secondScope,_previousValid,_previousMachine,_boundValid,_boundMachine,
    earlier,trace,capturedValid,allEarlier,world,history,issued,completed,_tickets,machine⟩ :=
    CoreAdmittedSecondCapturePrefix.admittedSecondCapturePrefix tables families required
      firstResumeRow firstCloseRow resumeRow closeRow
  let input := ScopedPorts.embedPort allocated.input.erase.erase.port
  have current : CoreInitialPrefix.Related graph (p40 d post second m input) := earlier.endpoints.2
  have branch := branchPrefix d post second m input current
  let ready := CoreAdmittedHandlerPrefix.reconfigure captured (startTarget d post second input)
  let selected := CoreAdmittedHandlerPrefix.reconfigure captured (discardTarget d post second input)
  have readyEq : ready = captured := by
    dsimp only [ready,CoreAdmittedHandlerPrefix.reconfigure]
    change captured.run.execution.machine = .eval (startTarget d post second input) at machine
    rw [← machine]
  have readyValid : CoreAdmittedPrefix.Admitted ready := by rw [readyEq]; exact capturedValid
  have isReady : RecursiveExpressions.Ready (startTarget d post second input).expression := by
    change RecursiveExpressions.Ready (.branch (.boolean false) yesCode noCode)
    exact .branch
  have branchStep : Stable.Step operations ready selected :=
    .computation (snapshot := captured) (issued := captured.run.execution.issued)
      (completed := captured.run.execution.completed) (actions := captured.run.tickets) isReady branch.2
  obtain ⟨branchEvent,selectedValid⟩ := branchStep.preserve readyValid
  have actualBranchEvent : LexicalUnwind.Event captured.run.execution selected.run.execution := by
    simpa only [readyEq] using branchEvent
  let discardRequest : Allocating.Request selected :=
    .discard (binder := CoreTranslation.ticket graph 0) (runtimeScope := falseScope)
      (stack := (discardTarget d post second input).stack)
      (issued := captured.run.execution.issued) (completed := captured.run.execution.completed)
      (actions := captured.run.tickets) rfl 0 (by rw [issued]; decide)
  obtain ⟨afterDiscard,discardEvent,realization,discardedValid⟩ := discardRequest.preserve selectedValid
  dsimp [discardRequest] at realization
  cases realization with
  | discard owner nextStack =>
    have determined := eventDiscard d post second input discardEvent rfl
    have ownerEq : owner = 1 := Owner.ticket.inj (List.cons.inj determined.2).1
    cases ownerEq
    have stackEq : nextStack = unwindStack d post second := (LexicalUnwind.Machine.unwind.inj determined.1).2
    cases stackEq
    let final : Snapshot operations :=
      { captured with
        resumes := RecursiveTransport.removeOwner 1 captured.resumes
        disposals := RecursiveTransport.removeOwner 1 captured.disposals
        annotatedStore := RecursiveTransport.removeOwner 1 captured.annotatedStore
        run := ⟨⟨.unwind falseScope (unwindStack d post second),
          captured.run.execution.issued ++ [.close 0], .ticket 1 :: captured.run.execution.completed⟩,
          captured.run.tickets⟩ }
    have finalValid : CoreAdmittedPrefix.Admitted final := discardedValid
    have actualDiscardEvent : LexicalUnwind.Event selected.run.execution final.run.execution := discardEvent
    have mapped := discardMapped d post second m input current
    have extensionChain : CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift (p40 d post second m input))
        (extensionPoints d post second m input) (p45 d post second m) :=
      CoreUnwindRelation.chain_append (CoreUnwindRelation.chain_lift branch.1)
        (.next mapped.1 (.last mapped.2.1))
    have chain : CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift p0)
        (priorPoints d post second m input ++ extensionPoints d post second m input) (p45 d post second m) :=
      CoreUnwindRelation.chain_append (CoreUnwindRelation.chain_lift earlier) extensionChain
    have coreSteps : CoreAllocationHistory.Steps graph 45 (CoreMachine.initial graph) s45 := by
      have steps := chain.core_steps
      have length : (priorPoints d post second m input ++ extensionPoints d post second m input).length = 45 := rfl
      rw [length] at steps
      exact steps
    have extensionValid : ∀ point ∈ extensionPoints d post second m input,
        ∃ snapshot : Snapshot operations,CoreAdmittedPrefix.Admitted snapshot ∧ snapshot.run.execution.machine = point.machine := by
      intro point member
      simp only [extensionPoints,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact ⟨captured,capturedValid,machine⟩
      · exact ⟨captured,capturedValid,machine⟩
      · exact ⟨selected,selectedValid,rfl⟩
      · exact ⟨selected,selectedValid,rfl⟩
      · exact ⟨final,finalValid,rfl⟩
    refine ⟨d,post,m,second,firstAllocated,allocated,captured,selected,final,
      firstResumeEq,firstCloseEq,resumeEq,closeEq,inputEq,focusContext,focusScope,handlerIdentity,handlerArms,
      postContext,postScope,secondContext,secondScope,capturedValid,machine,selectedValid,rfl,
      chain,coreSteps,.step (.step trace actualBranchEvent) actualDiscardEvent,finalValid,?_,world,history,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
    · intro point member
      refine ⟨everyPoint chain point member,?_⟩
      rcases List.mem_cons.mp member with equal | later
      · subst point
        exact (allEarlier p0 List.mem_cons_self).2
      · rcases List.mem_append.mp later with prior | extension
        · rcases List.mem_map.mp prior with ⟨old,inOld,rfl⟩
          exact (allEarlier old (List.mem_cons_of_mem _ inOld)).2
        · exact extensionValid point extension
    · change captured.run.execution.issued ++ [.close 0] = _
      rw [issued]
      rfl
    · change .ticket 1 :: captured.run.execution.completed = _
      rw [completed]


end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedDiscardPrefix

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedDiscardPrefix.branchPrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedDiscardPrefix.discardMapped
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedDiscardPrefix.admittedDiscardPrefix
