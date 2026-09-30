import CoreCaptureEntry
import CoreResumeFrames

/-! Exact live-owner cut and consuming resume. Supplied scope coherence and
annotation authentication remain explicit obligations. The captured prefix,
caller front, spent marker and outside spine retain their exact saved maps. -/
namespace Ash.OneShot.CoreResumeEntry
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreEffectFrames
  CoreRequestFrames CoreResumeFrames CoreStrictStack CoreStrictPotential CoreCaptureEntry

set_option linter.unusedSimpArgs false in
private theorem PushCarrier.owner_pass (frame : PushCarrier graph owners heap core target)
    (next : CoreMachine.findOwner handler owner rest = .ok cut) :
    CoreMachine.findOwner handler owner (core :: rest) = .ok { cut with inside := core :: cut.inside } := by
  cases frame with
  | ordinary related =>
      rename_i plain
      change FrameRel graph owners heap core plain.context at related
      generalize contextEq : plain.context = context at related
      cases related <;> simp [CoreMachine.findOwner,next,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | initializer related => cases related; simp [CoreMachine.findOwner,next,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | request related => cases related; simp [CoreMachine.findOwner,next,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | resume related => cases related; simp [CoreMachine.findOwner,next,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | cleanup related => cases related; simp [CoreMachine.findOwner,next,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | boundary related => cases related <;> simp [CoreMachine.findOwner,next,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Simultaneous static-owner cut. A spent matching owner has no success
constructor; different owners pass only their active outside spine. -/
inductive MappedOwnerCut (graph : CoreSyntax.Graph) (heap : Heap) (handler owner : Nat) :
    List MappedFrame → Stack → List MappedFrame → Stack → CoreTranslation.OwnerMap → Nat → Nat → HandlerData →
      Ty → List MappedFrame → Stack → List MappedFrame → Stack → Prop where
  | hit (header : OwnerHeader graph owners heap handler owner occurrence data)
      (captured : PushedWithMaps graph heap capturedMaps capturedTarget)
      (outside : PushedWithMaps graph heap outsideMaps outsideTarget) :
      MappedOwnerCut graph heap handler owner
        ((owners,.clauseBoundary handler owner occurrence ticket (some (framesOf capturedMaps))) :: outsideMaps)
        (.live ticket result data.answer capturedTarget data.scope outsideTarget)
        [] .nil owners occurrence ticket data result capturedMaps capturedTarget outsideMaps outsideTarget
  | push (frame : PushCarrier graph owners heap core targetFrame)
      (next : MappedOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
      MappedOwnerCut graph heap handler owner ((owners,core) :: whole) (.push targetFrame target)
        ((owners,core) :: front) (.push targetFrame frontTarget) savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget
  | live (header : OwnerHeader graph owners heap otherHandler otherOwner otherOccurrence oldData)
      (different : handler ≠ otherHandler ∨ owner ≠ otherOwner)
      (saved : PushedWithMaps graph heap savedMaps savedTarget)
      (next : MappedOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
      MappedOwnerCut graph heap handler owner
        ((owners,.clauseBoundary otherHandler otherOwner otherOccurrence oldTicket (some (framesOf savedMaps))) :: whole)
        (.live oldTicket oldResult oldData.answer savedTarget oldData.scope target)
        ((owners,.clauseBoundary otherHandler otherOwner otherOccurrence oldTicket (some (framesOf savedMaps))) :: front)
        (.live oldTicket oldResult oldData.answer savedTarget oldData.scope frontTarget)
        savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget
  | spent (header : OwnerHeader graph owners heap otherHandler otherOwner otherOccurrence oldData)
      (different : handler ≠ otherHandler ∨ owner ≠ otherOwner)
      (next : MappedOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
      MappedOwnerCut graph heap handler owner
        ((owners,.clauseBoundary otherHandler otherOwner otherOccurrence oldTicket none) :: whole)
        (.spent oldTicket oldData.answer oldData.scope target)
        ((owners,.clauseBoundary otherHandler otherOwner otherOccurrence oldTicket none) :: front)
        (.spent oldTicket oldData.answer oldData.scope frontTarget)
        savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget

set_option linter.unusedSimpArgs false in
theorem MappedOwnerCut.realizes
    (cut : MappedOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
    CoreMachine.findOwner handler owner (framesOf whole) =
      .ok ⟨framesOf front,handler,owner,occurrence,ticket,framesOf captured,framesOf outside⟩ ∧
    target = frontTarget.append (.live ticket result data.answer capturedTarget data.scope outsideTarget) ∧
    OwnerHeader graph savedOwners heap handler owner occurrence data ∧
    PushedWithMaps graph heap whole target ∧ PushedWithMaps graph heap front frontTarget ∧
    PushedWithMaps graph heap captured capturedTarget ∧ PushedWithMaps graph heap outside outsideTarget := by
  induction cut with
  | hit header captured outside =>
      exact ⟨by simp [framesOf_cons,CoreMachine.findOwner,framesOf],rfl,header,.live header captured outside,.nil,captured,outside⟩
  | push frame next ih =>
      rcases ih with ⟨found,shape,header,whole,front,captured,outside⟩
      exact ⟨by simpa only [framesOf_cons] using PushCarrier.owner_pass frame found,
        congrArg (Stack.push _) shape,header,frame.prepend whole,frame.prepend front,captured,outside⟩
  | live header different saved next ih =>
      rcases ih with ⟨found,shape,selected,whole,front,captured,outside⟩
      refine ⟨?_,congrArg (Stack.live _ _ _ _ _) shape,selected,.live header saved whole,.live header saved front,captured,outside⟩
      rcases different with different | different <;>
        simp [framesOf_cons,CoreMachine.findOwner,different,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | spent header different next ih =>
      rcases ih with ⟨found,shape,selected,whole,front,captured,outside⟩
      refine ⟨?_,congrArg (Stack.spent _ _ _) shape,selected,.spent header whole,.spent header front,captured,outside⟩
      rcases different with different | different <;>
        simp [framesOf_cons,CoreMachine.findOwner,different,found,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Resume restores capture ++ caller front ++ spent marker ++ outside.
The current scope must resolve this resume's exact static binder to the exact
selected dynamic ticket. This constructs the entire successor relation. -/
theorem resume_complete_mapped {base : CoreMachine.State}
    (cut : MappedOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget)
    (frame : ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (context : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue code)
    (resolve : plain.scope.resolve binder = some ticket) (runtimeScope : Scope) :
    ComponentMapped graph owners ((frameOwners,.resume handler owner) :: whole)
      { base with control := .returned coreValue, frames := .resume handler owner :: framesOf whole }
      ⟨.resume binder code,plain.scope,target⟩ ∧
    CoreMachine.next graph { base with control := .returned coreValue, frames := .resume handler owner :: framesOf whole } =
      .stepped { base with control := .returned coreValue, frames := framesOf captured ++ framesOf front ++ .clauseBoundary handler owner occurrence ticket none :: framesOf outside, observations := base.observations ++ [.resumed ticket] } ∧
    RawStep ⟨.resume binder code,plain.scope,target⟩
      ⟨code,plain.scope,capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩ [] [.ticket ticket] ∧
    ComponentMapped graph owners
      (captured ++ front ++ (savedOwners,.clauseBoundary handler owner occurrence ticket none) :: outside)
      { base with control := .returned coreValue, frames := framesOf captured ++ framesOf front ++ .clauseBoundary handler owner occurrence ticket none :: framesOf outside, observations := base.observations ++ [.resumed ticket] }
      ⟨code,plain.scope,capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩ := by
  obtain ⟨found,shape,header,current,front,captured,outside⟩ := cut.realizes
  have beforeStack := prepend_resume frame value.closed (pushed_mapped current) runtimeScope
  simp only [context,Context.plug] at beforeStack
  have afterStack := captured.append (front.append (.spent (ticket := ticket) header outside))
  refine ⟨⟨rfl,_,runtimeScope,.returned value,beforeStack⟩,?_,?_,?_⟩
  · simp only [CoreMachine.next,CoreMachine.returnResume,found]
  · rw [shape]
    exact .resume binder ticket plain.scope data.scope result data.answer frontTarget capturedTarget outsideTarget code value.closed resolve
  · exact ⟨by simp [framesOf,List.map_append],code,plain.scope,.returned value,pushed_mapped (by simpa only [List.append_assoc] using afterStack)⟩

/-- Completed Boolean selection restores its saved map and scope. The whole
branch before selection is reconstructed with its value-ready match frame. -/
theorem boolean_complete_mapped {base : CoreMachine.State}
    (yesTranslated : CoreTranslation.translateFuel graph fuel savedOwners yes = .ok rawYes)
    (noTranslated : CoreTranslation.translateFuel graph fuel savedOwners no = .ok rawNo)
    (yesSaved : EnvCloses graph savedOwners base.heap environment rawYes yesCode)
    (noSaved : EnvCloses graph savedOwners base.heap environment rawNo noCode)
    (condition reversed : Bool) (plain : PlainData)
    (context : plain.context = .branch yesCode noCode)
    (older : PushedWithMaps graph base.heap annotations target)
    (owners : CoreTranslation.OwnerMap) (runtimeScope : Scope) :
    ComponentMapped graph owners ((savedOwners,.matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) :: annotations)
      { base with control := .returned (.boolean condition), frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations }
      ⟨.branch (.boolean condition) yesCode noCode,plain.scope,target⟩ ∧
    CoreMachine.next graph { base with control := .returned (.boolean condition), frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations } =
      .stepped { base with control := .evaluate (if condition then yes else no) environment, frames := framesOf annotations } ∧
    RawStep ⟨.branch (.boolean condition) yesCode noCode,plain.scope,target⟩
      ⟨(if condition then yesCode else noCode),plain.scope,target⟩ [] [] ∧
    ComponentMapped graph savedOwners annotations
      { base with control := .evaluate (if condition then yes else no) environment, frames := framesOf annotations }
      ⟨(if condition then yesCode else noCode),plain.scope,target⟩ := by
  have frame : PlainFrameRel graph savedOwners base.heap
      (.matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) plain := by
    change FrameRel graph savedOwners base.heap _ plain.context
    rw [context]; exact .booleanMatch yesTranslated noTranslated yesSaved noSaved
  have value : ValueRel graph owners base.heap (.boolean condition) (.boolean condition) := .boolean
  have stack := prepend_mapped frame value.closed (pushed_mapped older) runtimeScope
  simp only [context,Context.plug] at stack
  obtain ⟨next,step,saved,translated⟩ := CoreStrictSteps.branch_complete (base := base)
    yesTranslated noTranslated yesSaved noSaved condition reversed (framesOf annotations) plain.scope target
  exact ⟨⟨rfl,_,runtimeScope,.returned value,stack⟩,next,step,
    ⟨rfl,_,plain.scope,.evaluate translated saved,pushed_mapped older⟩⟩

#print axioms boolean_complete_mapped

/-- Non-value resume operands use a genuine focus step; owner consumption is
reserved for completion after the operand returns. -/
theorem resume_focus_mapped {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .resume handler owner post operand)
    (translated : CoreTranslation.translateFuel graph fuel owners site = .ok (.resume binder raw))
    (current : EnvCloses graph owners base.heap environment (.resume binder raw) (.resume binder code))
    (notValue : ¬ code.IsValue) (plain : PlainData) (context : plain.context = .resume binder)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      { base with control := .evaluate site environment, frames := framesOf annotations }
      ⟨.resume binder code,plain.scope,target⟩ ∧
    CoreMachine.next graph { base with control := .evaluate site environment, frames := framesOf annotations } =
      .stepped { base with control := .evaluate operand environment, frames := .resume handler owner :: framesOf annotations, observations := base.observations ++ [.entered site] } ∧
    RawStep ⟨.resume binder code,plain.scope,target⟩ ⟨code,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.resume handler owner) :: annotations)
      { base with control := .evaluate operand environment, frames := .resume handler owner :: framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨code,plain.scope,.push (.plain plain) target⟩ := by
  obtain ⟨operandFuel,resolved,childTranslated⟩ := resume_translation_parts known kind translated
  obtain ⟨_,child,marker⟩ := resume_components current
  have frame : ResumeRel graph owners base.heap (.resume handler owner) plain :=
    .operand known kind translated resolved marker context
  have focus : Focus (.resume binder code) code plain.context := by rw [context]; exact .resume notValue
  exact ⟨⟨rfl,_,plain.scope,.evaluate translated current,pushed_mapped older⟩,
    (resume_entry_decreases (base := base) ordered known kind (framesOf annotations)).1,.focus plain focus target,
    ⟨rfl,_,plain.scope,.evaluate childTranslated child,pushed_mapped (.resume frame older)⟩⟩

/-- A matching spent occurrence stops lookup immediately, including when an
older occurrence with the same static owner is still live. -/
theorem spent_stops_older_live (capture : List CoreMachine.Frame) (outside : List CoreMachine.Frame) :
    CoreMachine.findOwner handler owner
      (.clauseBoundary handler owner occurrence ticket none ::
        .clauseBoundary handler owner olderOccurrence olderTicket (some capture) :: outside) =
      .error (.consumedOwner handler owner) := by simp [CoreMachine.findOwner]

/-- Dormant captures are not a fallback search space for a different owner. -/
theorem wrong_owner_does_not_search_capture :
    CoreMachine.findOwner 0 1
      [.clauseBoundary 0 0 0 0 (some [.clauseBoundary 0 1 1 1 (some [])])] =
      .error (.missingOwner 0 1) := rfl

#print axioms resume_focus_mapped
#print axioms spent_stops_older_live
#print axioms wrong_owner_does_not_search_capture

namespace Exported
open CoreExportedFixture CoreInitialPrefix CoreHandlerPrefix CoreCleanupEntry CoreOrdinaryCompletion CoreAdministrativeTransport
open CoreCaptureEntry.Exported
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0,.unit,[],none,.unit⟩
def ownedRaw (index : Nat) : Code := (CoreTranslation.translateFuel graph 56 clauseMaps index).toOption.getD .unit
def clauseEnv : CoreMachine.Environment := .binding 9 (.boolean true) methodsEnv
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl
private theorem translation_unique
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok rawCode)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok otherRaw) : rawCode = otherRaw := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index rawCode (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index otherRaw (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

private theorem owner_head_pushed
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

private theorem current_clause : EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 40) clauseTarget.expression ∧
    PushedWithMaps graph [] t28.annotations clauseTarget.stack := by
  obtain ⟨shape,code,scope,control,stack⟩ := reached_first_clause_related
  obtain ⟨rfl,rfl,pushed⟩ := owner_head_pushed stack
  cases control with
  | evaluate translated saved =>
      have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 40 = .ok (ownedRaw 40))
      cases same
      exact ⟨saved,pushed⟩

def yesCode : Code := match clauseTarget.expression with | .branch _ yes _ => yes | _ => .unit
def noCode : Code := match clauseTarget.expression with | .branch _ _ no => no | _ => .unit
def ticketScope : Scope := .ticket (CoreTranslation.ticket graph 0) 0
private def branchContext : Context := .branch yesCode noCode
def branchPlain : PlainData := ⟨branchContext,ticketScope,.boolean,.unit,
  (ticketScope.translate branchContext.dependencies).getD [],by decide⟩
def selectedTarget : Configuration := ⟨yesCode,ticketScope,clauseTarget.stack⟩

def s29 : CoreMachine.State := { s28 with control := .evaluate 30 clauseEnv, frames := .matchCases (CoreStrictSteps.booleanArms 38 39 false) clauseEnv :: s28.frames, observations := s28.observations ++ [.entered 40] }
def s30 : CoreMachine.State := { s29 with control := .returned (.boolean true), observations := s29.observations ++ [.entered 30] }
def s31 : CoreMachine.State := { s30 with control := .evaluate 38 clauseEnv, frames := s28.frames }
def t29 : Point := ⟨s29,clauseTarget,clauseMaps,(clauseMaps,.matchCases (CoreStrictSteps.booleanArms 38 39 false) clauseEnv) :: t28.annotations⟩
def t30 : Point := ⟨s30,clauseTarget,clauseMaps,t29.annotations⟩
def t31 : Point := ⟨s31,selectedTarget,clauseMaps,t28.annotations⟩

private theorem branch_parts : EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 30) (.boolean true) ∧
    EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 38) yesCode ∧
    EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 39) noCode := by
  exact branch_components current_clause.1

private theorem branchTraversal : SilentMapped graph clauseMaps clauseMaps t28.annotations t29.annotations s28 s29 clauseTarget := by
  exact boolean_entry_same_target (base := s28) (environment := clauseEnv) (scrutineeCode := .boolean true)
    (yesCode := yesCode) (noCode := noCode) (annotations := t28.annotations) ordered
    (rfl : graph.node 40 = some (node 40)) rfl
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 30 = .ok (ownedRaw 30))
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 38 = .ok (ownedRaw 38))
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 39 = .ok (ownedRaw 39))
    current_clause.1 branch_parts.1 branch_parts.2.1 branch_parts.2.2
    (ValueRel.boolean (graph := graph) (owners := clauseMaps) (heap := []) (value := true)).closed branchPlain rfl current_clause.2

private theorem return_condition : Link graph t29 t30 := by
  obtain ⟨value,lookup,witness,translated⟩ := CoreAdministrativeSteps.variable_evaluate (base := s29)
    (rfl : graph.node 30 = some (node 30)) rfl branch_parts.1
    (ValueRel.boolean (graph := graph) (owners := clauseMaps) (heap := []) (value := true)).closed s29.frames
  have valueEq : value = .boolean true := Option.some.inj (lookup.symm.trans rfl)
  cases valueEq
  have frame : PlainFrameRel graph clauseMaps [] (.matchCases (CoreStrictSteps.booleanArms 38 39 false) clauseEnv) branchPlain :=
    .booleanMatch (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 38 = .ok (ownedRaw 38))
      (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 39 = .ok (ownedRaw 39)) branch_parts.2.1 branch_parts.2.2
  have stack := prepend_mapped frame (ValueRel.boolean (graph := graph) (owners := clauseMaps) (heap := []) (value := true)).closed
    (pushed_mapped current_clause.2) ticketScope
  exact .value (value_entry_mapped witness rfl rfl stack)

private theorem choose_true : Link graph t30 t31 ∧ RawStep clauseTarget selectedTarget [] [] := by
  obtain ⟨before,next,step,after⟩ := boolean_complete_mapped (base := s30)
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 38 = .ok (ownedRaw 38))
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 39 = .ok (ownedRaw 39)) branch_parts.2.1 branch_parts.2.2
    true false branchPlain rfl current_clause.2 clauseMaps ticketScope
  exact ⟨.positive return_condition.endpoints.2 next (.one step) after,step⟩

def postWriteCode : Code := match yesCode with | .bind _ _ body => body | _ => .unit
def resumeCode : Code := .resume (CoreTranslation.ticket graph 0) .unit
def postPlain : PlainData := ⟨.bind 10 postWriteCode,ticketScope,.unit,.unit,[],by decide⟩
def resumePlain : PlainData := ⟨.resume (CoreTranslation.ticket graph 0),ticketScope,.unit,.unit,[0],by decide⟩
def resumeTarget : Configuration := ⟨resumeCode,ticketScope,.push (.plain postPlain) clauseTarget.stack⟩
def s32 : CoreMachine.State := { s31 with control := .evaluate 32 clauseEnv, frames := .bind 10 37 clauseEnv :: s31.frames, observations := s31.observations ++ [.entered 38] }
def s33 : CoreMachine.State := { s32 with control := .evaluate 31 clauseEnv, frames := .resume 0 0 :: s32.frames, observations := s32.observations ++ [.entered 32] }
def s34 : CoreMachine.State := { s33 with control := .returned .unit, observations := s33.observations ++ [.entered 31] }
def t32 : Point := ⟨s32,resumeTarget,clauseMaps,(clauseMaps,.bind 10 37 clauseEnv) :: t28.annotations⟩
def t33 : Point := ⟨s33,resumeTarget,clauseMaps,(clauseMaps,.resume 0 0) :: t32.annotations⟩
def t34 : Point := ⟨s34,resumeTarget,clauseMaps,t33.annotations⟩

private theorem postReady : ClosedExcept 10 postWriteCode := by
  have bound : postWriteCode.dependencies.all (fun dep => match dep with | .variable n => n == 10 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp bound (.variable n) member

private theorem bind_parts : EnvCloses graph clauseMaps [] clauseEnv (ownedRaw 32) resumeCode ∧
    EnvCloses graph clauseMaps [] clauseEnv (.lambda 10 (ownedRaw 37)) (.lambda 10 postWriteCode) :=
  CoreOrdinaryCompletion.bind_components branch_parts.2.1

private theorem postFrame : PlainFrameRel graph clauseMaps [] (.bind 10 37 clauseEnv) postPlain :=
  .bind (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 37 = .ok (ownedRaw 37)) bind_parts.2 postReady

private theorem focus_resume_bind : Link graph t31 t32 ∧ RawStep selectedTarget resumeTarget [] [] := by
  have after : Related graph t32 := ⟨rfl,_,ticketScope,.evaluate (fuel := 56) rfl bind_parts.1,
    pushed_mapped (.cons postFrame current_clause.2)⟩
  have focus : RawStep selectedTarget resumeTarget [] [] :=
    .focus postPlain (.bind (by simp [Code.subst,Code.instantiate,Code.IsValue])) clauseTarget.stack
  exact ⟨.positive choose_true.1.endpoints.2 rfl (.one focus) after,focus⟩

private theorem resumeTraversal : SilentMapped graph clauseMaps clauseMaps t32.annotations t33.annotations s32 s33 resumeTarget := by
  exact resume_entry_same_target_mapped (base := s32) (environment := clauseEnv)
    (annotations := t32.annotations) ordered (rfl : graph.node 32 = some (node 32)) rfl
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 32 = .ok (ownedRaw 32)) bind_parts.1
    (ValueRel.unit (graph := graph) (owners := clauseMaps) (heap := [])).closed resumePlain rfl
    (.cons postFrame current_clause.2)

private theorem resumeFrame : ResumeRel graph clauseMaps [] (.resume 0 0) resumePlain :=
  .operand (rfl : graph.node 32 = some (node 32)) rfl
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 32 = .ok (ownedRaw 32)) rfl
    (resume_components bind_parts.1).2.2 rfl

private theorem return_operand : Link graph t33 t34 := by
  obtain ⟨witness,translated⟩ := CoreAdministrativeSteps.unit_evaluate (base := s33)
    (rfl : graph.node 31 = some (node 31)) rfl (resume_components bind_parts.1).2.1 s33.frames
  have stack := prepend_resume resumeFrame (ValueRel.unit (graph := graph) (owners := clauseMaps) (heap := [])).closed
    (pushed_mapped (.cons postFrame current_clause.2)) ticketScope
  exact .value (value_entry_mapped witness rfl rfl stack)

private theorem owner_cut : MappedOwnerCut graph [] 0 0 t32.annotations resumeTarget.stack
    [(clauseMaps,.bind 10 37 clauseEnv)] (.push (.plain postPlain) .nil) [] 0 0 handlerData .unit
    capturedMaps capturedTarget outsideMaps (.push (.plain handlerPlain) cell) :=
  .push (.ordinary postFrame) (.hit first_capture_parts.1 first_capture_parts.2.1 first_capture_parts.2.2)

def restoredMaps : List MappedFrame := capturedMaps ++ [(clauseMaps,.bind 10 37 clauseEnv)] ++
  ([],.clauseBoundary 0 0 0 0 none) :: outsideMaps
def restoredTarget : Configuration := ⟨.unit,ticketScope,
  capturedTarget.append (.push (.plain postPlain) (.spent 0 .unit .none (.push (.plain handlerPlain) cell)))⟩
def s35 : CoreMachine.State := { s34 with control := .returned .unit, frames := framesOf restoredMaps, observations := s34.observations ++ [.resumed 0] }
def t35 : Point := ⟨s35,restoredTarget,clauseMaps,restoredMaps⟩

private theorem consume : Link graph t34 t35 ∧ RawStep resumeTarget restoredTarget [] [.ticket 0] := by
  obtain ⟨before,next,step,after⟩ := resume_complete_mapped (base := s34) owner_cut resumeFrame
    (rfl : resumePlain.context = .resume (CoreTranslation.ticket graph 0)) .unit rfl ticketScope
  exact ⟨.positive return_operand.endpoints.2 next (.one step) after,step⟩

theorem first_clause_to_resume : Chain graph t28 [t29,t30,t31,t32,t33,t34,t35] t35 :=
  .next (.traversal branchTraversal) (.next return_condition (.next choose_true.1
    (.next focus_resume_bind.1 (.next (.traversal resumeTraversal) (.next return_operand (.last consume.1))))))

theorem exported_resume_prefix : Chain graph p0
    [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20,r21,r22,r23,r24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35] t35 :=
  chain_append exported_capture_prefix first_clause_to_resume

theorem reached_restored_related : Related graph t35 := exported_resume_prefix.endpoints.2

theorem exported_resume_steps : CoreAllocationHistory.Steps graph 35 (CoreMachine.initial graph) s35 :=
  exported_resume_prefix.core_steps

theorem exported_resume_history : CoreAllocationHistory.History s35 :=
  CoreAllocationHistory.initial_steps_history graph exported_resume_steps

/-- Full captured prefix precedes the exact post-resume write11 frame and the
spent marker. The outside getter/cell spine remains after that marker. -/
theorem restored_frames_exact : s35.frames =
    [.bind 7 23 callbackEnv,.cleanupBoundary 27 callbackEnv 0,.handlerBoundary 41 methodsEnv 0,
      .bind 10 37 clauseEnv,.clauseBoundary 0 0 0 0 none,.bind 12 44 methodsEnv,.resourceBoundary 48 0 0] ∧
    (node 37).kind = .apply 33 36 ∧ (node 35).kind = .integer 11 ∧
    s35.nextOwner = 1 := ⟨rfl,rfl,rfl,rfl⟩

private theorem rawTrace_append (first : RawTrace before middle created discharged)
    (second : RawTrace middle after laterCreated laterDischarged) :
    RawTrace before after (created ++ laterCreated) (laterDischarged ++ discharged) := by
  induction first with
  | refl => simpa using second
  | next step rest ih => simpa [List.append_assoc] using RawTrace.next step (ih second)

theorem first_resume_ledger : RawTrace clauseTarget restoredTarget [] [.ticket 0] :=
  .next choose_true.2 (.next focus_resume_bind.2 (.next consume.2 (.refl _)))

theorem exported_resume_ledger : RawTrace rootTarget restoredTarget [.resource 0,.cleanup 0,.ticket 0] [.ticket 0] :=
  rawTrace_append exported_capture_ledger first_resume_ledger

theorem restored_owner_consumed : CoreMachine.findOwner 0 0 s35.frames =
    .error (.consumedOwner 0 0) := rfl

theorem second_resume_rejected : CoreMachine.returnResume s35 0 0 .unit =
    .rejected (.consumedOwner 0 0) := rfl

theorem restored_owner_not_live :
    ¬ MappedOwnerCut graph [] 0 0 restoredMaps target frontAnn frontStack savedOwners occurrence ticket data result
      capAnn capStack outerAnn outerStack := by
  intro cut
  have found := cut.realizes.1
  have spent : CoreMachine.findOwner 0 0 (framesOf restoredMaps) = .error (.consumedOwner 0 0) := restored_owner_consumed
  rw [spent] at found
  cases found

theorem resume_unchanged_rejected :
    ¬ SilentMapped graph clauseMaps clauseMaps t32.annotations t32.annotations s32 s32 resumeTarget := by
  intro witness
  exact unchanged_potential_rejected graph s32 witness.decreasing

#print axioms restored_owner_consumed
#print axioms second_resume_rejected
#print axioms restored_owner_not_live
#print axioms resume_unchanged_rejected
#print axioms first_clause_to_resume
#print axioms exported_resume_prefix
#print axioms reached_restored_related
#print axioms exported_resume_steps
#print axioms exported_resume_history
#print axioms restored_frames_exact
#print axioms first_resume_ledger
#print axioms exported_resume_ledger

end Exported

#print axioms MappedOwnerCut.realizes
#print axioms resume_complete_mapped
end Ash.OneShot.CoreResumeEntry
