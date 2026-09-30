import CoreResumeEntry

/-! The fixed initial prefix through its second user capture. Each new
endpoint is derived from the preceding component witness. Cleanup remains
armed; scope/type authentication and general simulation remain separate. -/
namespace Ash.OneShot.CoreSecondCapture
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreEffectFrames
  CoreRequestFrames CoreResumeFrames CoreStrictStack CoreStrictPotential CoreCaptureEntry
  CoreOrdinaryCompletion CoreAdministrativeTransport CoreInitialPrefix CoreHandlerPrefix
  CoreCleanupEntry CoreCaptureEntry.Exported CoreResumeEntry.Exported CoreExportedFixture
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private def node (index : Nat) : CoreSyntax.Node := (graph.node index).getD ⟨0,.unit,[],none,.unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl

private theorem translation_unique
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok code)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok other) : code = other := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index code (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index other (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

private theorem plug_not_unit (context : Context) (code : Code) : context.plug code ≠ .unit := by
  cases context <;> simp [Context.plug]

/-- No nonempty flattened prefix can produce Unit. -/
private theorem flat_unit (flat : FlattenedWithMaps graph heap annotations code scope result resultScope) :
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

private theorem restored_pushed : PushedWithMaps graph [] restoredMaps restoredTarget.stack := by
  obtain ⟨_,code,scope,control,stack⟩ := reached_restored_related
  obtain ⟨pre,tail,split,flat,pushed⟩ := stack
  obtain ⟨rfl,_,_⟩ := flat_unit flat rfl
  have same : tail = restoredMaps := by simpa [t35] using split.symm
  subst tail
  exact pushed

def tailTarget : Stack := .push (.armed actionData) (.push (.handler handlerData)
  (.push (.plain postPlain) (.spent 0 .unit .none (.push (.plain handlerPlain) cell))))

private theorem bind_parts :
    EnvCloses graph [] [] callbackEnv (.lambda 7 (raw 23)) (.lambda 7 suffix) ∧
    ClosedExcept 7 suffix ∧
    PushedWithMaps graph [] (restoredMaps.tail) (tailTarget) := by
  have pushed := restored_pushed
  change PushedWithMaps graph [] (([],.bind 7 23 callbackEnv) :: restoredMaps.tail)
    (.push (.plain bindPlain) tailTarget) at pushed
  cases pushed with
  | cons relation tail =>
      change FrameRel graph [] [] (.bind 7 23 callbackEnv) (.bind 7 suffix) at relation
      cases relation with
      | bind translated saved ready =>
          have equal := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 23 = .ok (raw 23))
          cases equal
          exact ⟨saved,ready,tail⟩
  | initializer relation tail => cases relation
  | boundary relation tail => cases relation
  | request relation tail => cases relation
  | resume relation tail => cases relation

def nextEnv : CoreMachine.Environment := .binding 7 .unit callbackEnv
def secondCode : Code := suffix.subst 7 .unit
def secondTarget : Configuration := ⟨secondCode,.none,tailTarget⟩
def s36 : CoreMachine.State := { s35 with control := .evaluate 23 nextEnv, frames := framesOf restoredMaps.tail }
def u36 : Point := ⟨s36,secondTarget,[],restoredMaps.tail⟩

private theorem return_bind : Link graph t35 u36 ∧
    RawStep restoredTarget ⟨.bind 7 .unit suffix,.none,tailTarget⟩ [] [] ∧
    RawStep ⟨.bind 7 .unit suffix,.none,tailTarget⟩ secondTarget [] [] := by
  obtain ⟨before,next,plug,bind,after⟩ := bind_return_mapped (base := s35)
    (rfl : CoreTranslation.translateFuel graph 56 [] 23 = .ok (raw 23)) bind_parts.1 bind_parts.2.1
    (ValueRel.unit (owners := clauseMaps)) bindPlain rfl bind_parts.2.2 ticketScope
  exact ⟨.positive reached_restored_related next (.next plug (.one bind)) after,plug,bind⟩

def setterCode : Code := match secondCode with | .bind _ _ body => body | _ => .unit
def secondBindPlain : PlainData := ⟨.bind 6 setterCode,.none,.unit,.unit,[],by decide⟩
def falsePlain : PlainData := ⟨.perform (.user 0 []) 0,.none,.boolean,.unit,[],rfl⟩
def falseTarget : Configuration := ⟨.perform (.user 0 []) 0 (.boolean false),.none,
  .push (.plain secondBindPlain) tailTarget⟩
def s37 : CoreMachine.State := { s36 with control := .evaluate 17 nextEnv, frames := .bind 6 22 nextEnv :: s36.frames, observations := s36.observations ++ [.entered 23] }
def s38 : CoreMachine.State := { s37 with control := .evaluate 16 nextEnv, frames := .request (.user 0 []) 0 nextEnv :: s37.frames, observations := s37.observations ++ [.entered 17] }
def s39 : CoreMachine.State := { s38 with control := .returned (.boolean false), observations := s38.observations ++ [.entered 16] }
def u37 : Point := ⟨s37,falseTarget,[],([], .bind 6 22 nextEnv) :: u36.annotations⟩
def u38 : Point := ⟨s38,falseTarget,[],([], .request (.user 0 []) 0 nextEnv) :: u37.annotations⟩
def u39 : Point := ⟨s39,falseTarget,[],u38.annotations⟩

private theorem second_parts :
    EnvCloses graph [] [] nextEnv (raw 17) (.perform (.user 0 []) 0 (.boolean false)) ∧
    EnvCloses graph [] [] nextEnv (.lambda 6 (raw 22)) (.lambda 6 setterCode) := by
  have current := bind_parts.1.beta_argument (ValueRel.unit (owners := []))
  change EnvCloses graph [] [] nextEnv (.bind 6 (raw 17) (raw 22))
    (.bind 6 (.perform (.user 0 []) 0 (.boolean false)) setterCode) at current
  exact bind_components current

private theorem setterReady : ClosedExcept 6 setterCode := by
  have bound : setterCode.dependencies.all (fun dep => match dep with | .variable n => n == 6 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp bound (.variable n) member

private theorem secondFrame : PlainFrameRel graph [] [] (.bind 6 22 nextEnv) secondBindPlain :=
  .bind (rfl : CoreTranslation.translateFuel graph 56 [] 22 = .ok (raw 22)) second_parts.2 setterReady
private theorem falseStack : PushedWithMaps graph [] u37.annotations falseTarget.stack :=
  .cons secondFrame bind_parts.2.2

private theorem focus_second_bind : Link graph u36 u37 ∧ RawStep secondTarget falseTarget [] [] := by
  have after : Related graph u37 := ⟨rfl,_,.none,.evaluate (fuel := 56) rfl second_parts.1,pushed_mapped falseStack⟩
  have step : RawStep secondTarget falseTarget [] [] :=
    .focus secondBindPlain (.bind (by simp [Code.subst,Code.instantiate,Code.IsValue])) tailTarget
  exact ⟨.positive return_bind.1.endpoints.2 rfl (.one step) after,step⟩

private theorem falseTraversal : SilentMapped graph [] [] u37.annotations u38.annotations s37 s38 falseTarget :=
  request_entry_same_target_mapped (base := s37) (environment := nextEnv)
    (requested := .user 0 []) (code := .boolean false) (annotations := u37.annotations) ordered
    (rfl : graph.node 17 = some (node 17)) rfl
    (rfl : CoreTranslation.translateFuel graph 56 [] 16 = .ok (.boolean false))
    second_parts.1 (ValueRel.boolean (graph := graph) (owners := []) (heap := []) (value := false)).closed
    falsePlain rfl falseStack

private theorem falseReturn : Link graph u38 u39 := by
  have saved := (perform_components second_parts.1).2
  obtain ⟨witness,_⟩ := CoreAdministrativeSteps.boolean_evaluate (base := s38)
    (rfl : graph.node 16 = some (node 16)) rfl saved s38.frames
  have frame : RequestRel graph [] [] (.request (.user 0 []) 0 nextEnv) falsePlain :=
    .operand (requested := .user 0 []) (perform_header_at second_parts.1 _ _ _ _ _ rfl rfl) rfl
  have stack := prepend_request frame (ValueRel.boolean (graph := graph) (owners := []) (heap := []) (value := false)).closed
    (pushed_mapped falseStack) .none
  exact .value (value_entry_mapped witness rfl rfl stack)

private theorem pushed_head
    (related : PushedWithMaps graph heap ((owners,core) :: rest) (.push frame target)) :
    PushCarrier graph owners heap core frame ∧ PushedWithMaps graph heap rest target := by
  cases related with
  | cons relation tail => exact ⟨.ordinary relation,tail⟩
  | initializer relation tail => exact ⟨.initializer relation,tail⟩
  | request relation tail => exact ⟨.request relation,tail⟩
  | resume relation tail => exact ⟨.resume relation,tail⟩
  | cleanup relation tail => exact ⟨.cleanup relation,tail⟩
  | boundary relation tail => exact ⟨.boundary relation,tail⟩

def secondInside : List MappedFrame := [([],.bind 6 22 nextEnv),([],.cleanupBoundary 27 callbackEnv 0)]
def secondCaptured : List MappedFrame := secondInside ++ [([],.handlerBoundary 41 methodsEnv 0)]
def secondOutside : List MappedFrame := [(clauseMaps,.bind 10 37 clauseEnv),([],.clauseBoundary 0 0 0 0 none)] ++ outsideMaps
def secondCap : Stack := .push (.plain secondBindPlain) (.push (.armed actionData) (.push (.handler handlerData) .nil))
def secondTail : Stack := .push (.plain postPlain) (.spent 0 .unit .none (.push (.plain handlerPlain) cell))

private theorem second_cut : MappedHandlerCut graph [] (.user 0 []) u37.annotations falseTarget.stack
    secondInside [] 41 methodsEnv handlerData secondOutside secondCap secondTail := by
  obtain ⟨bindFrame,rest⟩ := pushed_head falseStack
  obtain ⟨cleanupFrame,rest⟩ := pushed_head rest
  obtain ⟨handlerFrame,rest⟩ := pushed_head rest
  cases handlerFrame with
  | boundary header =>
    exact .push bindFrame (by simp [ExecFrame.erase,PlainData.erase,Frame.target])
      (.push cleanupFrame (by simp [ExecFrame.erase,ActionData.erase,Frame.target])
        (.hit (site := 41) (environment := methodsEnv) (data := handlerData) (owners := []) header rfl rest))

/-- Captured/outside annotations are retained from the same selected cut;
framesOf is not inverted to choose new lexical maps. -/
theorem second_capture_parts :
    PushedWithMaps graph [] secondCaptured secondCap ∧
    PushedWithMaps graph [] secondOutside secondTail := by
  obtain ⟨_,_,_,captured,outside⟩ := second_cut.realizes
  exact ⟨captured,outside⟩

#print axioms second_capture_parts

private theorem clause_unique {clauses : Clauses}
    (first : ClauseAt operation clauses parameter binder body)
    (second : ClauseAt operation clauses otherParameter otherBinder otherBody) :
    parameter = otherParameter ∧ binder = otherBinder ∧ body = otherBody := by
  induction first with
  | hit => cases second with
    | hit => exact ⟨rfl,rfl,rfl⟩
    | pass different next => exact False.elim (different rfl)
  | pass different next ih => cases second with
    | hit => exact False.elim (different rfl)
    | pass otherDifferent otherNext => exact ih otherNext

private theorem selection : ClauseAt 0 handlerData.clauses 9 (CoreTranslation.ticket graph 0) firstClauseBody := .hit
private theorem clauseReady : ClosedExcept 9 firstClauseBody := by
  have bound : firstClauseBody.dependencies.all (fun dep => match dep with | .variable n => n == 9 | _ => true) = true := by decide
  intro n member; simpa using List.all_eq_true.mp bound (.variable n) member

def secondClauseTarget : Configuration := ⟨firstClauseBody.subst 9 (.boolean false),
  .ticket (CoreTranslation.ticket graph 0) 1,.live 1 .unit .unit secondCap .none secondTail⟩
def s40 : CoreMachine.State := { s39 with control := .evaluate 40 (.binding 9 (.boolean false) methodsEnv), frames := .clauseBoundary 0 0 0 1 (some (framesOf secondCaptured)) :: framesOf secondOutside, nextOwner := 2, observations := s39.observations ++ [.captured 0 1] }
def u40 : Point := ⟨s40,secondClauseTarget,clauseMaps,([], .clauseBoundary 0 0 0 1 (some (framesOf secondCaptured))) :: secondOutside⟩

private theorem second_capture : Link graph u39 u40 ∧ RawStep falseTarget secondClauseTarget [.ticket 1] [] := by
  have requestCarrier := perform_header_at second_parts.1 _ _ _ _ _ rfl rfl
  obtain ⟨fuel,argument,rawBody,body,pattern,selected,translated,before,next,step,after⟩ :=
    capture_mapped (base := s39) second_cut (rfl : graph.node 41 = some (node 41)) rfl
      (clause := ⟨0,.binder ⟨9,.boolean⟩,0,40⟩) rfl .boolean requestCarrier falsePlain rfl
      (by intro parameter binder body selected
          obtain ⟨rfl,rfl,rfl⟩ := clause_unique selected selection
          exact clauseReady) .unit .none
  have argumentEq : argument = ⟨9,.boolean⟩ := (CoreSyntax.Pattern.binder.inj pattern).symm
  cases argumentEq
  obtain ⟨_,_,rfl⟩ := clause_unique selected selection
  exact ⟨.positive falseReturn.endpoints.2 next (.one step) after,step⟩

theorem resume_to_second_capture : Chain graph t35 [u36,u37,u38,u39,u40] u40 :=
  .next return_bind.1 (.next focus_second_bind.1 (.next (.traversal falseTraversal) (.next falseReturn (.last second_capture.1))))

theorem exported_second_capture_prefix : Chain graph p0
    [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20,r21,r22,r23,r24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35,u36,u37,u38,u39,u40] u40 :=
  chain_append exported_resume_prefix resume_to_second_capture

theorem reached_second_clause_related : Related graph u40 := exported_second_capture_prefix.endpoints.2

theorem exported_second_capture_steps : CoreAllocationHistory.Steps graph 40 (CoreMachine.initial graph) s40 :=
  exported_second_capture_prefix.core_steps

theorem exported_second_capture_history : CoreAllocationHistory.History s40 :=
  CoreAllocationHistory.initial_steps_history graph exported_second_capture_steps

private theorem rawTrace_append (first : RawTrace before middle created discharged)
    (second : RawTrace middle after laterCreated laterDischarged) :
    RawTrace before after (created ++ laterCreated) (laterDischarged ++ discharged) := by
  induction first with
  | refl => simpa using second
  | next step rest ih => simpa [List.append_assoc] using RawTrace.next step (ih second)

theorem second_capture_ledger : RawTrace restoredTarget secondClauseTarget [.ticket 1] [] :=
  .next return_bind.2.1 (.next return_bind.2.2 (.next focus_second_bind.2 (.next second_capture.2 (.refl _))))

theorem exported_second_capture_ledger : RawTrace rootTarget secondClauseTarget
    [.resource 0,.cleanup 0,.ticket 0,.ticket 1] [.ticket 0] :=
  rawTrace_append exported_resume_ledger second_capture_ledger

/-- The new live ticket saves the pending setter99, armed delayed callback27
and selected handler. The old write11 and spent0 remain in its outside spine. -/
theorem second_capture_frames_exact :
    s40.frames = [.clauseBoundary 0 0 0 1
      (some [.bind 6 22 nextEnv,.cleanupBoundary 27 callbackEnv 0,.handlerBoundary 41 methodsEnv 0]),
      .bind 10 37 clauseEnv,.clauseBoundary 0 0 0 0 none,.bind 12 44 methodsEnv,.resourceBoundary 48 0 0] ∧
    s40.control = .evaluate 40 (.binding 9 (.boolean false) methodsEnv) ∧ s40.nextOwner = 2 ∧
    (node 22).kind = .apply 18 21 ∧ (node 20).kind = .integer 99 ∧
    (node 35).kind = .integer 11 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- A live new owner cannot make the older matching spent owner resumable. -/
theorem old_ticket_still_spent : CoreMachine.findOwner 0 0 (framesOf secondOutside) =
    .error (.consumedOwner 0 0) := rfl

/-- The nearest matching live owner is ticket1 with this exact saved prefix;
its older spent marker cannot be selected through it. -/
theorem new_ticket_selected : CoreMachine.findOwner 0 0 s40.frames =
    .ok ⟨[],0,0,0,1,framesOf secondCaptured,framesOf secondOutside⟩ := rfl

/-- Registration remains delayed even across both captures and the resume. -/
theorem cleanup_still_armed :
    secondCap = .push (.plain secondBindPlain)
      (.push (.armed actionData) (.push (.handler handlerData) .nil)) ∧
    s40.observations.contains (.entered 27) = false := ⟨rfl,by decide⟩

#print axioms new_ticket_selected
#print axioms cleanup_still_armed

#print axioms resume_to_second_capture
#print axioms exported_second_capture_prefix
#print axioms reached_second_clause_related
#print axioms exported_second_capture_steps
#print axioms exported_second_capture_history
#print axioms second_capture_ledger
#print axioms exported_second_capture_ledger
#print axioms second_capture_frames_exact
#print axioms old_ticket_still_spent
end Ash.OneShot.CoreSecondCapture
