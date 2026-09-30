import CoreCleanupRunPrefix
import CoreCellWriteFrames

/-! The same initial chain through the running callback's exact cell0 write.
Cleanup remains running. Supplied annotations are retained, not authenticated. -/
namespace Ash.OneShot.CoreCleanupWritePrefix
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential
  CoreAdministrativeTransport CoreCleanupRunFrames CoreCellWriteFrames CoreCleanupRunPrefix
  CoreInitialPrefix CoreHandlerPrefix CoreCleanupEntry CoreCaptureEntry.Exported CoreResumeEntry.Exported
  CoreSecondCapture CoreDiscardPrefix CoreExportedFixture CoreRequestFrames CoreEffectFrames
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
private def node (i : Nat) : CoreSyntax.Node := (graph.node i).getD ⟨0,.unit,[],none,.unit⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl
private theorem unique
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok code)
    (second : CoreTranslation.translateFuel graph other owners index = .ok otherCode) : code = otherCode := by
  have a := CoreTranslationFuel.success_mono graph fuel (max fuel other) owners index code (Nat.le_max_left _ _) first
  have b := CoreTranslationFuel.success_mono graph other (max fuel other) owners index otherCode (Nat.le_max_right _ _) second
  exact Except.ok.inj (a.symm.trans b)
def pairCode : Code := .pair (.resourceRef (.activation 0)) (.integer 7)
def callTarget : Configuration := ⟨.app setter pairCode,.none,.nil⟩
def writeTarget : Configuration := ⟨.perform (.cell (.activation 0)) 1 pairCode,.none,.nil⟩
def bodyEnv : CoreMachine.Environment := .binding 5 .unit methodsEnv
def setterValue : CoreMachine.Value := .closure 2 6 getterEnv
def setterEnv : CoreMachine.Environment := .binding 2 (.location 0) getterEnv
def allocated : Heap := [.pair (.handle 0) (.integer 7)]

private theorem current_parts : RunningTail graph [] physicalTail lexicalTail ∧
    EnvCloses graph [] [] bodyEnv (.app (.variable 3) (.pair (.variable 4) (.integer 7))) callTarget.expression := by
  obtain ⟨physical,lexical,focus,carrier,frames,target,empty,control⟩ :=
    running_empty_parts reached_callback_body_related rfl rfl rfl (by decide)
  have physicalEq : physical = physicalTail := frames.symm
  have lexicalEq : lexical = lexicalTail := by
    have stack := congrArg Configuration.stack target
    simpa [attach,empty,CoreCleanupRunPrefix.bodyTarget,Stack.append] using stack.symm
  have codeEq : focus.expression = callTarget.expression := (congrArg Configuration.expression target).symm
  rw [physicalEq,lexicalEq] at carrier
  have interpreted : EnvCloses graph [] [] bodyEnv (.app (.variable 3) (.pair (.variable 4) (.integer 7))) callTarget.expression := by
    change ControlRel graph [] [] (.evaluate 12 bodyEnv) focus.expression at control
    cases control with
    | evaluate translated saved =>
        have equal := unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 12 = .ok (.app (.variable 3) (.pair (.variable 4) (.integer 7))))
        cases equal
        exact codeEq ▸ saved
  exact ⟨carrier,interpreted⟩
private theorem setter_related : ValueRel graph [] [] setterValue setter := by
  obtain ⟨value,lookup,related⟩ := current_parts.2.app_components.1.lookup (by
    change ClosedValue (.lambda 2 (.perform (.cell (.activation 0)) 1 (.variable 2)))
    simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies,Syntax.without,Instantiation.Effect.freeNames])
  have equal := Option.some.inj (lookup.symm.trans (rfl : bodyEnv.lookup 3 = some setterValue))
  cases equal
  exact related
private theorem pair_closed : ClosedValue pairCode := by
  simp [pairCode,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies]
private theorem handle_saved : EnvCloses graph [] [] bodyEnv (.variable 4) (.resourceRef (.activation 0)) :=
  (pair_components current_parts.2.app_components.2).1
private theorem integer_saved : EnvCloses graph [] [] bodyEnv (.integer 7) (.integer 7) :=
  (pair_components current_parts.2.app_components.2).2

def functionPlain : PlainData := ⟨.appFunction pairCode,.none,.function (.product (.reference 0) .integer) .unit [.cell 0] [],.unit,[],rfl⟩
def argumentPlain : PlainData := ⟨.appArgument setter,.none,.product (.reference 0) .integer,.unit,[],by decide⟩
def leftPlain : PlainData := ⟨.pairLeft (.integer 7),.none,.reference 0,.product (.reference 0) .integer,[],rfl⟩
def rightPlain : PlainData := ⟨.pairRight (.resourceRef (.activation 0)),.none,.integer,.product (.reference 0) .integer,[],by decide⟩
def requestPlain : PlainData := ⟨.perform (.cell (.activation 0)) 1,.none,.product (.reference 0) .integer,.unit,[],rfl⟩
def s52 : CoreMachine.State := { s51 with control := .evaluate 8 bodyEnv,frames := .applyFunction 11 bodyEnv :: physicalTail,observations := s51.observations ++ [.entered 12] }
def s53 : CoreMachine.State := { s52 with control := .returned setterValue,observations := s52.observations ++ [.entered 8] }
def s54 : CoreMachine.State := { s53 with control := .evaluate 11 bodyEnv,frames := .applyArgument setterValue :: physicalTail }
def s55 : CoreMachine.State := { s54 with control := .evaluate 9 bodyEnv,frames := .tupleLeft 10 bodyEnv :: s54.frames,observations := s54.observations ++ [.entered 11] }
def s56 : CoreMachine.State := { s55 with control := .returned (.handle 0),observations := s55.observations ++ [.entered 9] }
def s57 : CoreMachine.State := { s56 with control := .evaluate 10 bodyEnv,frames := .tupleRight (.handle 0) :: s54.frames }
def s58 : CoreMachine.State := { s57 with control := .returned (.integer 7),observations := s57.observations ++ [.entered 10] }
def s59 : CoreMachine.State := { s58 with control := .returned (.location 0),frames := s54.frames,heap := allocated }
def s60 : CoreMachine.State := { s59 with control := .evaluate 6 setterEnv,frames := physicalTail }
def s61 : CoreMachine.State := { s60 with control := .evaluate 5 setterEnv,frames := .request (.cell (.bound 0)) 1 setterEnv :: physicalTail,observations := s60.observations ++ [.entered 6] }
def s62 : CoreMachine.State := { s61 with control := .returned (.location 0),observations := s61.observations ++ [.entered 5] }
def maps52 : List MappedFrame := [([],.applyFunction 11 bodyEnv)]
def maps54 : List MappedFrame := [([],.applyArgument setterValue)]
def maps55 : List MappedFrame := ([],.tupleLeft 10 bodyEnv)::maps54
def maps57 : List MappedFrame := ([],.tupleRight (.handle 0))::maps54
def maps61 : List MappedFrame := [([],.request (.cell (.bound 0)) 1 setterEnv)]
def w52 : CoreUnwindRelation.Point := ⟨s52,.eval (attach callTarget lexicalTail),[],maps52⟩
def w53 : CoreUnwindRelation.Point := ⟨s53,w52.machine,[],maps52⟩
def w54 : CoreUnwindRelation.Point := ⟨s54,w52.machine,[],maps54⟩
def w55 : CoreUnwindRelation.Point := ⟨s55,w52.machine,[],maps55⟩
def w56 : CoreUnwindRelation.Point := ⟨s56,w52.machine,[],maps55⟩
def w57 : CoreUnwindRelation.Point := ⟨s57,w52.machine,[],maps57⟩
def w58 : CoreUnwindRelation.Point := ⟨s58,w52.machine,[],maps57⟩
def w59 : CoreUnwindRelation.Point := ⟨s59,w52.machine,[],maps54⟩
def w60 : CoreUnwindRelation.Point := ⟨s60,.eval (attach writeTarget lexicalTail),[],[]⟩
def w61 : CoreUnwindRelation.Point := ⟨s61,w60.machine,[],maps61⟩
def w62 : CoreUnwindRelation.Point := ⟨s62,w60.machine,[],maps61⟩

private theorem app52 : SilentMapped graph [] [] [] maps52 (isolate s51 []) (isolate s52 maps52) callTarget :=
  application_entry_same_target_mapped (base := isolate s51 []) ordered
    (rfl : graph.node 12 = some (node 12)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 8 = .ok (.variable 3))
    (rfl : CoreTranslation.translateFuel graph 2 [] 11 = .ok (.pair (.variable 4) (.integer 7)))
    current_parts.2 setter_related.closed functionPlain rfl .nil
private theorem value53 : TransportMapped graph [] [] maps52 maps52 (isolate s52 maps52) (isolate s53 maps52) callTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s52 maps52)
    (rfl : graph.node 8 = some (node 8)) rfl current_parts.2.app_components.1 setter_related.closed (framesOf maps52)
  have equal := Option.some.inj (lookup.symm.trans (rfl : bodyEnv.lookup 3 = some setterValue))
  cases equal
  have frame : PlainFrameRel graph [] [] (.applyFunction 11 bodyEnv) functionPlain :=
    .applyFunction (rfl : CoreTranslation.translateFuel graph 2 [] 11 = .ok (.pair (.variable 4) (.integer 7))) current_parts.2.app_components.2
  exact value_entry_mapped witness rfl rfl (prepend_mapped frame setter_related.closed (pushed_mapped .nil) .none)
private theorem app54 : SilentMapped graph [] [] maps52 maps54 (isolate s53 maps52) (isolate s54 maps54) callTarget :=
  application_argument_same_target_mapped (base := isolate s53 maps52)
    (rfl : CoreTranslation.translateFuel graph 2 [] 11 = .ok (.pair (.variable 4) (.integer 7)))
    current_parts.2.app_components.2 setter_related pair_closed functionPlain argumentPlain rfl rfl rfl .nil .none
private theorem argument_stack : OrdinaryWithMaps graph [] maps54 pairCode .none callTarget.expression .none .nil :=
  prepend_mapped (plain := argumentPlain) (.applyArgument setter_related) pair_closed (pushed_mapped .nil) .none
private theorem left_frame : PlainFrameRel graph [] [] (.tupleLeft 10 bodyEnv) leftPlain :=
  .tupleLeft (rfl : CoreTranslation.translateFuel graph 2 [] 10 = .ok (.integer 7)) integer_saved
private theorem right_frame : PlainFrameRel graph [] [] (.tupleRight (.handle 0)) rightPlain := .tupleRight ValueRel.handle
private theorem tuple55 : SilentMapped graph [] [] maps54 maps55 (isolate s54 maps54) (isolate s55 maps55) callTarget := by
  exact ⟨rfl,(tuple_entry_decreases (base := isolate s54 maps54) ordered (rfl : graph.node 11 = some (node 11)) rfl (framesOf maps54)).2,
    rfl,⟨rfl,pairCode,.none,.evaluate (rfl : CoreTranslation.translateFuel graph 3 [] 11 = .ok (.pair (.variable 4) (.integer 7))) current_parts.2.app_components.2,argument_stack⟩,
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
  tuple_allocation_mapped (base := isolate s58 maps57) ValueRel.handle ValueRel.integer rightPlain rfl argument_stack .none []
private theorem allocation_extension : HeapExtends s58.heap s59.heap :=
  (CoreAdministrativeSteps.tuple_allocate (base := isolate s58 maps57)
    (ValueRel.handle (graph := graph) (owners := []) (heap := [])) (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := 7)) (framesOf maps54)).2.1
private theorem location_related : ValueRel graph [] allocated (.location 0) pairCode := .location rfl .handle .integer
private theorem beta60 : CoreUnwindRelation.Link graph w59 w60 ∧ RawStep (attach callTarget lexicalTail) (attach writeTarget lexicalTail) [] [] := by
  have function := setter_related.heap_weaken allocation_extension
  obtain ⟨before,next,step,after⟩ := beta_complete_mapped (base := isolate s59 maps54)
    (show ValueRel graph [] allocated setterValue (.lambda 2 (.perform (.cell (.activation 0)) 1 (.variable 2))) from function)
    location_related argumentPlain rfl .nil .none []
  have carrier := current_parts.1.heap_weaken allocation_extension
  have current : CoreUnwindRelation.Related graph w59 := .runningCleanup carrier before rfl
  have successor : CoreUnwindRelation.Related graph w60 := .runningCleanup carrier after rfl
  have rawStep : RawStep (attach callTarget lexicalTail) (attach writeTarget lexicalTail) [] [] :=
    .beta 2 (.perform (.cell (.activation 0)) 1 (.variable 2)) pairCode .none lexicalTail location_related.closed function.closed
  exact ⟨.positive current rfl (CoreUnwindRelation.ordinary_step rawStep trivial) successor,rawStep⟩
private theorem setter_body : EnvCloses graph [] allocated setterEnv (.perform (.cell (.bound 0)) 1 (.variable 2)) writeTarget.expression := by
  obtain ⟨fuel,rawBody,translated,saved,_⟩ := setter_related.closure_view
  have equal := unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 6 = .ok (.perform (.cell (.bound 0)) 1 (.variable 2)))
  cases equal
  exact (saved.heap_weaken allocation_extension).beta_argument location_related
private theorem request61 : SilentMapped graph [] [] [] maps61 (isolate s60 []) (isolate s61 maps61) writeTarget :=
  request_entry_same_target_mapped (requested := .cell 0) (base := isolate s60 []) ordered (rfl : graph.node 6 = some (node 6)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 5 = .ok (.variable 2)) setter_body pair_closed requestPlain rfl .nil
private theorem value62 : TransportMapped graph [] [] maps61 maps61 (isolate s61 maps61) (isolate s62 maps61) writeTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s61 maps61)
    (rfl : graph.node 5 = some (node 5)) rfl (perform_components setter_body).2 pair_closed (framesOf maps61)
  have equal := Option.some.inj (lookup.symm.trans (rfl : setterEnv.lookup 2 = some (.location 0)))
  cases equal
  have frame : CoreRequestFrames.RequestRel graph [] allocated (.request (.cell (.bound 0)) 1 setterEnv) requestPlain :=
    .operand (requested := .cell 0) (perform_header_at setter_body _ _ _ (.cell (.activation 0)) pairCode rfl rfl) rfl
  exact value_entry_mapped witness rfl rfl (prepend_request frame pair_closed (pushed_mapped .nil) .none)

private theorem carrier7 : RunningTail graph allocated physicalTail lexicalTail := current_parts.1.heap_weaken allocation_extension
private theorem link52 : CoreUnwindRelation.Link graph w51 w52 :=
  .runningAdministration current_parts.1 (.traversal app52 rfl) rfl rfl rfl
private theorem link53 : CoreUnwindRelation.Link graph w52 w53 :=
  .runningAdministration current_parts.1 (.value value53 rfl) rfl rfl rfl
private theorem link54 : CoreUnwindRelation.Link graph w53 w54 :=
  .runningAdministration current_parts.1 (.traversal app54 rfl) rfl rfl rfl
private theorem link55 : CoreUnwindRelation.Link graph w54 w55 :=
  .runningAdministration current_parts.1 (.traversal tuple55 rfl) rfl rfl rfl
private theorem link56 : CoreUnwindRelation.Link graph w55 w56 :=
  .runningAdministration current_parts.1 (.value value56 rfl) rfl rfl rfl
private theorem link57 : CoreUnwindRelation.Link graph w56 w57 :=
  .runningAdministration current_parts.1 (.traversal tuple57 rfl) rfl rfl rfl
private theorem link58 : CoreUnwindRelation.Link graph w57 w58 :=
  .runningAdministration current_parts.1 (.value value58 rfl) rfl rfl rfl
private theorem link59 : CoreUnwindRelation.Link graph w58 w59 :=
  .runningAdministration current_parts.1 (.allocation allocate59 allocation_extension) rfl rfl rfl
private theorem link61 : CoreUnwindRelation.Link graph w60 w61 :=
  .runningAdministration carrier7 (.traversal request61 rfl) rfl rfl rfl
private theorem link62 : CoreUnwindRelation.Link graph w61 w62 :=
  .runningAdministration carrier7 (.value value62 rfl) rfl rfl rfl

def secondOutside7 : List MappedFrame := [(clauseMaps,.bind 10 37 clauseEnv),([],.clauseBoundary 0 0 0 0 none),
  ([],.bind 12 44 methodsEnv),([],.resourceBoundary 48 0 7)]
def secondTail7 : Stack := .push (.plain postPlain) (.spent 0 .unit .none (.push (.plain handlerPlain) (.push (.cell 0 7 .none .integer) .nil)))
def closingTailMaps7 : List MappedFrame := ([],.clauseBoundary 0 0 0 1 none)::secondOutside7
def physicalTail7 : List CoreMachine.Frame := .cleanupCompletion 0 .unit::.closeCompletion 0::framesOf closingTailMaps7
def lexicalTail7 : Stack := .push (.unwinding actionData) (.push (.handler handlerData)
  (.push (.closing 0 falseScope) (.spent 1 .unit .none secondTail7)))
def s63 : CoreMachine.State := { s62 with control := .returned .unit,frames := physicalTail7,observations := s62.observations ++ [.written 0 7] }
def w63 : CoreUnwindRelation.Point := ⟨s63,.eval ⟨.unit,.none,lexicalTail7⟩,[],[]⟩

private theorem outside_write : WriteCut graph [] 0 0 7 secondOutside secondTail secondOutside7 secondTail7 := by
  have outside := second_capture_parts.2
  cases outside with
  | cons post rest =>
    generalize targetEq : Stack.spent 0 .unit .none (.push (.plain handlerPlain) cell) = target at rest
    cases rest with
    | spent header rest =>
      obtain ⟨_,answerEq,scopeEq,restEq⟩ := Stack.spent.inj targetEq
      rw [← restEq] at rest
      cases rest with
      | cons caller rest =>
        cases rest with
        | boundary boundary rest =>
          cases boundary with
          | cell known kind =>
            have update := WriteCut.spent (ticket := 0) header
              (WriteCut.push (.ordinary caller) (by decide) (WriteCut.hit (owners := []) (scope := .none) (answer := .integer) (identity := 0) (old := 0) (new := 7) known kind rest))
            rw [← answerEq,← scopeEq] at update
            exact WriteCut.push (.ordinary post) (by decide) update
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
private theorem delayed_parts : CoreCleanupFrames.CleanupRel graph [] [] (.cleanupBoundary 27 callbackEnv 0) actionData ∧
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

private theorem updated_tail : RunningTail graph allocated physicalTail7 lexicalTail7 ∧ CellUpdate 0 0 7 lexicalTail lexicalTail7 := by
  have outside := WriteCut.spent (ticket := 1) (first_capture_parts.1.heap_weaken allocation_extension)
    (outside_write.heap_weaken allocation_extension)
  exact running_write (data := actionData) (pending := .bind 6 22 nextEnv)
    (action := 27) (environment := callbackEnv) (closing := []) (closeIdentity := 0) (closeScope := falseScope)
    (second_capture_parts.1.heap_weaken allocation_extension)
    (delayed_parts.1.heap_weaken allocation_extension) (delayed_parts.2.heap_weaken allocation_extension)
    outside closing_projection (by
      intro tail changed update
      exact .push (by decide) update)
private theorem write63 : CoreUnwindRelation.Link graph w62 w63 ∧ RawStep (attach writeTarget lexicalTail) ⟨.unit,.none,lexicalTail7⟩ [] [] := by
  have successor : CoreUnwindRelation.Related graph w63 := .runningCleanup (target := ⟨.unit,.none,.nil⟩) updated_tail.1
    ⟨rfl,.unit,.none,.returned .unit,pushed_mapped .nil⟩ rfl
  have rawStep : RawStep (attach writeTarget lexicalTail) ⟨.unit,.none,lexicalTail7⟩ [] [] :=
    .writeCell 0 0 7 .none lexicalTail lexicalTail7 updated_tail.2
  exact ⟨.positive (.runningCleanup carrier7 value62.successor rfl) rfl
    (CoreUnwindRelation.ordinary_step rawStep trivial) successor,rawStep⟩

theorem callback_to_cell_write : CoreUnwindRelation.Chain graph w51 [w52,w53,w54,w55,w56,w57,w58,w59,w60,w61,w62,w63] w63 :=
  .next link52 (.next link53 (.next link54 (.next link55 (.next link56 (.next link57 (.next link58
    (.next link59 (.next beta60.1 (.next link61 (.next link62 (.last write63.1)))))))))))

theorem exported_cleanup_write_prefix : CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift p0)
    (((([p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20,r21,r22,r23,r24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35,u36,u37,u38,u39,u40].map CoreUnwindRelation.lift) ++
      [CoreUnwindRelation.lift v41,CoreUnwindRelation.lift v42,CoreUnwindRelation.lift v43,v44,v45]) ++
      [w46,w47,w48,w49,w50,w51]) ++ [w52,w53,w54,w55,w56,w57,w58,w59,w60,w61,w62,w63]) w63 :=
  CoreUnwindRelation.chain_append exported_cleanup_run_prefix callback_to_cell_write

theorem reached_cell_write_related : CoreUnwindRelation.Related graph w63 := exported_cleanup_write_prefix.endpoints.2

theorem exported_cleanup_write_steps : CoreAllocationHistory.Steps graph 63 (CoreMachine.initial graph) s63 :=
  exported_cleanup_write_prefix.core_steps

theorem exported_cleanup_write_history : CoreAllocationHistory.History s63 :=
  CoreAllocationHistory.initial_steps_history graph exported_cleanup_write_steps

theorem cleanup_write_ledger : CoreUnwindRelation.Trace (.eval (attach CoreCleanupRunPrefix.bodyTarget lexicalTail))
    (.eval ⟨.unit,.none,lexicalTail7⟩) [] [] :=
  .next (.evaluate beta60.2 trivial) (.next (.evaluate write63.2 trivial) (.refl _))

theorem exported_cleanup_write_ledger : CoreUnwindRelation.Trace (.eval rootTarget)
    (.eval ⟨.unit,.none,lexicalTail7⟩)
    [.resource 0,.cleanup 0,.ticket 0,.ticket 1,.close 0] [.ticket 1,.ticket 0] := by
  simpa using exported_cleanup_run_ledger.append cleanup_write_ledger

theorem cell_write_exact : s63.heap = [.pair (.handle 0) (.integer 7)] ∧
    s63.observations.count (.written 0 7) = 1 ∧ s63.observations.count (.cleanupStarted 0) = 1 ∧
    s63.observations.contains (.cleanupFinished 0) = false ∧ s63.observations.contains (.closeFinished 0) = false :=
  ⟨rfl,by decide,by decide,by decide,by decide⟩

theorem cell_selection_exact : CoreMachine.findInterpreter graph (.cell (.activation 0)) physicalTail =
    .ok (.cell ⟨[.cleanupCompletion 0 .unit,.closeCompletion 0,.clauseBoundary 0 0 0 1 none,
      .bind 10 37 clauseEnv,.clauseBoundary 0 0 0 0 none,.bind 12 44 methodsEnv],48,0,0,[]⟩) := rfl

theorem wrong_handle_rejected : CoreMachine.cellOperand [.pair (.handle 1) (.integer 7)] 1 (.location 0) = .ok (1,some 7) ∧
    CoreMachine.next graph { s62 with heap := [.pair (.handle 1) (.integer 7)] } = .rejected .invalidCellOperand := ⟨rfl,rfl⟩

/-- Allocation transport cannot authorize an unchanged running state. -/
theorem unchanged_running_rejected : ¬ Administrative graph [] [] maps57 maps57 s58 s58 callTarget := by
  intro witness
  exact Nat.lt_irrefl _ witness.components.2.2.2

#print axioms unchanged_running_rejected
#print axioms callback_to_cell_write
#print axioms exported_cleanup_write_prefix
#print axioms reached_cell_write_related
#print axioms exported_cleanup_write_steps
#print axioms exported_cleanup_write_history
#print axioms cleanup_write_ledger
#print axioms exported_cleanup_write_ledger
#print axioms cell_write_exact
#print axioms cell_selection_exact
#print axioms wrong_handle_rejected
#print axioms outside_write
#print axioms allocation_extension
#print axioms beta60
#print axioms current_parts
#print axioms setter_related
end Ash.OneShot.CoreCleanupWritePrefix
