import CoreCleanupFinishPrefix

/-! Finish the same initial execution through post-resume write11, getter read11
and resource release. No M4 admission or general simulation is claimed. -/
namespace Ash.OneShot.CoreFinalPrefix
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack CoreStrictPotential
  CoreAdministrativeTransport CoreCleanupRunFrames CoreCellWriteFrames CoreCleanupFinishPrefix
  CoreCleanupWritePrefix CoreInitialPrefix CoreHandlerPrefix CoreCleanupEntry CoreCaptureEntry.Exported
  CoreResumeEntry.Exported CoreSecondCapture CoreDiscardPrefix CoreExportedFixture CoreRequestFrames CoreEffectFrames
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
def pairCode : Code := .pair (.resourceRef (.activation 0)) (.integer 11)
def callTarget : Configuration := ⟨.app setter pairCode,ticketScope,ordinaryTail7⟩
def writeTarget : Configuration := ⟨.perform (.cell (.activation 0)) 1 pairCode,.none,ordinaryTail7⟩
def bodyEnv : CoreMachine.Environment := .binding 10 .unit clauseEnv
def setterValue : CoreMachine.Value := .closure 2 6 getterEnv
def setterEnv : CoreMachine.Environment := .binding 2 (.location 1) getterEnv
def allocated11 : Heap := allocated ++ [.pair (.handle 0) (.integer 11)]
private theorem current_parts : PushedWithMaps graph allocated outsideMaps7 ordinaryTail7 ∧
    EnvCloses graph clauseMaps allocated bodyEnv (.app (.variable 3) (.pair (.variable 4) (.integer 11))) callTarget.expression := by
  obtain ⟨fuel,rawSuffix,translated,saved,ready,tail⟩ := post_parts
  have equal := unique translated (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 37 = .ok (.app (.variable 3) (.pair (.variable 4) (.integer 11))))
  cases equal
  exact ⟨tail,saved.beta_argument ValueRel.unit⟩
private theorem setter_related : ValueRel graph clauseMaps allocated setterValue setter := by
  obtain ⟨value,lookup,related⟩ := current_parts.2.app_components.1.lookup (by
    change ClosedValue (.lambda 2 (.perform (.cell (.activation 0)) 1 (.variable 2)))
    simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.Effect.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies,Syntax.without])
  have equal := Option.some.inj (lookup.symm.trans (rfl : bodyEnv.lookup 3 = some setterValue))
  cases equal
  exact related
private theorem pair_closed : ClosedValue pairCode := by
  simp [pairCode,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies]
private theorem handle_saved : EnvCloses graph clauseMaps allocated bodyEnv (.variable 4) (.resourceRef (.activation 0)) :=
  (pair_components current_parts.2.app_components.2).1
private theorem integer_saved : EnvCloses graph clauseMaps allocated bodyEnv (.integer 11) (.integer 11) :=
  (pair_components current_parts.2.app_components.2).2

def functionPlain : PlainData := ⟨.appFunction pairCode,ticketScope,.function (.product (.reference 0) .integer) .unit [.cell 0] [],.unit,[],rfl⟩
def argumentPlain : PlainData := ⟨.appArgument setter,ticketScope,.product (.reference 0) .integer,.unit,[],by decide⟩
def leftPlain : PlainData := ⟨.pairLeft (.integer 11),ticketScope,.reference 0,.product (.reference 0) .integer,[],rfl⟩
def rightPlain : PlainData := ⟨.pairRight (.resourceRef (.activation 0)),ticketScope,.integer,.product (.reference 0) .integer,[],by decide⟩
def requestPlain : PlainData := ⟨.perform (.cell (.activation 0)) 1,.none,.product (.reference 0) .integer,.unit,[],rfl⟩
def s68 : CoreMachine.State := { s67 with control := .evaluate 33 bodyEnv,frames := .applyFunction 36 bodyEnv::framesOf outsideMaps7,observations := s67.observations ++ [.entered 37] }
def s69 : CoreMachine.State := { s68 with control := .returned setterValue,observations := s68.observations ++ [.entered 33] }
def s70 : CoreMachine.State := { s69 with control := .evaluate 36 bodyEnv,frames := .applyArgument setterValue::framesOf outsideMaps7 }
def s71 : CoreMachine.State := { s70 with control := .evaluate 34 bodyEnv,frames := .tupleLeft 35 bodyEnv::s70.frames,observations := s70.observations ++ [.entered 36] }
def s72 : CoreMachine.State := { s71 with control := .returned (.handle 0),observations := s71.observations ++ [.entered 34] }
def s73 : CoreMachine.State := { s72 with control := .evaluate 35 bodyEnv,frames := .tupleRight (.handle 0)::s70.frames }
def s74 : CoreMachine.State := { s73 with control := .returned (.integer 11),observations := s73.observations ++ [.entered 35] }
def s75 : CoreMachine.State := { s74 with control := .returned (.location 1),frames := s70.frames,heap := allocated11 }
def s76 : CoreMachine.State := { s75 with control := .evaluate 6 setterEnv,frames := framesOf outsideMaps7 }
def s77 : CoreMachine.State := { s76 with control := .evaluate 5 setterEnv,frames := .request (.cell (.bound 0)) 1 setterEnv::framesOf outsideMaps7,observations := s76.observations ++ [.entered 6] }
def s78 : CoreMachine.State := { s77 with control := .returned (.location 1),observations := s77.observations ++ [.entered 5] }
def maps68 : List MappedFrame := (clauseMaps,.applyFunction 36 bodyEnv)::outsideMaps7
def maps70 : List MappedFrame := (clauseMaps,.applyArgument setterValue)::outsideMaps7
def maps71 : List MappedFrame := (clauseMaps,.tupleLeft 35 bodyEnv)::maps70
def maps73 : List MappedFrame := (clauseMaps,.tupleRight (.handle 0))::maps70
def maps77 : List MappedFrame := ([],.request (.cell (.bound 0)) 1 setterEnv)::outsideMaps7
def w68 : CoreUnwindRelation.Point := ⟨s68,.eval callTarget,clauseMaps,maps68⟩
def w69 : CoreUnwindRelation.Point := ⟨s69,w68.machine,clauseMaps,maps68⟩
def w70 : CoreUnwindRelation.Point := ⟨s70,w68.machine,clauseMaps,maps70⟩
def w71 : CoreUnwindRelation.Point := ⟨s71,w68.machine,clauseMaps,maps71⟩
def w72 : CoreUnwindRelation.Point := ⟨s72,w68.machine,clauseMaps,maps71⟩
def w73 : CoreUnwindRelation.Point := ⟨s73,w68.machine,clauseMaps,maps73⟩
def w74 : CoreUnwindRelation.Point := ⟨s74,w68.machine,clauseMaps,maps73⟩
def w75 : CoreUnwindRelation.Point := ⟨s75,w68.machine,clauseMaps,maps70⟩
def w76 : CoreUnwindRelation.Point := ⟨s76,.eval writeTarget,[],outsideMaps7⟩
def w77 : CoreUnwindRelation.Point := ⟨s77,w76.machine,[],maps77⟩
def w78 : CoreUnwindRelation.Point := ⟨s78,w76.machine,[],maps77⟩

private theorem app68 : SilentMapped graph clauseMaps clauseMaps outsideMaps7 maps68 (isolate s67 outsideMaps7) (isolate s68 maps68) callTarget :=
  application_entry_same_target_mapped (base := isolate s67 outsideMaps7) ordered
    (rfl : graph.node 37 = some (node 37)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 33 = .ok (.variable 3))
    (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 36 = .ok (.pair (.variable 4) (.integer 11)))
    current_parts.2 setter_related.closed functionPlain rfl current_parts.1
private theorem value69 : TransportMapped graph clauseMaps clauseMaps maps68 maps68 (isolate s68 maps68) (isolate s69 maps68) callTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s68 maps68)
    (rfl : graph.node 33 = some (node 33)) rfl current_parts.2.app_components.1 setter_related.closed (framesOf maps68)
  have equal := Option.some.inj (lookup.symm.trans (rfl : bodyEnv.lookup 3 = some setterValue))
  cases equal
  have frame : PlainFrameRel graph clauseMaps allocated (.applyFunction 36 bodyEnv) functionPlain :=
    .applyFunction (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 36 = .ok (.pair (.variable 4) (.integer 11))) current_parts.2.app_components.2
  exact value_entry_mapped witness rfl rfl (prepend_mapped frame setter_related.closed (pushed_mapped current_parts.1) .none)
private theorem app70 : SilentMapped graph clauseMaps clauseMaps maps68 maps70 (isolate s69 maps68) (isolate s70 maps70) callTarget :=
  application_argument_same_target_mapped (base := isolate s69 maps68)
    (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 36 = .ok (.pair (.variable 4) (.integer 11)))
    current_parts.2.app_components.2 setter_related pair_closed functionPlain argumentPlain rfl rfl rfl current_parts.1 .none
private theorem argument_stack : OrdinaryWithMaps graph allocated maps70 pairCode ticketScope callTarget.expression ticketScope ordinaryTail7 :=
  prepend_mapped (plain := argumentPlain) (.applyArgument setter_related) pair_closed (pushed_mapped current_parts.1) ticketScope
private theorem left_frame : PlainFrameRel graph clauseMaps allocated (.tupleLeft 35 bodyEnv) leftPlain :=
  .tupleLeft (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 35 = .ok (.integer 11)) integer_saved
private theorem right_frame : PlainFrameRel graph clauseMaps allocated (.tupleRight (.handle 0)) rightPlain := .tupleRight ValueRel.handle
private theorem tuple71 : SilentMapped graph clauseMaps clauseMaps maps70 maps71 (isolate s70 maps70) (isolate s71 maps71) callTarget := by
  exact ⟨rfl,(tuple_entry_decreases (base := isolate s70 maps70) ordered (rfl : graph.node 36 = some (node 36)) rfl (framesOf maps70)).2,
    rfl,⟨rfl,pairCode,ticketScope,.evaluate (rfl : CoreTranslation.translateFuel graph 3 clauseMaps 36 = .ok (.pair (.variable 4) (.integer 11))) current_parts.2.app_components.2,argument_stack⟩,
    ⟨rfl,_,.none,.evaluate (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 34 = .ok (.variable 4)) handle_saved,
      prepend_mapped left_frame (ValueRel.handle (graph := graph) (owners := clauseMaps) (heap := allocated)).closed argument_stack .none⟩⟩
private theorem value72 : TransportMapped graph clauseMaps clauseMaps maps71 maps71 (isolate s71 maps71) (isolate s72 maps71) callTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s71 maps71)
    (rfl : graph.node 34 = some (node 34)) rfl handle_saved (ValueRel.handle (graph := graph) (owners := clauseMaps) (heap := allocated)).closed (framesOf maps71)
  have equal := Option.some.inj (lookup.symm.trans (rfl : bodyEnv.lookup 4 = some (.handle 0)))
  cases equal
  exact value_entry_mapped witness rfl rfl
    (prepend_mapped left_frame (ValueRel.handle (graph := graph) (owners := clauseMaps) (heap := allocated)).closed argument_stack .none)
private theorem tuple73 : SilentMapped graph clauseMaps clauseMaps maps71 maps73 (isolate s72 maps71) (isolate s73 maps73) callTarget := by
  exact ⟨rfl,(tuple_right_decreases (graph := graph) (isolate s72 maps71) (framesOf maps70)).2,rfl,
    value72.successor,
    ⟨rfl,_,.none,.evaluate (rfl : CoreTranslation.translateFuel graph 2 clauseMaps 35 = .ok (.integer 11)) integer_saved,
      prepend_mapped right_frame (ValueRel.integer (graph := graph) (owners := clauseMaps) (heap := allocated) (value := 11)).closed argument_stack .none⟩⟩
private theorem value74 : TransportMapped graph clauseMaps clauseMaps maps73 maps73 (isolate s73 maps73) (isolate s74 maps73) callTarget := by
  obtain ⟨witness,_⟩ := CoreAdministrativeSteps.integer_evaluate (base := isolate s73 maps73)
    (rfl : graph.node 35 = some (node 35)) rfl integer_saved (framesOf maps73)
  exact value_entry_mapped witness rfl rfl
    (prepend_mapped right_frame (ValueRel.integer (graph := graph) (owners := clauseMaps) (heap := allocated) (value := 11)).closed argument_stack .none)
private theorem allocate75 : TransportMapped graph clauseMaps clauseMaps maps73 maps70 (isolate s74 maps73) (isolate s75 maps70) callTarget :=
  tuple_allocation_mapped (base := isolate s74 maps73) ValueRel.handle ValueRel.integer rightPlain rfl argument_stack .none clauseMaps
private theorem allocation_extension : HeapExtends s74.heap s75.heap :=
  (CoreAdministrativeSteps.tuple_allocate (base := isolate s74 maps73)
    (ValueRel.handle (graph := graph) (owners := clauseMaps) (heap := allocated)) (ValueRel.integer (graph := graph) (owners := clauseMaps) (heap := allocated) (value := 11)) (framesOf maps70)).2.1
private theorem location_related : ValueRel graph [] allocated11 (.location 1) pairCode := .location rfl .handle .integer
private theorem beta76 : CoreUnwindRelation.Link graph w75 w76 ∧ RawStep callTarget writeTarget [] [] := by
  have function := setter_related.heap_weaken allocation_extension
  obtain ⟨before,next,step,after⟩ := beta_complete_mapped (base := isolate s75 maps70)
    (show ValueRel graph clauseMaps allocated11 setterValue (.lambda 2 (.perform (.cell (.activation 0)) 1 (.variable 2))) from function)
    (location_related.owner_transport clauseMaps) argumentPlain rfl (current_parts.1.heap_weaken allocation_extension) .none clauseMaps
  exact ⟨.positive (.eval before) next (CoreUnwindRelation.ordinary_step step trivial) (.eval after),step⟩
private theorem setter_body : EnvCloses graph [] allocated11 setterEnv (.perform (.cell (.bound 0)) 1 (.variable 2)) writeTarget.expression := by
  obtain ⟨fuel,rawBody,translated,saved,_⟩ := setter_related.closure_view
  have equal := unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 6 = .ok (.perform (.cell (.bound 0)) 1 (.variable 2)))
  cases equal
  exact (saved.heap_weaken allocation_extension).beta_argument location_related
private theorem request77 : SilentMapped graph [] [] outsideMaps7 maps77 (isolate s76 outsideMaps7) (isolate s77 maps77) writeTarget :=
  request_entry_same_target_mapped (requested := .cell 0) (base := isolate s76 outsideMaps7) ordered (rfl : graph.node 6 = some (node 6)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 5 = .ok (.variable 2)) setter_body pair_closed requestPlain rfl (current_parts.1.heap_weaken allocation_extension)
private theorem value78 : TransportMapped graph [] [] maps77 maps77 (isolate s77 maps77) (isolate s78 maps77) writeTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := isolate s77 maps77)
    (rfl : graph.node 5 = some (node 5)) rfl (perform_components setter_body).2 pair_closed (framesOf maps77)
  have equal := Option.some.inj (lookup.symm.trans (rfl : setterEnv.lookup 2 = some (.location 1)))
  cases equal
  have frame : CoreRequestFrames.RequestRel graph [] allocated11 (.request (.cell (.bound 0)) 1 setterEnv) requestPlain :=
    .operand (requested := .cell 0) (perform_header_at setter_body _ _ _ (.cell (.activation 0)) pairCode rfl rfl) rfl
  exact value_entry_mapped witness rfl rfl (prepend_request frame pair_closed (pushed_mapped (current_parts.1.heap_weaken allocation_extension)) .none)


private theorem link68 : CoreUnwindRelation.Link graph w67 w68 := .traversal app68
private theorem link69 : CoreUnwindRelation.Link graph w68 w69 := .value value69
private theorem link70 : CoreUnwindRelation.Link graph w69 w70 := .traversal app70
private theorem link71 : CoreUnwindRelation.Link graph w70 w71 := .traversal tuple71
private theorem link72 : CoreUnwindRelation.Link graph w71 w72 := .value value72
private theorem link73 : CoreUnwindRelation.Link graph w72 w73 := .traversal tuple73
private theorem link74 : CoreUnwindRelation.Link graph w73 w74 := .value value74
private theorem link75 : CoreUnwindRelation.Link graph w74 w75 := .value allocate75
private theorem link77 : CoreUnwindRelation.Link graph w76 w77 := .traversal request77
private theorem link78 : CoreUnwindRelation.Link graph w77 w78 := .value value78

def getterMaps11 : List MappedFrame := [([],.bind 12 44 methodsEnv),([],.resourceBoundary 48 0 11)]
def callerMaps11 : List MappedFrame := ([],.clauseBoundary 0 0 0 0 none)::getterMaps11
def cellMaps11 : List MappedFrame := [([],.resourceBoundary 48 0 11)]
def cell11 : Stack := .push (.cell 0 11 .none .integer) .nil
def getterTail11 : Stack := .push (.plain handlerPlain) cell11
def callerTail11 : Stack := .spent 0 .unit .none getterTail11
def s79 : CoreMachine.State := { s78 with control := .returned .unit,frames := framesOf callerMaps11,observations := s78.observations ++ [.written 0 11] }
def s80 : CoreMachine.State := { s79 with frames := framesOf getterMaps11,observations := s79.observations ++ [.clauseReturned 0] }
def getterCaller : CoreMachine.Environment := .binding 12 .unit methodsEnv
def s81 : CoreMachine.State := { s80 with control := .evaluate 44 getterCaller,frames := framesOf cellMaps11 }
def getterCall : Configuration := ⟨.app getter (.resourceRef (.activation 0)),.none,cell11⟩
def w79 : CoreUnwindRelation.Point := ⟨s79,.eval ⟨.unit,.none,callerTail11⟩,[],callerMaps11⟩
def w80 : CoreUnwindRelation.Point := ⟨s80,.eval ⟨.unit,.none,getterTail11⟩,[],getterMaps11⟩
def w81 : CoreUnwindRelation.Point := ⟨s81,.eval getterCall,[],cellMaps11⟩

private theorem caller_write : WriteCut graph allocated11 0 7 11 outsideMaps7 ordinaryTail7 callerMaps11 callerTail11 := by
  have tail := current_parts.1.heap_weaken allocation_extension
  generalize targetEq : ordinaryTail7 = target at tail
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
                    (WriteCut.push (.ordinary caller) (by decide)
                      (WriteCut.hit (owners := []) (scope := .none) (answer := .integer) (identity := 0) (old := 7) (new := 11) known kind rest))
                  rw [← answerEq,← scopeEq] at cut
                  rw [← answerEq,← scopeEq,← restEq]
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

theorem write11_target : RawStep writeTarget ⟨.unit,.none,callerTail11⟩ [] [] :=
  .writeCell 0 7 11 .none ordinaryTail7 callerTail11 caller_write.components.2.2
private theorem write79 : CoreUnwindRelation.Link graph w78 w79 :=
  .positive (.eval value78.successor) rfl (CoreUnwindRelation.ordinary_step write11_target trivial)
    (.eval ⟨rfl,.unit,.none,.returned .unit,pushed_mapped caller_write.components.2.1⟩)
private theorem getter_tail : PushedWithMaps graph allocated11 getterMaps11 getterTail11 := by
  have tail := caller_write.components.2.1
  generalize targetEq : callerTail11 = target at tail
  cases tail with
  | spent header tail => exact (Stack.spent.inj targetEq).2.2.2.symm ▸ tail
  | cons frame tail => cases frame
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | cleanup frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

theorem return_first_spent_target : RawStep ⟨.unit,.none,callerTail11⟩ ⟨.unit,.none,getterTail11⟩ [] [] :=
  .leaveClause 0 .unit .unit (ValueRel.unit (graph := graph) (owners := []) (heap := allocated11)).closed .none .none getterTail11
private theorem return80 : CoreUnwindRelation.Link graph w79 w80 :=
  .positive write79.endpoints.2 rfl (CoreUnwindRelation.ordinary_step return_first_spent_target trivial)
    (.eval ⟨rfl,.unit,.none,.returned .unit,pushed_mapped getter_tail⟩)
private theorem getter_parts : ∃ fuel rawSuffix,
    CoreTranslation.translateFuel graph fuel [] 44 = .ok rawSuffix ∧
    EnvCloses graph [] allocated11 methodsEnv (.lambda 12 rawSuffix) (.lambda 12 (close2 (raw 44))) ∧
    ClosedExcept 12 (close2 (raw 44)) ∧ PushedWithMaps graph allocated11 cellMaps11 cell11 := by
  have tail := getter_tail
  cases tail with
  | cons frame tail =>
      change FrameRel graph [] allocated11 (.bind 12 44 methodsEnv) (.bind 12 (close2 (raw 44))) at frame
      cases frame with
      | bind translated saved ready => exact ⟨_,_,translated,saved,ready,tail⟩
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

def getterBindTarget : Configuration := ⟨.bind 12 .unit (close2 (raw 44)),.none,cell11⟩
theorem getter_bind_target : RawStep ⟨.unit,.none,getterTail11⟩ getterBindTarget [] [] ∧ RawStep getterBindTarget getterCall [] [] := by
  obtain ⟨fuel,rawSuffix,translated,saved,ready,tail⟩ := getter_parts
  obtain ⟨_,_,plug,bind,_⟩ := bind_return_mapped (base := s80) translated saved ready
    (ValueRel.unit (graph := graph) (owners := []) (heap := allocated11)) handlerPlain rfl tail .none
  exact ⟨plug,bind⟩
private theorem bind81 : CoreUnwindRelation.Link graph w80 w81 := by
  obtain ⟨fuel,rawSuffix,translated,saved,ready,tail⟩ := getter_parts
  obtain ⟨current,next,plug,bind,successor⟩ := bind_return_mapped (base := s80) translated saved ready
    (ValueRel.unit (graph := graph) (owners := []) (heap := allocated11)) handlerPlain rfl tail .none
  exact .positive (.eval current) next (.next (.evaluate plug trivial) (CoreUnwindRelation.ordinary_step bind trivial)) (.eval successor)
private theorem cell_tail : PushedWithMaps graph allocated11 cellMaps11 cell11 := by
  obtain ⟨_,_,_,_,_,tail⟩ := getter_parts
  exact tail
private theorem getter_current : EnvCloses graph [] allocated11 getterCaller (.app (.variable 11) (.variable 4)) getterCall.expression := by
  obtain ⟨fuel,rawSuffix,translated,saved,_,_⟩ := getter_parts
  have equal := unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 44 = .ok (.app (.variable 11) (.variable 4)))
  cases equal
  exact saved.beta_argument ValueRel.unit
private theorem getter_related : ValueRel graph [] allocated11 (.closure 1 3 acquired) getter := by
  obtain ⟨value,lookup,related⟩ := getter_current.app_components.1.lookup (by
    change ClosedValue (.lambda 1 (.perform (.cell (.activation 0)) 0 (.variable 1)))
    simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Instantiation.Effect.freeNames,Instantiation.ResourceName.freeNames,Code.dependencies,Syntax.without])
  have equal := Option.some.inj (lookup.symm.trans (rfl : getterCaller.lookup 11 = some (.closure 1 3 acquired)))
  cases equal
  exact related

def getterFunction : PlainData := ⟨.appFunction (.resourceRef (.activation 0)),.none,.function (.reference 0) .integer [.cell 0] [],.integer,[],rfl⟩
def getterArgument : PlainData := ⟨.appArgument getter,.none,.reference 0,.integer,[],by decide⟩
def readPlain : PlainData := ⟨.perform (.cell (.activation 0)) 0,.none,.reference 0,.integer,[],rfl⟩
def getterBodyEnv : CoreMachine.Environment := .binding 1 (.handle 0) acquired
def readTarget : Configuration := ⟨.perform (.cell (.activation 0)) 0 (.resourceRef (.activation 0)),.none,cell11⟩
def s82 : CoreMachine.State := { s81 with control := .evaluate 42 getterCaller,frames := .applyFunction 43 getterCaller::framesOf cellMaps11,observations := s81.observations ++ [.entered 44] }
def s83 : CoreMachine.State := { s82 with control := .returned (.closure 1 3 acquired),observations := s82.observations ++ [.entered 42] }
def s84 : CoreMachine.State := { s83 with control := .evaluate 43 getterCaller,frames := .applyArgument (.closure 1 3 acquired)::framesOf cellMaps11 }
def s85 : CoreMachine.State := { s84 with control := .returned (.handle 0),observations := s84.observations ++ [.entered 43] }
def s86 : CoreMachine.State := { s85 with control := .evaluate 3 getterBodyEnv,frames := framesOf cellMaps11 }
def s87 : CoreMachine.State := { s86 with control := .evaluate 2 getterBodyEnv,frames := .request (.cell (.bound 0)) 0 getterBodyEnv::framesOf cellMaps11,observations := s86.observations ++ [.entered 3] }
def s88 : CoreMachine.State := { s87 with control := .returned (.handle 0),observations := s87.observations ++ [.entered 2] }
def s89 : CoreMachine.State := { s88 with control := .returned (.integer 11),frames := framesOf cellMaps11,observations := s88.observations ++ [.read 0 11] }
def s90 : CoreMachine.State := { s89 with frames := [],observations := s89.observations ++ [.released 0] }
def maps82 : List MappedFrame := ([],.applyFunction 43 getterCaller)::cellMaps11
def maps84 : List MappedFrame := ([],.applyArgument (.closure 1 3 acquired))::cellMaps11
def maps87 : List MappedFrame := ([],.request (.cell (.bound 0)) 0 getterBodyEnv)::cellMaps11
def w82 : CoreUnwindRelation.Point := ⟨s82,.eval getterCall,[],maps82⟩
def w83 : CoreUnwindRelation.Point := ⟨s83,w82.machine,[],maps82⟩
def w84 : CoreUnwindRelation.Point := ⟨s84,w82.machine,[],maps84⟩
def w85 : CoreUnwindRelation.Point := ⟨s85,w82.machine,[],maps84⟩
def w86 : CoreUnwindRelation.Point := ⟨s86,.eval readTarget,[],cellMaps11⟩
def w87 : CoreUnwindRelation.Point := ⟨s87,w86.machine,[],maps87⟩
def w88 : CoreUnwindRelation.Point := ⟨s88,w86.machine,[],maps87⟩
def w89 : CoreUnwindRelation.Point := ⟨s89,.eval ⟨.integer 11,.none,cell11⟩,[],cellMaps11⟩
def finalTarget : Configuration := ⟨.integer 11,.none,.nil⟩
def w90 : CoreUnwindRelation.Point := ⟨s90,.eval finalTarget,[],[]⟩

private theorem app82 : SilentMapped graph [] [] cellMaps11 maps82 s81 s82 getterCall :=
  application_entry_same_target_mapped (base := s81) ordered (rfl : graph.node 44 = some (node 44)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 42 = .ok (.variable 11))
    (rfl : CoreTranslation.translateFuel graph 2 [] 43 = .ok (.variable 4)) getter_current getter_related.closed getterFunction rfl cell_tail
private theorem value83 : TransportMapped graph [] [] maps82 maps82 s82 s83 getterCall := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := s82)
    (rfl : graph.node 42 = some (node 42)) rfl getter_current.app_components.1 getter_related.closed (framesOf maps82)
  have equal := Option.some.inj (lookup.symm.trans (rfl : getterCaller.lookup 11 = some (.closure 1 3 acquired)))
  cases equal
  have frame : PlainFrameRel graph [] allocated11 (.applyFunction 43 getterCaller) getterFunction :=
    .applyFunction (rfl : CoreTranslation.translateFuel graph 2 [] 43 = .ok (.variable 4)) getter_current.app_components.2
  exact value_entry_mapped witness rfl rfl (prepend_mapped frame getter_related.closed (pushed_mapped cell_tail) .none)
private theorem argument84 : SilentMapped graph [] [] maps82 maps84 s83 s84 getterCall :=
  application_argument_same_target_mapped (base := s83)
    (rfl : CoreTranslation.translateFuel graph 2 [] 43 = .ok (.variable 4)) getter_current.app_components.2
    getter_related (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed
    getterFunction getterArgument rfl rfl rfl cell_tail .none
private theorem value85 : TransportMapped graph [] [] maps84 maps84 s84 s85 getterCall := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := s84)
    (rfl : graph.node 43 = some (node 43)) rfl getter_current.app_components.2 (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed (framesOf maps84)
  have equal := Option.some.inj (lookup.symm.trans (rfl : getterCaller.lookup 4 = some (.handle 0)))
  cases equal
  have frame : PlainFrameRel graph [] allocated11 (.applyArgument (.closure 1 3 acquired)) getterArgument := .applyArgument getter_related
  exact value_entry_mapped witness rfl rfl (prepend_mapped frame (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed (pushed_mapped cell_tail) .none)
private theorem beta86 : CoreUnwindRelation.Link graph w85 w86 ∧ RawStep getterCall readTarget [] [] := by
  obtain ⟨before,next,step,after⟩ := beta_complete_mapped (base := s85)
    (show ValueRel graph [] allocated11 (.closure 1 3 acquired) (.lambda 1 (.perform (.cell (.activation 0)) 0 (.variable 1))) from getter_related)
    (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)) getterArgument rfl cell_tail .none []
  exact ⟨.positive (.eval before) next (CoreUnwindRelation.ordinary_step step trivial) (.eval after),step⟩
private theorem getter_body : EnvCloses graph [] allocated11 getterBodyEnv (.perform (.cell (.bound 0)) 0 (.variable 1)) readTarget.expression := by
  obtain ⟨fuel,rawBody,translated,saved,_⟩ := getter_related.closure_view
  have equal := unique translated (rfl : CoreTranslation.translateFuel graph 56 [] 3 = .ok (.perform (.cell (.bound 0)) 0 (.variable 1)))
  cases equal
  exact saved.beta_argument ValueRel.handle
private theorem request87 : SilentMapped graph [] [] cellMaps11 maps87 s86 s87 readTarget :=
  request_entry_same_target_mapped (requested := .cell 0) (base := s86) ordered (rfl : graph.node 3 = some (node 3)) rfl
    (rfl : CoreTranslation.translateFuel graph 2 [] 2 = .ok (.variable 1)) getter_body
    (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed readPlain rfl cell_tail
private theorem value88 : TransportMapped graph [] [] maps87 maps87 s87 s88 readTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := s87)
    (rfl : graph.node 2 = some (node 2)) rfl (perform_components getter_body).2
    (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed (framesOf maps87)
  have equal := Option.some.inj (lookup.symm.trans (rfl : getterBodyEnv.lookup 1 = some (.handle 0)))
  cases equal
  have frame : RequestRel graph [] allocated11 (.request (.cell (.bound 0)) 0 getterBodyEnv) readPlain :=
    .operand (requested := .cell 0) (perform_header_at getter_body _ _ _ (.cell (.activation 0)) (.resourceRef (.activation 0)) rfl rfl) rfl
  exact value_entry_mapped witness rfl rfl (prepend_request frame (ValueRel.handle (graph := graph) (owners := []) (heap := allocated11)).closed (pushed_mapped cell_tail) .none)

theorem read11_target : RawStep readTarget ⟨.integer 11,.none,cell11⟩ [] [] := .readCell 0 11 .none cell11 cell11 .hit
private theorem read89 : CoreUnwindRelation.Link graph w88 w89 :=
  .positive (.eval value88.successor) rfl (CoreUnwindRelation.ordinary_step read11_target trivial)
    (.eval ⟨rfl,.integer 11,.none,.returned .integer,pushed_mapped cell_tail⟩)
theorem release_target : RawStep ⟨.integer 11,.none,cell11⟩ finalTarget [] [.resource 0] :=
  .leaveCell 0 11 .integer .none .none (.integer 11) (ValueRel.integer (graph := graph) (owners := []) (heap := allocated11) (value := 11)).closed .nil
private theorem release90 : CoreUnwindRelation.Link graph w89 w90 :=
  .positive read89.endpoints.2 rfl (CoreUnwindRelation.ordinary_step release_target trivial)
    (.eval ⟨rfl,.integer 11,.none,.returned .integer,pushed_mapped .nil⟩)

private theorem link82 : CoreUnwindRelation.Link graph w81 w82 := .traversal app82
private theorem link83 : CoreUnwindRelation.Link graph w82 w83 := .value value83
private theorem link84 : CoreUnwindRelation.Link graph w83 w84 := .traversal argument84
private theorem link85 : CoreUnwindRelation.Link graph w84 w85 := .value value85
private theorem link87 : CoreUnwindRelation.Link graph w86 w87 := .traversal request87
private theorem link88 : CoreUnwindRelation.Link graph w87 w88 := .value value88

theorem post_beta_target : RawStep callTarget writeTarget [] [] := beta76.2
theorem getter_beta_target : RawStep getterCall readTarget [] [] := beta86.2

def finalPoints : List CoreUnwindRelation.Point := [w68,w69,w70,w71,w72,w73,w74,w75,w76,w77,w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90]
theorem caller_to_final : CoreUnwindRelation.Chain graph w67 finalPoints w90 :=
  .next link68 (.next link69 (.next link70 (.next link71 (.next link72 (.next link73 (.next link74
  (.next link75 (.next beta76.1 (.next link77 (.next link78 (.next write79 (.next return80 (.next bind81
  (.next link82 (.next link83 (.next link84 (.next link85 (.next beta86.1 (.next link87 (.next link88
  (.next read89 (.last release90))))))))))))))))))))))

theorem exported_final_prefix : CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift p0) (through67 ++ finalPoints) w90 :=
  CoreUnwindRelation.chain_append exported_cleanup_finish_prefix caller_to_final
theorem reached_final_related : CoreUnwindRelation.Related graph w90 := exported_final_prefix.endpoints.2

theorem exported_final_steps : CoreAllocationHistory.Steps graph 90 (CoreMachine.initial graph) s90 := exported_final_prefix.core_steps

theorem exported_final_history : CoreAllocationHistory.History s90 := CoreAllocationHistory.initial_steps_history graph exported_final_steps

theorem caller_final_ledger : CoreUnwindRelation.Trace w67.machine w90.machine [] [.resource 0] := by
  obtain ⟨plug,bind⟩ := getter_bind_target
  exact .next (.evaluate post_beta_target trivial) (.next (.evaluate write11_target trivial)
    (.next (.evaluate return_first_spent_target trivial) (.next (.evaluate plug trivial) (.next (.evaluate bind trivial)
      (.next (.evaluate getter_beta_target trivial) (.next (.evaluate read11_target trivial)
        (.next (.evaluate release_target trivial) (.refl _))))))))

theorem exported_final_ledger : CoreUnwindRelation.Trace (.eval rootTarget) (.eval finalTarget)
    [.resource 0,.cleanup 0,.ticket 0,.ticket 1,.close 0]
    [.resource 0,.close 0,.cleanup 0,.ticket 1,.ticket 0] := by
  exact (exported_cleanup_write_ledger.append cleanup_completion_ledger).append caller_final_ledger

def completionObservation : CoreMachine.Observation → Bool
  | .cleanupStarted _ | .cleanupFinished _ | .closeStarted _ | .closeFinished _
      | .written _ _ | .read _ _ | .released _ => true
  | _ => false

theorem final_observation_order : s90.observations.filter completionObservation =
    [.closeStarted 0,.cleanupStarted 0,.written 0 7,.cleanupFinished 0,.closeFinished 0,
      .written 0 11,.read 0 11,.released 0] := by decide

theorem final_result_exact : s90.control = .returned (.integer 11) ∧ s90.frames = [] ∧
    s90.heap = [.pair (.handle 0) (.integer 7),.pair (.handle 0) (.integer 11)] ∧
    CoreMachine.next graph s90 = .done (.integer 11) ∧ finalTarget.expression = .integer 11 ∧ finalTarget.stack = .nil :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The final terminal observation is not an extra successful Core transition. -/
theorem final_not_step (after : CoreMachine.State) : ¬ CoreMachine.Step graph s90 after :=
  CoreMachine.done_not_step graph s90 (.integer 11) rfl after

#print axioms post_beta_target
#print axioms write11_target
#print axioms return_first_spent_target
#print axioms getter_bind_target
#print axioms getter_beta_target
#print axioms read11_target
#print axioms release_target
#print axioms caller_to_final
#print axioms exported_final_prefix
#print axioms reached_final_related
#print axioms exported_final_steps
#print axioms exported_final_history
#print axioms caller_final_ledger
#print axioms exported_final_ledger
#print axioms final_observation_order
#print axioms final_result_exact
#print axioms final_not_step
#print axioms caller_write
#print axioms getter_parts
#print axioms getter_related
#print axioms beta86
#print axioms release90
#print axioms current_parts
#print axioms beta76
end Ash.OneShot.CoreFinalPrefix
