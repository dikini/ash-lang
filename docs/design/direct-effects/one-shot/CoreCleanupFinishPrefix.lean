import CoreCleanupWritePrefix

/-! Complete the same running cleanup and close, then restore the exact saved
caller continuation. The target-only retained handler is explicitly advanced. -/
namespace Ash.OneShot.CoreCleanupFinishPrefix
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack CoreUnwindRelation
  CoreCleanupWritePrefix CoreCleanupRunPrefix CoreCleanupRunFrames CoreHandlerPrefix CoreInitialPrefix
  CoreCleanupEntry CoreCaptureEntry.Exported CoreResumeEntry.Exported CoreSecondCapture CoreDiscardPrefix CoreExportedFixture
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def spentTail : Stack := .spent 1 .unit .none secondTail7
def outsideMaps7 : List MappedFrame := [([],.clauseBoundary 0 0 0 0 none),([],.bind 12 44 methodsEnv),([],.resourceBoundary 48 0 7)]
def getterTail7 : Stack := .push (.plain handlerPlain) (.push (.cell 0 7 .none .integer) .nil)
def ordinaryTail7 : Stack := .spent 0 .unit .none getterTail7

def s64 : CoreMachine.State := { s63 with frames := .closeCompletion 0::framesOf closingTailMaps7,observations := s63.observations ++ [.cleanupFinished 0] }
def s65 : CoreMachine.State := { s64 with frames := framesOf closingTailMaps7,observations := s64.observations ++ [.closeFinished 0] }
def s66 : CoreMachine.State := { s65 with frames := framesOf secondOutside7,observations := s65.observations ++ [.clauseReturned 1] }
def s67 : CoreMachine.State := { s66 with control := .evaluate 37 (.binding 10 .unit clauseEnv),frames := framesOf outsideMaps7 }
def w64 : CoreUnwindRelation.Point := ⟨s64,.unwind .none (.push (.closing 0 falseScope) spentTail),[],closingTailMaps7⟩
def w65 : CoreUnwindRelation.Point := ⟨s65,.eval ⟨.unit,falseScope,spentTail⟩,[],closingTailMaps7⟩
def w66 : CoreUnwindRelation.Point := ⟨s66,.eval ⟨.unit,.none,secondTail7⟩,[],secondOutside7⟩
def postTarget : Configuration := ⟨postWriteCode.subst 10 .unit,ticketScope,ordinaryTail7⟩
def bindTarget : Configuration := ⟨.bind 10 .unit postWriteCode,ticketScope,ordinaryTail7⟩
def w67 : CoreUnwindRelation.Point := ⟨s67,.eval postTarget,clauseMaps,outsideMaps7⟩

private theorem outside : PushedWithMaps graph allocated secondOutside7 secondTail7 := by
  have tail := cell_write_parts
  generalize targetEq : Stack.spent 1 .unit .none secondTail7 = target at tail
  cases tail with
  | spent header tail => exact (Stack.spent.inj targetEq).2.2.2.symm ▸ tail
  | cons frame tail => cases frame
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | cleanup frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

/-- The actual post-resume binding is inverted from the SAME reached tail. -/
theorem post_parts : ∃ fuel rawSuffix,
    CoreTranslation.translateFuel graph fuel clauseMaps 37 = .ok rawSuffix ∧
    EnvCloses graph clauseMaps allocated clauseEnv (.lambda 10 rawSuffix) (.lambda 10 postWriteCode) ∧
    ClosedExcept 10 postWriteCode ∧ PushedWithMaps graph allocated outsideMaps7 ordinaryTail7 := by
  have tail := outside
  cases tail with
  | cons frame tail =>
      change FrameRel graph clauseMaps allocated (.bind 10 37 clauseEnv) (.bind 10 postWriteCode) at frame
      cases frame with
      | bind translated saved ready => exact ⟨_,_,translated,saved,ready,tail⟩
  | initializer frame tail => cases frame
  | boundary frame tail => cases frame
  | request frame tail => cases frame
  | resume frame tail => cases frame

def cleanupUnwind : LexicalUnwind.Machine := .unwind .none
  (.push (.handler handlerData) (.push (.closing 0 falseScope) spentTail))
theorem cleanup_finish_event : LexicalUnwind.Transition w63.machine cleanupUnwind [] [.cleanup 0] := .finishCleanup
theorem retained_handler_advance_event : LexicalUnwind.Transition cleanupUnwind w64.machine [] [] := .advance .handler
theorem finish_cleanup_target : Positive w63.machine w64.machine [] [.cleanup 0] :=
  .next cleanup_finish_event (.one retained_handler_advance_event)
private theorem finish64 : CoreUnwindRelation.Link graph w63 w64 :=
  .positive reached_cell_write_related rfl finish_cleanup_target (.awaitingClose rfl rfl cell_write_parts)

theorem finish_close_target : Positive w64.machine w65.machine [] [.close 0] := .one .finishClose
private theorem finish65 : CoreUnwindRelation.Link graph w64 w65 :=
  .positive finish64.endpoints.2 rfl finish_close_target
    (.eval ⟨rfl,.unit,falseScope,.returned .unit,pushed_mapped cell_write_parts⟩)

theorem return_spent_target : RawStep ⟨.unit,falseScope,spentTail⟩ ⟨.unit,.none,secondTail7⟩ [] [] :=
  .leaveClause 1 .unit .unit (ValueRel.unit (graph := graph) (owners := []) (heap := allocated)).closed falseScope .none secondTail7
private theorem return66 : CoreUnwindRelation.Link graph w65 w66 :=
  .positive finish65.endpoints.2 rfl (ordinary_step return_spent_target trivial)
    (.eval ⟨rfl,.unit,.none,.returned .unit,pushed_mapped outside⟩)

theorem caller_bind_target : RawStep ⟨.unit,.none,secondTail7⟩ bindTarget [] [] ∧ RawStep bindTarget postTarget [] [] := by
  obtain ⟨fuel,rawSuffix,translated,saved,ready,tail⟩ := post_parts
  obtain ⟨_,_,plug,bind,_⟩ := bind_return_mapped (base := s66) translated saved ready
    (ValueRel.unit (graph := graph) (owners := []) (heap := allocated)) postPlain rfl tail .none
  exact ⟨plug,bind⟩
private theorem bind67 : CoreUnwindRelation.Link graph w66 w67 := by
  obtain ⟨fuel,rawSuffix,translated,saved,ready,tail⟩ := post_parts
  obtain ⟨current,next,plug,bind,successor⟩ := bind_return_mapped (base := s66) translated saved ready
    (ValueRel.unit (graph := graph) (owners := []) (heap := allocated)) postPlain rfl tail .none
  exact .positive (.eval current) next (.next (.evaluate plug trivial) (ordinary_step bind trivial)) (.eval successor)

theorem cleanup_to_caller : CoreUnwindRelation.Chain graph w63 [w64,w65,w66,w67] w67 :=
  .next finish64 (.next finish65 (.next return66 (.last bind67)))
theorem reached_post_body_related : CoreUnwindRelation.Related graph w67 := cleanup_to_caller.endpoints.2

def through67 : List CoreUnwindRelation.Point :=
  (((([p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20,r21,r22,r23,r24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35,u36,u37,u38,u39,u40].map lift) ++
    [lift v41,lift v42,lift v43,v44,v45]) ++ [w46,w47,w48,w49,w50,w51]) ++
    [w52,w53,w54,w55,w56,w57,w58,w59,w60,w61,w62,w63]) ++ [w64,w65,w66,w67]
theorem exported_cleanup_finish_prefix : CoreUnwindRelation.Chain graph (lift p0) through67 w67 :=
  chain_append exported_cleanup_write_prefix cleanup_to_caller

theorem cleanup_completion_ledger : CoreUnwindRelation.Trace w63.machine w67.machine [] [.close 0,.cleanup 0] := by
  obtain ⟨plug,bind⟩ := caller_bind_target
  exact finish_cleanup_target.trace.append (finish_close_target.trace.append
    ((ordinary_step return_spent_target trivial).trace.append
      (.next (.evaluate plug trivial) (.next (.evaluate bind trivial) (.refl _)))))

#print axioms post_parts
#print axioms cleanup_finish_event
#print axioms retained_handler_advance_event
#print axioms finish_cleanup_target
#print axioms finish_close_target
#print axioms return_spent_target
#print axioms caller_bind_target
#print axioms cleanup_to_caller
#print axioms reached_post_body_related
#print axioms exported_cleanup_finish_prefix
#print axioms cleanup_completion_ledger
end Ash.OneShot.CoreCleanupFinishPrefix
