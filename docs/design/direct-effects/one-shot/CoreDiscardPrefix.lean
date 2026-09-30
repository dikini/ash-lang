import CoreSecondCapture
import CoreUnwindRelation

/-! Connected false-clause entry into the current lexical unwind semantics.
The endpoint precedes callback execution. The retained user handler is absent
from Core's projected close vector; dispatch agreement is proved only for the
actual cell0 callback request, not for arbitrary effects. -/
namespace Ash.OneShot.CoreDiscardPrefix
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreEffectFrames
  CoreRequestFrames CoreResumeFrames CoreStrictStack CoreStrictPotential CoreCaptureEntry
  CoreResumeEntry CoreOrdinaryCompletion CoreAdministrativeTransport CoreInitialPrefix CoreHandlerPrefix
  CoreCleanupEntry CoreCaptureEntry.Exported CoreResumeEntry.Exported CoreSecondCapture CoreExportedFixture
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

def falseEnv : CoreMachine.Environment := .binding 9 (.boolean false) methodsEnv
def falseScope : Scope := .ticket (CoreTranslation.ticket graph 0) 1
private theorem current_clause : EnvCloses graph clauseMaps [] falseEnv (ownedRaw 40) secondClauseTarget.expression ∧
    PushedWithMaps graph [] u40.annotations secondClauseTarget.stack := by
  obtain ⟨shape,code,scope,control,stack⟩ := reached_second_clause_related
  obtain ⟨rfl,rfl,pushed⟩ := owner_head_pushed stack
  cases control with
  | evaluate translated saved =>
      have same := translation_unique translated (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 40 = .ok (ownedRaw 40))
      cases same
      exact ⟨saved,pushed⟩

def falseYes : Code := match secondClauseTarget.expression with | .branch _ yes _ => yes | _ => .unit
def falseNo : Code := match secondClauseTarget.expression with | .branch _ _ no => no | _ => .unit
def branchPlain : PlainData := ⟨.branch falseYes falseNo,falseScope,.boolean,.unit,
  (falseScope.translate (.branch falseYes falseNo : Context).dependencies).getD [],by decide⟩
def discardTarget : Configuration := ⟨.discard (CoreTranslation.ticket graph 0),falseScope,secondClauseTarget.stack⟩
def s41 : CoreMachine.State := { s40 with control := .evaluate 30 falseEnv, frames := .matchCases (CoreStrictSteps.booleanArms 38 39 false) falseEnv :: s40.frames, observations := s40.observations ++ [.entered 40] }
def s42 : CoreMachine.State := { s41 with control := .returned (.boolean false), observations := s41.observations ++ [.entered 30] }
def s43 : CoreMachine.State := { s42 with control := .evaluate 39 falseEnv, frames := s40.frames }
def s44 : CoreMachine.State := { s43 with control := .discard 0 0, observations := s43.observations ++ [.entered 39] }
def v41 : CoreInitialPrefix.Point := ⟨s41,secondClauseTarget,clauseMaps,(clauseMaps,.matchCases (CoreStrictSteps.booleanArms 38 39 false) falseEnv) :: u40.annotations⟩
def v42 : CoreInitialPrefix.Point := ⟨s42,secondClauseTarget,clauseMaps,v41.annotations⟩
def v43 : CoreInitialPrefix.Point := ⟨s43,discardTarget,clauseMaps,u40.annotations⟩
def v44 : CoreUnwindRelation.Point := ⟨s44,.eval discardTarget,clauseMaps,u40.annotations⟩

private theorem branch_parts : EnvCloses graph clauseMaps [] falseEnv (ownedRaw 30) (.boolean false) ∧
    EnvCloses graph clauseMaps [] falseEnv (ownedRaw 38) falseYes ∧
    EnvCloses graph clauseMaps [] falseEnv (ownedRaw 39) falseNo :=
  branch_components current_clause.1

private theorem branchTraversal : SilentMapped graph clauseMaps clauseMaps u40.annotations v41.annotations s40 s41 secondClauseTarget :=
  boolean_entry_same_target (base := s40) (environment := falseEnv) (scrutineeCode := .boolean false)
    (yesCode := falseYes) (noCode := falseNo) (annotations := u40.annotations) ordered
    (rfl : graph.node 40 = some (node 40)) rfl
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 30 = .ok (ownedRaw 30))
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 38 = .ok (ownedRaw 38))
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 39 = .ok (ownedRaw 39))
    current_clause.1 branch_parts.1 branch_parts.2.1 branch_parts.2.2
    (ValueRel.boolean (graph := graph) (owners := clauseMaps) (heap := []) (value := false)).closed branchPlain rfl current_clause.2

private theorem conditionWitness : TransportMapped graph clauseMaps clauseMaps v41.annotations v42.annotations s41 s42 secondClauseTarget := by
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := s41)
    (rfl : graph.node 30 = some (node 30)) rfl branch_parts.1
    (ValueRel.boolean (graph := graph) (owners := clauseMaps) (heap := []) (value := false)).closed s41.frames
  have valueEq : value = .boolean false := Option.some.inj (lookup.symm.trans rfl)
  cases valueEq
  have frame : PlainFrameRel graph clauseMaps [] (.matchCases (CoreStrictSteps.booleanArms 38 39 false) falseEnv) branchPlain :=
    .booleanMatch (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 38 = .ok (ownedRaw 38))
      (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 39 = .ok (ownedRaw 39)) branch_parts.2.1 branch_parts.2.2
  have stack := prepend_mapped frame (ValueRel.boolean (graph := graph) (owners := clauseMaps) (heap := []) (value := false)).closed
    (pushed_mapped current_clause.2) falseScope
  exact value_entry_mapped witness rfl rfl stack

private theorem choose_false : CoreInitialPrefix.Link graph v42 v43 ∧ RawStep secondClauseTarget discardTarget [] [] := by
  obtain ⟨before,next,step,after⟩ := boolean_complete_mapped (base := s42)
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 38 = .ok (ownedRaw 38))
    (rfl : CoreTranslation.translateFuel graph 56 clauseMaps 39 = .ok (ownedRaw 39)) branch_parts.2.1 branch_parts.2.2
    false false branchPlain rfl current_clause.2 clauseMaps falseScope
  exact ⟨.positive conditionWitness.successor next (.one step) after,step⟩

private theorem carrier : CoreUnwindRelation.DiscardCarrier graph clauseMaps [] falseEnv 0 0 (CoreTranslation.ticket graph 0) :=
  .site (rfl : graph.node 39 = some (node 39)) rfl rfl branch_parts.2.2
private theorem pending_related : CoreUnwindRelation.Related graph v44 :=
  .discard carrier rfl rfl current_clause.2
private theorem discard_entry_decreases : potential graph s44 < potential graph s43 := by
  have cost := cost_recurrence ordered (rfl : graph.node 39 = some (node 39))
  simp only [CoreSyntax.Kind.children,List.map_nil,List.sum_nil] at cost
  simp only [potential,s44,s43]
  omega

private theorem discardEntry : CoreUnwindRelation.Link graph (CoreUnwindRelation.lift v43) v44 :=
  .discardEntry (.eval choose_false.1.endpoints.2) pending_related rfl rfl
    ⟨39,falseEnv,0,0,rfl,rfl⟩ discard_entry_decreases

private theorem owner_cut : MappedOwnerCut graph [] 0 0 u40.annotations secondClauseTarget.stack
    [] .nil [] 0 1 handlerData .unit secondCaptured secondCap secondOutside secondTail :=
  .hit first_capture_parts.1 second_capture_parts.1 second_capture_parts.2

/-- This fixture has no nested live owner in its captured prefix. -/
theorem closing_projection : CoreMachine.closeFuel (CoreMachine.framesMass (framesOf secondCaptured) + 1)
    (framesOf secondCaptured) = .ok ([.cleanupBoundary 27 callbackEnv 0],[]) := rfl

def closingTailMaps : List MappedFrame := ([],.clauseBoundary 0 0 0 1 none) :: secondOutside
def unwindStack : Stack := secondCap.append (.push (.closing 0 falseScope) (.spent 1 .unit .none secondTail))
def s45 : CoreMachine.State := { s44 with control := .returned .unit, frames := .cleanupBoundary 27 callbackEnv 0 :: .closeCompletion 0 :: framesOf closingTailMaps, nextClose := 1, observations := s44.observations ++ [.discarded 1] ++ [.closeStarted 0] }
def v45 : CoreUnwindRelation.Point := ⟨s45,.unwind falseScope unwindStack,clauseMaps,closingTailMaps⟩

private theorem discard : CoreUnwindRelation.Link graph v44 v45 ∧
    LexicalUnwind.Transition (.eval discardTarget) (.unwind falseScope unwindStack) [.close 0] [.ticket 1] := by
  obtain ⟨after,before,next,step,related⟩ := CoreUnwindRelation.discard_projected (base := s44)
    owner_cut carrier (rfl : falseScope.resolve (CoreTranslation.ticket graph 0) = some 1)
    (rfl : ProtectionContexts.protectedMode secondCap.erase = false) closing_projection rfl
  have same : after = s45 := CoreMachine.Outcome.stepped.inj (next.symm.trans rfl)
  cases same
  exact ⟨.positive pending_related next (.one step) related,step⟩

/-- Ordinary branch selection is lifted with the current lexical guard;
the obsolete raw discard rule is never used. -/
private theorem chooseFalseLexical : CoreUnwindRelation.Link graph (CoreUnwindRelation.lift v42) (CoreUnwindRelation.lift v43) :=
  .positive (.eval conditionWitness.successor) choose_false.1.core_next
    (CoreUnwindRelation.ordinary_step choose_false.2 trivial) (.eval choose_false.1.endpoints.2)

theorem second_clause_to_unwind : CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift u40)
    [CoreUnwindRelation.lift v41,CoreUnwindRelation.lift v42,CoreUnwindRelation.lift v43,v44,v45] v45 :=
  .next (.traversal branchTraversal) (.next (.value conditionWitness)
    (.next chooseFalseLexical (.next discardEntry (.last discard.1))))

theorem reached_unwind_related : CoreUnwindRelation.Related graph v45 := second_clause_to_unwind.endpoints.2

/-- The already-related actual initial chain and new lexical-machine suffix
share exactly u40. No arbitrary starting component is supplied. -/
theorem connected_initial_unwind :
    CoreInitialPrefix.Chain graph p0
      [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20,r21,r22,r23,r24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35,u36,u37,u38,u39,u40] u40 ∧
    CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift u40)
      [CoreUnwindRelation.lift v41,CoreUnwindRelation.lift v42,CoreUnwindRelation.lift v43,v44,v45] v45 :=
  ⟨exported_second_capture_prefix,second_clause_to_unwind⟩

private theorem steps_append (first : CoreAllocationHistory.Steps graph count before middle)
    (second : CoreAllocationHistory.Steps graph later middle after) :
    CoreAllocationHistory.Steps graph (count + later) before after := by
  induction second with
  | refl => simpa using first
  | snoc previous step ih => simpa [Nat.add_assoc] using CoreAllocationHistory.Steps.snoc (ih first) step

theorem exported_discard_steps : CoreAllocationHistory.Steps graph 45 (CoreMachine.initial graph) s45 :=
  steps_append exported_second_capture_steps second_clause_to_unwind.core_steps

theorem exported_discard_history : CoreAllocationHistory.History s45 :=
  CoreAllocationHistory.initial_steps_history graph exported_discard_steps

/-- The target suffix uses the current lexical machine; silent source entry
and operand traversal add no target events. Nested consumption is [] here. -/
theorem lexical_discard_ledger : CoreUnwindRelation.Positive (.eval secondClauseTarget)
    (.unwind falseScope unwindStack) [.close 0] [.ticket 1] :=
  .next (.evaluate choose_false.2 trivial) (.one discard.2)

/-- Explicit two-phase ledger evidence: the ordinary related initial prefix,
then its connected current lexical unwind suffix. This does not assert that
an arbitrary old RawTrace can be lifted without per-step ordinary guards. -/
theorem connected_discard_ledger :
    RawTrace rootTarget secondClauseTarget [.resource 0,.cleanup 0,.ticket 0,.ticket 1] [.ticket 0] ∧
    CoreUnwindRelation.Positive (.eval secondClauseTarget) (.unwind falseScope unwindStack)
      [.close 0] [.ticket 1] ∧
    ([.resource 0,.cleanup 0,.ticket 0,.ticket 1] ++ [.close 0] : List Owner) =
      [.resource 0,.cleanup 0,.ticket 0,.ticket 1,.close 0] ∧
    ([.ticket 1] ++ [.ticket 0] : List Owner) = [.ticket 1,.ticket 0] :=
  ⟨exported_second_capture_ledger,lexical_discard_ledger,rfl,rfl⟩

theorem discard_spines_exact :
    s45.frames = [.cleanupBoundary 27 callbackEnv 0,.closeCompletion 0,.clauseBoundary 0 0 0 1 none,
      .bind 10 37 clauseEnv,.clauseBoundary 0 0 0 0 none,.bind 12 44 methodsEnv,.resourceBoundary 48 0 0] ∧
    unwindStack = .push (.plain secondBindPlain) (.push (.armed actionData) (.push (.handler handlerData)
      (.push (.closing 0 falseScope) (.spent 1 .unit .none secondTail)))) ∧
    s45.control = .returned .unit ∧ s45.nextClose = 1 := ⟨rfl,rfl,rfl,rfl⟩

/-- Mirror only the projected close vector for comparing its callback routes. -/
def projectedStack : Stack := .push (.armed actionData) (.push (.closing 0 falseScope) (.spent 1 .unit .none secondTail))

theorem callback_cell_dispatch :
    actionData.requests = [.cell 0] ∧
    unwindStack.erase.resolve (.cell 0) = some (.builtin 0) ∧
    projectedStack.erase.resolve (.cell 0) = some (.builtin 0) ∧
    CoreMachine.findInterpreter graph (.cell (.activation 0)) s45.frames =
      .ok (.cell ⟨[.cleanupBoundary 27 callbackEnv 0,.closeCompletion 0,.clauseBoundary 0 0 0 1 none,
        .bind 10 37 clauseEnv,.clauseBoundary 0 0 0 0 none,.bind 12 44 methodsEnv],48,0,0,[]⟩) := ⟨rfl,rfl,rfl,rfl⟩

theorem callback_requests_preserved : SameRequests unwindStack.erase projectedStack.erase actionData.requests :=
  .cons (.cell 0) [] (.builtin 0) rfl rfl .nil

/-- Projection does change unrelated user-effect dispatch. The restricted
callback theorem must not be promoted to all-effect equality. -/
theorem user_dispatch_not_preserved : unwindStack.erase.resolve (.user 0 []) = some (.source 0) ∧
    projectedStack.erase.resolve (.user 0 []) = none := ⟨rfl,rfl⟩

theorem cleanup_not_started : s45.observations.contains (.cleanupStarted 0) = false := by decide

#print axioms closing_projection
#print axioms second_clause_to_unwind
#print axioms reached_unwind_related
#print axioms connected_initial_unwind
#print axioms exported_discard_steps
#print axioms exported_discard_history
#print axioms lexical_discard_ledger
#print axioms connected_discard_ledger
#print axioms discard_spines_exact
#print axioms callback_cell_dispatch
#print axioms callback_requests_preserved
#print axioms user_dispatch_not_preserved
#print axioms cleanup_not_started
/-- One current lexical-machine chain preserves all inherited related points. -/
theorem exported_lexical_unwind_prefix : CoreUnwindRelation.Chain graph (CoreUnwindRelation.lift p0)
    (([p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,q13,q14,q15,q16,q17,q18,q19,q20,r21,r22,r23,r24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35,u36,u37,u38,u39,u40].map CoreUnwindRelation.lift) ++
      [CoreUnwindRelation.lift v41,CoreUnwindRelation.lift v42,CoreUnwindRelation.lift v43,v44,v45]) v45 :=
  CoreUnwindRelation.chain_append (CoreUnwindRelation.chain_lift exported_second_capture_prefix) second_clause_to_unwind

theorem exported_lexical_discard_ledger : CoreUnwindRelation.Trace (.eval rootTarget) (.unwind falseScope unwindStack)
    [.resource 0,.cleanup 0,.ticket 0,.ticket 1,.close 0] [.ticket 1,.ticket 0] :=
  (CoreUnwindRelation.raw_trace_lift exported_second_capture_ledger (by intro identity; simp)).append
    lexical_discard_ledger.trace

/-- The strengthened inherited interface cannot admit legacy raw discard. -/
theorem legacy_discard_positive_rejected :
    ¬ CoreInitialPrefix.Positive ⟨.discard binder,scope,stack⟩ after := by
  intro positive
  cases positive with
  | one step allowed => exact allowed
  | next step rest allowed => exact allowed

#print axioms exported_lexical_unwind_prefix
#print axioms exported_lexical_discard_ledger
#print axioms legacy_discard_positive_rejected

end Ash.OneShot.CoreDiscardPrefix
