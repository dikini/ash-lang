import CoreEffectEntry
import CoreAllocationHistory

/-! A fixed related prefix from the actual exported Core initial state through
wrapper/main/Unit-match/resource entry. Every Core transition is linked to a
positive RawStep sequence or an existing ranked same-target witness. This is
one exact prefix, not general simulation, source admission or suffix execution.
RawSteps do not supply M4 Valid, fresh-world equality or annotation provenance. -/
namespace Ash.OneShot.CoreInitialPrefix
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreStrictPotential CoreAdministrativeTransport CoreOrdinaryCompletion CoreEffectEntry CoreEffectFrames
open CoreExportedFixture

/-- No zero-length target execution occurs in a positive link. -/
inductive Positive : Configuration → Configuration → Prop where
  | one (step : RawStep before after created discharged) : Positive before after
  | next (step : RawStep before middle created discharged) (rest : Positive middle after) : Positive before after

structure Point where
  state : CoreMachine.State
  target : Configuration
  owners : CoreTranslation.OwnerMap
  annotations : List MappedFrame

def Related (graph : CoreSyntax.Graph) (point : Point) : Prop :=
  ComponentMapped graph point.owners point.annotations point.state point.target

/-- Each silent constructor shares literally one target and the existing strict
potential/family witness. There is no generic unrestricted stutter constructor. -/
inductive Link (graph : CoreSyntax.Graph) : Point → Point → Prop where
  | positive (current : Related graph before)
      (core : CoreMachine.next graph before.state = .stepped after.state)
      (target : Positive before.target after.target) (successor : Related graph after) : Link graph before after
  | traversal (witness : SilentMapped graph beforeOwners afterOwners beforeMaps afterMaps before after target) :
      Link graph ⟨before, target, beforeOwners, beforeMaps⟩ ⟨after, target, afterOwners, afterMaps⟩
  | value (witness : TransportMapped graph beforeOwners afterOwners beforeMaps afterMaps before after target) :
      Link graph ⟨before, target, beforeOwners, beforeMaps⟩ ⟨after, target, afterOwners, afterMaps⟩

inductive Chain (graph : CoreSyntax.Graph) : Point → List Point → Point → Prop where
  | last (link : Link graph before after) : Chain graph before [after] after
  | next (link : Link graph before middle) (rest : Chain graph middle points after) :
      Chain graph before (middle :: points) after

theorem Link.endpoints (link : Link graph before after) : Related graph before ∧ Related graph after := by
  cases link with
  | positive current core target successor => exact ⟨current, successor⟩
  | traversal witness => exact ⟨witness.current, witness.successor⟩
  | value witness => exact ⟨witness.current, witness.successor⟩

theorem Link.core_next (link : Link graph before after) :
    CoreMachine.next graph before.state = .stepped after.state := by
  cases link with
  | positive current core target successor => exact core
  | traversal witness => exact witness.core
  | value witness => exact witness.core

theorem Chain.endpoints (chain : Chain graph before points after) : Related graph before ∧ Related graph after := by
  induction chain with
  | last link => exact link.endpoints
  | next link rest ih => exact ⟨link.endpoints.1, ih.2⟩

theorem Chain.core_steps (chain : Chain graph before points after) :
    CoreAllocationHistory.Steps graph points.length before.state after.state := by
  have extend : ∀ {count start}, CoreAllocationHistory.Steps graph count start before.state →
      CoreAllocationHistory.Steps graph (count + points.length) start after.state := by
    induction chain with
    | last link =>
        intro count start earlier
        exact CoreAllocationHistory.Steps.snoc earlier link.core_next
    | next link rest ih =>
        intro count start earlier
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (CoreAllocationHistory.Steps.snoc earlier link.core_next)
  simpa using extend (CoreAllocationHistory.Steps.refl before.state)

theorem Chain.every_point_related (chain : Chain graph before points after) :
    ∀ point ∈ points, Related graph point := by
  induction chain with
  | last link =>
      intro point member
      have equal := List.mem_singleton.mp member
      cases equal
      exact link.endpoints.2
  | next link rest ih =>
      intro point member
      rcases List.mem_cons.mp member with equal | tail
      · cases equal; exact link.endpoints.2
      · exact ih point tail

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def body47 : Code := (CoreTranslation.translateFuel graph 56 [] 47).toOption.getD .unit
def resourceCode : Code := .resource 0 (.integer 0) (.bind 4 (.resourceRef (.bound 0)) body47)
def mainCode : Code := .bind (CoreTranslation.dummy graph 49) (.variable 0) resourceCode
def functionCode : Code := .lambda 0 mainCode
def rootCode : Code := .bind 13 functionCode (.app (.variable 13) .unit)
def template : MEnv := .functionTemplate 13 0 49 .empty
def called : MEnv := .binding 0 .unit template
private def functionPlain : PlainData := ⟨.appFunction .unit, .none, .unit, .integer, [], rfl⟩
private def argumentPlain : PlainData := ⟨.appArgument functionCode, .none, .unit, .integer, [], rfl⟩
private def unitPlain : PlainData := ⟨.bind (CoreTranslation.dummy graph 49) resourceCode, .none, .unit, .integer, [], rfl⟩
private def resourcePlain : PlainData := ⟨.resource 0 (.bind 4 (.resourceRef (.bound 0)) body47), .none, .integer, .integer, [], rfl⟩
private def applyFrame : CoreMachine.Frame := .applyArgument (.closure 0 49 template)
private def unitFrame : CoreMachine.Frame := .matchCases [⟨.unit, 48⟩] called
private def initializerFrame : CoreMachine.Frame := .resourceInitializer 48 0 ⟨4, .reference (.bound 0)⟩ 47 called
private def wrapperNode : CoreSyntax.Node :=
  ⟨54, .integer, [], some ⟨1, 1, 0, 549⟩, .recursiveBind [⟨⟨13, .function .unit .integer []⟩, 50⟩] 53⟩
private def functionNode : CoreSyntax.Node :=
  ⟨50, .function .unit .integer [], [], some ⟨1, 1, 88, 548⟩, .function ⟨0, .unit⟩ 49⟩
private def matchNode : CoreSyntax.Node :=
  ⟨49, .integer, [], some ⟨1, 1, 69, 548⟩, .matchCases 0 [⟨.unit, 48⟩]⟩
private def resourceNode : CoreSyntax.Node :=
  ⟨47, .integer, [], some ⟨1, 1, 98, 548⟩, .resource 0 ⟨4, .reference (.bound 0)⟩ 1 47⟩

/-- All states are fixed from CoreMachine.initial; no caller supplies a start
state, environment, counter, target validity or desired endpoint relation. -/
def s0 : CoreMachine.State := CoreMachine.initial graph
def s1 : CoreMachine.State := { s0 with control := .evaluate 53 template, observations := s0.observations ++ [.entered 54] }
def s2 : CoreMachine.State := { s1 with control := .evaluate 51 template, frames := [.applyFunction 52 template], observations := s1.observations ++ [.entered 53] }
def s3 : CoreMachine.State := { s2 with control := .returned (.closure 0 49 template), observations := s2.observations ++ [.entered 51] }
def s4 : CoreMachine.State := { s3 with control := .evaluate 52 template, frames := [applyFrame] }
def s5 : CoreMachine.State := { s4 with control := .returned .unit, observations := s4.observations ++ [.entered 52] }
def s6 : CoreMachine.State := { s5 with control := .evaluate 49 called, frames := [] }
def s7 : CoreMachine.State := { s6 with control := .evaluate 0 called, frames := [unitFrame], observations := s6.observations ++ [.entered 49] }
def s8 : CoreMachine.State := { s7 with control := .returned .unit, observations := s7.observations ++ [.entered 0] }
def s9 : CoreMachine.State := { s8 with control := .evaluate 48 called, frames := [] }
def s10 : CoreMachine.State := { s9 with control := .evaluate 1 called, frames := [initializerFrame], observations := s9.observations ++ [.entered 48] }
def s11 : CoreMachine.State := { s10 with control := .returned (.integer 0), observations := s10.observations ++ [.entered 1] }
def s12 : CoreMachine.State := { s11 with control := .evaluate 47 (.binding 4 (.handle 0) (.resource 0 0 called)), frames := [.resourceBoundary 48 0 0], nextActivation := 1, observations := s11.observations ++ [.acquired 48 0] }

def rootTarget : Configuration := ⟨rootCode, .none, .nil⟩
def appTarget : Configuration := ⟨.app functionCode .unit, .none, .nil⟩
def unitTarget : Configuration := ⟨.bind (CoreTranslation.dummy graph 49) .unit resourceCode, .none, .nil⟩
def resourceTarget : Configuration := ⟨resourceCode, .none, .nil⟩
def cellTarget : Configuration := ⟨(body47.instantiate (Instantiation.Environment.empty.bind 0 0)).subst 4 (.resourceRef (.activation 0)), .none, .push (.cell 0 0 .none .integer) .nil⟩
def point (state : CoreMachine.State) (target : Configuration) : Point :=
  ⟨state, target, [], uniformFrames [] state.frames⟩
def p0 : Point := point s0 rootTarget
def p1 : Point := point s1 appTarget
def p2 : Point := point s2 appTarget
def p3 : Point := point s3 appTarget
def p4 : Point := point s4 appTarget
def p5 : Point := point s5 appTarget
def p6 : Point := point s6 unitTarget
def p7 : Point := point s7 unitTarget
def p8 : Point := point s8 unitTarget
def p9 : Point := point s9 resourceTarget
def p10 : Point := point s10 resourceTarget
def p11 : Point := point s11 resourceTarget
def p12 : Point := point s12 cellTarget

private theorem callable : CallableCertificate graph 0 49 mainCode :=
  CoreCallableChecks.checkFunction_certificate (site := 50) (checked := ⟨0, 49, mainCode⟩) rfl
private theorem fnClosed : ClosedValue functionCode := by
  have deps : functionCode.dependencies = [] := by decide
  have resources : functionCode.freeNames = [] := by decide
  exact ⟨trivial, resources, by rw [deps]; simp⟩
private theorem unitClosed : ClosedValue Code.unit := (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed
private theorem selfAbsent : Syntax.Dependency.variable 13 ∉ functionCode.dependencies := by decide
private theorem mainValue : ValueRel graph [] [] (.closure 0 49 template) functionCode :=
  .closure (fuel := 56) rfl callable (.templateUnused selfAbsent .empty) fnClosed
private theorem currentApp : EnvCloses graph [] [] template (.app (.variable 13) .unit) (.app functionCode .unit) :=
  .templateExpand (fuel := 56) rfl callable selfAbsent EnvCloses.empty fnClosed EnvCloses.empty
private theorem resourceCurrent : EnvCloses graph [] [] called resourceCode resourceCode := by
  apply EnvCloses.binding ValueRel.unit
  rw [ScopedTyping.subst_absent resourceCode 0 .unit (by decide)]
  exact .templateUnused (by decide) .empty
private theorem resourceReady : ClosedExcept (CoreTranslation.dummy graph 49) resourceCode := by
  have deps : resourceCode.dependencies = [] := by decide
  intro name member; rw [deps] at member; cases member
private theorem bodyReady : ClosedExcept 4 body47 := by
  have supported : body47.dependencies.all (fun dep => match dep with | .variable name => name == 4 | _ => true) = true := by decide
  intro name member
  simpa using List.all_eq_true.mp supported (.variable name) member

/-- The public root entry point succeeds on the actual retained graph. -/
theorem exported_root_translation : CoreTranslation.translate graph = .ok rootCode := rfl

/-- The fixed initial component is constructed from actual successful root
translation and empty lexical/stack interpretation. -/
theorem initial_related : Related graph p0 := by
  exact ⟨rfl, rootCode, .none, .evaluate (fuel := 56) rfl EnvCloses.empty, pushed_mapped PushedWithMaps.nil⟩

private theorem link01 : Link graph p0 p1 := by
  have ready : ClosedExcept 13 (.app (.variable 13) .unit) := by simp [ClosedExcept, Code.dependencies]
  obtain ⟨before, next, step, after⟩ := template_entry (base := s0) (graph := graph) (owners := []) (fuel := 56)
    (site := 54) (body := 53) (environment := .empty) (functionCode := functionCode) (bodyCode := .app (.variable 13) .unit)
    (annotations := []) (target := .nil) (node := wrapperNode) (member := ⟨⟨13, .function .unit .integer []⟩, 50⟩)
    (functionNode := functionNode) (parameter := ⟨0, .unit⟩) (functionBody := 49) (rawFunctionBody := mainCode)
    (rawBody := .app (.variable 13) .unit) rfl rfl rfl rfl rfl rfl rfl callable selfAbsent EnvCloses.empty
    fnClosed ready PushedWithMaps.nil Execution.Scope.none
  exact .positive initial_related next (.one step) after

private def applicationNode : CoreSyntax.Node :=
  ⟨53, .integer, [], some ⟨1, 1, 69, 73⟩, .apply 51 52⟩
private theorem ordered : Postorder graph := CoreTranslationFuel.checkShape_postorder (graph := graph) rfl

private theorem link12 : Link graph p1 p2 := by
  have witness := application_entry_same_target_mapped (base := s1) (graph := graph) (owners := [])
    (site := 53) (node := applicationNode) (fuel := 56) (function := 51) (argument := 52)
    (rawFunction := .variable 13) (rawArgument := .unit) (functionCode := functionCode) (argumentCode := .unit)
    (environment := template) (annotations := []) (target := .nil)
    ordered rfl rfl rfl rfl currentApp fnClosed functionPlain rfl PushedWithMaps.nil
  exact .traversal witness

private theorem link23 : Link graph p2 p3 := by
  obtain ⟨functionSaved, argumentSaved⟩ := currentApp.app_components
  have frame : PlainFrameRel graph [] [] (.applyFunction 52 template) functionPlain :=
    FrameRel.applyFunction (fuel := 56) rfl argumentSaved
  have stack : OrdinaryWithMaps graph [] [([], .applyFunction 52 template)] functionCode .none
      (.app functionCode .unit) .none .nil :=
    prepend_mapped frame fnClosed (pushed_mapped PushedWithMaps.nil) Execution.Scope.none
  obtain ⟨value, lookup, witness, translated⟩ := CoreAdministrativeSteps.variable_evaluate
    (base := s2) (graph := graph) (owners := []) (index := 51)
    (node := ⟨51, .function .unit .integer [], [], some ⟨1, 1, 69, 73⟩, .variable 13⟩)
    rfl rfl functionSaved fnClosed [.applyFunction 52 template]
  have valueEq : value = .closure 0 49 template := by
    simpa [template, CoreMachine.Environment.lookup] using lookup.symm
  cases valueEq
  exact .value (value_entry_mapped witness rfl rfl stack)

private theorem link34 : Link graph p3 p4 := by
  obtain ⟨functionSaved, argumentSaved⟩ := currentApp.app_components
  have witness := application_argument_same_target_mapped (base := s3) (graph := graph)
    (owners := []) (savedOwners := []) (fuel := 56) (argument := 52) (rawArgument := .unit)
    (environment := template) (argumentCode := .unit) (functionCode := functionCode)
    (annotations := []) (target := .nil)
    rfl argumentSaved mainValue unitClosed functionPlain argumentPlain rfl rfl rfl PushedWithMaps.nil Execution.Scope.none
  exact .traversal witness

private theorem link45 : Link graph p4 p5 := by
  obtain ⟨functionSaved, argumentSaved⟩ := currentApp.app_components
  have frame : PlainFrameRel graph [] [] applyFrame argumentPlain := FrameRel.applyArgument mainValue
  have stack : OrdinaryWithMaps graph [] [([], applyFrame)] .unit .none
      (.app functionCode .unit) .none .nil :=
    prepend_mapped frame unitClosed (pushed_mapped PushedWithMaps.nil) Execution.Scope.none
  obtain ⟨witness, translated⟩ := CoreAdministrativeSteps.unit_evaluate
    (base := s4) (graph := graph) (owners := []) (index := 52)
    (node := ⟨52, .unit, [], some ⟨1, 1, 69, 73⟩, .unit⟩) rfl rfl argumentSaved [applyFrame]
  exact .value (value_entry_mapped witness rfl rfl stack)

private theorem link56 : Link graph p5 p6 := by
  obtain ⟨before, next, step, after⟩ := beta_complete_mapped
    (base := s5) (graph := graph) (codeOwners := []) (parameter := 0) (body := 49)
    (saved := template) (result := mainCode) (annotations := []) (target := .nil)
    mainValue ValueRel.unit argumentPlain rfl PushedWithMaps.nil Execution.Scope.none []
  have substitution : mainCode.subst 0 .unit = .bind (CoreTranslation.dummy graph 49) .unit resourceCode := by
    simp only [mainCode, Code.subst, ↓reduceIte]
    rw [if_neg (by decide : ¬ (0 : Nat) = CoreTranslation.dummy graph 49),
      ScopedTyping.subst_absent resourceCode 0 .unit (by decide)]
  rw [substitution] at step after
  exact .positive before next (.one step) after

private theorem currentUnit : EnvCloses graph [] [] called
    (.bind (CoreTranslation.dummy graph 49) (.variable 0) resourceCode)
    (.bind (CoreTranslation.dummy graph 49) .unit resourceCode) := by
  apply EnvCloses.binding ValueRel.unit
  simp only [Code.subst, ↓reduceIte]
  rw [if_neg (by decide : ¬ (0 : Nat) = CoreTranslation.dummy graph 49),
    ScopedTyping.subst_absent resourceCode 0 .unit (by decide)]
  exact .templateUnused (by decide) .empty

private theorem unitBodySaved : EnvCloses graph [] [] called resourceCode resourceCode := by
  obtain ⟨scrutineeSaved, savedBody⟩ := bind_components currentUnit
  have opened := savedBody.lambda_argument_at _ _ _ .unit rfl rfl unitClosed
  rw [ScopedTyping.subst_absent resourceCode (CoreTranslation.dummy graph 49) .unit (by decide)] at opened
  exact opened

private theorem unitRelation : PlainFrameRel graph [] [] unitFrame unitPlain :=
  FrameRel.unitMatch (site := 49) (node := matchNode) (fuel := 56)
    rfl rfl rfl unitBodySaved (by decide) resourceReady

private theorem link67 : Link graph p6 p7 := by
  have witness := unit_entry_same_target (base := s6) (graph := graph) (owners := [])
    (site := 49) (node := matchNode) (fuel := 56) (scrutinee := 0) (body := 48)
    (environment := called) (rawScrutinee := .variable 0) (rawBody := resourceCode)
    (scrutineeCode := .unit) (suffix := resourceCode) (annotations := []) (target := .nil)
    ordered rfl rfl rfl rfl currentUnit (by decide) (by decide) unitClosed resourceReady unitPlain rfl PushedWithMaps.nil
  exact .traversal witness

private theorem link78 : Link graph p7 p8 := by
  obtain ⟨scrutineeSaved, savedBody⟩ := bind_components currentUnit
  have stack : OrdinaryWithMaps graph [] [([], unitFrame)] .unit .none
      (.bind (CoreTranslation.dummy graph 49) .unit resourceCode) .none .nil :=
    prepend_mapped unitRelation unitClosed (pushed_mapped PushedWithMaps.nil) Execution.Scope.none
  obtain ⟨value, lookup, witness, translated⟩ := CoreAdministrativeSteps.variable_evaluate
    (base := s7) (graph := graph) (owners := []) (index := 0)
    (node := ⟨48, .unit, [], some ⟨1, 1, 69, 548⟩, .variable 0⟩)
    rfl rfl scrutineeSaved unitClosed [unitFrame]
  have valueEq : value = .unit := by simpa [called, CoreMachine.Environment.lookup] using lookup.symm
  cases valueEq
  exact .value (value_entry_mapped witness rfl rfl stack)

private theorem link89 : Link graph p8 p9 := by
  obtain ⟨before, next, plug, bind, after⟩ := unit_match_complete
    (base := s8) (graph := graph) (codeOwners := []) (savedOwners := [])
    (site := 49) (node := matchNode) (fuel := 56) (scrutinee := 0) (body := 48)
    (environment := called) (raw := resourceCode) (suffix := resourceCode) (annotations := []) (target := .nil)
    rfl rfl rfl unitBodySaved (by decide) resourceReady unitPlain rfl PushedWithMaps.nil Execution.Scope.none
  exact .positive link78.endpoints.2 next (.one bind) after

private theorem link910 : Link graph p9 p10 := by
  have witness := resource_entry_same_target (base := s9) (graph := graph) (owners := []) (fuel := 56)
    (site := 48) (node := resourceNode) (identity := 0) (handle := ⟨4, .reference (.bound 0)⟩)
    (initializer := 1) (body := 47) (rawInitializer := .integer 0) (rawBody := body47)
    (initializerCode := .integer 0) (suffix := .bind 4 (.resourceRef (.bound 0)) body47)
    (environment := called) (annotations := []) (target := .nil)
    ordered rfl rfl rfl rfl unitBodySaved
    (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := 0)).closed resourcePlain rfl PushedWithMaps.nil
  exact .traversal witness

private theorem link1011 : Link graph p10 p11 := by
  obtain ⟨initializerSaved, carrier⟩ := resource_components unitBodySaved
  have frame : CoreEffectFrames.InitializerRel graph [] [] initializerFrame resourcePlain :=
    .resource (site := 48) (node := resourceNode) (fuel := 56) rfl rfl rfl carrier rfl
  have stack : OrdinaryWithMaps graph [] [([], initializerFrame)] (.integer 0) .none resourceCode .none .nil :=
    prepend_initializer frame (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := 0)).closed
      (pushed_mapped PushedWithMaps.nil) Execution.Scope.none
  obtain ⟨witness, translated⟩ := CoreAdministrativeSteps.integer_evaluate
    (base := s10) (graph := graph) (owners := []) (index := 1)
    (node := ⟨0, .integer, [], some ⟨1, 1, 119, 120⟩, .integer 0⟩)
    rfl rfl initializerSaved [initializerFrame]
  exact .value (value_entry_mapped witness rfl rfl stack)

private theorem link1112 : Link graph p11 p12 := by
  obtain ⟨before, next, enter, bind, after⟩ := cell_acquire_mapped
    (base := s11) (graph := graph) (savedOwners := []) (codeOwners := [])
    (site := 48) (node := resourceNode) (identity := 0) (handle := ⟨4, .reference (.bound 0)⟩)
    (initializer := 1) (body := 47) (fuel := 56) (rawBody := body47) (bodyCode := body47)
    (payload := 0) (environment := called) (annotations := []) (target := .nil)
    rfl rfl rfl unitBodySaved (by change resourceCode.freeNames = []; decide) bodyReady
    resourcePlain rfl PushedWithMaps.nil Execution.Scope.none Ty.integer
  exact .positive before next (.next enter (.one bind)) after

/-- Twelve actual linked transitions from CoreMachine.initial, ending at the
actual body47 control/environment, key0 boundary, and nextActivation1. -/
theorem exported_initial_prefix : Chain graph p0
    [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12] p12 :=
  .next link01 (.next link12 (.next link23 (.next link34 (.next link45 (.next link56
    (.next link67 (.next link78 (.next link89 (.next link910 (.next link1011 (.last link1112)))))))))))

theorem reached_body47_related : Related graph p12 := exported_initial_prefix.endpoints.2

theorem initial_is_actual : p0.state = CoreMachine.initial graph := rfl

theorem reached_body47_control : p12.state.control =
    .evaluate 47 (.binding 4 (.handle 0) (.resource 0 0 called)) := rfl

theorem reached_body47_allocation : p12.state.nextActivation = 1 ∧
    p12.state.frames = [.resourceBoundary 48 0 0] := ⟨rfl, rfl⟩

/-- The Core count/history comes from the same linked chain. -/
theorem exported_core_steps : CoreAllocationHistory.Steps graph 12
    (CoreMachine.initial graph) s12 := exported_initial_prefix.core_steps

theorem exported_acquisition_history : CoreAllocationHistory.History s12 :=
  CoreAllocationHistory.initial_steps_history graph exported_core_steps

/-- The target trace records exactly one resource creation and no completion.
This is a raw ledger trace; source admission and target freshness remain separate. -/
theorem exported_target_ledger : RawTrace rootTarget cellTarget [.resource 0] [] := by
  have rootStep : RawStep rootTarget appTarget [] [] := by
    have ready : ClosedExcept 13 (.app (.variable 13) .unit) := by simp [ClosedExcept, Code.dependencies]
    simpa [rootTarget, rootCode, appTarget, Code.subst] using
      RawStep.bind 13 functionCode (.app (.variable 13) .unit) .none .nil fnClosed ready
  have betaStep : RawStep appTarget unitTarget [] [] := by
    simpa [appTarget, functionCode, mainCode, unitTarget, Code.subst,
      show ¬ (0 : Nat) = CoreTranslation.dummy graph 49 by decide,
      ScopedTyping.subst_absent resourceCode 0 .unit (by decide)] using
      RawStep.beta 0 mainCode .unit .none .nil unitClosed fnClosed
  have unitStep : RawStep unitTarget resourceTarget [] [] := by
    simpa [unitTarget, resourceTarget,
      ScopedTyping.subst_absent resourceCode (CoreTranslation.dummy graph 49) .unit (by decide)] using
      RawStep.bind (CoreTranslation.dummy graph 49) .unit resourceCode .none .nil unitClosed resourceReady
  obtain ⟨before, next, enter, bind, after⟩ := cell_acquire_mapped
    (base := s11) (graph := graph) (savedOwners := []) (codeOwners := [])
    (site := 48) (node := resourceNode) (identity := 0) (handle := ⟨4, .reference (.bound 0)⟩)
    (initializer := 1) (body := 47) (fuel := 56) (rawBody := body47) (bodyCode := body47)
    (payload := 0) (environment := called) (annotations := []) (target := .nil)
    rfl rfl rfl unitBodySaved (by change resourceCode.freeNames = []; decide) bodyReady
    resourcePlain rfl PushedWithMaps.nil Execution.Scope.none Ty.integer
  exact .next rootStep (.next betaStep (.next unitStep (.next enter (.next bind (.refl _)))))

#print axioms Chain.core_steps
#print axioms exported_core_steps
#print axioms exported_acquisition_history
#print axioms exported_target_ledger
#print axioms link67
#print axioms link78
#print axioms link89
#print axioms link910
#print axioms link1011
#print axioms link1112
#print axioms exported_initial_prefix
#print axioms reached_body47_related

#print axioms link12
#print axioms link23
#print axioms link34
#print axioms link45
#print axioms link56

#print axioms exported_root_translation
#print axioms Link.core_next
#print axioms Chain.every_point_related
#print axioms initial_related
#print axioms link01
end Ash.OneShot.CoreInitialPrefix
