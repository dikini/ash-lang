import CoreGraphProgram

/-! The actual exported ordinary prefix, starting from its constructed source
admission. Resource entry retains the answer selected by source preservation. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedPrefix
open ScopedExpressions ScopedExecution ProtectionContracts
open InstallationSupport InstallationSupport.Preservation
open CoreInitialExample CoreInitialPrefix

private theorem fnClosed : ClosedValue functionCode := by
  have deps : functionCode.dependencies = [] := by decide
  have resources : functionCode.freeNames = [] := by decide
  exact ⟨trivial, resources, by rw [deps]; simp⟩
private theorem unitClosed : ClosedValue Code.unit :=
  (CoreValueRelation.ValueRel.unit (graph := CoreExportedFixture.graph) (owners := []) (heap := [])).closed
private theorem resourceReady : ClosedExcept (CoreTranslation.dummy CoreExportedFixture.graph 49) resourceCode := by
  have deps : resourceCode.dependencies = [] := by decide
  intro name member
  rw [deps] at member
  cases member

theorem rootStep : RawStep rootTarget appTarget [] [] := by
  have ready : ClosedExcept 13 (.app (.variable 13) .unit) := by simp [ClosedExcept, Code.dependencies]
  simpa [rootTarget, rootCode, appTarget, Code.subst] using
    RawStep.bind 13 functionCode (.app (.variable 13) .unit) .none .nil fnClosed ready

theorem betaStep : RawStep appTarget unitTarget [] [] := by
  simpa [appTarget, functionCode, mainCode, unitTarget, Code.subst,
    show ¬ (0 : Nat) = CoreTranslation.dummy CoreExportedFixture.graph 49 by decide,
    ScopedTyping.subst_absent resourceCode 0 .unit (by decide)] using
    RawStep.beta 0 mainCode .unit .none .nil unitClosed fnClosed

theorem unitStep : RawStep unitTarget resourceTarget [] [] := by
  simpa [unitTarget, resourceTarget,
    ScopedTyping.subst_absent resourceCode (CoreTranslation.dummy CoreExportedFixture.graph 49) .unit (by decide)] using
    RawStep.bind (CoreTranslation.dummy CoreExportedFixture.graph 49) .unit resourceCode .none .nil unitClosed resourceReady

def initial (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) : Snapshot operations :=
  Snapshot.ofState (CoreGraphProgram.closed_initial_state tables families required)

def targetSnapshot (snapshot : Snapshot operations) (target : Configuration) : Snapshot operations :=
  { snapshot with run := ⟨⟨.eval target, [], []⟩, InitialAdmission.actions⟩ }

def Admitted (snapshot : Snapshot operations) :=
  Valid policy [] [] [] ports InitialAdmission.emptyRows .integer .integer snapshot

theorem initial_at : targetSnapshot (initial tables families required) rootTarget = initial tables families required := rfl

theorem ordinaryPrefix (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) :
    RawTrace (initial tables families required).run.execution 3
      (targetSnapshot (initial tables families required) resourceTarget).run.execution ∧
    Admitted (initial tables families required) ∧
    Admitted (targetSnapshot (initial tables families required) appTarget) ∧
    Admitted (targetSnapshot (initial tables families required) unitTarget) ∧
    Admitted (targetSnapshot (initial tables families required) resourceTarget) := by
  let start := initial tables families required
  have valid : Admitted (targetSnapshot start rootTarget) := valid_ofState (CoreGraphProgram.closed_initial_state tables families required)
  have first : Stable.Step operations (targetSnapshot start rootTarget) (targetSnapshot start appTarget) :=
    .computation (RecursiveExpressions.Ready.bind trivial) rootStep
  obtain ⟨event1, valid1⟩ := first.preserve valid
  have second : Stable.Step operations (targetSnapshot start appTarget) (targetSnapshot start unitTarget) :=
    .computation (RecursiveExpressions.Ready.app trivial) betaStep
  obtain ⟨event2, valid2⟩ := second.preserve valid1
  have third : Stable.Step operations (targetSnapshot start unitTarget) (targetSnapshot start resourceTarget) :=
    .computation (RecursiveExpressions.Ready.bind trivial) unitStep
  obtain ⟨event3, valid3⟩ := third.preserve valid2
  exact ⟨.step (.step (.step .refl event1) event2) event3, valid, valid1, valid2, valid3⟩

/-- Restrict the already named positive/ranked Core chain to the resource
initializer value. No unrestricted same-target transition is added. -/
theorem coreToInitializer : CoreInitialPrefix.Chain CoreExportedFixture.graph p0
    [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] p11 := by
  cases exported_initial_prefix with
  | next l1 rest =>
    cases rest with
    | next l2 rest =>
      cases rest with
      | next l3 rest =>
        cases rest with
        | next l4 rest =>
          cases rest with
          | next l5 rest =>
            cases rest with
            | next l6 rest =>
              cases rest with
              | next l7 rest =>
                cases rest with
                | next l8 rest =>
                  cases rest with
                  | next l9 rest =>
                    cases rest with
                    | next l10 rest =>
                      cases rest with
                      | next l11 rest =>
                        exact .next l1 (.next l2 (.next l3 (.next l4 (.next l5
                          (.next l6 (.next l7 (.next l8 (.next l9 (.next l10 (.last l11))))))))))

private theorem bodyReady : ClosedExcept 4 body47 := by
  have supported : body47.dependencies.all (fun dep => match dep with
    | .variable name => name == 4 | _ => true) = true := by decide
  intro name member
  simpa using List.all_eq_true.mp supported (.variable name) member

private theorem resourceCurrent : CoreValueRelation.EnvCloses CoreExportedFixture.graph [] [] called resourceCode resourceCode := by
  apply CoreValueRelation.EnvCloses.binding CoreValueRelation.ValueRel.unit
  rw [ScopedTyping.subst_absent resourceCode 0 .unit (by decide)]
  exact .templateUnused (by decide) .empty

private def resourcePlain : PlainData :=
  ⟨.resource 0 (.bind 4 (.resourceRef (.bound 0)) body47), .none, .integer, .integer, [], rfl⟩
private def resourceNode : CoreSyntax.Node :=
  ⟨47, .integer, [], some ⟨1, 1, 98, 548⟩, .resource 0 ⟨4, .reference (.bound 0)⟩ 1 47⟩

def openedTarget (answer : Ty) : Configuration :=
  ⟨.bind 4 (.resourceRef (.activation 0)) (body47.instantiate (Instantiation.Environment.empty.bind 0 0)),
    .none, .push (.cell 0 0 .none answer) .nil⟩

def bodyTarget (answer : Ty) : Configuration :=
  ⟨(body47.instantiate (Instantiation.Environment.empty.bind 0 0)).subst 4 (.resourceRef (.activation 0)),
    .none, .push (.cell 0 0 .none answer) .nil⟩

def endpoint (answer : Ty) : CoreInitialPrefix.Point :=
  ⟨s12, bodyTarget answer, [], [([], .resourceBoundary 48 0 0)]⟩

/-- The same actual Core acquisition accepts the source-selected answer in its
mapped cell boundary. The generated handle bind is a second positive step. -/
theorem acquisitionMapped (answer : Ty) :
    CoreInitialPrefix.Related CoreExportedFixture.graph p11 ∧
    CoreMachine.next CoreExportedFixture.graph s11 = .stepped s12 ∧
    RawStep resourceTarget (openedTarget answer) [.resource 0] [] ∧
    RawStep (openedTarget answer) (bodyTarget answer) [] [] ∧
    CoreInitialPrefix.Related CoreExportedFixture.graph (endpoint answer) := by
  exact CoreEffectEntry.cell_acquire_mapped
    (base := s11) (graph := CoreExportedFixture.graph) (savedOwners := []) (codeOwners := [])
    (site := 48) (node := resourceNode) (identity := 0) (handle := ⟨4, .reference (.bound 0)⟩)
    (initializer := 1) (body := 47) (fuel := 56) (rawBody := body47) (bodyCode := body47)
    (payload := 0) (environment := called) (annotations := []) (target := .nil)
    rfl rfl rfl resourceCurrent (by change resourceCode.freeNames = []; decide) bodyReady
    resourcePlain rfl CoreStrictStack.PushedWithMaps.nil Execution.Scope.none answer

theorem corePrefix (answer : Ty) : CoreInitialPrefix.Chain CoreExportedFixture.graph p0
    [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, endpoint answer] (endpoint answer) := by
  obtain ⟨current, next, enter, bind, related⟩ := acquisitionMapped answer
  have last : CoreInitialPrefix.Link CoreExportedFixture.graph p11 (endpoint answer) :=
    .positive current next (.next enter (.one bind)) related
  have append : ∀ {start points finish}, CoreInitialPrefix.Chain CoreExportedFixture.graph start points finish →
      CoreInitialPrefix.Link CoreExportedFixture.graph finish (endpoint answer) →
      CoreInitialPrefix.Chain CoreExportedFixture.graph start (points ++ [endpoint answer]) (endpoint answer) := by
    intro start points finish chain
    induction chain with
    | last link => intro ending; exact .next link (.last ending)
    | next link rest ih => intro ending; exact .next link (ih ending)
  exact append coreToInitializer last


def acquired (snapshot : Snapshot operations) (answer : Ty) : Snapshot operations :=
  { snapshot with
    world := snapshot.world ++ [0]
    run := ⟨⟨.eval (openedTarget answer), [.resource 0], []⟩, InitialAdmission.actions⟩ }

def finished (snapshot : Snapshot operations) (answer : Ty) : Snapshot operations :=
  { acquired snapshot answer with
    run := ⟨⟨.eval (bodyTarget answer), [.resource 0], []⟩, InitialAdmission.actions⟩ }

/-- Resource metadata is selected by preservation, after freshness has been
proved from the admitted world's concrete empty value. Every positive target
configuration retains its full invariant. -/
theorem resourcePrefix (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) :
    ∃ answer,
      RawTrace (initial tables families required).run.execution 5
        (finished (initial tables families required) answer).run.execution ∧
      Admitted (initial tables families required) ∧
      Admitted (targetSnapshot (initial tables families required) appTarget) ∧
      Admitted (targetSnapshot (initial tables families required) unitTarget) ∧
      Admitted (targetSnapshot (initial tables families required) resourceTarget) ∧
      Admitted (acquired (initial tables families required) answer) ∧
      Admitted (finished (initial tables families required) answer) := by
  let start := initial tables families required
  let predecessor := targetSnapshot start resourceTarget
  obtain ⟨trace, valid0, valid1, valid2, valid3⟩ := ordinaryPrefix tables families required
  let request : Allocating.Request predecessor :=
    .enterResource (binder := 0) (initializer := .integer 0)
      (body := .bind 4 (.resourceRef (.bound 0)) body47) (identity := 0)
      rfl trivial (by change (0 : Nat) ∉ ([] : List Nat); simp)
  obtain ⟨after, event4, realizes, valid4⟩ := request.preserve valid3
  dsimp [request] at realizes
  cases realizes with
  | enterResource payload answer expressionEq =>
    have payloadEq : payload = 0 := by injection expressionEq with eq; exact eq.symm
    subst payload
    have selected : Admitted (acquired start answer) := valid4
    have event : LexicalUnwind.Event predecessor.run.execution (acquired start answer).run.execution := event4
    have fifth : Stable.Step operations (acquired start answer) (finished start answer) :=
      .computation (snapshot := acquired start answer)
        (issued := [.resource 0]) (completed := []) (actions := InitialAdmission.actions)
        (RecursiveExpressions.Ready.bind (value := .resourceRef (.activation 0)) trivial)
        (acquisitionMapped answer).2.2.2.1
    obtain ⟨event5, valid5⟩ := fifth.preserve selected
    exact ⟨answer, .step (.step trace event) event5, valid0, valid1, valid2, valid3, selected, valid5⟩


def points (answer : Ty) : List CoreInitialPrefix.Point :=
  [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, endpoint answer]

/-- Fixed Core steps share constructed admitted targets. All intermediate
configurations, including the opened handle bind, retain M4 evidence. The
endpoint is the actual s12/body47, with the source-selected boundary answer. -/
theorem admittedCorePrefix (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) :
    ∃ answer,
      CoreInitialPrefix.Chain CoreExportedFixture.graph p0 (points answer) (endpoint answer) ∧
      RawTrace (initial tables families required).run.execution 5
        (finished (initial tables families required) answer).run.execution ∧
      Admitted (acquired (initial tables families required) answer) ∧
      Admitted (finished (initial tables families required) answer) ∧
      (∀ point ∈ p0 :: points answer,
        CoreInitialPrefix.Related CoreExportedFixture.graph point ∧
        ∃ snapshot : Snapshot operations, Admitted snapshot ∧
          snapshot.run.execution.machine = .eval point.target) ∧
      (finished (initial tables families required) answer).world = [0] ∧
      (finished (initial tables families required) answer).history = [] ∧
      (finished (initial tables families required) answer).run.execution.issued = [.resource 0] ∧
      (finished (initial tables families required) answer).run.execution.completed = [] ∧
      (finished (initial tables families required) answer).run.execution.machine = .eval (endpoint answer).target := by
  obtain ⟨answer, trace, valid0, valid1, valid2, valid3, valid4, valid5⟩ := resourcePrefix tables families required
  let start := initial tables families required
  have chain := corePrefix answer
  have admitted : ∀ point ∈ p0 :: points answer,
      ∃ snapshot : Snapshot operations, Admitted snapshot ∧ snapshot.run.execution.machine = .eval point.target := by
    intro point member
    simp only [points, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨start, valid0, rfl⟩
    · exact ⟨targetSnapshot start appTarget, valid1, rfl⟩
    · exact ⟨targetSnapshot start appTarget, valid1, rfl⟩
    · exact ⟨targetSnapshot start appTarget, valid1, rfl⟩
    · exact ⟨targetSnapshot start appTarget, valid1, rfl⟩
    · exact ⟨targetSnapshot start appTarget, valid1, rfl⟩
    · exact ⟨targetSnapshot start unitTarget, valid2, rfl⟩
    · exact ⟨targetSnapshot start unitTarget, valid2, rfl⟩
    · exact ⟨targetSnapshot start unitTarget, valid2, rfl⟩
    · exact ⟨targetSnapshot start resourceTarget, valid3, rfl⟩
    · exact ⟨targetSnapshot start resourceTarget, valid3, rfl⟩
    · exact ⟨targetSnapshot start resourceTarget, valid3, rfl⟩
    · exact ⟨finished start answer, valid5, rfl⟩
  refine ⟨answer, chain, trace, valid4, valid5, ?_, rfl, rfl, rfl, rfl, rfl⟩
  intro point member
  refine ⟨?_, admitted point member⟩
  rcases List.mem_cons.mp member with equal | later
  · subst point; exact chain.endpoints.1
  · exact chain.every_point_related point later

/-- Admission starts at the public translation, with no normalized-source
substitution between the Core root and the initial target. -/
theorem initialTranslation : CoreTranslation.translate CoreExportedFixture.graph =
    .ok CoreGraphAdmission.Main.root := by
  rw [CoreGraphProgram.actualRoot]
  exact exported_root_translation

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedPrefix

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedPrefix.ordinaryPrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedPrefix.coreToInitializer
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedPrefix.acquisitionMapped
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedPrefix.corePrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedPrefix.resourcePrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedPrefix.admittedCorePrefix
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreAdmittedPrefix.initialTranslation
