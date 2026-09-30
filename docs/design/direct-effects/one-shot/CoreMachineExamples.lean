import CoreMachine
import CoreExportedFixture

/-! Development checks for the independent Core machine.
The generated 55-node graph comes from the actual validated Rust fixture and
exercises the complete vertical execution. Other small graphs below are
hand-built syntax examples, not an export-authentication or admission proof. -/
namespace Ash.OneShot.CoreMachineExamples
open CoreSyntax CoreMachine

private def node (original : Nat) (kind : CoreSyntax.Kind)
    (type : CoreSyntax.ValueType := .unit) : Node := ⟨original, type, [], none, kind⟩

def integerResult : RunResult → Option Int
  | .done (.integer value) _ => some value
  | _ => none

def unitResult : RunResult → Bool
  | .done .unit _ => true
  | _ => false

def errorResult : RunResult → Option CoreMachine.Error
  | .stopped error _ => some error
  | _ => none

def observations : RunResult → List Observation
  | .done _ state | .stopped _ state | .exhausted state => state.observations

def operations (result : RunResult) : List Observation :=
  (observations result).filter fun event => match event with
    | .entered _ => false
    | _ => true

/-- A single evaluator transition is independent of target calculus events. -/
example : CoreMachine.Step ⟨[node 0 .unit], 0⟩
    (initial ⟨[node 0 .unit], 0⟩)
    { control := .returned .unit, observations := [.entered 0] } := rfl

/-- A closure retains the lexical binding 17 even though the caller shadows
    that name with 99 before application. -/
def lexicalClosure : Graph := ⟨[
  node 0 (.integer 17) .integer,
  node 1 (.variable 1) .integer,
  node 2 (.function ⟨2, .unit⟩ 1) (.function .unit .integer []),
  node 3 (.variable 3) (.function .unit .integer []),
  node 4 .unit,
  node 5 (.apply 3 4) .integer,
  node 6 (.integer 99) .integer,
  node 7 (.bind ⟨1, .integer⟩ 6 5) .integer,
  node 8 (.bind ⟨3, .function .unit .integer []⟩ 2 7) .integer,
  node 9 (.bind ⟨1, .integer⟩ 0 8) .integer], 9⟩

example : checkShape lexicalClosure = .ok () := rfl
example : integerResult (run lexicalClosure 100 (initial lexicalClosure)) = some 17 := rfl

/-- Function-template lookup captures the same finite recursive entry suffix,
    rather than only its tail or a cyclic heap location. -/
example : Environment.lookup (.functionTemplate 5 8 2 (.binding 1 (.integer 17) .empty)) 5 =
    some (.closure 8 2 (.functionTemplate 5 8 2 (.binding 1 (.integer 17) .empty))) := rfl

def entryWrapper : Graph := ⟨[
  node 0 (.integer 17) .integer,
  node 1 (.function ⟨8, .unit⟩ 0) (.function .unit .integer []),
  node 2 (.variable 5) (.function .unit .integer []),
  node 3 .unit,
  node 4 (.apply 2 3) .integer,
  node 5 (.recursiveBind [⟨⟨5, .function .unit .integer []⟩, 1⟩] 4) .integer], 5⟩

example : checkShape entryWrapper = .ok () := rfl
example : integerResult (run entryWrapper 100 (initial entryWrapper)) = some 17 := rfl

/-- Strict binary tuples allocate a real heap cell and return its location. -/
def tupleGraph : Graph := ⟨[
  node 0 (.integer 17) .integer, node 1 (.boolean true) .boolean,
  node 2 (.tuple [0, 1]) (.product .integer .boolean)], 2⟩

def tupleResult : RunResult → Bool
  | .done (.location 0) state => match state.heap with
      | [.pair (.integer 17) (.boolean true)] => true
      | _ => false
  | _ => false

example : tupleResult (run tupleGraph 20 (initial tupleGraph)) = true := rfl

/-- Exact exhaustive Boolean matching supports either source arm order. -/
def boolGraph : Graph := ⟨[
  node 0 (.boolean false) .boolean, node 1 (.integer 11) .integer,
  node 2 (.integer 7) .integer,
  node 3 (.matchCases 0 [⟨.boolean true, 1⟩, ⟨.boolean false, 2⟩]) .integer], 3⟩

example : integerResult (run boolGraph 20 (initial boolGraph)) = some 7 := rfl
example : selectArm [⟨.boolean false, 2⟩, ⟨.boolean true, 1⟩] (.boolean true) = .ok 1 := rfl
example : selectArm [⟨.boolean true, 1⟩] (.boolean true) = .error .unsupportedMatch := rfl
example : selectArm [⟨.unit, 1⟩] (.integer 0) = .error .unsupportedMatch := rfl

/-- Cell writes use the tuple heap; interpreter lookup resolves the lexical
    bound identity to its activation and checks the operand handle exactly. -/
def cellGraph : Graph := ⟨[
  node 0 (.integer 0) .integer,
  node 1 (.variable 4) (.reference (.bound 3)),
  node 2 (.integer 7) .integer,
  node 3 (.tuple [1, 2]) (.product (.reference (.bound 3)) .integer),
  node 4 (.request (.cell (.bound 3)) 1 3),
  node 5 (.request (.cell (.bound 3)) 0 1) .integer,
  node 6 (.bind ⟨5, .unit⟩ 4 5) .integer,
  node 7 (.resource 3 ⟨4, .reference (.bound 3)⟩ 0 6) .integer], 7⟩

example : checkShape cellGraph = .ok () := rfl
example : integerResult (run cellGraph 100 (initial cellGraph)) = some 7 := rfl
example : operations (run cellGraph 100 (initial cellGraph)) =
    [.acquired 7 0, .written 0 7, .read 0 7, .released 0] := rfl

/-- Repeated calls to one static resource site acquire distinct dynamic keys. -/
def repeatedCell : Graph := ⟨[
  node 0 (.variable 8) .integer,
  node 1 (.variable 4) (.reference (.bound 3)),
  node 2 (.request (.cell (.bound 3)) 0 1) .integer,
  node 3 (.resource 3 ⟨4, .reference (.bound 3)⟩ 0 2) .integer,
  node 4 (.function ⟨8, .integer⟩ 3) (.function .integer .integer []),
  node 5 (.variable 6) (.function .integer .integer []),
  node 6 (.integer 11) .integer,
  node 7 (.apply 5 6) .integer,
  node 8 (.integer 22) .integer,
  node 9 (.apply 5 8) .integer,
  node 10 (.bind ⟨7, .integer⟩ 7 9) .integer,
  node 11 (.bind ⟨6, .function .integer .integer []⟩ 4 10) .integer], 11⟩

example : checkShape repeatedCell = .ok () := rfl
example : integerResult (run repeatedCell 200 (initial repeatedCell)) = some 22 := rfl
example : operations (run repeatedCell 200 (initial repeatedCell)) =
    [.acquired 3 0, .read 0 11, .released 0, .acquired 3 1, .read 1 22, .released 1] := rfl

/-- A pure closure may retain an unused cell handle within its owner's scope.
    This does not yet resolve the callable-support admission discrepancy D4. -/
def capturedCell : Graph := ⟨[
  node 0 (.integer 0) .integer,
  node 1 (.variable 4) (.reference (.bound 3)),
  node 2 .unit,
  node 3 (.bind ⟨9, .reference (.bound 3)⟩ 1 2),
  node 4 (.function ⟨8, .unit⟩ 3) (.function .unit .unit []),
  node 5 (.variable 6) (.function .unit .unit []),
  node 6 (.apply 5 2),
  node 7 (.bind ⟨6, .function .unit .unit []⟩ 4 6),
  node 8 (.resource 3 ⟨4, .reference (.bound 3)⟩ 0 7)], 8⟩

example : unitResult (run capturedCell 100 (initial capturedCell)) = true := rfl
example : operations (run capturedCell 100 (initial capturedCell)) =
    [.acquired 8 0, .released 0] := rfl

/-- The complete generated graph is evaluated directly by the independent
    source machine, including nested capture/resume/discard and cleanup. -/
theorem exported_result : integerResult (run CoreExportedFixture.graph 1000 (initial CoreExportedFixture.graph)) =
    some 11 := by decide +kernel

def writtenValues (result : RunResult) : List Int :=
  (observations result).filterMap fun event => match event with
    | .written _ value => some value
    | _ => none

theorem exported_write_order : writtenValues (run CoreExportedFixture.graph 1000 (initial CoreExportedFixture.graph)) =
    [7, 11] := by decide +kernel

/-- The consumed nearest activation blocks an older live same-static owner. -/
example : findOwner 1 2 [.clauseBoundary 1 2 10 11 none,
    .clauseBoundary 1 2 20 21 (some [])] = .error (.consumedOwner 1 2) := rfl

example : closeFuel 10 [.cleanupCompletion 3 .unit] = .error .runningCloseBlocked := rfl
example : closeFuel 10 [.closeCompletion 3] = .error .runningCloseBlocked := rfl

/-- Resume restores the entire capture above the unchanged clause prefix. -/
example : returnResume
    { control := .returned .unit,
      frames := [.bind 8 0 .empty, .clauseBoundary 1 2 3 4
          (some [.resourceBoundary 0 5 17, .handlerBoundary 1 .empty 3])] }
    1 2 (.integer 11) = .stepped
    { control := .returned (.integer 11),
      frames := [.resourceBoundary 0 5 17, .handlerBoundary 1 .empty 3,
        .bind 8 0 .empty, .clauseBoundary 1 2 3 4 none],
      observations := [.resumed 4] } := rfl

/-- A nearer matching source handler overrides the builtin cell interpreter. -/
example : findInterpreter ⟨[node 0 .unit,
    node 1 (.handler 7 (.cell (.bound 3)) 0 [])], 1⟩ (.cell (.activation 5))
    [.handlerBoundary 1 (.resource 3 5 .empty) 9, .resourceBoundary 0 5 17] =
    .ok (.handler [] 1 (.resource 3 5 .empty) 9 [.resourceBoundary 0 5 17]) := rfl

/-- An empty nearest exact handler rejects a missing operation rather than
    falling through to an older handler or the builtin resource interpreter.
    These malformed raw states test error boundaries, not accepted Core. -/
def maskedCell : Graph := ⟨[
  node 0 .unit,
  node 1 (.handler 7 (.cell (.bound 3)) 0 []),
  node 2 (.handler 8 (.cell (.bound 3)) 0 [⟨0, .binder ⟨9, .unit⟩, 10, 0⟩])], 1⟩

example : request maskedCell
    { control := .returned (.handle 5),
      frames := [.handlerBoundary 1 (.resource 3 5 .empty) 9,
        .handlerBoundary 2 (.resource 3 5 .empty) 10, .resourceBoundary 0 5 17] }
    (.cell (.bound 3)) 0 (.resource 3 5 .empty) (.handle 5) =
    .rejected (.missingClause 0) := rfl

example : request cellGraph
    { control := .returned (.handle 6), frames := [.resourceBoundary 7 5 17] }
    (.cell (.bound 3)) 0 (.resource 3 5 .empty) (.handle 6) =
    .rejected .invalidCellOperand := rfl

example : request cellGraph { control := .returned (.handle 5) }
    (.cell (.bound 3)) 0 .empty (.handle 5) = .rejected (.unboundResource 3) := rfl

/-- Distinct activation arguments do not match even for the same static effect. -/
example : findInterpreter maskedCell (.cell (.activation 6))
    [.handlerBoundary 1 (.resource 3 5 .empty) 9, .resourceBoundary 0 6 17] =
    .ok (.cell ⟨[.handlerBoundary 1 (.resource 3 5 .empty) 9], 0, 6, 17, []⟩) := rfl

/-- Capture moves the complete inner prefix and selected handler, uses the
    handler's lexical environment, and leaves only its outside control active. -/
def captureGraph : Graph := ⟨[node 0 .unit,
  node 1 (.handler 7 (.cell (.bound 3)) 0 [⟨0, .binder ⟨9, .unit⟩, 10, 0⟩])], 1⟩

example : request captureGraph
    { control := .returned (.handle 5),
      frames := [.bind 8 0 .empty,
        .handlerBoundary 1 (.binding 100 (.integer 17) (.resource 3 5 .empty)) 9,
        .resourceBoundary 0 5 17] }
    (.cell (.bound 3)) 0 (.binding 100 (.integer 99) (.resource 3 5 .empty)) (.handle 5) =
    .stepped
    { control := .evaluate 0 (.binding 9 (.handle 5)
        (.binding 100 (.integer 17) (.resource 3 5 .empty))),
      frames := [.clauseBoundary 7 10 9 0 (some
        [.bind 8 0 .empty,
          .handlerBoundary 1 (.binding 100 (.integer 17) (.resource 3 5 .empty)) 9]),
        .resourceBoundary 0 5 17],
      nextOwner := 1, observations := [.captured 9 0] } := rfl

/-- Both completion forms stop at the consumed nearest matching activation. -/
def consumedState : CoreMachine.State :=
  { control := .returned .unit,
    frames := [.clauseBoundary 1 2 10 11 none,
      .clauseBoundary 1 2 20 21 (some [.resourceBoundary 0 5 17])] }

example : returnResume consumedState 1 2 .unit = .rejected (.consumedOwner 1 2) := rfl
example : discardOwner consumedState 1 2 = .rejected (.consumedOwner 1 2) := rfl

/-- Projection recursively includes the nested live ticket at its exact frame
    position. Consumed tickets, ordinary suffixes and handlers add no owners.
    The raw state isolates structural ownership independently of admission. -/
def nestedCapture : List CoreMachine.Frame :=
  [.cleanupBoundary 0 .empty 10,
    .clauseBoundary 2 3 20 21 (some
      [.resourceBoundary 0 1 11, .cleanupBoundary 0 .empty 11,
        .resourceBoundary 0 2 22, .handlerBoundary 0 .empty 20]),
    .clauseBoundary 4 5 30 31 none,
    .bind 90 1 .empty, .resourceBoundary 0 3 33, .handlerBoundary 0 .empty 3]

example : closeFuel (framesMass nestedCapture + 1) nestedCapture = .ok
    ([.cleanupBoundary 0 .empty 10, .resourceBoundary 0 1 11,
      .cleanupBoundary 0 .empty 11, .resourceBoundary 0 2 22,
      .resourceBoundary 0 3 33], [.nestedConsumed 21]) := rfl

def nestedCloseGraph : Graph := ⟨[node 0 .unit, node 1 (.integer 99) .integer,
  node 2 (.integer 17) .integer], 0⟩

def nestedCloseState : CoreMachine.State :=
  { control := .discard 1 2,
    frames := [.bind 8 2 .empty, .clauseBoundary 1 2 3 4 (some nestedCapture)],
    nextActivation := 4, nextOwner := 32, nextCleanup := 12 }

example : integerResult (run nestedCloseGraph 100 nestedCloseState) = some 17 := rfl
example : operations (run nestedCloseGraph 100 nestedCloseState) =
    [.discarded 4, .nestedConsumed 21, .closeStarted 0,
      .cleanupStarted 10, .cleanupFinished 10, .released 1,
      .cleanupStarted 11, .cleanupFinished 11, .released 2, .released 3,
      .closeFinished 0, .clauseReturned 4] := rfl

example : (observations (run nestedCloseGraph 100 nestedCloseState)).contains (.entered 1) =
    false := rfl

/-- Running cleanup or close completion blocks even under a nested live ticket. -/
example : discardOwner
    { control := .discard 1 2, frames := [.clauseBoundary 1 2 3 4
      (some [.clauseBoundary 2 3 5 6 (some [.cleanupCompletion 7 .unit])])] }
    1 2 = .rejected .runningCloseBlocked := rfl

example : next nestedCloseGraph
    { control := .returned .unit, frames := [.clauseBoundary 1 2 3 4 (some [])] } =
    .rejected (.liveClauseReturn 1 2) := rfl

example : next nestedCloseGraph
    { control := .returned (.integer 7), frames := [.cleanupCompletion 10 .unit] } =
    .rejected .cleanupResult := rfl

example : ∀ after, ¬ CoreMachine.Step nestedCloseGraph
    { control := .returned .unit, frames := [.clauseBoundary 1 2 3 4 (some [])] } after := by
  intro after
  exact rejected_not_step _ _ (.liveClauseReturn 1 2) rfl after

#print axioms exported_result
#print axioms exported_write_order
#print axioms CoreMachine.rejected_not_step
#print axioms CoreMachine.done_not_step

end Ash.OneShot.CoreMachineExamples
