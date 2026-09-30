import CoreUnwindRelation

/-! Generic consumed-clause return and already-completed Unit close redexes.
The outside spine is explicitly PushedWithMaps. The close rule uses the locally
matched Core/target label required by Related.awaitingClose; it establishes no
global close-name mapping, empty-discard coverage or nested-ticket retirement.
No future interpretation or execution success is an input. -/
namespace Ash.OneShot.CoreCompletionSteps
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack
  CoreRequestFrames CoreUnwindRelation

def clauseBefore (base : CoreMachine.State) (handler owner occurrence ticket : Nat)
    (value : CoreMachine.Value) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned value,
    frames := .clauseBoundary handler owner occurrence ticket none :: framesOf maps }

def clauseAfter (base : CoreMachine.State) (ticket : Nat)
    (value : CoreMachine.Value) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned value, frames := framesOf maps,
    observations := base.observations ++ [.clauseReturned ticket] }

/-- A consumed clause returns any related value, restores its saved handler
scope/map, and preserves every supplied outside annotation. -/
theorem leave_clause_complete
    (header : OwnerHeader graph savedOwners base.heap handler owner occurrence data)
    (value : ValueRel graph currentOwners base.heap returned code)
    (outside : PushedWithMaps graph base.heap maps target)
    (ticket : Nat) (scope : Scope) :
    ComponentMapped graph currentOwners
      ((savedOwners,.clauseBoundary handler owner occurrence ticket none)::maps)
      (clauseBefore base handler owner occurrence ticket returned maps)
      ⟨code,scope,.spent ticket data.answer data.scope target⟩ ∧
    CoreMachine.next graph (clauseBefore base handler owner occurrence ticket returned maps) =
      .stepped (clauseAfter base ticket returned maps) ∧
    LexicalUnwind.Transition
      (.eval ⟨code,scope,.spent ticket data.answer data.scope target⟩)
      (.eval ⟨code,data.scope,target⟩) [] [] ∧
    ComponentMapped graph savedOwners maps (clauseAfter base ticket returned maps)
      ⟨code,data.scope,target⟩ := by
  have raw : RawStep ⟨code,scope,.spent ticket data.answer data.scope target⟩
      ⟨code,data.scope,target⟩ [] [] :=
    .leaveClause ticket data.answer code value.closed scope data.scope target
  exact ⟨⟨rfl,code,scope,.returned value,pushed_mapped (.spent header outside)⟩,
    rfl,.evaluate raw (raw_without_close_ordinary raw (by simp)),
    ⟨rfl,code,data.scope,.returned (value.owner_transport savedOwners),pushed_mapped outside⟩⟩

def closeBefore (base : CoreMachine.State) (identity : Nat) (maps : List MappedFrame) : CoreMachine.State :=
  { base with control := .returned .unit, frames := .closeCompletion identity :: framesOf maps }

def closeAfter (base : CoreMachine.State) (identity : Nat) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned .unit, frames := framesOf maps,
    observations := base.observations ++ [.closeFinished identity] }

/-- Complete the current awaitingClose redex with one locally matched label.
This uses the current lexical unwind transition, never RawStep.finishClose. -/
theorem finish_close_unit
    (outside : PushedWithMaps graph base.heap maps target)
    (identity : Nat) (owners : CoreTranslation.OwnerMap) (scope callerScope : Scope) :
    Related graph ⟨closeBefore base identity maps,
      .unwind scope (.push (.closing identity callerScope) target),owners,maps⟩ ∧
    CoreMachine.next graph (closeBefore base identity maps) = .stepped (closeAfter base identity maps) ∧
    LexicalUnwind.Transition
      (.unwind scope (.push (.closing identity callerScope) target))
      (.eval ⟨.unit,callerScope,target⟩) [] [.close identity] ∧
    ComponentMapped graph owners maps (closeAfter base identity maps) ⟨.unit,callerScope,target⟩ := by
  exact ⟨.awaitingClose rfl rfl outside,rfl,.finishClose,
    ⟨rfl,.unit,callerScope,.returned .unit,pushed_mapped outside⟩⟩

/-- Returning across a still-live owner is rejected, never implicit retirement. -/
theorem live_clause_rejected {base : CoreMachine.State} :
    CoreMachine.next graph { base with
      control := .returned value,
      frames := .clauseBoundary handler owner occurrence ticket (some captured) :: framesOf maps } =
      .rejected (.liveClauseReturn handler owner) := rfl

theorem live_clause_not_step {base : CoreMachine.State} (after : CoreMachine.State) :
    ¬ CoreMachine.Step graph { base with
      control := .returned value,
      frames := .clauseBoundary handler owner occurrence ticket (some captured) :: framesOf maps } after :=
  CoreMachine.rejected_not_step graph _ (.liveClauseReturn handler owner) live_clause_rejected after

/-- A completed close accepts only the actual Unit return. -/
theorem nonunit_close_rejected {base : CoreMachine.State} (notUnit : value ≠ CoreMachine.Value.unit) :
    CoreMachine.next graph { base with
      control := .returned value,
      frames := .closeCompletion identity :: framesOf maps } = .rejected .closeResult := by
  cases value <;> first | exact False.elim (notUnit rfl) | rfl

theorem nonunit_close_not_step {base : CoreMachine.State} (notUnit : value ≠ CoreMachine.Value.unit)
    (after : CoreMachine.State) :
    ¬ CoreMachine.Step graph { base with
      control := .returned value,
      frames := .closeCompletion identity :: framesOf maps } after :=
  CoreMachine.rejected_not_step graph _ .closeResult (nonunit_close_rejected notUnit) after

#print axioms leave_clause_complete
#print axioms finish_close_unit
#print axioms live_clause_rejected
#print axioms live_clause_not_step
#print axioms nonunit_close_rejected
#print axioms nonunit_close_not_step
end Ash.OneShot.CoreCompletionSteps
