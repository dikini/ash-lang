import CoreInitialPrefix

/-! Historical resource correspondence for the independent Core evaluator and
existing target creation ledgers. This is not target M4 validity, live ownership,
handler/ticket/cleanup freshness, capacity safety or a general simulation. -/
namespace Ash.OneShot.CoreAllocationCorrespondence
open ScopedExpressions ScopedExecution
open CoreAllocationHistory

/-- Both sides remember all issued resources, including released resources. -/
def Corresponds (state : CoreMachine.State) (issued : List Owner) : Prop :=
  acquiredKeys state.observations = ScopedTyping.resourceWorld issued

/-- Local event agreement only: the actual counter identifies whether this
Core step allocates, and the target segment creates the same resource key.
Non-resource owner events are deliberately outside this projection. -/
def MatchesAllocation (before after : CoreMachine.State) (created : List Owner) : Prop :=
  (after.nextActivation = before.nextActivation ∧ ScopedTyping.resourceWorld created = []) ∨
  (after.nextActivation = before.nextActivation + 1 ∧
    ScopedTyping.resourceWorld created = [before.nextActivation])

theorem initial_correspondence (graph : CoreSyntax.Graph) : Corresponds (CoreMachine.initial graph) [] := rfl

/-- Derive successor history from actual next and local event matching, not a
supplied successor-world equality. RawTrace grounds the target creation list in
an actual target segment, including multi-step acquisition or silent identity. -/
theorem paired_segment_preserves (graph : CoreSyntax.Graph)
    {before after : CoreMachine.State} {targetBefore targetAfter : Configuration}
    {issued created discharged : List Owner}
    (core : CoreMachine.Step graph before after)
    (_target : RawTrace targetBefore targetAfter created discharged)
    (current : Corresponds before issued) (matched : MatchesAllocation before after created) :
    Corresponds after (issued ++ created) := by
  rcases next_delta graph before after core with ⟨counter, history⟩ | ⟨counter, history⟩
  · rcases matched with ⟨same, none⟩ | ⟨increment, one⟩
    · simp only [Corresponds, ScopedTyping.resource_world_append, none, List.append_nil]
      exact history.trans current
    · omega
  · rcases matched with ⟨same, none⟩ | ⟨increment, one⟩
    · omega
    · simp only [Corresponds, ScopedTyping.resource_world_append, one]
      exact history.trans (congrArg (· ++ [before.nextActivation]) current)

/-- The next Core counter is fresh in the current target resource world because
it is absent from the actual initial-to-current acquisition history. -/
theorem current_counter_fresh (graph : CoreSyntax.Graph) {count : Nat}
    {state : CoreMachine.State} {issued : List Owner}
    (reached : CoreAllocationHistory.Steps graph count (CoreMachine.initial graph) state)
    (current : Corresponds state issued) :
    state.nextActivation ∉ ScopedTyping.resourceWorld issued ∧
      Owner.resource state.nextActivation ∉ issued := by
  have fresh : state.nextActivation ∉ ScopedTyping.resourceWorld issued := by
    rw [← current]
    exact history_fresh state (initial_steps_history graph reached)
  exact ⟨fresh, fun member => fresh (ScopedTyping.mem_resource_world.mpr member)⟩

/-- A point in the existing linked prefix is reached by actual next transitions.
This extracts a prefix without inventing another transition relation. -/
theorem chain_member_steps
    {before after : CoreInitialPrefix.Point} {points : List CoreInitialPrefix.Point}
    (chain : CoreInitialPrefix.Chain CoreExportedFixture.graph before points after)
    (point : CoreInitialPrefix.Point) (member : point ∈ points) :
    ∃ count, CoreAllocationHistory.Steps CoreExportedFixture.graph count before.state point.state := by
  induction chain with
  | last link =>
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨1, .snoc (.refl _) link.core_next⟩
  | next link rest ih =>
    rcases List.mem_cons.mp member with same | remaining
    · cases same; exact ⟨1, .snoc (.refl _) link.core_next⟩
    · obtain ⟨count, suffix⟩ := ih remaining
      exact ⟨1 + count, CoreAllocationHistory.Steps.trans (.snoc (.refl _) link.core_next) suffix⟩

open CoreInitialPrefix
open CoreExportedFixture (graph)

def targetInitial : RunState := ⟨rootTarget, [], []⟩
def targetEndpoint : RunState := ⟨cellTarget, [.resource 0], []⟩

/-- The complete frozen prefix's actual raw creation list enacts this concrete
historical ledger. Owner freshness is discharged for this empty-ledger case. -/
theorem exported_target_steps : RunSteps targetInitial targetEndpoint := by
  simpa [targetInitial, targetEndpoint] using
    (raw_trace_enacts (issued := []) (completed := []) exported_target_ledger (by decide))

theorem exported_endpoint_correspondence : Corresponds s12 targetEndpoint.issued := by
  have history := exported_acquisition_history
  simpa [History, Corresponds, targetEndpoint, s12, ScopedTyping.resourceWorld] using history

theorem exported_target_world : ScopedTyping.resourceWorld targetEndpoint.issued = [0] := rfl

/-- Exact initial/endpoint history and both actual executions are constructed;
no caller supplies resource-world equality or successor correspondence. -/
theorem exported_prefix_resource_history :
    CoreAllocationHistory.Steps graph 12 (CoreMachine.initial graph) s12 ∧
    RunSteps targetInitial targetEndpoint ∧
    Corresponds (CoreMachine.initial graph) targetInitial.issued ∧
    Corresponds s12 targetEndpoint.issued ∧
    ScopedTyping.resourceWorld targetEndpoint.issued = [0] ∧
    s12.nextActivation ∉ ScopedTyping.resourceWorld targetEndpoint.issued := by
  exact ⟨exported_core_steps, exported_target_steps, initial_correspondence graph,
    exported_endpoint_correspondence, exported_target_world,
    (current_counter_fresh graph exported_core_steps exported_endpoint_correspondence).1⟩

theorem before_acquisition_reached : ∃ count, CoreAllocationHistory.Steps graph count (CoreMachine.initial graph) s11 := by
  simpa [p0, p11, point, s0] using chain_member_steps exported_initial_prefix p11 (by simp)

theorem before_acquisition_correspondence : Corresponds s11 [] := rfl

theorem exported_acquisition_fresh : s11.nextActivation ∉ ScopedTyping.resourceWorld [] ∧
    Owner.resource s11.nextActivation ∉ ([] : List Owner) := by
  obtain ⟨count, reached⟩ := before_acquisition_reached
  exact current_counter_fresh graph reached before_acquisition_correspondence

/- Allocation is checked once more as the exact local pair: one Core transition
and two raw target steps (enter cell, then ordinary handle binding). -/
private def acquiredTarget : Configuration :=
  ⟨.bind 4 (.resourceRef (.activation 0))
    (body47.instantiate (Instantiation.Environment.empty.bind 0 0)), .none,
    .push (.cell 0 0 .none .integer) .nil⟩

theorem exported_acquisition_target : RawTrace resourceTarget cellTarget [.resource 0] [] := by
  have resourceClosed : resourceCode.ResourceClosed := by
    change resourceCode.freeNames = []
    decide
  have enter : RawStep resourceTarget acquiredTarget [.resource 0] [] := by
    simpa [resourceTarget, resourceCode, acquiredTarget, Code.instantiate,
      Instantiation.ResourceName.instantiate, Instantiation.Environment.bind] using
      RawStep.enterCell 0 0 0 (.bind 4 (.resourceRef (.bound 0)) body47) .none .integer .nil resourceClosed
  have bodyReady : ClosedExcept 4 (body47.instantiate (Instantiation.Environment.empty.bind 0 0)) := by
    have supported : (body47.instantiate (Instantiation.Environment.empty.bind 0 0)).dependencies.all
        (fun dependency => match dependency with | .variable name => name == 4 | _ => true) = true := by decide
    intro name member
    simpa using List.all_eq_true.mp supported (.variable name) member
  have handleClosed : ClosedValue (.resourceRef (.activation 0)) :=
    (CoreValueRelation.ValueRel.handle (graph := graph) (owners := []) (heap := []) (key := 0)).closed
  have bind : RawStep acquiredTarget cellTarget [] [] := by
    exact RawStep.bind 4 _ _ .none _ handleClosed bodyReady
  exact .next enter (.next bind (.refl _))

theorem exported_acquisition_matches : MatchesAllocation s11 s12 [.resource 0] :=
  Or.inr ⟨rfl, rfl⟩

theorem exported_acquisition_correspondence : Corresponds s12 [.resource 0] :=
  paired_segment_preserves graph (before := s11) (after := s12) (issued := [])
    (by rfl) exported_acquisition_target before_acquisition_correspondence exported_acquisition_matches

#print axioms initial_correspondence
#print axioms exported_target_world
#print axioms before_acquisition_correspondence
#print axioms paired_segment_preserves
#print axioms current_counter_fresh
#print axioms chain_member_steps
#print axioms exported_target_steps
#print axioms exported_endpoint_correspondence
#print axioms exported_prefix_resource_history
#print axioms before_acquisition_reached
#print axioms exported_acquisition_fresh
#print axioms exported_acquisition_target
#print axioms exported_acquisition_matches
#print axioms exported_acquisition_correspondence
end Ash.OneShot.CoreAllocationCorrespondence
