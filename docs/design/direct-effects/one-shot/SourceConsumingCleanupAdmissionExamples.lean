import SourceConsumingCleanupAdmission

/-! Source admission examples for effectful cleanup around one-shot consumption.
The positive source writes a cell and chooses resume or dispose, while the
registered cleanup reads that cell. Independent negative cases check declared
cleanup dependencies and the consumed-owner phase. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.Examples
open SourceConsumingClauseAnnotations (Body Admitted)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open OwnerPhaseTransitions (Phases spend)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)

def actions : Syntax.UsageTickets := fun owner => if owner = 19 then some ⟨true, true⟩ else none
def phases : Phases := OwnerPhaseTransitions.available [19]
def waiting : Forest (Hints.cell (identity := 4) .nil) := .cell .nil
def whole := Forest.live (owner := 19) .nil waiting

def context (phases : Phases) : Context [4] 19 [] actions phases whole .nil .nil waiting where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨.operations .nil, rfl⟩
  closing := fun _ => ⟨.operations .nil, rfl⟩
  disposal := fun _ => ⟨rfl, rfl⟩
  after := .cell (.operations .nil)
  tailReady := rfl

/-- Empty saved code and the cell-only waiting tail carry no explicit bounds,
so this example admits every annotation without a metadata premise. -/
theorem every_annotation_bounds (other : Context [4] 19 [] actions phases whole .nil .nil waiting) :
    (context phases).BoundsAgree other := by
  constructor
  · intro permission
    rw [SourceScheduledSourceRechecking.retained_nil_eq (other.resumption permission).val]
    rfl
  · intro permission
    rw [SourceScheduledSourceRechecking.retained_nil_eq (other.closing permission).val]
    rfl
  · cases other.after with
    | operations => rfl
    | cell tail => rw [SourceScheduledSourceRechecking.retained_nil_eq tail]; rfl

def continuation := Plan.choice (.invoke (key := ⟨19, .resume⟩)) (.invoke (key := ⟨19, .dispose⟩))
def clause (needs : List Instance) := Plan.cleanup (needs := needs)
  (.request (effect := .cell 4) (operation := 0))
  (.sequence (.request (effect := .cell 4) (operation := 1)) continuation)

def body (needs : List Instance) : Body [4] 19 (clause needs) :=
  .cleanup [(.cell 4, 0)] .request .request
    (.sequence [(.cell 4, 1)] .request .request (.choice .resume .dispose))

theorem source_admitted : Admitted ⟨true, true⟩ [] [] (body needs) [(.cell 4, 0), (.cell 4, 1)] :=
  .cleanup (.sequence (.choice (.resume rfl) (.dispose rfl)))

/-- The actual compiler emits no new saved-source obligations here: the saved
forest is empty. The separate clause check still verifies the callback's read. -/
theorem primitive_checks : Checked [] ((context phases).cleanupChecks
    (RequestFootprint.request (effect := .cell 4) (operation := 0))
    (Declared.request (world := [4])) [.cell 4]) := by
  apply checked_iff.mpr
  change True ∧ True
  exact ⟨True.intro, True.intro⟩

/-- Admission accepts an effectful callback and both permitted consumption
branches; it does not use a successful successor annotation as evidence. -/
theorem contextual_admitted : At (recipeLaws []) (fun evidence => evidence)
    (body [.cell 4]) (context phases) := by
  refine At.cleanupSource ?_ (fun _ => .empty) (fun _ => .empty) (.sequence (.choice .resume .dispose))
  intro request member
  exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member))

theorem clause_checked : (body [.cell 4]).BoundCheck [] [] actions phases
    (.live 19 .nil (.cell 4 .nil)) (.cell 4 .nil) .nil :=
  source_admitted.at_capture rfl rfl rfl

theorem generated_clause : ∃ annotation : Code [4] (clause [.cell 4]) whole,
    annotation.Valid [] actions phases :=
  contextual_admitted.generate clause_checked

theorem scheduled_clause : SourceScheduledChecks.Local [] actions phases [4] (clause [.cell 4]) whole :=
  contextual_admitted.scheduled clause_checked

/-- A footprint omission is rejected even though the read operation exists at
registration. This is the source-level check motivated by the route counterexample. -/
theorem omitted_dependency_rejected : ¬ At (recipeLaws []) (fun evidence => evidence)
    (body []) (context phases) := by
  intro admitted
  have impossible := admitted.cleanup_dependencies (.cell 4, 0) (by simp)
  cases impossible

/-- Primitive cleanup checks do not carry phase information. They can still
hold after consumption; the independent clause contract rejects another use. -/
theorem consumed_owner_rejected :
    Checked [] ((context (spend phases 19)).cleanupChecks
      (RequestFootprint.request (effect := .cell 4) (operation := 0))
      (Declared.request (world := [4])) [.cell 4]) ∧
    ¬ (body [.cell 4]).BoundCheck [] [] actions (spend phases 19)
      (.live 19 .nil (.cell 4 .nil)) (.cell 4 .nil) .nil := by
  refine ⟨primitive_checks, ?_⟩
  intro checked
  have available := checked.1.2.1.2.1
  simp [spend] at available

/-- A resource binder is interleaved between cleanup registration and owner
consumption. The new resource operation is supplied for every fresh identity. -/
def resourceClause := Plan.cleanup (needs := [.cell 4])
  (.request (effect := .cell 4) (operation := 0))
  (.resource (fun identity => .sequence (.request (effect := .cell identity) (operation := 0)) continuation))

def resourceBody : Body [4] 19 resourceClause :=
  .cleanup [(.cell 4, 0)] .request .request (.resource (fun identity _ =>
    .sequence [(.cell identity, 0)] .request .request (.choice .resume .dispose)))

theorem resource_source_admitted : Admitted ⟨true, true⟩ [] [] resourceBody [(.cell 4, 0)] := by
  apply Admitted.cleanup
  apply Admitted.resource
  intro identity fresh
  apply Admitted.weaken (.sequence (.choice (.resume rfl) (.dispose rfl)))
  intro request member
  exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp member))

theorem resource_contextual_admitted : At (recipeLaws []) (fun evidence => evidence)
    resourceBody (context phases) := by
  refine At.cleanupSource ?_ (fun _ => .empty) (fun _ => .empty) (.resource (fun _ _ => .sequence (.choice .resume .dispose)))
  intro request member
  exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member))

theorem resource_scheduled : SourceScheduledChecks.Local [] actions phases [4] resourceClause whole :=
  resource_contextual_admitted.scheduled
    (resource_source_admitted.at_capture rfl rfl rfl)

end Ash.OneShot.SourceConsumingCleanupAdmission.Examples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.source_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.primitive_checks
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.contextual_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.clause_checked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.generated_clause
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.scheduled_clause
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.omitted_dependency_rejected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.consumed_owner_rejected

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.resource_source_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.resource_contextual_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.resource_scheduled

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Examples.every_annotation_bounds
