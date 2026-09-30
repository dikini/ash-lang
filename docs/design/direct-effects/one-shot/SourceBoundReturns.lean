import SourceBoundSnapshots

/-! Returned values restore the exact queued source bounds. The existing
context grammar determines the pure value prefixes in the recomposed plan. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan)

def Annotation.plug {plan : Plan dependencies} (bounds : Annotation world plan)
    (position : SourceAnnotatedCode.Context) :
    Σ nextDependencies, Σ nextPlan : Plan nextDependencies, Annotation world nextPlan :=
  match position with
  | .appArgument _ _ => ⟨_, .sequence .pure (.sequence .pure plan), .sequence .absent (.sequence .absent bounds)⟩
  | _ => ⟨_, .sequence .pure plan, .sequence .absent bounds⟩

def returnPath (position : SourceAnnotatedCode.Context) (path : Path) : Path :=
  match position with
  | .appArgument _ _ => .second (.second path)
  | _ => .second path

/-- Every queued bound remains at the same source position beneath the
value prefixes. Ordinary/protected differences and absence are unchanged. -/
theorem Annotation.plug_lookup {plan : Plan dependencies} (bounds : Annotation world plan)
    (position : SourceAnnotatedCode.Context) :
    (bounds.plug position).2.2.lookup (returnPath position path) operation held = bounds.lookup path operation held := by
  cases position <;> rfl

end Ash.OneShot.SourcePlanBounds

namespace Ash.OneShot.SourceBoundSnapshots
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Return recomposition consumes precisely the head metadata frame and
retains the same tail, including all recursively dormant annotations. -/
inductive Returned (position : SourceAnnotatedCode.Context) : Snapshot world → Snapshot world → Prop where
  | plain {current : Plan currentDependencies} {context : Plan contextDependencies}
      {hints : Hints scope} {forest : Forest hints}
      (currentBounds : Annotation world current) (queued : Annotation world context) (remaining : Retained world forest) :
      Returned position
        ⟨_, current, currentBounds, _, .plain hints, .plain context forest, .plain queued remaining⟩
        (Snapshot.returned (.plain queued remaining) (queued.plug position).2.1 (queued.plug position).2.2)

theorem Returned.forest {before after : Snapshot world} (returned : Returned position before after) :
    ∃ dependencies, ∃ context : Plan dependencies, HEq before.forest (Forest.plain context after.forest) := by
  cases returned
  exact ⟨_, _, HEq.rfl⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourcePlanBounds.Annotation.plug_lookup
#print axioms Ash.OneShot.SourceBoundSnapshots.Returned.forest
