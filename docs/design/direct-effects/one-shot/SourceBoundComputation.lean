import SourceBoundSnapshots
import SourceAnnotatedCode

/-! Ordinary computation selects existing checking plans and their exact bound
packets. Source substitution separately authenticates the rewritten expression
at the stable signature; this relation does not identify old literal clauses
with substituted clauses or establish declaration admission at handler entry. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan)

def Annotation.left {first : Plan firstDependencies} {second : Plan secondDependencies} :
    Annotation world (.choice first second) → Annotation world first
  | .absent => .absent
  | .choice first _ => first

def Annotation.right {first : Plan firstDependencies} {second : Plan secondDependencies} :
    Annotation world (.choice first second) → Annotation world second
  | .absent => .absent
  | .choice _ second => second

inductive ComputationRule where
  | bind | beta | ifTrue | ifFalse

inductive Reduced (world : List Nat) : ComputationRule →
    {beforeDependencies afterDependencies : SourceDependencyAnnotations.Dependencies} →
    {before : Plan beforeDependencies} → {after : Plan afterDependencies} →
    Annotation world before → Annotation world after → Prop where
  | bind (source : Annotation world (.sequence initial body)) :
      Reduced world .bind source source.second
  | beta (source : Annotation world (.sequence function (.sequence argument body))) :
      Reduced world .beta source source.second.second
  | ifTrue (source : Annotation world (.sequence condition (.choice yes no))) :
      Reduced world .ifTrue source source.second.left
  | ifFalse (source : Annotation world (.sequence condition (.choice yes no))) :
      Reduced world .ifFalse source source.second.right

def ComputationRule.sourcePath (rule : ComputationRule) (path : Path) : Path :=
  match rule with
  | .bind => .second path
  | .beta => .second (.second path)
  | .ifTrue => .second (.first path)
  | .ifFalse => .second (.second path)

theorem Annotation.left_lookup {first : Plan firstDependencies} {second : Plan secondDependencies}
    (annotation : Annotation world (.choice first second)) :
    annotation.left.lookup path operation held = annotation.lookup (.first path) operation held := by
  cases annotation <;> rfl

theorem Annotation.right_lookup {first : Plan firstDependencies} {second : Plan secondDependencies}
    (annotation : Annotation world (.choice first second)) :
    annotation.right.lookup path operation held = annotation.lookup (.second path) operation held := by
  cases annotation <;> rfl

/-- Every surviving bound is the original observation at the selected path.
This covers absent packets and both ordinary and protected operation modes. -/
theorem Reduced.lookup {before : Plan beforeDependencies} {after : Plan afterDependencies}
    {source : Annotation world before} {next : Annotation world after}
    (reduced : Reduced world rule source next) :
    next.lookup path operation held = source.lookup (rule.sourcePath path) operation held := by
  cases reduced <;> simp only [ComputationRule.sourcePath, Annotation.second_lookup, Annotation.left_lookup, Annotation.right_lookup]

end Ash.OneShot.SourcePlanBounds

namespace Ash.OneShot.SourceAnnotatedCode

/-- The rule is read from source syntax, not extracted from proof data.
The supplied reduction restricts the source to bind, beta or a Boolean branch. -/
def Reduction.rule {before : Term} (_step : Reduction before scope after nextScope) : SourcePlanBounds.ComputationRule :=
  match before with
  | .bind _ _ _ _ => .bind
  | .app _ _ _ => .beta
  | .branch _ (.boolean _ true) _ _ => .ifTrue
  | _ => .ifFalse

end Ash.OneShot.SourceAnnotatedCode

namespace Ash.OneShot.SourceBoundSnapshots
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation Reduced ComputationRule)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Computation changes the current plan only; the complete retained data,
including dormant branches and callback bounds, are the same value. -/
def Snapshot.computed (source : Snapshot world) (plan : Plan nextDependencies)
    (bounds : Annotation world plan) : Snapshot world :=
  ⟨_, plan, bounds, source.scope, source.hints, source.forest, source.pending⟩

inductive Computed (rule : ComputationRule) : Snapshot world → Snapshot world → Prop where
  | step (source : Snapshot world) {next : Plan nextDependencies} (bounds : Annotation world next)
      (selected : Reduced world rule source.current bounds) :
      Computed rule source (source.computed next bounds)

theorem Computed.forest {before after : Snapshot world} (step : Computed rule before after) :
    HEq before.forest after.forest := by cases step; rfl

theorem Computed.pending {before after : Snapshot world} (step : Computed rule before after) :
    HEq before.pending after.pending := by cases step; rfl

theorem Computed.lookup {before after : Snapshot world} (step : Computed rule before after) :
    after.current.lookup path operation held = before.current.lookup (rule.sourcePath path) operation held := by
  cases step with
  | step source bounds selected => exact selected.lookup

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourcePlanBounds.Annotation.left_lookup
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.right_lookup
#print axioms Ash.OneShot.SourcePlanBounds.Reduced.lookup
#print axioms Ash.OneShot.SourceBoundSnapshots.Computed.forest
#print axioms Ash.OneShot.SourceBoundSnapshots.Computed.pending
#print axioms Ash.OneShot.SourceBoundSnapshots.Computed.lookup
