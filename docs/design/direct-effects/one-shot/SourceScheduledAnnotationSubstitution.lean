import SourceScheduledAnnotationRewriting
import SourceAnnotatedSubstitution

/-! Connect annotation rewriting to the existing closed source substitution
proof and exact saved-plan registries. This does not replace source typing or
assert that arbitrary clause changes are semantics-preserving. -/
namespace Ash.OneShot.SourcePlanRewriting
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Saved Annotations Matches)

def ClauseMap.saved (change : ClauseMap) (source : Saved) : Saved :=
  ⟨source.scope, source.hints, change.forest source.forest⟩

def ClauseMap.annotations (change : ClauseMap) (source : Annotations) : Annotations :=
  fun owner => (source owner).map change.saved

theorem ClauseMap.annotation_scopes (change : ClauseMap) (source : Annotations) :
    (change.annotations source).scopes = source.scopes := by
  funext owner
  simp only [ClauseMap.annotations, Annotations.scopes]
  cases source owner <;> rfl

theorem ClauseMap.annotation_insert (change : ClauseMap) (source : Annotations) (entry : Saved) :
    change.annotations (source.insert owner entry) = (change.annotations source).insert owner (change.saved entry) := by
  funext other
  simp only [ClauseMap.annotations, Annotations.insert]
  split <;> rfl

/-- Every recursively saved branch stays linked to its own rewritten plan.
Scope-only equality is not used as a substitute for registry agreement. -/
theorem ClauseMap.matches (change : ClauseMap) {hints : Hints scope} {forest : Forest hints}
    {registry : Annotations} (matched : Matches registry forest) :
    Matches (change.annotations registry) (change.forest forest) := by
  induction matched with
  | nil => exact .nil
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live known inside tail ihInside ihTail =>
      exact .live (by simp only [ClauseMap.annotations, known, Option.map_some, ClauseMap.saved]) ihInside ihTail
  | spent next ih => exact .spent ih

end Ash.OneShot.SourcePlanRewriting

namespace Ash.OneShot.SourcePlannedRecipeDeclarations
open SourceDeclarationPlans (ClausePlans)

/-- Substitution retargets the selected literal clause and keeps its exact
offered plans. This applies to both modes and to any number of skipped clauses;
it does not require the selected plans to belong to the older recipe grammar. -/
theorem Selected.substitution {declarations : ClausePlans clauses families}
    (selected : Selected operation held declarations parameter binder body plans) :
    Selected operation held (SourcePlanSignatures.substituteClauses declarations name value)
      parameter binder (if name = parameter then body else body.subst name value) plans := by
  induction selected with
  | ordinary => exact .ordinary
  | protectedMode => exact .protectedMode
  | pass different next ih => exact .pass different ih

end Ash.OneShot.SourcePlannedRecipeDeclarations

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceAnnotatedSources (Expression ValueSummary)

/-- Closed substitution retains rich source typing and the independently
validated scheduling annotation. The source proof is the existing substitution
theorem; the checking-witness rewrite reuses stable declaration signatures. -/
theorem source_substitution {hints : Hints receiving} {forest : Forest hints} {plan : Plan dependencies}
    (source : Expression operations policy contracts world allowed scope (environment.extend name input)
      expression result demand requirements (signature plan))
    (replacement : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ScopedExpressions.ClosedValue value.erase)
    (annotation : Code world plan forest) (validated : annotation.Valid outward actions phases) :
    let change := SourcePlanRewriting.substitution name value.erase closed.1
    Expression operations policy contracts world allowed scope environment (expression.subst name value)
      result demand requirements (signature (change.plan plan)) ∧
    (annotation.rewrite change).Valid outward actions phases := by
  dsimp only
  constructor
  · rw [SourcePlanRewriting.ClauseMap.plan_signature]
    exact SourceAnnotatedSources.substitution source replacement closed
  · exact (annotation.valid_rewrite _).mpr validated

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourcePlanRewriting.ClauseMap.annotation_scopes
#print axioms Ash.OneShot.SourcePlanRewriting.ClauseMap.annotation_insert
#print axioms Ash.OneShot.SourcePlanRewriting.ClauseMap.matches
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Selected.substitution
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.source_substitution
