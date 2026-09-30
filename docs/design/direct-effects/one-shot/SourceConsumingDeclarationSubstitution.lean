import SourceConsumingClauseAdmission
import SourceScheduledAnnotationSubstitution

/-! Closed substitution preserves the new structural declaration judgment.
Actual offered plans remain the same; the existing source substitution theorem
separately authenticates the substituted clause code and its rich types. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (ClausePlans)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)

section
variable [declarations : DeclarationPolicy]

def Declarations.substitution {plans : ClausePlans clauses families}
    (annotated : Declarations world plans) (name : Nat) (value : ScopedExpressions.Code) :
    Declarations world (SourcePlanSignatures.substituteClauses plans name value) :=
  match annotated with
  | .nil => .nil
  | .cons ordinary protectedMode rest => .cons ordinary protectedMode (rest.substitution name value)

private theorem mode_substitution {body : ScopedExpressions.Code}
    {modes : Modes world plans}
    (admitted : ModeAdmitted body.requiredActions resumeRequired closeRequired required modes)
    (isValue : value.IsValue) :
    ModeAdmitted (if name = parameter then body else body.subst name value).requiredActions
      resumeRequired closeRequired required modes := by
  split
  · exact admitted
  · simpa only [ScopedExpressions.Code.substitution_required_actions _ _ isValue] using admitted

/-- Reuse the established preservation of required continuation actions under
value substitution. No new declaration or future-body proof is supplied. -/
theorem DeclarationAdmitted.substitution {plans : ClausePlans clauses families}
    {annotated : Declarations world plans} (admitted : DeclarationAdmitted required annotated)
    (isValue : value.IsValue) : DeclarationAdmitted required (annotated.substitution name value) := by
  induction admitted with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      simp only [Declarations.substitution, SourcePlanSignatures.substituteClauses]
      exact .cons (mode_substitution ordinary isValue) (mode_substitution protectedMode isValue) ih

/-- Selection after substitution retains the admitted exact offered body and
its interface bounds, using the existing selection-substitution theorem. -/
theorem DeclarationAdmitted.selected_substitution {plans : ClausePlans clauses families}
    {annotated : Declarations world plans} (admitted : DeclarationAdmitted required annotated)
    (selected : SourcePlannedRecipeDeclarations.Selected operation held plans parameter binder code bodies)
    (isValue : value.IsValue) :
    ∃ resumeRequired closeRequired needed, ∃ body : Body world owner (bodies owner),
      Admitted (if name = parameter then code else code.subst name value).requiredActions
        resumeRequired closeRequired body needed ∧ needed ⊆ required :=
  (admitted.substitution (name := name) isValue).selected selected.substitution

end

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DeclarationAdmitted.substitution
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DeclarationAdmitted.selected_substitution
