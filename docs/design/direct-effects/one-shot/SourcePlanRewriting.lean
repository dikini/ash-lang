import SourceScheduledNeutral
import SourcePlanSignatures

/-! Signature-preserving changes of literal clause witnesses. The checking
dependency tree, ordered scopes and owner identities stay fixed. Actual source
typing must independently justify the corresponding expression transformation. -/
namespace Ash.OneShot.SourcePlanRewriting
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (Signature signature clauseSignatures)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledNeutral (OwnerCut)

/-- A rewrite changes literal clause syntax while preserving the authenticated
checking signature, including the required continuation actions. -/
structure ClauseMap where
  apply : {clauses : ScopedExpressions.Clauses} → {families : SourceDependencyAnnotations.ClauseDependencies} →
    ClausePlans clauses families → Σ nextClauses, ClausePlans nextClauses families
  preserves : ∀ {clauses families} (plans : ClausePlans clauses families),
    clauseSignatures (apply plans).2 = clauseSignatures plans

@[reducible] def ClauseMap.plan (rewrite : ClauseMap) (source : Plan dependencies) : Plan dependencies :=
  match source with
  | .pure => .pure
  | .request => .request
  | .invoke => .invoke
  | .sequence first second => .sequence (rewrite.plan first) (rewrite.plan second)
  | .choice first second => .choice (rewrite.plan first) (rewrite.plan second)
  | .handler required declarations body => .handler required (rewrite.apply declarations).2 (rewrite.plan body)
  | .cleanup callback body => .cleanup (rewrite.plan callback) (rewrite.plan body)
  | .resource body => .resource (fun identity => rewrite.plan (body identity))

theorem ClauseMap.plan_signature (rewrite : ClauseMap) (source : Plan dependencies) :
    signature (rewrite.plan source) = signature source := by
  cases source with
  | pure | request | invoke => rfl
  | sequence first second =>
      change Signature.sequence (signature (rewrite.plan first)) (signature (rewrite.plan second)) =
        Signature.sequence (signature first) (signature second)
      exact congr (congrArg Signature.sequence (rewrite.plan_signature first)) (rewrite.plan_signature second)
  | choice first second =>
      change Signature.choice (signature (rewrite.plan first)) (signature (rewrite.plan second)) =
        Signature.choice (signature first) (signature second)
      exact congr (congrArg Signature.choice (rewrite.plan_signature first)) (rewrite.plan_signature second)
  | handler required declarations body =>
      change Signature.handler required (clauseSignatures (rewrite.apply declarations).2) (signature (rewrite.plan body)) =
        Signature.handler required (clauseSignatures declarations) (signature body)
      exact congr (congrArg (Signature.handler required) (rewrite.preserves declarations)) (rewrite.plan_signature body)
  | cleanup callback body =>
      change Signature.cleanup (signature (rewrite.plan callback)) (signature (rewrite.plan body)) =
        Signature.cleanup (signature callback) (signature body)
      exact congr (congrArg Signature.cleanup (rewrite.plan_signature callback)) (rewrite.plan_signature body)
  | resource body => exact congrArg Signature.resource (funext (fun identity => rewrite.plan_signature (body identity)))
termination_by structural source

@[reducible] def ClauseMap.forest (rewrite : ClauseMap) (source : Forest hints) : Forest hints :=
  match source with
  | .nil => .nil
  | .plain plan rest => .plain (rewrite.plan plan) (rewrite.forest rest)
  | .handler rest => .handler (rewrite.forest rest)
  | .cell rest => .cell (rewrite.forest rest)
  | .cleanup plan rest => .cleanup (rewrite.plan plan) (rewrite.forest rest)
  | .running rest => .running (rewrite.forest rest)
  | .live saved rest => .live (rewrite.forest saved) (rewrite.forest rest)
  | .spent rest => .spent (rewrite.forest rest)

theorem ClauseMap.forest_append (rewrite : ClauseMap) (first : Forest front) (second : Forest tail) :
    rewrite.forest (first.append second) = (rewrite.forest first).append (rewrite.forest second) := by
  induction first <;> simp_all [ClauseMap.forest, Forest.append] <;> rfl

theorem ClauseMap.forest_closing (rewrite : ClauseMap) (source : Forest hints) :
    rewrite.forest source.forClosing = (rewrite.forest source).forClosing := by
  induction source with
  | nil => rfl
  | plain plan rest ih | handler rest ih | spent rest ih => exact ih
  | cell rest ih => exact congrArg Forest.cell ih
  | cleanup plan rest ih => exact congrArg (Forest.cleanup (rewrite.plan plan)) ih
  | running rest ih => exact congrArg Forest.running ih
  | live saved rest ihSaved ihRest =>
      change rewrite.forest (saved.forClosing.append (.running rest.forClosing)) =
        (rewrite.forest saved).forClosing.append (.running (rewrite.forest rest).forClosing)
      rw [rewrite.forest_append saved.forClosing (.running rest.forClosing)]
      change (rewrite.forest saved.forClosing).append (.running (rewrite.forest rest.forClosing)) = _
      rw [ihSaved, ihRest]

/-- Selection retains exactly the rewritten saved and waiting source pieces.
The rewrite cannot change nearest-handler selection or continuation selection. -/
theorem ClauseMap.cut (rewrite : ClauseMap)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting) :
    SourceScheduledNeutral.Cut effect operation contract modes
      (rewrite.forest whole) (rewrite.forest saved) (rewrite.forest waiting) := by
  induction cut with
  | hit known declared => exact .hit known declared
  | plain next ih => exact .plain ih
  | handler different next ih => exact .handler different ih
  | cell different next ih => exact .cell different ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem ClauseMap.owner_cut (rewrite : ClauseMap) (cut : OwnerCut owner whole front saved tail) :
    OwnerCut owner (rewrite.forest whole) (rewrite.forest front) (rewrite.forest saved) (rewrite.forest tail) := by
  induction cut with
  | hit => exact .hit
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live different next ih => exact .live different ih
  | spent next ih => exact .spent ih

/-- Reuse the established source substitution law for declaration signatures.
This map is a checking-witness transformation, not a source-typing theorem. -/
def substitution (name : Nat) (value : ScopedExpressions.Code) (isValue : value.IsValue) : ClauseMap where
  apply plans := ⟨_, SourcePlanSignatures.substituteClauses plans name value⟩
  preserves plans := SourcePlanSignatures.substitution_signature plans isValue

end Ash.OneShot.SourcePlanRewriting

#print axioms Ash.OneShot.SourcePlanRewriting.ClauseMap.plan_signature
#print axioms Ash.OneShot.SourcePlanRewriting.ClauseMap.forest_append
#print axioms Ash.OneShot.SourcePlanRewriting.ClauseMap.forest_closing
#print axioms Ash.OneShot.SourcePlanRewriting.ClauseMap.cut
#print axioms Ash.OneShot.SourcePlanRewriting.ClauseMap.owner_cut
