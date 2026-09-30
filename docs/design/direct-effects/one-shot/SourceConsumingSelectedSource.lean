import SourceConsumingBoundGeneration

/-! Select the actual consuming source annotation, not merely another body with
the same plan. The existing ordered offered-mode selection controls this relation.
Bounds, nested admission and substitution retain that exact source witness. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlannedRecipeDeclarations (Selected)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)

variable [declarations : DeclarationPolicy]

inductive SelectedSource (owner : Nat) :
    {world : List Nat} → {operation : Nat} → {held : Bool} →
    {clauses : ScopedExpressions.Clauses} → {families : SourceDependencyAnnotations.ClauseDependencies} →
    {plans : ClausePlans clauses families} → Declarations world plans →
    {parameter binder : Nat} → {code : ScopedExpressions.Code} →
    {family : Nat → SourceDependencyAnnotations.Dependencies} → {bodies : ∀ owner, Plan (family owner)} →
    Selected operation held plans parameter binder code bodies → Body world owner (bodies owner) → Prop where
  | ordinary : SelectedSource owner (.cons (.available annotations) protectedMode rest)
      (Selected.ordinary (operation := operation) (parameter := parameter) (binder := binder) (body := code)) (annotations owner)
  | protectedMode : SelectedSource owner (.cons ordinary (.available annotations) rest)
      (Selected.protectedMode (operation := operation) (parameter := parameter) (binder := binder) (body := code)) (annotations owner)
  | pass (different : operation ≠ other)
      (next : SelectedSource owner rest selected body) :
      SelectedSource owner (.cons ordinary protectedMode rest) (.pass different selected) body

/-- Every actual offered selection returns a witness from the stored source. -/
theorem Declarations.selected_source {plans : ClausePlans clauses families}
    (annotations : Declarations world plans)
    (selected : Selected operation held plans parameter binder code bodies) :
    ∃ body : Body world owner (bodies owner), SelectedSource owner annotations selected body := by
  induction selected with
  | ordinary => cases annotations with
    | cons ordinary protectedMode rest => cases ordinary with
      | available bodies => exact ⟨bodies owner, .ordinary⟩
  | protectedMode => cases annotations with
    | cons ordinary protectedMode rest => cases protectedMode with
      | available bodies => exact ⟨bodies owner, .protectedMode⟩
  | pass different next ih => cases annotations with
    | cons ordinary protectedMode rest =>
        obtain ⟨body, source⟩ := ih rest
        exact ⟨body, .pass different source⟩

/-- The relation cannot substitute another annotation with the same plan. -/
theorem SelectedSource.unique {plans : ClausePlans clauses families}
    {annotations : Declarations world plans}
    {selected : Selected operation held plans parameter binder code bodies}
    {body other : Body world owner (bodies owner)}
    (source : SelectedSource owner annotations selected body)
    (next : SelectedSource owner annotations selected other) : body = other := by
  induction source with
  | ordinary => cases next with
    | ordinary => rfl
    | pass different next => exact False.elim (different rfl)
  | protectedMode => cases next with
    | protectedMode => rfl
    | pass different next => exact False.elim (different rfl)
  | pass different rest ih => cases next with
    | ordinary | protectedMode => exact False.elim (different rfl)
    | pass different next => exact ih next

/-- Admission belongs to the source selected above, with the bound actually
stored for that offered mode. No replacement annotation is selected afterward. -/
theorem SelectedSource.admitted {plans : ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    {selected : Selected operation held plans parameter binder code bodies}
    {body : Body world owner (bodies owner)}
    (source : SelectedSource owner annotations selected body)
    (bounded : Bounded bounds annotations required) :
    ∃ contract needed, bounds.lookup operation held = some contract ∧
      Admitted code.requiredActions contract.resume contract.close body needed ∧
      needed ⊆ required ∧ body.Nested := by
  induction source generalizing required with
  | ordinary => cases bounded with
    | cons ordinary protectedMode rest => cases ordinary with
      | available source nested => exact ⟨_, _, by simp [ClauseBounds.lookup, ModeBounds.value], available_body source,
          (fun item member => List.mem_append_left _ (List.mem_append_left _ member)), nested owner⟩
  | protectedMode => cases bounded with
    | cons ordinary protectedMode rest => cases protectedMode with
      | available source nested => exact ⟨_, _, by simp [ClauseBounds.lookup, ModeBounds.value], available_body source,
          (fun item member => List.mem_append_left _ (List.mem_append_right _ member)), nested owner⟩
  | pass different next ih => cases bounded with
    | cons ordinary protectedMode rest =>
        obtain ⟨contract, needed, found, admitted, included, nested⟩ := ih rest
        exact ⟨contract, needed, by simpa only [ClauseBounds.lookup, if_neg different] using found,
          admitted, (fun item member => List.mem_append_right _ (included member)), nested⟩

theorem SelectedSource.world_weaken {plans : ClausePlans clauses families}
    {annotations : Declarations world plans}
    {selected : Selected operation held plans parameter binder code bodies}
    {body : Body world owner (bodies owner)}
    (source : SelectedSource owner annotations selected body) (larger : world ⊆ next) :
    SelectedSource owner (annotations.world_weaken larger) selected (body.world_weaken larger) := by
  induction source with
  | ordinary => exact .ordinary
  | protectedMode => exact .protectedMode
  | pass different next ih => exact .pass different (ih larger)

theorem SelectedSource.substitution {plans : ClausePlans clauses families}
    {annotations : Declarations world plans}
    {selected : Selected operation held plans parameter binder code bodies}
    {body : Body world owner (bodies owner)}
    (source : SelectedSource owner annotations selected body) :
    SelectedSource owner (annotations.substitution name value) selected.substitution body := by
  induction source with
  | ordinary => exact .ordinary
  | protectedMode => exact .protectedMode
  | pass different next ih => exact .pass different ih

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Declarations.selected_source
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.SelectedSource.admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.SelectedSource.world_weaken
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.SelectedSource.substitution

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.SelectedSource.unique
