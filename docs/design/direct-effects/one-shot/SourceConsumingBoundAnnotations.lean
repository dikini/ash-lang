import SourceConsumingDeclarationSubstitution

/-! Structural declaration admission checks the explicit continuation bounds
against actual clause bodies and offered modes. Ordinary and protected offers
may carry different bounds. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceContextualHints (Requirement)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)


section
variable [declarations : DeclarationPolicy]

mutual
/-- Every nested handler validates the bounds it actually records. This
judgment is independent of the outer continuation's consumption requirements. -/
inductive Body.Nested : {world : List Nat} → {owner : Nat} →
    {dependencies : SourceDependencyAnnotations.Dependencies} → {plan : Plan dependencies} →
    Body world owner plan → Prop where
  | resume : Body.Nested .resume
  | dispose : Body.Nested .dispose
  | sequence : Body.Nested body → Body.Nested (.sequence required footprint declared body)
  | choice : Body.Nested first → Body.Nested second → Body.Nested (.choice first second)
  | handler (source : Declarations world plans) (checked : Bounded bounds source required)
      (body : Body.Nested code) :
      Body.Nested (.handler (world := world) (effect := effect) (table := table) (required := required) bounds evidence code)
  | cleanup : Body.Nested body → Body.Nested (.cleanup required footprint declared body)
  | resource (body : ∀ identity fresh, Body.Nested (code identity fresh)) : Body.Nested (.resource code)

inductive BoundedMode : Syntax.OneShotRights → {world : List Nat} →
    {family : Option (Nat → SourceDependencyAnnotations.Dependencies)} → {plans : ModePlans family} →
    ModeBounds plans → Modes world plans → List Requirement → Prop where
  | unavailable : BoundedMode rights .unavailable .unavailable []
  | available (source : ModeAdmitted rights bounds.resume bounds.close required (.available bodies))
      (nested : ∀ owner, Body.Nested (bodies owner)) :
      BoundedMode rights (.available bounds) (.available bodies) required

inductive Bounded : {world : List Nat} → {clauses : ScopedExpressions.Clauses} →
    {families : SourceDependencyAnnotations.ClauseDependencies} → {plans : ClausePlans clauses families} →
      ClauseBounds plans → Declarations world plans → List Requirement → Prop where
  | nil : Bounded .nil .nil []
  | cons {body : ScopedExpressions.Code}
      (ordinary : BoundedMode body.requiredActions ordinaryBounds ordinaryAnnotation ordinaryRequired)
      (protectedMode : BoundedMode body.requiredActions protectedBounds protectedAnnotation protectedRequired)
      (rest : Bounded restBounds restAnnotation restRequired) :
      Bounded (ClauseBounds.cons (body := body) ordinaryBounds protectedBounds restBounds)
        (.cons ordinaryAnnotation protectedAnnotation restAnnotation)
        (ordinaryRequired ++ protectedRequired ++ restRequired)

end

theorem Body.Nested.requests {body : Body world owner plan} (checked : body.Nested)
    (requests : List Requirement) : (body.requests requests).Nested := by
  induction requests with
  | nil => exact checked
  | cons request rest ih => exact .sequence ih

theorem available_body
    (source : ModeAdmitted rights resumeRequired closeRequired required (.available bodies)) :
    Admitted rights resumeRequired closeRequired (bodies owner) required := by
  cases source with
  | available source => exact source owner

/-- Selection returns the bound actually recorded for the selected offer,
not an unrelated existential interface chosen after seeing a capture. -/
theorem Bounded.selected_nested {plans : ClausePlans clauses families} {annotations : Declarations world plans}
    {bounds : ClauseBounds plans} (admitted : Bounded bounds annotations required)
    (selected : SourcePlannedRecipeDeclarations.Selected operation held plans parameter binder code bodies) :
    ∃ contract needed, ∃ body : Body world owner (bodies owner),
      bounds.lookup operation held = some contract ∧
      Admitted code.requiredActions contract.resume contract.close body needed ∧ needed ⊆ required ∧ body.Nested := by
  induction selected generalizing required with
  | ordinary => cases admitted with
    | cons ordinary protectedMode rest => cases ordinary with
      | available source nested =>
          exact ⟨_, _, _, by simp [ClauseBounds.lookup, ModeBounds.value], available_body source,
            (fun item member => List.mem_append_left _ (List.mem_append_left _ member)), nested owner⟩
  | protectedMode => cases admitted with
    | cons ordinary protectedMode rest => cases protectedMode with
      | available source nested =>
          exact ⟨_, _, _, by simp [ClauseBounds.lookup, ModeBounds.value], available_body source,
            (fun item member => List.mem_append_left _ (List.mem_append_right _ member)), nested owner⟩
  | pass different next ih => cases admitted with
    | cons ordinary protectedMode rest =>
        obtain ⟨contract, needed, body, found, source, included, nested⟩ := ih rest
        exact ⟨contract, needed, body, by simpa only [ClauseBounds.lookup, if_neg different] using found,
          source, (fun item member => List.mem_append_right _ (included member)), nested⟩

theorem Bounded.selected {plans : ClausePlans clauses families} {annotations : Declarations world plans}
    {bounds : ClauseBounds plans} (admitted : Bounded bounds annotations required)
    (selected : SourcePlannedRecipeDeclarations.Selected operation held plans parameter binder code bodies) :
    ∃ contract needed, ∃ body : Body world owner (bodies owner),
      bounds.lookup operation held = some contract ∧
      Admitted code.requiredActions contract.resume contract.close body needed ∧ needed ⊆ required := by
  obtain ⟨contract, needed, body, found, source, included, _⟩ := admitted.selected_nested selected
  exact ⟨contract, needed, body, found, source, included⟩

theorem Body.Nested.world_weaken {body : Body world owner plan}
    (checked : body.Nested) (larger : world ⊆ next) : (body.world_weaken larger).Nested := by
  induction checked using Body.Nested.rec
      (motive_2 := fun rights {world} {_} {_} bounds annotations required _ =>
        ∀ next, ∀ larger : world ⊆ next,
          BoundedMode rights bounds (annotations.world_weaken larger) required)
      (motive_3 := fun {world} {_} {_} {_} bounds annotations required _ =>
        ∀ next, ∀ larger : world ⊆ next,
          Bounded bounds (annotations.world_weaken larger) required)
      generalizing next with
  | resume => exact .resume
  | dispose => exact .dispose
  | sequence body ih => exact .sequence (ih larger)
  | choice first second ihFirst ihSecond => exact .choice (ihFirst larger) (ihSecond larger)
  | handler source admitted body ihSource ihBody =>
      exact .handler (source.world_weaken larger) (ihSource _ larger) (ihBody larger)
  | cleanup body ih => exact .cleanup (ih larger)
  | resource body ih =>
      exact .resource (fun identity fresh =>
        ih identity (fun member => fresh (larger member))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
  | unavailable => exact .unavailable
  | available source nested ih =>
      rename_i next larger
      exact .available (source.world_weaken larger) (fun owner => ih owner larger)
  | nil => exact .nil
  | cons ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i next larger
      exact .cons (ihOrdinary _ larger) (ihProtected _ larger) (ihRest _ larger)

theorem BoundedMode.world_weaken {bounds : ModeBounds plans} {annotations : Modes world plans}
    (admitted : BoundedMode rights bounds annotations required) (larger : world ⊆ next) :
    BoundedMode rights bounds (annotations.world_weaken larger) required := by
  cases admitted with
  | unavailable => exact .unavailable
  | available source nested =>
      exact .available (source.world_weaken larger) (fun owner => (nested owner).world_weaken larger)

theorem Bounded.world_weaken {bounds : ClauseBounds plans} {annotations : Declarations world plans}
    (admitted : Bounded bounds annotations required) (larger : world ⊆ next) :
    Bounded bounds (annotations.world_weaken larger) required := by
  induction bounds generalizing required with
  | nil => cases admitted; exact .nil
  | cons ordinaryBounds protectedBounds restBounds ih =>
      cases admitted with
      | cons ordinary protectedMode rest =>
          exact .cons (ordinary.world_weaken larger) (protectedMode.world_weaken larger) (ih rest)

end

/-- Value substitution changes literal witnesses, retaining the same bounds. -/
def ClauseBounds.substitution {plans : ClausePlans clauses families}
    (bounds : ClauseBounds plans) (name : Nat) (value : ScopedExpressions.Code) :
    ClauseBounds (SourcePlanSignatures.substituteClauses plans name value) :=
  match bounds with
  | .nil => .nil
  | .cons ordinary protectedMode rest => .cons ordinary protectedMode (rest.substitution name value)

theorem ClauseBounds.lookup_substitution {plans : ClausePlans clauses families}
    (bounds : ClauseBounds plans) :
    (bounds.substitution name value).lookup operation held = bounds.lookup operation held := by
  induction bounds <;> simp_all [ClauseBounds.substitution, ClauseBounds.lookup]

section
variable [declarations : DeclarationPolicy]

private theorem mode_substitution {body : ScopedExpressions.Code}
    {bounds : ModeBounds plans} {annotations : Modes world plans}
    (admitted : BoundedMode body.requiredActions bounds annotations required) (isValue : value.IsValue) :
    BoundedMode (if name = parameter then body else body.subst name value).requiredActions bounds annotations required := by
  split
  · exact admitted
  · simpa only [ScopedExpressions.Code.substitution_required_actions _ _ isValue] using admitted

theorem Bounded.substitution {bounds : ClauseBounds plans} {annotations : Declarations world plans}
    (admitted : Bounded bounds annotations required) (isValue : value.IsValue) :
    Bounded (bounds.substitution name value) (annotations.substitution name value) required := by
  induction bounds generalizing required with
  | nil => cases admitted; exact .nil
  | cons ordinaryBounds protectedBounds restBounds ih =>
      cases admitted with
      | cons ordinary protectedMode rest =>
          exact .cons (mode_substitution ordinary isValue) (mode_substitution protectedMode isValue)
            (ih rest)

end
end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.selected
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundedMode.world_weaken
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.world_weaken
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ClauseBounds.lookup_substitution
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.substitution

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.available_body

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.selected_nested
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Nested.world_weaken

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Nested.requests
