import SourceScheduledCapabilityAnnotations
import SourceScheduledPhaseRestriction

/-! Preserve the same capability annotation under independent permission and
phase changes. Unlike reconstruction, this keeps every optional bound field.
Existing owner-support and phase-restriction lemmas supply the recursive cuts. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture (Scope)
open SourceDependencyOwners (owners)
open SourceScheduledPhaseRestriction (AvailableOn owners_append owners_closing)
open OwnerPhaseTransitions (Phases spend introduce)

private theorem permission_transport (extension : Syntax.UsageExtension actions nextActions)
    (permission : Syntax.OneShotRights → Bool)
    (checked : (actions owner).any permission = true) :
    (nextActions owner).any permission = true := by
  cases known : actions owner with
  | none => simp [known] at checked
  | some rights => simpa only [extension _ _ known, known, Option.any_some] using checked

variable [declarationPolicy : DeclarationPolicy]

/-- Only live owners in the actual receiving forest can affect validation.
Each recursive invocation reuses spending monotonicity on that owner support. -/
theorem valid_transport_all (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (annotation : Code world plan forest) before nextActions after,
      annotation.Valid outward actions before → Syntax.UsageExtension actions nextActions →
      AvailableOn (owners scope) before after → annotation.Valid outward nextActions after) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (annotation : Retained world forest outside)
      before nextActions after,
      annotation.Valid outward actions before → Syntax.UsageExtension actions nextActions →
      AvailableOn (owners (scope.append outsideScope)) before after → annotation.Valid outward nextActions after) := by
  constructor
  all_goals first
    | (intro world dependencies scope hints plan forest annotation
       apply Code.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ before nextActions after, annotation.Valid outward actions before →
             Syntax.UsageExtension actions nextActions → AvailableOn (owners scope) before after →
             annotation.Valid outward nextActions after)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ before nextActions after, annotation.Valid outward actions before →
             Syntax.UsageExtension actions nextActions → AvailableOn (owners (scope.append outsideScope)) before after →
             annotation.Valid outward nextActions after)
         (t := annotation))
    | (intro world scope outsideScope hints outsideHints forest outside annotation
       apply Retained.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ before nextActions after, annotation.Valid outward actions before →
             Syntax.UsageExtension actions nextActions → AvailableOn (owners scope) before after →
             annotation.Valid outward nextActions after)
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ before nextActions after, annotation.Valid outward actions before →
             Syntax.UsageExtension actions nextActions → AvailableOn (owners (scope.append outsideScope)) before after →
             annotation.Valid outward nextActions after)
         (t := annotation))
  all_goals intros
  all_goals first
    | (rename_i required footprint declared before nextActions after checked permissions phases
       exact checked)
    | (rename_i interfaces before nextActions after checked permissions phases
       exact checked)
    | (rename_i cut bounded closing ih before nextActions after checked permissions phases
       refine ⟨checked.1, fun disposes => ih disposes _ _ _ (checked.2 disposes) permissions (phases.weaken ?_)⟩
       rw [cut.erase.reconstruct_scope]
       simpa only [SourceScheduledPhaseRestriction.owners_append, owners] using
         ScopedExpressions.append_subset (owners_closing _) (List.Subset.refl _))
    | (rename_i cut inside caller tail ihInside ihCaller ihTail before nextActions after checked permissions phases
       have located := SourceContextualInvocationHints.selected_cut cut.found
       have restored := SourceScheduledPhaseRestriction.resumed_owners located
       refine ⟨permission_transport permissions _ checked.1,
         phases _ (SourceScheduledPhaseRestriction.selected_owner located) checked.2.1,
         ihInside _ _ _ checked.2.2.1 permissions (phases.spend.weaken restored),
         ihCaller _ _ _ checked.2.2.2.1 permissions (phases.spend.weaken ?_),
         ihTail _ _ _ checked.2.2.2.2 permissions (phases.spend.weaken ?_)⟩
       · apply List.Subset.trans _ restored
         simp only [SourceDependencyCapture.OwnerSelection.resumed, SourceScheduledPhaseRestriction.owners_append, owners]
         exact List.subset_append_right _ _
       · apply List.Subset.trans _ restored
         simp only [SourceDependencyCapture.OwnerSelection.resumed, SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil]
         exact (List.subset_append_right _ _).trans (List.subset_append_right _ _))
    | (rename_i cut closing caller tail ihClosing ihCaller ihTail before nextActions after checked permissions phases
       have located := SourceContextualInvocationHints.selected_cut cut.found
       have scheduled := SourceScheduledPhaseRestriction.disposed_owners located
       refine ⟨permission_transport permissions _ checked.1,
         phases _ (SourceScheduledPhaseRestriction.selected_owner located) checked.2.1,
         checked.2.2.1, checked.2.2.2.1,
         ihClosing _ _ _ checked.2.2.2.2.1 permissions (phases.spend.weaken scheduled),
         ihCaller _ _ _ checked.2.2.2.2.2.1 permissions (phases.spend.weaken ?_),
         ihTail _ _ _ checked.2.2.2.2.2.2 permissions (phases.spend.weaken ?_)⟩
       · apply List.Subset.trans _ scheduled
         simp only [SourceDependencyCapture.OwnerSelection.disposed, SourceScheduledPhaseRestriction.owners_append, owners]
         exact List.subset_append_right _ _
       · apply List.Subset.trans _ scheduled
         simp only [SourceDependencyCapture.OwnerSelection.disposed, SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil]
         exact (List.subset_append_right _ _).trans (List.subset_append_right _ _))
    | (rename_i first second ihFirst ihSecond before nextActions after checked permissions phases
       exact ⟨ihFirst _ _ _ checked.1 permissions phases, ihSecond _ _ _ checked.2 permissions phases⟩)
    | (rename_i declarations body bounds ih before nextActions after checked permissions phases
       exact ⟨checked.1, ih _ _ _ checked.2 permissions phases⟩)
    | (rename_i body ih before nextActions after checked permissions phases
       exact fun identity fresh => ih identity fresh _ _ _ (checked identity fresh) permissions phases)
    | (rename_i tail ih before nextActions after checked permissions phases
       exact ⟨checked.1, ih _ _ _ checked.2 permissions phases⟩)
    | (rename_i tail ih before nextActions after checked permissions phases
       exact ih _ _ _ checked permissions phases)
    | (rename_i saved tail ihSaved ihTail before nextActions after checked permissions phases
       refine ⟨ihSaved _ _ _ checked.1 permissions (phases.weaken ?_),
         ihTail _ _ _ checked.2 permissions (phases.weaken ?_)⟩
       · simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
         exact List.subset_cons_self _ _
       · simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
         exact (List.subset_append_right _ _).trans (List.subset_cons_self _ _))

theorem Code.valid_transport {hints : Hints scope} {plan : Plan dependencies} {forest : Forest hints}
    (annotation : Code world plan forest) (checked : annotation.Valid outward actions before)
    (permissions : Syntax.UsageExtension actions nextActions)
    (phases : AvailableOn (owners scope) before after) : annotation.Valid outward nextActions after :=
  (valid_transport_all outward actions).1 _ _ _ annotation _ _ _ checked permissions phases

theorem Retained.valid_transport {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (checked : annotation.Valid outward actions before)
    (permissions : Syntax.UsageExtension actions nextActions)
    (phases : AvailableOn (owners (scope.append outsideScope)) before after) :
    annotation.Valid outward nextActions after :=
  (valid_transport_all outward actions).2 _ _ _ annotation _ _ _ checked permissions phases

omit declarationPolicy in
private theorem introduced_phases : AvailableOn names before (introduce before owner) := by
  intro actual member available
  by_cases same : actual = owner
  · simp only [introduce, if_pos same]
  · simpa only [introduce, if_neg same] using available

omit declarationPolicy in
private theorem spent_fresh_phases (fresh : owner ∉ names) :
    AvailableOn names before (spend (introduce before owner) owner) := by
  intro actual member available
  have different : actual ≠ owner := fun same => fresh (same ▸ member)
  simpa only [spend, introduce, if_neg different] using available

/-- Fresh allocation retains the annotation data and all previously checked
capabilities. The new permission entry is independent of its phase. -/
theorem Code.valid_fresh_owner {hints : Hints scope} {plan : Plan dependencies} {forest : Forest hints}
    (annotation : Code world plan forest) (checked : annotation.Valid outward actions phases)
    (fresh : actions owner = none) :
    annotation.Valid outward (actions.insert owner rights) (introduce phases owner) :=
  annotation.valid_transport checked (Syntax.fresh_usage_insert_extends fresh) introduced_phases

theorem Retained.valid_fresh_owner {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (checked : annotation.Valid outward actions phases)
    (fresh : actions owner = none) :
    annotation.Valid outward (actions.insert owner rights) (introduce phases owner) :=
  annotation.valid_transport checked (Syntax.fresh_usage_insert_extends fresh) introduced_phases

/-- Spending the fresh outer capability cannot invalidate an older saved
source whose actual receiving forest contains no such owner. -/
theorem Code.valid_spent_fresh_owner {hints : Hints scope} {plan : Plan dependencies} {forest : Forest hints}
    (annotation : Code world plan forest) (checked : annotation.Valid outward actions phases)
    (fresh : actions owner = none) (absent : owner ∉ owners scope) :
    annotation.Valid outward (actions.insert owner rights) (spend (introduce phases owner) owner) :=
  annotation.valid_transport checked (Syntax.fresh_usage_insert_extends fresh) (spent_fresh_phases absent)

theorem Retained.valid_spent_fresh_owner {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (checked : annotation.Valid outward actions phases)
    (fresh : actions owner = none) (absent : owner ∉ owners (scope.append outsideScope)) :
    annotation.Valid outward (actions.insert owner rights) (spend (introduce phases owner) owner) :=
  annotation.valid_transport checked (Syntax.fresh_usage_insert_extends fresh) (spent_fresh_phases absent)

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.valid_transport_all
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.valid_transport
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.valid_transport
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.valid_fresh_owner
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.valid_fresh_owner
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.valid_spent_fresh_owner
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.valid_spent_fresh_owner
