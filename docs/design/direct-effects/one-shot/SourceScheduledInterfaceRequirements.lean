import SourceScheduledInterfaceWorld

/-! Finite boundary requirements for ordinary retained source, including its
callbacks and dormant captures. Internal checks are preserved by the existing
ordered-scope transport theorem; no exchange of interpretations is assumed. -/
namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceHandlerRequirements (outwardRequirements requirements_outward requirements_transport)

private def scopeOf {hints : Hints scope} (_ : Forest hints) : Scope := scope

/-- Operations supplied inside the retained suffix are discharged there.
Only the remaining requirements reach the replacement receiving scope. -/
def Interfaces.exposed {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) : List Requirement :=
  match interfaces with
  | .nil => []
  | .plain rest required _ _ next => outwardRequirements (scopeOf rest) required ++ next.exposed
  | .handler (required := required) rest next => outwardRequirements (scopeOf rest) required ++ next.exposed
  | .cell next | .running next | .spent next => next.exposed
  | .cleanup rest required _ _ next => outwardRequirements (.running (scopeOf rest)) required ++ next.exposed
  | .live rest saved next => outwardRequirements (scopeOf rest) saved.exposed ++ next.exposed

theorem Interfaces.exposed_requirements {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (checked : interfaces.check outside = true) :
    checkRequirements outside interfaces.exposed = true := by
  induction interfaces generalizing outside with
  | nil => rfl
  | cell next ih | running next ih | spent next ih => exact ih checked
  | plain rest required footprint declared next ih | handler rest next ih =>
      simp only [Interfaces.check, Bool.and_eq_true] at checked
      simp only [Interfaces.exposed, checkRequirements, List.all_append, Bool.and_eq_true]
      exact ⟨requirements_outward checked.1, ih checked.2⟩
  | cleanup rest required footprint declared next ih =>
      simp only [Interfaces.check, Bool.and_eq_true] at checked
      simp only [Interfaces.exposed, checkRequirements, List.all_append, Bool.and_eq_true]
      exact ⟨requirements_outward (front := .running (scopeOf rest)) checked.1, ih checked.2⟩
  | live rest saved next ihSaved ihRest =>
      simp only [Interfaces.check, Bool.and_eq_true] at checked
      simp only [Interfaces.exposed, checkRequirements, List.all_append, Bool.and_eq_true]
      exact ⟨requirements_outward (ihSaved checked.1), ihRest checked.2⟩

/-- Reuse the existing operation-boundary transport proof at every retained
position. Matching internal handlers, including missing operations, are kept. -/
theorem Interfaces.check_transport {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (checked : interfaces.check before = true)
    (supplied : checkRequirements after interfaces.exposed = true) : interfaces.check after = true := by
  induction interfaces generalizing before after with
  | nil => rfl
  | cell next ih | running next ih | spent next ih => exact ih checked supplied
  | plain rest required footprint declared next ih | handler rest next ih =>
      simp only [Interfaces.check, Bool.and_eq_true] at checked ⊢
      simp only [Interfaces.exposed, checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      exact ⟨requirements_transport checked.1 supplied.1, ih checked.2 supplied.2⟩
  | cleanup rest required footprint declared next ih =>
      simp only [Interfaces.check, Bool.and_eq_true] at checked ⊢
      simp only [Interfaces.exposed, checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      exact ⟨requirements_transport (front := .running (scopeOf rest)) checked.1 supplied.1,
        ih checked.2 supplied.2⟩
  | live rest saved next ihSaved ihRest =>
      simp only [Interfaces.check, Bool.and_eq_true] at checked ⊢
      simp only [Interfaces.exposed, checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      exact ⟨ihSaved checked.1 (requirements_transport (saved.exposed_requirements checked.1) supplied.1),
        ihRest checked.2 supplied.2⟩

/-- Given the original retained check, the finite boundary interface exactly
characterizes every replacement receiver. It is not a whole-body premise. -/
theorem Interfaces.check_replace_iff {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (checked : interfaces.check before = true) :
    interfaces.check after = true ↔ checkRequirements after interfaces.exposed = true :=
  ⟨interfaces.exposed_requirements, interfaces.check_transport checked⟩

theorem Interfaces.exposed_world_weaken {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (larger : world ⊆ next) :
    (interfaces.world_weaken larger).exposed = interfaces.exposed := by
  induction interfaces <;> simp_all [Interfaces.world_weaken, Interfaces.exposed]

/-- A source contract may overapproximate operations by membership. Duplicate
entries do not grant extra uses of any continuation owner. -/
theorem Interfaces.check_from_bound {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (checked : interfaces.check before = true)
    (bounded : interfaces.exposed ⊆ required)
    (supplied : checkRequirements after required = true) : interfaces.check after = true :=
  interfaces.check_transport checked (SourceContextualRequirements.check_requirements_subset bounded supplied)

end Ash.OneShot.SourceScheduledRetainedInterfaces

#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.exposed_requirements
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_transport
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_replace_iff
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.exposed_world_weaken
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_from_bound
