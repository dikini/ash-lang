import ScopedClosure

/-!
Runtime dependency transport for scoped code. Source binders do not filter
activation atoms. Instantiation introduces only atoms supplied by its lexical
environment; ordinary substitution retains resource dependencies explicitly.
These are ingredients for live-support preservation, not source admission.
-/

namespace Ash.OneShot.ScopedExpressions
open Instantiation Syntax

mutual
theorem Code.subst_dependencies (expression : Code) (name : Nat) (value : Code) :
    (expression.subst name value).dependencies ⊆ expression.dependencies ++ value.dependencies := by
  cases expression with
  | unit | boolean _ | integer _ | resourceRef _ | discard _ =>
      exact self_dependency_bound _ _
  | «variable» other =>
      by_cases same : name = other
      · simp [Code.subst, same, Code.dependencies]
      · simpa only [Code.subst, if_neg same] using
          self_dependency_bound (Code.variable other).dependencies value.dependencies
  | pair left right | app left right | cleanup left right =>
      exact append_dependency_bound (left.subst_dependencies name value)
        (right.subst_dependencies name value)
  | lambda parameter body =>
      by_cases same : name = parameter
      · simpa only [Code.subst, if_pos same] using
          self_dependency_bound (Code.lambda parameter body).dependencies value.dependencies
      · simpa only [Code.subst, if_neg same, Code.dependencies] using
          without_dependency_bound (body.subst_dependencies name value) (.variable parameter)
  | bind parameter initializer body =>
      have hi := initializer.subst_dependencies name value
      by_cases same : name = parameter
      · simpa only [Code.subst, if_pos same, Code.dependencies] using
          append_dependency_bound hi
            (self_dependency_bound (without (.variable parameter) body.dependencies) value.dependencies)
      · simpa only [Code.subst, if_neg same, Code.dependencies] using
          append_dependency_bound hi
            (without_dependency_bound (body.subst_dependencies name value) (.variable parameter))
  | branch condition yes no =>
      exact append_dependency_bound
        (append_dependency_bound (condition.subst_dependencies name value)
          (yes.subst_dependencies name value)) (no.subst_dependencies name value)
  | perform effectInst operation operand =>
      exact append_dependency_bound (self_dependency_bound _ _)
        (operand.subst_dependencies name value)
  | handle effectInst body clauses =>
      exact append_dependency_bound
        (append_dependency_bound (self_dependency_bound _ _) (body.subst_dependencies name value))
        (clauses.subst_dependencies name value)
  | resume ticket operand =>
      exact cons_dependency_bound (operand.subst_dependencies name value) (.ticket ticket)
  | resource resource initializer body =>
      exact append_dependency_bound (initializer.subst_dependencies name value)
        (body.subst_dependencies name value)

theorem Clauses.subst_dependencies (clauses : Clauses) (name : Nat) (value : Code) :
    (clauses.subst name value).dependencies ⊆ clauses.dependencies ++ value.dependencies := by
  cases clauses with
  | nil => exact self_dependency_bound _ _
  | cons operation parameter ticket body rest =>
      have hr := rest.subst_dependencies name value
      by_cases same : name = parameter
      · simpa only [Clauses.subst, if_pos same, Clauses.dependencies] using
          append_dependency_bound (self_dependency_bound _ _) hr
      · simpa only [Clauses.subst, if_neg same, Clauses.dependencies] using
          append_dependency_bound
            (without_dependency_bound
              (without_dependency_bound (body.subst_dependencies name value) (.variable parameter))
              (.ticket ticket)) hr
end

def Provided (environment : Environment) (introduced : List Nat) : Prop :=
  ∀ name identity, environment name = some identity → identity ∈ introduced

theorem provided_mask (provided : Provided environment introduced) :
    Provided (Environment.mask environment binder) introduced := by
  intro name identity known
  by_cases same : name = binder
  · simp [Environment.mask, same] at known
  · exact provided name identity (by simpa only [Environment.mask, if_neg same] using known)

theorem argument_instantiation_resources (argument : Argument) (environment : Environment) :
    (argument.instantiate environment).resources = argument.resources.map (ResourceName.instantiate environment) := by
  induction argument <;> simp_all [Argument.instantiate, Argument.resources]

theorem effect_instantiation_resources (effect : Effect) (environment : Environment) :
    (effect.instantiate environment).resources = effect.resources.map (ResourceName.instantiate environment) := by
  cases effect with
  | cell => rfl
  | user family arguments =>
      change (arguments.map (Argument.instantiate environment)).flatMap Argument.resources =
        (arguments.flatMap Argument.resources).map (ResourceName.instantiate environment)
      induction arguments with
      | nil => rfl
      | cons argument rest ih => simp only [List.map_cons, List.flatMap_cons, argument_instantiation_resources, List.map_append, ih]

theorem effect_instantiation_atoms (effect : Effect) (environment : Environment)
    (provided : Provided environment introduced) :
    effectAtoms (effect.instantiate environment) ⊆ effectAtoms effect ++ introduced := by
  intro identity present
  obtain ⟨instantiated, member, atom⟩ := List.mem_filterMap.mp present
  rw [effect_instantiation_resources] at member
  obtain ⟨source, original, same⟩ := List.mem_map.mp member
  subst instantiated
  cases source with
  | activation key =>
      exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨.activation key, original, atom⟩)
  | bound name =>
      cases known : environment name with
      | none => simp [ResourceName.instantiate, known] at atom
      | some key =>
          simp [ResourceName.instantiate, known] at atom
          subst identity
          exact List.mem_append_right _ (provided name key known)

theorem effect_instantiation_dependencies (effect : Effect) (environment : Environment)
    (provided : Provided environment introduced) :
    (effectAtoms (effect.instantiate environment)).map Dependency.resource ⊆
      (effectAtoms effect).map Dependency.resource ++ introduced.map Dependency.resource := by
  intro dependency retained
  obtain ⟨identity, member, rfl⟩ := List.mem_map.mp retained
  rcases List.mem_append.mp (effect_instantiation_atoms effect environment provided member) with previous | new
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨identity, previous, rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨identity, new, rfl⟩)

mutual
/-- Only keys supplied by the lexical environment can be introduced. Existing
    runtime atoms remain dependencies even beneath a same-number source binder. -/
theorem Code.instantiation_dependencies (code : Code) (environment : Environment) (introduced : List Nat)
    (provided : Provided environment introduced) :
    (code.instantiate environment).dependencies ⊆ code.dependencies ++ introduced.map Dependency.resource := by
  cases code with
  | unit | boolean _ | integer _ | «variable» _ | discard _ => exact self_dependency_bound _ _
  | resourceRef source =>
      cases source with
      | activation => exact self_dependency_bound _ _
      | bound name =>
          cases known : environment name with
          | none => simp [Code.instantiate, ResourceName.instantiate, known, Code.dependencies]
          | some identity =>
              simp only [Code.instantiate, ResourceName.instantiate, known, Code.dependencies, List.nil_append]
              intro dependency member
              have same := List.mem_singleton.mp member
              subst dependency
              exact List.mem_map.mpr ⟨identity, provided name identity known, rfl⟩
  | pair left right | app left right | cleanup left right =>
      exact append_dependency_bound (left.instantiation_dependencies environment introduced provided)
        (right.instantiation_dependencies environment introduced provided)
  | lambda parameter body =>
      exact without_dependency_bound (body.instantiation_dependencies environment introduced provided) (.variable parameter)
  | bind parameter initializer body =>
      exact append_dependency_bound (initializer.instantiation_dependencies environment introduced provided)
        (without_dependency_bound (body.instantiation_dependencies environment introduced provided) (.variable parameter))
  | branch condition yes no =>
      exact append_dependency_bound
        (append_dependency_bound (condition.instantiation_dependencies environment introduced provided)
          (yes.instantiation_dependencies environment introduced provided)) (no.instantiation_dependencies environment introduced provided)
  | perform effect operation operand =>
      exact append_dependency_bound (effect_instantiation_dependencies effect environment provided)
        (operand.instantiation_dependencies environment introduced provided)
  | handle effect body clauses =>
      exact append_dependency_bound
        (append_dependency_bound (effect_instantiation_dependencies effect environment provided)
          (body.instantiation_dependencies environment introduced provided)) (clauses.instantiation_dependencies environment introduced provided)
  | resume ticket operand => exact cons_dependency_bound (operand.instantiation_dependencies environment introduced provided) (.ticket ticket)
  | resource binder initializer body =>
      exact append_dependency_bound (initializer.instantiation_dependencies environment introduced provided)
        (body.instantiation_dependencies (environment.mask binder) introduced (provided_mask provided))

theorem Clauses.instantiation_dependencies (clauses : Clauses) (environment : Environment) (introduced : List Nat)
    (provided : Provided environment introduced) :
    (clauses.instantiate environment).dependencies ⊆ clauses.dependencies ++ introduced.map Dependency.resource := by
  cases clauses with
  | nil => exact self_dependency_bound _ _
  | cons operation parameter ticket body rest =>
      exact append_dependency_bound
        (without_dependency_bound (without_dependency_bound (body.instantiation_dependencies environment introduced provided)
          (.variable parameter)) (.ticket ticket)) (rest.instantiation_dependencies environment introduced provided)
end

theorem acquisition_dependency_bound (binder identity : Nat) (body : Code) :
    (body.instantiate (Environment.empty.bind binder identity)).dependencies ⊆ body.dependencies ++ [.resource identity] := by
  apply body.instantiation_dependencies _ [identity]
  intro name key known
  by_cases same : name = binder
  · simp [Environment.bind, same] at known
    simp [← known]
  · simp [Environment.bind, same, Environment.empty] at known

theorem closed_names_are_atoms (checked : ListRealizes (NameRealizes Environment.empty) names identities) :
    names = identities.map ResourceName.activation := by
  induction checked with
  | nil => rfl
  | cons head rest ih => cases head with
      | activation => simp only [List.map_cons, ih]
      | bound known => cases known

@[simp] theorem frozen_effect_atoms (effect : Instance) : effectAtoms (freezeEffect effect) = effect.resources := by
  unfold effectAtoms
  rw [closed_names_are_atoms (effect_resources_realize (frozen_effect_realizes Environment.empty effect))]
  simp [List.filterMap_map, Function.comp_def]

@[simp] theorem resource_dependencies_map (identities : List Nat) :
    resourceDependencies (identities.map Dependency.resource) = identities := by
  simp [resourceDependencies, Function.comp_def]

@[simp] theorem resource_dependencies_without_variable (items : List Dependency) (name : Nat) :
    resourceDependencies (without (.variable name) items) = resourceDependencies items := by
  induction items with
  | nil => rfl
  | cons dependency rest ih =>
      cases dependency <;> simp_all [without, resourceDependencies]
      rw [List.filter_cons]
      split <;> simp_all

theorem substitution_resource_support (body value : Code) (name : Nat)
    (bodySupported : resourceDependencies body.dependencies ⊆ available)
    (valueSupported : resourceDependencies value.dependencies ⊆ available) :
    resourceDependencies (body.subst name value).dependencies ⊆ available := by
  intro resource retained
  rcases List.mem_append.mp (body.subst_dependencies name value (mem_resourceDependencies.mp retained)) with original | inserted
  · exact bodySupported (mem_resourceDependencies.mpr original)
  · exact valueSupported (mem_resourceDependencies.mpr inserted)

end Ash.OneShot.ScopedExpressions

#print axioms Ash.OneShot.ScopedExpressions.Code.subst_dependencies
#print axioms Ash.OneShot.ScopedExpressions.Code.instantiation_dependencies
#print axioms Ash.OneShot.ScopedExpressions.acquisition_dependency_bound
