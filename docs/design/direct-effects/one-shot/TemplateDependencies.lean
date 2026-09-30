import ReturnBoundaries

/-!
Free stored dependencies of resource templates. Bound resource names are
retained until their resource binder removes them; activation atoms never bind.
This metadata belongs to the existing Code grammar, not another evaluator.
-/

namespace Ash.OneShot.TemplateDependencies
open Instantiation ScopedExpressions

inductive Dep where
  | resource : ResourceName → Dep
  | variable : Nat → Dep
  | ticket : Nat → Dep
  deriving DecidableEq, Repr

def without (binder : Dep) (dependencies : List Dep) : List Dep :=
  dependencies.filter (fun dependency => decide (dependency ≠ binder))

def Dep.instantiate (environment : Instantiation.Environment) : Dep → Dep
  | .resource name => .resource (name.instantiate environment)
  | .variable name => .variable name
  | .ticket name => .ticket name

def Dep.runtime : Dep → Option Syntax.Dependency
  | .resource (.activation identity) => some (.resource identity)
  | .resource (.bound _) => none
  | .variable name => some (.variable name)
  | .ticket name => some (.ticket name)

def Dep.boundName : Dep → Option Nat
  | .resource (.bound name) => some name
  | _ => none

mutual
def dependencies : Code → List Dep
  | .unit | .boolean _ | .integer _ => []
  | .variable name => [.variable name]
  | .resourceRef name => [.resource name]
  | .pair left right | .app left right | .cleanup left right => dependencies left ++ dependencies right
  | .lambda parameter body => without (.variable parameter) (dependencies body)
  | .bind parameter initializer body => dependencies initializer ++ without (.variable parameter) (dependencies body)
  | .branch condition yes no => dependencies condition ++ dependencies yes ++ dependencies no
  | .perform effect _ operand => effect.resources.map Dep.resource ++ dependencies operand
  | .handle effect body clauses => effect.resources.map Dep.resource ++ dependencies body ++ clauseDependencies clauses
  | .resume ticket operand => .ticket ticket :: dependencies operand
  | .discard ticket => [.ticket ticket]
  | .resource binder initializer body => dependencies initializer ++ without (.resource (.bound binder)) (dependencies body)

def clauseDependencies : Clauses → List Dep
  | .nil => []
  | .cons _ parameter ticket body rest =>
      without (.ticket ticket) (without (.variable parameter) (dependencies body)) ++ clauseDependencies rest
end

theorem instantiate_without_variable (items : List Dep) (parameter : Nat) :
    without (.variable parameter) (items.map (Dep.instantiate environment)) =
      (without (.variable parameter) items).map (Dep.instantiate environment) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | resource | ticket => simp_all [without, Dep.instantiate]
      | «variable» name => by_cases same : name = parameter <;> simp_all [without, Dep.instantiate]

theorem instantiate_without_ticket (items : List Dep) (ticket : Nat) :
    without (.ticket ticket) (items.map (Dep.instantiate environment)) =
      (without (.ticket ticket) items).map (Dep.instantiate environment) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | resource | «variable» => simp_all [without, Dep.instantiate]
      | ticket name => by_cases same : name = ticket <;> simp_all [without, Dep.instantiate]

/-- The initializer uses the full environment; only the body masks this name.
    A same-number activation is unaffected by either masking or filtering. -/
theorem instantiate_without_bound (items : List Dep) (binder : Nat) :
    without (.resource (.bound binder)) (items.map (Dep.instantiate (environment.mask binder))) =
      (without (.resource (.bound binder)) items).map (Dep.instantiate environment) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | «variable» | ticket => simp_all [without, Dep.instantiate]
      | resource name => cases name with
          | activation => simp_all [without, Dep.instantiate, ResourceName.instantiate]
          | bound name =>
              by_cases same : name = binder
              · simp_all [without, Dep.instantiate, ResourceName.instantiate, Instantiation.Environment.mask]
              · cases known : environment name <;>
                  simp_all [without, Dep.instantiate, ResourceName.instantiate, Instantiation.Environment.mask]

mutual
theorem dependencies_instantiate (code : Code) (environment : Instantiation.Environment) :
    dependencies (code.instantiate environment) = (dependencies code).map (Dep.instantiate environment) := by
  cases code with
  | unit | boolean | integer | «variable» | resourceRef | discard => rfl
  | pair left right | app left right | cleanup left right =>
      simp only [Code.instantiate, dependencies, dependencies_instantiate left environment,
        dependencies_instantiate right environment, List.map_append]
  | lambda parameter body =>
      simp only [Code.instantiate, dependencies, dependencies_instantiate body environment, instantiate_without_variable]
  | bind parameter initializer body =>
      simp only [Code.instantiate, dependencies, dependencies_instantiate initializer environment,
        dependencies_instantiate body environment, instantiate_without_variable, List.map_append]
  | branch condition yes no =>
      simp only [Code.instantiate, dependencies, dependencies_instantiate condition environment,
        dependencies_instantiate yes environment, dependencies_instantiate no environment, List.map_append]
  | perform effect operation operand =>
      simp [Code.instantiate, dependencies, dependencies_instantiate operand environment,
        effect_instantiation_resources, List.map_map, Dep.instantiate]
  | handle effect body clauses =>
      simp [Code.instantiate, dependencies, dependencies_instantiate body environment, clauses_instantiate clauses environment,
        effect_instantiation_resources, List.map_map, Dep.instantiate]
  | resume ticket operand =>
      simp only [Code.instantiate, dependencies, dependencies_instantiate operand environment, List.map_cons, Dep.instantiate]
  | resource binder initializer body =>
      simp only [Code.instantiate, dependencies, dependencies_instantiate initializer environment,
        dependencies_instantiate body (environment.mask binder), instantiate_without_bound, List.map_append]
termination_by sizeOf code

theorem clauses_instantiate (clauses : Clauses) (environment : Instantiation.Environment) :
    clauseDependencies (clauses.instantiate environment) =
      (clauseDependencies clauses).map (Dep.instantiate environment) := by
  cases clauses with
  | nil => rfl
  | cons operation parameter ticket body rest =>
      simp only [Clauses.instantiate, clauseDependencies, dependencies_instantiate body environment, clauses_instantiate rest environment,
        instantiate_without_ticket, instantiate_without_variable, List.map_append]
termination_by sizeOf clauses
end

theorem runtime_without_variable (items : List Dep) (parameter : Nat) :
    (without (.variable parameter) items).filterMap Dep.runtime =
      Syntax.without (.variable parameter) (items.filterMap Dep.runtime) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | resource name => cases name <;> simp_all [without, Syntax.without, Dep.runtime, List.filterMap_cons]
      | «variable» name => by_cases same : name = parameter <;> simp_all [without, Syntax.without, Dep.runtime]
      | ticket => simp_all [without, Syntax.without, Dep.runtime]

theorem runtime_without_ticket (items : List Dep) (ticket : Nat) :
    (without (.ticket ticket) items).filterMap Dep.runtime =
      Syntax.without (.ticket ticket) (items.filterMap Dep.runtime) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | resource name => cases name <;> simp_all [without, Syntax.without, Dep.runtime, List.filterMap_cons]
      | ticket name => by_cases same : name = ticket <;> simp_all [without, Syntax.without, Dep.runtime]
      | «variable» => simp_all [without, Syntax.without, Dep.runtime]

theorem runtime_without_bound (items : List Dep) (binder : Nat) :
    (without (.resource (.bound binder)) items).filterMap Dep.runtime = items.filterMap Dep.runtime := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | resource name => cases name with
          | activation => simp_all [without, Dep.runtime]
          | bound name => by_cases same : name = binder <;> simp_all [without, Dep.runtime, List.filterMap_cons]
      | «variable» | ticket => simp_all [without, Dep.runtime]

theorem runtime_effect (effect : Effect) :
    (effect.resources.map Dep.resource).filterMap Dep.runtime =
      (effectAtoms effect).map Syntax.Dependency.resource := by
  unfold effectAtoms
  induction effect.resources with
  | nil => rfl
  | cons name rest ih => cases name <;> simp_all [Dep.runtime, List.filterMap_cons]

mutual
theorem runtime_dependencies (code : Code) : (dependencies code).filterMap Dep.runtime = code.dependencies := by
  cases code with
  | unit | boolean | integer | «variable» | discard => rfl
  | resourceRef name => cases name <;> rfl
  | pair left right | app left right | cleanup left right =>
      simp only [dependencies, Code.dependencies, List.filterMap_append, runtime_dependencies left, runtime_dependencies right]
  | branch condition yes no =>
      simp only [dependencies, Code.dependencies, List.filterMap_append, runtime_dependencies condition,
        runtime_dependencies yes, runtime_dependencies no]
  | lambda parameter body => simp only [dependencies, Code.dependencies, runtime_without_variable, runtime_dependencies body]
  | bind parameter initializer body =>
      simp only [dependencies, Code.dependencies, List.filterMap_append, runtime_without_variable,
        runtime_dependencies initializer, runtime_dependencies body]
  | perform effect operation operand =>
      simp only [dependencies, Code.dependencies, List.filterMap_append, runtime_effect, runtime_dependencies operand]
  | handle effect body clauses =>
      simp only [dependencies, Code.dependencies, List.filterMap_append, runtime_effect, runtime_dependencies body, runtime_clauses clauses]
  | resume ticket operand =>
      simp only [dependencies, Code.dependencies, List.filterMap_cons, Dep.runtime, runtime_dependencies operand]
  | resource binder initializer body =>
      simp only [dependencies, Code.dependencies, List.filterMap_append, runtime_without_bound,
        runtime_dependencies initializer, runtime_dependencies body]
termination_by sizeOf code

theorem runtime_clauses (clauses : Clauses) :
    (clauseDependencies clauses).filterMap Dep.runtime = clauses.dependencies := by
  cases clauses with
  | nil => rfl
  | cons operation parameter ticket body rest =>
      simp only [clauseDependencies, Clauses.dependencies, List.filterMap_append,
        runtime_without_ticket, runtime_without_variable, runtime_dependencies body, runtime_clauses rest]
termination_by sizeOf clauses
end

theorem bound_without_variable (items : List Dep) (parameter : Nat) :
    (without (.variable parameter) items).filterMap Dep.boundName = items.filterMap Dep.boundName := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | resource name => cases name <;> simp_all [without, Dep.boundName, List.filterMap_cons]
      | «variable» name => by_cases same : name = parameter <;> simp_all [without, Dep.boundName, List.filterMap_cons]
      | ticket => simp_all [without, Dep.boundName, List.filterMap_cons]

theorem bound_without_ticket (items : List Dep) (ticket : Nat) :
    (without (.ticket ticket) items).filterMap Dep.boundName = items.filterMap Dep.boundName := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | resource name => cases name <;> simp_all [without, Dep.boundName, List.filterMap_cons]
      | ticket name => by_cases same : name = ticket <;> simp_all [without, Dep.boundName, List.filterMap_cons]
      | «variable» => simp_all [without, Dep.boundName, List.filterMap_cons]

theorem bound_without_bound (items : List Dep) (binder : Nat) :
    (without (.resource (.bound binder)) items).filterMap Dep.boundName =
      (items.filterMap Dep.boundName).filter (· != binder) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | resource name => cases name with
          | activation => simp_all [without, Dep.boundName, List.filterMap_cons]
          | bound name => by_cases same : name = binder <;> simp_all [without, Dep.boundName]
      | «variable» | ticket => simp_all [without, Dep.boundName, List.filterMap_cons]

theorem bound_argument (argument : Argument) :
    (argument.resources.map Dep.resource).filterMap Dep.boundName = argument.freeNames := by
  induction argument with
  | nominal => rfl
  | resource name => cases name <;> rfl
  | apply head argument ihHead ihArgument =>
      simp only [Argument.resources, Argument.freeNames, List.map_append, List.filterMap_append, ihHead, ihArgument]

theorem bound_effect (effect : Effect) :
    (effect.resources.map Dep.resource).filterMap Dep.boundName = effect.freeNames := by
  cases effect with
  | cell name => cases name <;> rfl
  | user family arguments =>
      simp only [Effect.resources, Effect.freeNames, List.map_flatMap, List.filterMap_flatMap, bound_argument]

mutual
theorem bound_dependencies (code : Code) : (dependencies code).filterMap Dep.boundName = code.freeNames := by
  cases code with
  | unit | boolean | integer | «variable» | discard => rfl
  | resourceRef name => cases name <;> rfl
  | pair left right | app left right | cleanup left right =>
      simp only [dependencies, Code.freeNames, List.filterMap_append, bound_dependencies left, bound_dependencies right]
  | branch condition yes no =>
      simp only [dependencies, Code.freeNames, List.filterMap_append, bound_dependencies condition,
        bound_dependencies yes, bound_dependencies no]
  | lambda parameter body => simp only [dependencies, Code.freeNames, bound_without_variable, bound_dependencies body]
  | bind parameter initializer body =>
      simp only [dependencies, Code.freeNames, List.filterMap_append, bound_without_variable,
        bound_dependencies initializer, bound_dependencies body]
  | perform effect operation operand =>
      simp only [dependencies, Code.freeNames, List.filterMap_append, bound_effect, bound_dependencies operand]
  | handle effect body clauses =>
      simp only [dependencies, Code.freeNames, List.filterMap_append, bound_effect, bound_dependencies body, bound_clauses clauses]
  | resume ticket operand =>
      simp only [dependencies, Code.freeNames, List.filterMap_cons, Dep.boundName, bound_dependencies operand]
  | resource binder initializer body =>
      simp only [dependencies, Code.freeNames, List.filterMap_append, bound_without_bound,
        bound_dependencies initializer, bound_dependencies body]
termination_by sizeOf code

theorem bound_clauses (clauses : Clauses) :
    (clauseDependencies clauses).filterMap Dep.boundName = clauses.freeNames := by
  cases clauses with
  | nil => rfl
  | cons operation parameter ticket body rest =>
      simp only [clauseDependencies, Clauses.freeNames, List.filterMap_append,
        bound_without_ticket, bound_without_variable, bound_dependencies body, bound_clauses rest]
termination_by sizeOf clauses
end

theorem closed_dependencies_have_no_bound (closed : code.ResourceClosed) :
    ∀ name, Dep.resource (.bound name) ∉ dependencies code := by
  intro name member
  have present : name ∈ (dependencies code).filterMap Dep.boundName := List.mem_filterMap.mpr ⟨_, member, rfl⟩
  rw [bound_dependencies, closed] at present
  cases present

end Ash.OneShot.TemplateDependencies

#print axioms Ash.OneShot.TemplateDependencies.instantiate_without_variable
#print axioms Ash.OneShot.TemplateDependencies.instantiate_without_ticket
#print axioms Ash.OneShot.TemplateDependencies.instantiate_without_bound
#print axioms Ash.OneShot.TemplateDependencies.dependencies_instantiate
#print axioms Ash.OneShot.TemplateDependencies.clauses_instantiate
#print axioms Ash.OneShot.TemplateDependencies.runtime_without_variable
#print axioms Ash.OneShot.TemplateDependencies.runtime_without_ticket
#print axioms Ash.OneShot.TemplateDependencies.runtime_without_bound
#print axioms Ash.OneShot.TemplateDependencies.runtime_effect
#print axioms Ash.OneShot.TemplateDependencies.runtime_dependencies
#print axioms Ash.OneShot.TemplateDependencies.runtime_clauses
#print axioms Ash.OneShot.TemplateDependencies.bound_without_variable
#print axioms Ash.OneShot.TemplateDependencies.bound_without_ticket
#print axioms Ash.OneShot.TemplateDependencies.bound_without_bound
#print axioms Ash.OneShot.TemplateDependencies.bound_argument
#print axioms Ash.OneShot.TemplateDependencies.bound_effect
#print axioms Ash.OneShot.TemplateDependencies.bound_dependencies
#print axioms Ash.OneShot.TemplateDependencies.bound_clauses
#print axioms Ash.OneShot.TemplateDependencies.closed_dependencies_have_no_bound
