import TemplateSupport

/-!
Finite template return bounds survive replacement by actual closed values
whose stored support lies within the ordinary environment's bounds. These
are substitution and local entry results, not general calculus admission.
-/

namespace Ash.OneShot.TemplateSubstitution
open Instantiation ScopedExpressions ScopedExecution
open ResultSummaries (Summary analyze)
open ReturnSupport (Below)

/-- Only stored support is compared. Known-call unfolding needs the stronger
    result relation and a separate realization theorem. -/
theorem substitution_below (code : Code) (name : Nat)
    (closed : ClosedValue value)
    (bound : Below (analyze environment value) (environment name)) :
    Below (analyze environment (code.subst name value)) (analyze environment code) := by
  apply Below.trans (Below.of_support_eq (ResultSummaries.analyze_code_substitution code name closed).storage.support)
  apply ReturnSupport.analyze_monotone
  intro other
  by_cases same : other = name
  · subst other
    simpa only [ResultSummaries.extendAnalysis, ↓reduceIte] using bound
  · simp only [ResultSummaries.extendAnalysis, if_neg same]
    exact Below.refl _

/-- Each list entry contains an actual closed value and checks its storage
    against the bound for that ordinary variable. No runtime safety premise
    is hidden in this judgment. -/
inductive BindingsChecked (environment : ResultSummaries.Environment) : List (Nat × Code) → Prop where
  | nil : BindingsChecked environment []
  | cons (closed : ClosedValue value)
      (bound : Below (analyze environment value) (environment name))
      (rest : BindingsChecked environment tail) :
      BindingsChecked environment ((name, value) :: tail)

/-- Canonical first-order ports can supply a binding's storage check once
    the expression is an actual typed value. This does not infer the result
    of a pending operation or application. -/
theorem typed_first_order_binding
    (typed : ScopedPorts.Typed signature world ScopedPorts.TypeEnv.empty ticket allowed value type)
    (isValue : value.IsValue) (shape : type.FirstOrder)
    (known : (environment name).support = some type.resources) :
    BindingsChecked environment [(name, value)] := by
  have closed := ScopedPorts.typed_value_closed typed isValue
  apply BindingsChecked.cons closed _ .nil
  apply Below.of_support_eq
  rw [ResultSummaries.closed_value_storage_sound closed,
    ScopedPorts.typed_first_order_value_support typed isValue shape, known]

/-- Ordered applications of the existing capture-avoiding closed-value
    substitution. This function describes code replacement, not evaluation
    of a list of nested bind expressions. -/
def replaceAll : List (Nat × Code) → Code → Code
  | [], code => code
  | (name, value) :: rest, code => replaceAll rest (code.subst name value)

theorem replacements_below (checked : BindingsChecked environment bindings) (code : Code) :
    Below (analyze environment (replaceAll bindings code)) (analyze environment code) := by
  induction checked generalizing code with
  | nil => exact Below.refl _
  | cons closed bound _ ih =>
      exact (ih (code.subst _ _)).trans (substitution_below code _ closed bound)

theorem replacements_resource_closed (checked : BindingsChecked environment bindings)
    (closed : code.ResourceClosed) : (replaceAll bindings code).ResourceClosed := by
  induction checked generalizing code with
  | nil => exact closed
  | cons valueClosed _ _ ih =>
      exact ih (code.subst_resource_closed _ _ closed valueClosed.2.1)

theorem replacements_instantiate (checked : BindingsChecked environment bindings)
    (code : Code) (resources : Instantiation.Environment) :
    (replaceAll bindings code).instantiate resources = replaceAll bindings (code.instantiate resources) := by
  induction checked generalizing code with
  | nil => rfl
  | cons closed _ _ ih =>
      simp only [replaceAll, ih, Code.instantiation_subst _ _ _ _ closed.2.1]

theorem replacements_integer (bindings : List (Nat × Code)) :
    replaceAll bindings (.integer payload) = .integer payload := by
  induction bindings with
  | nil => rfl
  | cons first rest ih => cases first; exact ih

theorem replacements_resource (bindings : List (Nat × Code)) (body : Code) :
    replaceAll bindings (.resource binder (.integer payload) body) =
      .resource binder (.integer payload) (replaceAll bindings body) := by
  induction bindings generalizing body with
  | nil => rfl
  | cons first rest ih => cases first; exact ih _

theorem opened_replacements_bound
    (bound : TemplateSupport.SourceBound environment world body)
    (closed : (Code.resource binder initializer body).ResourceClosed)
    (checked : BindingsChecked environment bindings) :
    ∃ resources, (analyze environment
      ((replaceAll bindings body).instantiate (Instantiation.Environment.empty.bind binder identity))).support = some resources ∧
      resources ⊆ world := by
  obtain ⟨resources, known, contained⟩ := TemplateSupport.opened_source_bound bound closed (identity := identity)
  obtain ⟨retained, actual, smaller⟩ := replacements_below checked
    (body.instantiate (Instantiation.Environment.empty.bind binder identity)) resources known
  rw [replacements_instantiate checked]
  exact ⟨retained, actual, smaller.trans contained⟩

theorem source_bound_replacements
    (bound : TemplateSupport.SourceBound environment world body)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (checked : BindingsChecked environment bindings) :
    TemplateSupport.SourceBound environment world (replaceAll bindings body) := by
  let identity := world.foldr (fun n bound => max (n + 1) bound) 0
  have fresh : identity ∉ world := by
    intro member
    exact (Nat.lt_irrefl identity) (ScopedPortProgress.activation_below member)
  have resourceClosed := replacements_resource_closed checked closed
  rw [replacements_resource] at resourceClosed
  apply TemplateSupport.check_iff_source_bound.mp
  apply (TemplateSupport.fresh_opening_runtime_iff resourceClosed fresh).mpr
  exact opened_replacements_bound bound closed checked

/-- The original finite checker succeeds on the substituted template itself.
    The proof's fresh number is only a witness for reflection through opening;
    it is not a chosen runtime allocation or a liveness certificate. -/
theorem checked_replacements_preserve_check
    (bound : TemplateSupport.check environment world body = true)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (checked : BindingsChecked environment bindings) :
    TemplateSupport.check environment world (replaceAll bindings body) = true :=
  TemplateSupport.check_iff_source_bound.mpr
    (source_bound_replacements (TemplateSupport.check_iff_source_bound.mp bound) closed checked)

theorem replaced_entry_certificate
    (bound : TemplateSupport.SourceBound environment world body)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (checked : BindingsChecked environment bindings)
    (fresh : identity ∉ world) :
    ReturnBoundaries.AllocationReturn environment [.resource identity]
      ⟨(replaceAll bindings body).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  have resourceClosed := replacements_resource_closed checked closed
  rw [replacements_resource] at resourceClosed
  exact TemplateSupport.source_entry_certificate
    (source_bound_replacements bound closed checked) resourceClosed fresh

theorem checked_replaced_entry
    (bound : TemplateSupport.check environment world body = true)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (checked : BindingsChecked environment bindings)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) (replaceAll bindings body), scope, tail⟩
      ⟨(replaceAll bindings body).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    ReturnBoundaries.AllocationReturn environment [.resource identity]
      ⟨(replaceAll bindings body).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  have resourceClosed := replacements_resource_closed checked closed
  rw [replacements_resource] at resourceClosed
  exact TemplateSupport.checked_source_entry
    (checked_replacements_preserve_check bound closed checked) resourceClosed fresh

/-- An actual strict bind is followed by entry of the same substituted
    resource body. The return certificate is derived from its earlier finite
    check; typing, live ownership and issuance history are still separate. -/
theorem bind_then_entry
    (bound : TemplateSupport.check environment world body = true)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (valueClosed : ClosedValue value)
    (valueBound : Below (analyze environment value) (environment name))
    (suffixClosed : ClosedExcept name (.resource binder (.integer payload) body))
    (fresh : identity ∉ world) :
    RawStep ⟨.bind name value (.resource binder (.integer payload) body), scope, tail⟩
      ⟨.resource binder (.integer payload) (body.subst name value), scope, tail⟩ [] [] ∧
    RawStep ⟨.resource binder (.integer payload) (body.subst name value), scope, tail⟩
      ⟨(body.subst name value).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    ReturnBoundaries.AllocationReturn environment [.resource identity]
      ⟨(body.subst name value).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  have entry := checked_replaced_entry bound closed
    (BindingsChecked.cons valueClosed valueBound .nil) fresh (scope := scope) (tail := tail) (answer := answer)
  exact ⟨.bind name value _ scope tail valueClosed suffixClosed, entry⟩

namespace Examples

def aliasBody : Code := .lambda 0 (.bind 1 (.variable 3) (.integer 42))

def outerEnvironment : ResultSummaries.Environment :=
  fun name => if name = 3 then .resource 8 else .unknown

theorem alias_template_checked : TemplateSupport.check outerEnvironment [8] aliasBody = true := rfl

theorem alias_replacement_is_retaining_integer_function :
    aliasBody.subst 3 (.resourceRef (.activation 8)) = ResultSummaries.Examples.retainingConstant 8 := rfl

theorem outer_value_closed : ClosedValue (.resourceRef (.activation 8)) := by
  refine ⟨trivial, rfl, ?_⟩
  intro dependency member
  simp only [Code.dependencies, List.mem_singleton] at member
  subst dependency
  trivial

theorem outer_value_bound :
    Below (analyze outerEnvironment (.resourceRef (.activation 8))) (outerEnvironment 3) :=
  Below.refl (.resource 8)

theorem outer_value_checked : BindingsChecked outerEnvironment [(3, .resourceRef (.activation 8))] := by
  exact .cons outer_value_closed outer_value_bound .nil

theorem outer_function_checked :
    BindingsChecked outerEnvironment [(3, ResultSummaries.Examples.retainingConstant 8)] := by
  refine .cons ?_ (Below.refl (.resource 8)) .nil
  simp [ClosedValue, ResultSummaries.Examples.retainingConstant, Code.IsValue,
    Code.ResourceClosed, Code.freeNames, ResourceName.freeNames, Code.dependencies, Syntax.without]

theorem substituted_function_template_checked :
    TemplateSupport.check outerEnvironment [8]
      (replaceAll [(3, ResultSummaries.Examples.retainingConstant 8)] aliasBody) = true :=
  checked_replacements_preserve_check alias_template_checked
    (binder := 4) (payload := 41) rfl outer_function_checked

theorem actual_alias_bind_and_entry (fresh : identity ∉ [8]) :
    RawStep ⟨.bind 3 (.resourceRef (.activation 8)) (.resource 4 (.integer 41) aliasBody), .none, .nil⟩
      ⟨.resource 4 (.integer 41) (aliasBody.subst 3 (.resourceRef (.activation 8))), .none, .nil⟩ [] [] ∧
    RawStep ⟨.resource 4 (.integer 41) (aliasBody.subst 3 (.resourceRef (.activation 8))), .none, .nil⟩
      ⟨(aliasBody.subst 3 (.resourceRef (.activation 8))).instantiate (Instantiation.Environment.empty.bind 4 identity), .none,
        .push (.cell identity 41 .none ReturnBoundaries.Examples.callbackAnswer) .nil⟩ [.resource identity] [] ∧
    ReturnBoundaries.AllocationReturn outerEnvironment [.resource identity]
      ⟨(aliasBody.subst 3 (.resourceRef (.activation 8))).instantiate (Instantiation.Environment.empty.bind 4 identity), .none,
        .push (.cell identity 41 .none ReturnBoundaries.Examples.callbackAnswer) .nil⟩ := by
  apply bind_then_entry alias_template_checked _ outer_value_closed outer_value_bound _ fresh
  · rfl
  · intro name member
    simpa [Code.dependencies, aliasBody, Syntax.without] using member

/-- Replacing an empty-bound variable by a retaining value must fail even
    though both values could have an identity-free declared function port. -/
theorem empty_bound_rejects_retaining_value :
    ¬ Below (analyze TemplateSupport.Examples.unknownEnvironment
      (ResultSummaries.Examples.retainingConstant 8)) .scalar := by
  intro bound
  obtain ⟨resources, known, contained⟩ := bound [] rfl
  have same : [8] = resources := Option.some.inj known
  subst resources
  exact List.not_mem_nil (contained List.mem_cons_self)

theorem repeated_names_do_not_overwrite_inserted_values :
    replaceAll [(3, .integer 1), (3, .integer 2)] (.variable 3) = .integer 1 := rfl

end Examples
end Ash.OneShot.TemplateSubstitution

#print axioms Ash.OneShot.TemplateSubstitution.substitution_below
#print axioms Ash.OneShot.TemplateSubstitution.typed_first_order_binding
#print axioms Ash.OneShot.TemplateSubstitution.replacements_below
#print axioms Ash.OneShot.TemplateSubstitution.replacements_resource_closed
#print axioms Ash.OneShot.TemplateSubstitution.replacements_instantiate
#print axioms Ash.OneShot.TemplateSubstitution.replacements_integer
#print axioms Ash.OneShot.TemplateSubstitution.replacements_resource
#print axioms Ash.OneShot.TemplateSubstitution.opened_replacements_bound
#print axioms Ash.OneShot.TemplateSubstitution.source_bound_replacements
#print axioms Ash.OneShot.TemplateSubstitution.checked_replacements_preserve_check
#print axioms Ash.OneShot.TemplateSubstitution.replaced_entry_certificate
#print axioms Ash.OneShot.TemplateSubstitution.checked_replaced_entry
#print axioms Ash.OneShot.TemplateSubstitution.bind_then_entry
#print axioms Ash.OneShot.TemplateSubstitution.Examples.alias_template_checked
#print axioms Ash.OneShot.TemplateSubstitution.Examples.alias_replacement_is_retaining_integer_function
#print axioms Ash.OneShot.TemplateSubstitution.Examples.outer_value_closed
#print axioms Ash.OneShot.TemplateSubstitution.Examples.outer_value_bound
#print axioms Ash.OneShot.TemplateSubstitution.Examples.outer_value_checked
#print axioms Ash.OneShot.TemplateSubstitution.Examples.outer_function_checked
#print axioms Ash.OneShot.TemplateSubstitution.Examples.substituted_function_template_checked
#print axioms Ash.OneShot.TemplateSubstitution.Examples.actual_alias_bind_and_entry
#print axioms Ash.OneShot.TemplateSubstitution.Examples.empty_bound_rejects_retaining_value
#print axioms Ash.OneShot.TemplateSubstitution.Examples.repeated_names_do_not_overwrite_inserted_values
