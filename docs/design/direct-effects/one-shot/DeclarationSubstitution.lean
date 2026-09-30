import DeclarationTemplates

/-!
Ordinary closed-value substitution preserves declaration-derived template
checks. The existing structural binding certificates and concrete Code
substitution are reused; no second value-binding or execution grammar is added.
-/

namespace Ash.OneShot.DeclarationSubstitution
open Instantiation ScopedExpressions ScopedExecution
open ReturnSupport (Below)
open OperationResults (analyze)
open DeclarationResults (signature)
open TemplateSubstitution (BindingsChecked replaceAll replacements_resource_closed
  replacements_instantiate replacements_integer replacements_resource)

/-- Both analyzers compute the same actual closed-value storage. This lets
    the existing structural binding certificate serve the new observer. -/
theorem closed_value_bound_iff (closed : ClosedValue value) :
    Below (analyze signatures environment value) upper ↔
      Below (ResultSummaries.analyze environment value) upper := by
  have same := OperationResults.closed_value_old_support (signature := signatures) (environment := environment)
    (other := environment) closed
  exact ⟨fun bound => (Below.of_support_eq same.symm).trans bound,
    fun bound => (Below.of_support_eq same).trans bound⟩

/-- Only stored support is compared. Known-call unfolding needs the stronger
    result relation and a separate realization theorem. -/
theorem substitution_below (code : Code) (name : Nat)
    (closed : ClosedValue value)
    (bound : Below (analyze signatures environment value) (environment name)) :
    Below (analyze signatures environment (code.subst name value)) (analyze signatures environment code) := by
  apply Below.trans (Below.of_support_eq (OperationResults.analyze_substitution_support code name closed))
  apply OperationResults.analyze_monotone
  intro other
  by_cases same : other = name
  · subst other
    simpa only [ResultSummaries.extendAnalysis, ↓reduceIte] using bound
  · simp only [ResultSummaries.extendAnalysis, if_neg same]
    exact Below.refl _

theorem replacements_below (checked : BindingsChecked environment bindings) (code : Code) :
    Below (analyze signatures environment (replaceAll bindings code)) (analyze signatures environment code) := by
  induction checked generalizing code with
  | nil => exact Below.refl _
  | cons closed bound rest ih =>
      exact (ih (code.subst _ _)).trans
        (substitution_below code _ closed ((closed_value_bound_iff closed).mpr bound))

theorem opened_replacements_bound
    (bound : DeclarationTemplates.SourceBound declarations environment world body)
    (closed : (Code.resource binder initializer body).ResourceClosed)
    (checked : BindingsChecked environment bindings) :
    ∃ resources, (analyze (signature declarations) environment
      ((replaceAll bindings body).instantiate (Instantiation.Environment.empty.bind binder identity))).support = some resources ∧
      resources ⊆ world := by
  obtain ⟨resources, known, contained⟩ := DeclarationTemplates.opened_source_bound bound closed (identity := identity)
  obtain ⟨retained, actual, smaller⟩ := replacements_below checked
    (body.instantiate (Instantiation.Environment.empty.bind binder identity)) resources known
  rw [replacements_instantiate checked]
  exact ⟨retained, actual, smaller.trans contained⟩

theorem source_bound_replacements
    (bound : DeclarationTemplates.SourceBound declarations environment world body)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (checked : BindingsChecked environment bindings) :
    DeclarationTemplates.SourceBound declarations environment world (replaceAll bindings body) := by
  let identity := world.foldr (fun n bound => max (n + 1) bound) 0
  have fresh : identity ∉ world := by
    intro member
    exact (Nat.lt_irrefl identity) (ScopedPortProgress.activation_below member)
  have resourceClosed := replacements_resource_closed checked closed
  rw [replacements_resource] at resourceClosed
  apply DeclarationTemplates.check_iff_source_bound.mp
  apply (DeclarationTemplates.fresh_opening_runtime_iff resourceClosed fresh).mpr
  exact opened_replacements_bound bound closed checked

/-- The original finite checker succeeds on the substituted template itself.
    The proof's fresh number is only a witness for reflection through opening;
    it is not a chosen runtime allocation or a liveness certificate. -/
theorem checked_replacements_preserve_check
    (bound : DeclarationTemplates.check declarations environment world body = true)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (checked : BindingsChecked environment bindings) :
    DeclarationTemplates.check declarations environment world (replaceAll bindings body) = true :=
  DeclarationTemplates.check_iff_source_bound.mpr
    (source_bound_replacements (DeclarationTemplates.check_iff_source_bound.mp bound) closed checked)

theorem replaced_entry_certificate
    (bound : DeclarationTemplates.SourceBound declarations environment world body)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (checked : BindingsChecked environment bindings)
    (fresh : identity ∉ world) :
    OperationReturns.AllocationReturn (signature declarations) environment [.resource identity]
      ⟨(replaceAll bindings body).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  have resourceClosed := replacements_resource_closed checked closed
  rw [replacements_resource] at resourceClosed
  exact DeclarationTemplates.source_entry_certificate
    (source_bound_replacements bound closed checked) resourceClosed fresh

theorem checked_replaced_entry
    (bound : DeclarationTemplates.check declarations environment world body = true)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (checked : BindingsChecked environment bindings)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) (replaceAll bindings body), scope, tail⟩
      ⟨(replaceAll bindings body).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    OperationReturns.AllocationReturn (signature declarations) environment [.resource identity]
      ⟨(replaceAll bindings body).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  have resourceClosed := replacements_resource_closed checked closed
  rw [replacements_resource] at resourceClosed
  exact DeclarationTemplates.checked_source_entry
    (checked_replacements_preserve_check bound closed checked) resourceClosed fresh

/-- An actual strict bind is followed by entry of the same substituted
    resource body. The return certificate is derived from its earlier finite
    check; typing, live ownership and issuance history are still separate. -/
theorem bind_then_entry
    (bound : DeclarationTemplates.check declarations environment world body = true)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (valueClosed : ClosedValue value)
    (valueBound : Below (analyze (signature declarations) environment value) (environment name))
    (suffixClosed : ClosedExcept name (.resource binder (.integer payload) body))
    (fresh : identity ∉ world) :
    RawStep ⟨.bind name value (.resource binder (.integer payload) body), scope, tail⟩
      ⟨.resource binder (.integer payload) (body.subst name value), scope, tail⟩ [] [] ∧
    RawStep ⟨.resource binder (.integer payload) (body.subst name value), scope, tail⟩
      ⟨(body.subst name value).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    OperationReturns.AllocationReturn (signature declarations) environment [.resource identity]
      ⟨(body.subst name value).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  have entry := checked_replaced_entry bound closed
    (BindingsChecked.cons valueClosed ((closed_value_bound_iff valueClosed).mp valueBound) .nil) fresh (scope := scope) (tail := tail) (answer := answer)
  exact ⟨.bind name value _ scope tail valueClosed suffixClosed, entry⟩


/-- Current value typing derives the ordinary lexical premises of raw bind;
    it also establishes resource closure of the later resource template. -/
theorem typed_bind_ready
    (typed : ScopedPorts.ConfigurationTyped signatures tickets world
      ⟨.bind name value suffix, scope, tail⟩ result)
    (isValue : value.IsValue) :
    ClosedValue value ∧ ClosedExcept name suffix ∧ suffix.ResourceClosed := by
  obtain ⟨type, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | bind input body => exact ⟨ScopedPorts.typed_value_closed input isValue,
          ScopedPorts.typed_suffix_ready body, ScopedPorts.typed_resource_closed body⟩

/-- The two events are actual named execution steps. The initial template
    check survives bind and supplies admission for the following fresh entry. -/
theorem checked_bind_resource_progress
    (valid : ScopedPortJoint.Valid (signature declarations) policy registry ambient
      ⟨⟨⟨.bind name value (.resource binder (.integer payload) body), scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : value.IsValue)
    (valueBound : Below (analyze (signature declarations) environment value) (environment name))
    (templateChecked : DeclarationTemplates.check declarations environment (ScopedTyping.resourceWorld issued) body = true)
    (checked : OperationReturns.ConfigurationChecked (signature declarations) environment
      ⟨.bind name value (.resource binder (.integer payload) body), scope, tail⟩) :
    ∃ middle after,
      middle.execution.configuration = ⟨.resource binder (.integer payload) (body.subst name value), scope, tail⟩ ∧
      NamedAccessStep ambient
        ⟨⟨⟨.bind name value (.resource binder (.integer payload) body), scope, tail⟩, issued, completed⟩, activations⟩ middle ∧
      NamedAccessStep ambient middle after ∧
      ScopedPortJoint.Valid (signature declarations) policy registry ambient middle result outgoing ∧
      ScopedPortJoint.Valid (signature declarations) policy registry ambient after result outgoing ∧
      OperationReturns.ConfigurationChecked (signature declarations) environment middle.execution.configuration ∧
      OperationReturns.ConfigurationChecked (signature declarations) environment after.execution.configuration := by
  obtain ⟨closed, suffixReady, resourceClosed⟩ := typed_bind_ready
    (ScopedPorts.effect_configuration_has_types valid.effects) isValue
  let next : Configuration := ⟨.resource binder (.integer payload) (body.subst name value), scope, tail⟩
  let middle : NamedState := ⟨⟨next, issued, completed⟩, activations⟩
  have ordinary : ScopedPortJoint.OrdinaryStep
      ⟨.bind name value (.resource binder (.integer payload) body), scope, tail⟩ next :=
    .bind closed suffixReady
  have both := ScopedPortJoint.ordinary_step_preserves_joint_configuration ordinary valid
  have step : NamedAccessStep ambient
      ⟨⟨⟨.bind name value (.resource binder (.integer payload) body), scope, tail⟩, issued, completed⟩, activations⟩ middle := by
    simpa only [ScopedPortJoint.advanceState, enteredActivations, List.append_nil, List.nil_append] using both.1
  have middleValid : ScopedPortJoint.Valid (signature declarations) policy registry ambient middle result outgoing := by
    simpa only [signature, middle, ScopedPortJoint.advanceState, enteredActivations, List.append_nil, List.nil_append] using both.2
  have middleChecked : OperationReturns.ConfigurationChecked (signature declarations) environment next := checked
  have substituted : DeclarationTemplates.check declarations environment (ScopedTyping.resourceWorld issued)
      (body.subst name value) = true :=
    checked_replacements_preserve_check templateChecked resourceClosed
      (BindingsChecked.cons closed ((closed_value_bound_iff closed).mp valueBound) .nil)
  obtain ⟨after, entry, afterValid, afterChecked⟩ :=
    DeclarationTemplates.checked_resource_entry_progress middleValid substituted middleChecked
  exact ⟨middle, after, rfl, step, entry, middleValid, afterValid, middleChecked, afterChecked⟩

namespace Examples

def declarations : DeclarationRegistry := fun _ => none
def environment : ResultSummaries.Environment := fun name => if name = 3 then .scalar else .unknown
def body : Code := .bind 7 (.perform (.cell (.bound 4)) 0 (.resourceRef (.bound 4)))
  (.lambda 0 (.pair (.variable 3) (.variable 7)))

theorem earlier_template_checked :
    DeclarationTemplates.check declarations environment [] body = true ∧
    TemplateSupport.check environment [] body = false := ⟨rfl, rfl⟩

theorem copied_integer_binding : BindingsChecked environment [(3, .integer 17)] := by
  refine .cons ?_ (Below.refl .scalar) .nil
  exact ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem substituted_template_checked :
    DeclarationTemplates.check declarations environment [] (body.subst 3 (.integer 17)) = true :=
  checked_replacements_preserve_check earlier_template_checked.1
    (binder := 4) (payload := 41) rfl copied_integer_binding

theorem typed_integer_supplies_same_binding : BindingsChecked environment [(3, .integer 17)] :=
  TemplateSubstitution.typed_first_order_binding
    (signature := signature declarations) (world := []) (ticket := .none) (allowed := [])
    ScopedPorts.Typed.integer trivial ScopedPorts.Port.FirstOrder.integer rfl

theorem retained_outer_function_preserves_template :
    DeclarationTemplates.check declarations TemplateSubstitution.Examples.outerEnvironment [8]
      (body.subst 3 (ResultSummaries.Examples.retainingConstant 8)) = true :=
  checked_replacements_preserve_check (declarations := declarations) (world := [8]) (body := body) (by rfl)
    (binder := 4) (payload := 41) rfl TemplateSubstitution.Examples.outer_function_checked

/-- A closed function may hide a retained handle despite an identity-free
    function port. Replacing a scalar-bounded variable with it is not certified. -/
theorem unchecked_function_replacement_breaks_check :
    DeclarationTemplates.check declarations environment [] body = true ∧
    DeclarationTemplates.check declarations environment []
      (body.subst 3 (ResultSummaries.Examples.retainingConstant 8)) = false ∧
    ¬ BindingsChecked environment [(3, ResultSummaries.Examples.retainingConstant 8)] := by
  refine ⟨rfl, rfl, ?_⟩
  intro checked
  cases checked with
  | cons closed bound rest =>
      obtain ⟨resources, known, contained⟩ := bound [] rfl
      have same : resources = [8] := (Option.some.inj known).symm
      subst resources
      exact List.not_mem_nil (contained List.mem_cons_self)

theorem repeated_names_keep_order :
    replaceAll [(3, .integer 17), (3, .integer 99)] body = body.subst 3 (.integer 17) := rfl

def initialCode : Code := .bind 3 (.integer 17) (.resource 4 (.integer 41) body)
def initial : NamedState := ⟨⟨⟨initialCode, .none, .nil⟩, [], []⟩, []⟩
def policy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly
def result : ScopedPorts.Port := .function .unit (.product .integer .integer) []

theorem initial_typed : ScopedPorts.Typed (signature declarations) [] ScopedPorts.TypeEnv.empty .none [] initialCode result := by
  refine .bind .integer (.resource (residual := []) .integer ?_
    (List.nil_subset _) (List.nil_subset _) (List.nil_subset _))
  intro identity fresh
  change ScopedPorts.Typed (signature declarations) [identity] (ScopedPorts.TypeEnv.empty.extend 3 .integer) .none [.cell identity]
    (.bind 7 (.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)))
      (.lambda 0 (.pair (.variable 3) (.variable 7)))) result
  exact .bind (.perform rfl List.mem_cons_self (.reference List.mem_cons_self) (List.nil_subset _))
    (.lambda (.pair (.variable rfl (List.nil_subset _)) (.variable rfl (List.nil_subset _))) (List.nil_subset _))

theorem initial_valid : ScopedPortJoint.Valid (signature declarations) policy (fun _ => none) [] initial result [] :=
  ScopedPortJoint.initial_configuration_valid initial_typed
    (.bind .integer (.resource .integer (.bind (.perform .resourceRef) (.lambda (.pair .variable .variable))))) rfl

theorem actual_bind_then_joint_entry :
    ∃ middle after,
      middle.execution.configuration = ⟨.resource 4 (.integer 41) (body.subst 3 (.integer 17)), .none, .nil⟩ ∧
      NamedAccessStep [] initial middle ∧ NamedAccessStep [] middle after ∧
      ScopedPortJoint.Valid (signature declarations) policy (fun _ => none) [] middle result [] ∧
      ScopedPortJoint.Valid (signature declarations) policy (fun _ => none) [] after result [] ∧
      OperationReturns.ConfigurationChecked (signature declarations) environment middle.execution.configuration ∧
      OperationReturns.ConfigurationChecked (signature declarations) environment after.execution.configuration :=
  checked_bind_resource_progress initial_valid trivial (Below.refl .scalar) earlier_template_checked.1 trivial

end Examples

end Ash.OneShot.DeclarationSubstitution

#print axioms Ash.OneShot.DeclarationSubstitution.closed_value_bound_iff
#print axioms Ash.OneShot.DeclarationSubstitution.substitution_below
#print axioms Ash.OneShot.DeclarationSubstitution.replacements_below
#print axioms Ash.OneShot.DeclarationSubstitution.opened_replacements_bound
#print axioms Ash.OneShot.DeclarationSubstitution.source_bound_replacements
#print axioms Ash.OneShot.DeclarationSubstitution.checked_replacements_preserve_check
#print axioms Ash.OneShot.DeclarationSubstitution.replaced_entry_certificate
#print axioms Ash.OneShot.DeclarationSubstitution.checked_replaced_entry
#print axioms Ash.OneShot.DeclarationSubstitution.bind_then_entry
#print axioms Ash.OneShot.DeclarationSubstitution.typed_bind_ready
#print axioms Ash.OneShot.DeclarationSubstitution.checked_bind_resource_progress
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.earlier_template_checked
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.copied_integer_binding
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.substituted_template_checked
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.typed_integer_supplies_same_binding
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.retained_outer_function_preserves_template
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.unchecked_function_replacement_breaks_check
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.repeated_names_keep_order
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.initial_typed
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.initial_valid
#print axioms Ash.OneShot.DeclarationSubstitution.Examples.actual_bind_then_joint_entry
