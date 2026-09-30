import SymbolicTemplates

/-!
Structural finite result bounds for nested resource computations on the same
Code grammar. Resource bodies are checked at every fresh opening. This is a
result-support layer, not complete initial-term admission or a decision procedure.
-/

namespace Ash.OneShot.GenerativeResults
open Instantiation ScopedExpressions ScopedExecution
open ResultSummaries (Summary extendAnalysis)
open ReturnSupport (Below)
open DeclarationResults (signature)

/-- Only storage is represented; this summary supplies no callable behavior. -/
def summary : List Nat → Summary
  | [] => .scalar
  | identity :: rest => .product (.resource identity) (summary rest)

theorem summary_support (resources : List Nat) : (summary resources).support = some resources := by
  induction resources with
  | nil => rfl
  | cons identity rest ih => simp [summary, Summary.support, ih]

/-- Value leaves inspect stored captures. Latent function-body safety is a
    separate obligation. Strict computation constructors retain their children. -/
inductive Derives (declarations : DeclarationRegistry) :
    ResultSummaries.Environment → List Nat → Code → List Nat → Prop where
  | leaf (shape : code.IsValue ∨ ∃ name, code = .variable name)
      (closed : code.ResourceClosed)
      (checked : DeclarationTemplates.check declarations environment bound code = true) :
      Derives declarations environment world code bound
  | pair (leftChecked : Derives declarations environment world left leftBound)
      (rightChecked : Derives declarations environment world right rightBound) :
      Derives declarations environment world (.pair left right) (leftBound ++ rightBound)
  | bind (initializerChecked : Derives declarations environment world initializer inputBound)
      (bodyChecked : Derives declarations (extendAnalysis environment name (summary inputBound)) world body outputBound) :
      Derives declarations environment world (.bind name initializer body) outputBound
  | branch (conditionChecked : Derives declarations environment world condition conditionBound)
      (yesChecked : Derives declarations environment world yes bound)
      (noChecked : Derives declarations environment world no bound) :
      Derives declarations environment world (.branch condition yes no) bound
  | perform (operandChecked : Derives declarations environment world operand operandBound)
      (closed : (Code.perform effect operation operand).ResourceClosed)
      (checked : DeclarationTemplates.check declarations environment bound (.perform effect operation operand) = true) :
      Derives declarations environment world (.perform effect operation operand) bound
  | resource (initializerChecked : Derives declarations environment world initializer initializerBound)
      (closed : (Code.resource binder initializer body).ResourceClosed)
      (bodyChecked : ∀ identity, identity ∉ world →
        Derives declarations environment (world ++ [identity])
          (body.instantiate (Environment.empty.bind binder identity)) bound)
      (outward : bound ⊆ world) :
      Derives declarations environment world (.resource binder initializer body) bound

theorem resource_closed (checked : Derives declarations environment world code bound) : code.ResourceClosed := by
  induction checked with
  | leaf shape closed bound | perform operand closed bound ih | resource initializer closed body outward ihInit ihBody => exact closed
  | pair left right ihLeft ihRight | bind initializer body ihLeft ihRight =>
      exact List.append_eq_nil_iff.mpr ⟨ihLeft, ihRight⟩
  | branch condition yes no ihCondition ihYes ihNo =>
      exact List.append_eq_nil_iff.mpr ⟨List.append_eq_nil_iff.mpr ⟨ihCondition, ihYes⟩, ihNo⟩

theorem finite_check_value_support
    (checked : DeclarationTemplates.check declarations environment bound value = true)
    (closed : ClosedValue value) : Syntax.resourceDependencies value.dependencies ⊆ bound := by
  obtain ⟨resources, known, included⟩ := DeclarationTemplates.check_iff_source_bound.mp checked
  rw [DeclarationTemplates.runtime_agreement value closed.2.1,
    OperationResults.closed_value_storage_sound closed] at known
  have same := TemplateSupport.lift_injective (a₂ := some resources) known
  cases same
  exact included

theorem value_support (checked : Derives declarations environment world value bound)
    (closed : ClosedValue value) : Syntax.resourceDependencies value.dependencies ⊆ bound := by
  induction checked with
  | leaf shape resourceClosed finite => exact finite_check_value_support finite closed
  | pair left right ihLeft ihRight =>
      have leftClosed : ClosedValue _ := ⟨closed.1.1, (List.append_eq_nil_iff.mp closed.2.1).1,
        fun dependency member => closed.2.2 dependency (List.mem_append_left _ member)⟩
      have rightClosed : ClosedValue _ := ⟨closed.1.2, (List.append_eq_nil_iff.mp closed.2.1).2,
        fun dependency member => closed.2.2 dependency (List.mem_append_right _ member)⟩
      simpa only [Code.dependencies, resource_dependencies_append] using
        (ScopedExpressions.append_subset (ihLeft leftClosed) (ihRight rightClosed))
  | bind | branch | perform | resource => cases closed.1

theorem checked_substitution
    (checked : DeclarationTemplates.check declarations environment bound code = true)
    (codeClosed : code.ResourceClosed) (closed : ClosedValue value)
    (valueBound : Below (OperationResults.analyze (signature declarations) environment value) (environment name)) :
    DeclarationTemplates.check declarations environment bound (code.subst name value) = true := by
  have whole : (Code.resource 0 (.integer 0) code).ResourceClosed := by
    change ([] ++ code.freeNames.filter (· != 0)) = []
    rw [show code.freeNames = [] from codeClosed]
    rfl
  exact DeclarationSubstitution.checked_replacements_preserve_check checked whole
    (TemplateSubstitution.BindingsChecked.cons closed
      ((DeclarationSubstitution.closed_value_bound_iff closed).mp valueBound) .nil)

theorem value_substitution_shape {code value : Code} {name : Nat} (shape : code.IsValue) : (code.subst name value).IsValue := by
  cases code with
  | unit | boolean | integer | lambda => trivial
  | resourceRef resource => exact shape
  | pair left right => exact ⟨value_substitution_shape shape.1, value_substitution_shape shape.2⟩
  | «variable» | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases shape
termination_by sizeOf code

theorem leaf_substitution_shape {code value : Code} {name : Nat} (shape : code.IsValue ∨ ∃ n, code = .variable n)
    (valueShape : value.IsValue) : (code.subst name value).IsValue ∨ ∃ n, code.subst name value = .variable n := by
  rcases shape with shape | ⟨n, rfl⟩
  · exact Or.inl (value_substitution_shape shape)
  · by_cases same : name = n
    · simp only [Code.subst, if_pos same]
      exact Or.inl valueShape
    · simp only [Code.subst, if_neg same]
      exact Or.inr ⟨n, rfl⟩

theorem substitution (checked : Derives declarations environment world code bound)
    (closed : ClosedValue value)
    (valueBound : Below (OperationResults.analyze (signature declarations) environment value) (environment name)) :
    Derives declarations environment world (code.subst name value) bound := by
  induction checked with
  | leaf shape codeClosed finite =>
      exact .leaf (leaf_substitution_shape shape closed.1)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1)
        (checked_substitution finite codeClosed closed valueBound)
  | pair left right ihLeft ihRight => exact .pair (ihLeft valueBound) (ihRight valueBound)
  | @bind environment world initializer inputBound name' body outputBound initializerChecked bodyChecked ihInit ihBody =>
      change Derives _ _ _ (.bind name' (initializer.subst name value)
        (if name = name' then body else body.subst name value)) _
      by_cases same : name = name'
      · rw [if_pos same]
        exact .bind (ihInit valueBound) bodyChecked
      · rw [if_neg same]
        apply Derives.bind (ihInit valueBound)
        apply ihBody
        intro resources known
        have nameDifferent : name ≠ name' := same
        simp only [extendAnalysis, if_neg nameDifferent] at known
        obtain ⟨retained, actual, included⟩ := valueBound resources known
        exact ⟨retained, (OperationResults.closed_value_environment_support closed).trans actual, included⟩
  | branch condition yes no ihCondition ihYes ihNo =>
      exact .branch (ihCondition valueBound) (ihYes valueBound) (ihNo valueBound)
  | perform operand codeClosed finite ih =>
      exact .perform (ih valueBound) (Code.subst_resource_closed _ _ _ codeClosed closed.2.1)
        (checked_substitution finite codeClosed closed valueBound)
  | resource initializer codeClosed body outward ihInit ihBody =>
      apply Derives.resource (ihInit valueBound)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1) _ outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact ihBody identity fresh valueBound

theorem value_below_summary (checked : Derives declarations environment world value bound)
    (closed : ClosedValue value) :
    Below (OperationResults.analyze (signature declarations) otherEnvironment value) (summary bound) := by
  intro resources known
  rw [summary_support] at known
  cases known
  exact ⟨Syntax.resourceDependencies value.dependencies,
    OperationResults.closed_value_storage_sound closed, value_support checked closed⟩

/-- The reduct retains the initializer's justified support environment. A
    surrounding ordinary continuation must retain its own environment. -/
theorem bind_value_derivation
    (checked : Derives declarations environment world (.bind name value body) bound)
    (closed : ClosedValue value) :
    ∃ inputBound, Derives declarations (extendAnalysis environment name (summary inputBound)) world
      (body.subst name value) bound := by
  cases checked with
  | leaf shape resourceClosed finite =>
      rcases shape with impossible | ⟨n, same⟩
      · cases impossible
      · cases same
  | bind initializer suffix =>
      rename_i inputBound
      refine ⟨inputBound, substitution suffix closed ?_⟩
      simpa only [extendAnalysis, ↓reduceIte] using
        (value_below_summary (otherEnvironment := extendAnalysis environment name (summary inputBound)) initializer closed)

/-- The original outward bound is retained while the new body runs. It must
    later travel with the actual cell frame in a full control certificate. -/
theorem resource_entry
    (checked : Derives declarations environment world (.resource binder (.integer payload) body) bound)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩
      [.resource identity] [] ∧
    Derives declarations environment (world ++ [identity])
      (body.instantiate (Environment.empty.bind binder identity)) bound ∧ identity ∉ bound := by
  cases checked with
  | leaf shape closed checked => rcases shape with impossible | ⟨name, same⟩ <;> cases ‹_›
  | resource initializer closed bodyChecked outward =>
      exact ⟨.enterCell binder identity payload body scope answer tail closed,
        bodyChecked identity fresh, fun member => fresh (outward member)⟩

theorem world_mono (checked : Derives declarations environment world code bound)
    (included : world ⊆ larger) : Derives declarations environment larger code bound := by
  induction checked generalizing larger with
  | leaf shape closed finite => exact .leaf shape closed finite
  | pair left right ihLeft ihRight => exact .pair (ihLeft included) (ihRight included)
  | bind initializer body ihInit ihBody => exact .bind (ihInit included) (ihBody included)
  | branch condition yes no ihCondition ihYes ihNo =>
      exact .branch (ihCondition included) (ihYes included) (ihNo included)
  | perform operand closed finite ih => exact .perform (ih included) closed finite
  | resource initializer closed body outward ihInit ihBody =>
      apply Derives.resource (ihInit included) closed _ (outward.trans included)
      intro identity fresh
      exact ihBody identity (fun member => fresh (included member))
        (ScopedExpressions.append_subset included (List.Subset.refl _))

/-- A consecutive spine of actual cell frames can pass this same outward
    bound unchanged. This does not cover ordinary frames or handler forests. -/
inductive CellSpine (bound : List Nat) : Stack → Prop where
  | nil : CellSpine bound .nil
  | cell (absent : identity ∉ bound) (rest : CellSpine bound tail) :
      CellSpine bound (.push (.cell identity payload scope answer) tail)

theorem resource_entry_preserves_spine
    (checked : Derives declarations environment world (.resource binder (.integer payload) body) bound)
    (spine : CellSpine bound tail) (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩
      [.resource identity] [] ∧
    Derives declarations environment (world ++ [identity])
      (body.instantiate (Environment.empty.bind binder identity)) bound ∧
    CellSpine bound (.push (.cell identity payload scope answer) tail) := by
  obtain ⟨step, bodyChecked, absent⟩ := resource_entry checked fresh
  exact ⟨step, bodyChecked, .cell absent spine⟩

theorem value_return_access
    (checked : Derives declarations environment world value bound)
    (closed : ClosedValue value) (absent : identity ∉ bound) :
    AccessChecks ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ ambient := by
  constructor
  · intro other payload' answer' saved' scope' value' tail' same valueClosed
    cases same
    exact fun member => absent (value_support checked closed member)
  · intro requested operation operand scope' whole cap tail' handler same cut valueClosed
    cases same
    cases closed.1
  · intro binder ticket scope' caller input answer' front cap tail' plan same resolve built
    have expression := congrArg Configuration.expression same
    change value = .discard binder at expression
    rw [expression] at closed
    cases closed.1

theorem cell_return_preserves_spine
    (checked : Derives declarations environment world value bound)
    (closed : ClosedValue value)
    (spine : CellSpine bound (.push (.cell identity payload savedScope answer) tail)) :
    RawStep ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩
      ⟨value, savedScope, tail⟩ [] [.resource identity] ∧
    CellSpine bound tail ∧
    AccessChecks ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ ambient := by
  cases spine with
  | cell absent rest => exact ⟨.leaveCell identity payload answer savedScope scope value closed tail,
      rest, value_return_access checked closed absent⟩

theorem cell_return_preserves_joint
    (valid : ScopedPortJoint.Valid (signature declarations) policy registry ambient
      ⟨⟨⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (checked : Derives declarations environment (ScopedTyping.resourceWorld issued) value bound)
    (closed : ClosedValue value)
    (spine : CellSpine bound (.push (.cell identity payload savedScope answer) tail)) :
    let before : NamedState := ⟨⟨⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩, issued, completed⟩, activations⟩
    let after : NamedState := ScopedPortJoint.advanceState before ⟨value, savedScope, tail⟩ [] [.resource identity]
    NamedAccessStep ambient before after ∧
    ScopedPortJoint.Valid (signature declarations) policy registry ambient after result outgoing ∧
    CellSpine bound tail := by
  obtain ⟨raw, rest, access⟩ := cell_return_preserves_spine checked closed spine
  exact ⟨(ScopedPortJoint.checked_value_event_constructs_joint_step raw closed.1 valid access).1,
    (ScopedPortJoint.checked_value_event_constructs_joint_step raw closed.1 valid access).2, rest⟩

theorem bind_preserves_spine_and_joint
    (valid : ScopedPortJoint.Valid (signature declarations) policy registry ambient
      ⟨⟨⟨.bind name value body, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (checked : Derives declarations environment (ScopedTyping.resourceWorld issued) (.bind name value body) bound)
    (isValue : value.IsValue) (spine : CellSpine bound tail) :
    ∃ inputBound,
      let before : NamedState := ⟨⟨⟨.bind name value body, scope, tail⟩, issued, completed⟩, activations⟩
      let after := ScopedPortJoint.advanceState before ⟨body.subst name value, scope, tail⟩ [] []
      NamedAccessStep ambient before after ∧
      ScopedPortJoint.Valid (signature declarations) policy registry ambient after result outgoing ∧
      Derives declarations (extendAnalysis environment name (summary inputBound))
        (ScopedTyping.resourceWorld issued) (body.subst name value) bound ∧ CellSpine bound tail := by
  obtain ⟨closed, suffixClosed, resourceClosed⟩ := DeclarationSubstitution.typed_bind_ready
    (ScopedPorts.effect_configuration_has_types valid.effects) isValue
  obtain ⟨inputBound, afterBound⟩ := bind_value_derivation checked closed
  have ordinary : ScopedPortJoint.OrdinaryStep ⟨.bind name value body, scope, tail⟩
      ⟨body.subst name value, scope, tail⟩ := .bind closed suffixClosed
  have step := ScopedPortJoint.ordinary_step_preserves_joint_configuration ordinary valid
  exact ⟨inputBound, step.1, step.2, afterBound, spine⟩

theorem owned_reference_return_rejected :
    ¬ Derives declarations environment world
      (.resource binder initializer (.resourceRef (.bound binder))) bound := by
  intro checked
  cases checked with
  | leaf shape closed finite => rcases shape with impossible | ⟨name, same⟩ <;> cases ‹_›
  | resource initializer closed body outward =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name world
      have opened := body identity fresh
      simp only [Code.instantiate, ResourceName.instantiate, Environment.bind] at opened
      have valueClosed : ClosedValue (.resourceRef (.activation identity)) :=
        ⟨trivial, rfl, by
          intro dependency member
          simp only [Code.dependencies, List.mem_cons, List.not_mem_nil, or_false] at member
          cases member
          trivial⟩
      have included := value_support opened valueClosed
      exact fresh (outward (included (by simp [Code.dependencies, Syntax.resourceDependencies])))

namespace Examples

def declarations : DeclarationRegistry := fun _ => none
def environment : ResultSummaries.Environment := fun _ => .unknown
def callback : Code := .lambda 0 (.integer 17)
def inner : Code := .resource 4 (.integer 99) callback
def program : Code := .resource 4 (.integer 41) inner
def answer : Ty := .function .unit .integer [] []
def initial : RunState := ⟨⟨program, .none, .nil⟩, [], []⟩
def outerState : Configuration := ⟨inner, .none, .push (.cell 8 41 .none answer) .nil⟩
def innerState : Configuration := ⟨callback, .none,
  .push (.cell 9 99 .none answer) (.push (.cell 8 41 .none answer) .nil)⟩
def returnedInner : Configuration := ⟨callback, .none, .push (.cell 8 41 .none answer) .nil⟩
def terminal : RunState := ⟨⟨callback, .none, .nil⟩, [.resource 8, .resource 9], [.resource 8, .resource 9]⟩

theorem callback_closed : ClosedValue callback := ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem callback_bound (world : List Nat) : Derives declarations environment world callback [] :=
  .leaf (Or.inl trivial) rfl rfl

theorem inner_bound (world : List Nat) : Derives declarations environment world inner [] := by
  refine Derives.resource (initializerBound := []) ?_ ?_ ?_ (List.nil_subset _)
  · exact .leaf (Or.inl trivial) rfl rfl
  · rfl
  · intro identity fresh
    exact callback_bound _

theorem program_bound : Derives declarations environment [] program [] := by
  refine Derives.resource (initializerBound := []) ?_ ?_ ?_ (List.nil_subset _)
  · exact .leaf (Or.inl trivial) rfl rfl
  · rfl
  · intro identity fresh
    exact inner_bound _

theorem old_observer_loses_nested_result :
    DeclarationTemplates.check declarations environment [] inner = false ∧
    OperationResults.analyze (signature declarations) environment inner = .unknown := ⟨rfl, rfl⟩

theorem outer_entry_keeps_recursive_bound :
    RawStep initial.configuration outerState [.resource 8] [] ∧
    Derives declarations environment [8] inner [] ∧ CellSpine [] outerState.stack :=
  resource_entry_preserves_spine program_bound .nil (by decide)

theorem inner_entry_keeps_recursive_bound :
    RawStep outerState innerState [.resource 9] [] ∧
    Derives declarations environment [8, 9] callback [] ∧ CellSpine [] innerState.stack :=
  resource_entry_preserves_spine (inner_bound [8]) outer_entry_keeps_recursive_bound.2.2 (by decide)

theorem inner_return_keeps_bound :
    RawStep innerState returnedInner [] [.resource 9] ∧ CellSpine [] returnedInner.stack ∧
    AccessChecks innerState [] :=
  cell_return_preserves_spine (callback_bound [8, 9]) callback_closed inner_entry_keeps_recursive_bound.2.2

theorem outer_return_keeps_bound :
    RawStep returnedInner terminal.configuration [] [.resource 8] ∧ CellSpine [] terminal.configuration.stack ∧
    AccessChecks returnedInner [] :=
  cell_return_preserves_spine (callback_bound [8, 9]) callback_closed inner_return_keeps_bound.2.1

/-- RawTrace stores completion history newest-first. The event sequence
    releases inner 9 before outer 8, yielding final history [8,9]. -/
theorem nested_trace :
    RawTrace initial.configuration terminal.configuration [.resource 8, .resource 9] [.resource 8, .resource 9] :=
  .next outer_entry_keeps_recursive_bound.1 (.next inner_entry_keeps_recursive_bound.1
    (.next inner_return_keeps_bound.1 (.next outer_return_keeps_bound.1 (.refl _))))

theorem nested_execution : RunSteps initial terminal :=
  raw_trace_enacts nested_trace (issued := []) (completed := []) (by decide)

theorem nested_ownership_complete : Ledger terminal.erase ∧ terminal.completed.Nodup :=
  ⟨run_steps_preserve_ledger nested_execution ⟨.refl _, by decide⟩,
    run_no_double_completion nested_execution ⟨.refl _, by decide⟩⟩

def unsafeIgnored : Code := .bind 3
  (.resource 4 (.integer 41) (.resourceRef (.bound 4))) (.integer 17)

theorem ignored_unsafe_initializer_rejected :
    DeclarationTemplates.check declarations environment [] unsafeIgnored = true ∧
    ∀ bound, ¬ Derives declarations environment [] unsafeIgnored bound := by
  refine ⟨rfl, ?_⟩
  intro bound checked
  cases checked with
  | leaf shape closed finite => rcases shape with impossible | ⟨name, same⟩ <;> cases ‹_›
  | bind initializer body => exact owned_reference_return_rejected initializer

def boundEnvironment : ResultSummaries.Environment := extendAnalysis environment 3 (summary [])
def pendingCallback : Code := .lambda 0 (.variable 3)
def pendingInner : Code := .resource 4 (.integer 99) pendingCallback
def pendingProgram : Code := .resource 4 (.integer 41) pendingInner

theorem pending_inner_bound (world : List Nat) : Derives declarations boundEnvironment world pendingInner [] := by
  refine Derives.resource (initializerBound := []) ?_ ?_ ?_ (List.nil_subset _)
  · exact .leaf (Or.inl trivial) rfl rfl
  · rfl
  · intro identity fresh
    exact .leaf (Or.inl trivial) rfl rfl

theorem pending_program_bound : Derives declarations boundEnvironment [] pendingProgram [] := by
  refine Derives.resource (initializerBound := []) ?_ ?_ ?_ (List.nil_subset _)
  · exact .leaf (Or.inl trivial) rfl rfl
  · rfl
  · intro identity fresh
    exact pending_inner_bound _

theorem integer_substitution_preserves_nested_derivation :
    Derives declarations boundEnvironment [] (pendingProgram.subst 3 (.integer 17)) [] ∧
    pendingProgram.subst 3 (.integer 17) = program := by
  refine ⟨substitution pending_program_bound ?_ (Below.refl .scalar), rfl⟩
  exact ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem preceding_bind_retains_initializer_derivation :
    Derives declarations environment [] (.bind 3 (.integer 17) pendingProgram) [] :=
  .bind (.leaf (Or.inl trivial) rfl rfl) pending_program_bound

theorem actual_bind_then_nested_execution :
    RawTrace ⟨.bind 3 (.integer 17) pendingProgram, .none, .nil⟩ terminal.configuration
      [.resource 8, .resource 9] [.resource 8, .resource 9] := by
  have step : RawStep ⟨.bind 3 (.integer 17) pendingProgram, .none, .nil⟩ initial.configuration [] [] :=
    .bind 3 (.integer 17) pendingProgram .none .nil
      ⟨trivial, rfl, by intro dependency member; cases member⟩
      (by simp [ClosedExcept, pendingProgram, pendingInner, pendingCallback, Code.dependencies, Syntax.without])
  exact .next step nested_trace

def result : ScopedPorts.Port := .function .unit .integer []
def policy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly

theorem inner_typed (world : List Nat) (allowed : List Instance) :
    ScopedPorts.Typed (signature declarations) world ScopedPorts.TypeEnv.empty .none allowed inner result := by
  refine .resource (residual := []) .integer ?_ (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)
  intro identity fresh
  exact .lambda .integer (List.nil_subset _)

theorem program_typed :
    ScopedPorts.Typed (signature declarations) [] ScopedPorts.TypeEnv.empty .none [] program result := by
  refine .resource (residual := []) .integer ?_ (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)
  intro identity fresh
  exact inner_typed [identity] [.cell identity]

theorem initial_joint_valid :
    ScopedPortJoint.Valid (signature declarations) policy (fun _ => none) [] ⟨initial, []⟩ result [] :=
  ScopedPortJoint.initial_configuration_valid program_typed
    (.resource .integer (.resource .integer (.lambda .integer))) rfl

def beforeBind : NamedState := ⟨⟨⟨.bind 3 (.integer 17) pendingProgram, .none, .nil⟩, [], []⟩, []⟩

theorem preceding_bind_typed :
    ScopedPorts.Typed (signature declarations) [] ScopedPorts.TypeEnv.empty .none []
      (.bind 3 (.integer 17) pendingProgram) result := by
  refine .bind .integer (.resource (residual := []) .integer ?_
    (List.nil_subset _) (List.nil_subset _) (List.nil_subset _))
  intro outer outerFresh
  refine .resource (residual := []) .integer ?_ (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)
  intro inner innerFresh
  exact .lambda (.variable rfl (List.nil_subset _)) (List.nil_subset _)

theorem before_bind_valid :
    ScopedPortJoint.Valid (signature declarations) policy (fun _ => none) [] beforeBind result [] :=
  ScopedPortJoint.initial_configuration_valid preceding_bind_typed
    (.bind .integer (.resource .integer (.resource .integer (.lambda .variable)))) rfl

theorem actual_joint_bind_derives_replacement_bound :
    ∃ inputBound, NamedAccessStep [] beforeBind ⟨initial, []⟩ ∧
      ScopedPortJoint.Valid (signature declarations) policy (fun _ => none) [] ⟨initial, []⟩ result [] ∧
      Derives declarations (extendAnalysis environment 3 (summary inputBound)) [] program [] ∧ CellSpine [] .nil :=
  bind_preserves_spine_and_joint before_bind_valid preceding_bind_retains_initializer_derivation trivial .nil

theorem returned_callback_application :
    RawStep ⟨.app callback .unit, .none, .nil⟩ ⟨.integer 17, .none, .nil⟩ [] [] :=
  .beta 0 (.integer 17) .unit .none .nil
    ⟨trivial, rfl, by intro dependency member; cases member⟩ callback_closed

end Examples

end Ash.OneShot.GenerativeResults

#print axioms Ash.OneShot.GenerativeResults.summary_support
#print axioms Ash.OneShot.GenerativeResults.resource_closed
#print axioms Ash.OneShot.GenerativeResults.finite_check_value_support
#print axioms Ash.OneShot.GenerativeResults.value_support
#print axioms Ash.OneShot.GenerativeResults.checked_substitution
#print axioms Ash.OneShot.GenerativeResults.value_substitution_shape
#print axioms Ash.OneShot.GenerativeResults.leaf_substitution_shape
#print axioms Ash.OneShot.GenerativeResults.substitution
#print axioms Ash.OneShot.GenerativeResults.resource_entry
#print axioms Ash.OneShot.GenerativeResults.world_mono
#print axioms Ash.OneShot.GenerativeResults.resource_entry_preserves_spine
#print axioms Ash.OneShot.GenerativeResults.value_return_access
#print axioms Ash.OneShot.GenerativeResults.cell_return_preserves_spine
#print axioms Ash.OneShot.GenerativeResults.cell_return_preserves_joint
#print axioms Ash.OneShot.GenerativeResults.owned_reference_return_rejected
#print axioms Ash.OneShot.GenerativeResults.Examples.callback_closed
#print axioms Ash.OneShot.GenerativeResults.Examples.callback_bound
#print axioms Ash.OneShot.GenerativeResults.Examples.inner_bound
#print axioms Ash.OneShot.GenerativeResults.Examples.program_bound
#print axioms Ash.OneShot.GenerativeResults.Examples.old_observer_loses_nested_result
#print axioms Ash.OneShot.GenerativeResults.Examples.outer_entry_keeps_recursive_bound
#print axioms Ash.OneShot.GenerativeResults.Examples.inner_entry_keeps_recursive_bound
#print axioms Ash.OneShot.GenerativeResults.Examples.inner_return_keeps_bound
#print axioms Ash.OneShot.GenerativeResults.Examples.outer_return_keeps_bound
#print axioms Ash.OneShot.GenerativeResults.Examples.nested_trace
#print axioms Ash.OneShot.GenerativeResults.Examples.nested_execution
#print axioms Ash.OneShot.GenerativeResults.Examples.nested_ownership_complete
#print axioms Ash.OneShot.GenerativeResults.Examples.ignored_unsafe_initializer_rejected
#print axioms Ash.OneShot.GenerativeResults.Examples.pending_inner_bound
#print axioms Ash.OneShot.GenerativeResults.Examples.pending_program_bound
#print axioms Ash.OneShot.GenerativeResults.Examples.integer_substitution_preserves_nested_derivation
#print axioms Ash.OneShot.GenerativeResults.Examples.preceding_bind_retains_initializer_derivation
#print axioms Ash.OneShot.GenerativeResults.Examples.actual_bind_then_nested_execution
#print axioms Ash.OneShot.GenerativeResults.Examples.inner_typed
#print axioms Ash.OneShot.GenerativeResults.Examples.program_typed
#print axioms Ash.OneShot.GenerativeResults.Examples.initial_joint_valid

#print axioms Ash.OneShot.GenerativeResults.Examples.returned_callback_application

#print axioms Ash.OneShot.GenerativeResults.value_below_summary
#print axioms Ash.OneShot.GenerativeResults.bind_value_derivation
#print axioms Ash.OneShot.GenerativeResults.bind_preserves_spine_and_joint

#print axioms Ash.OneShot.GenerativeResults.Examples.preceding_bind_typed
#print axioms Ash.OneShot.GenerativeResults.Examples.before_bind_valid
#print axioms Ash.OneShot.GenerativeResults.Examples.actual_joint_bind_derives_replacement_bound
