import ScopedSubstitution

/-!
Lexical readiness derived from scoped typing. Free ordinary variables belong
to the value environment and free tickets belong to the current static ticket
scope. Resource support and runtime ticket translation remain separate.
-/

namespace Ash.OneShot.ScopedExpressions
open Syntax Instantiation

theorem append_subset {left right nextLeft nextRight : List α}
    (l : left ⊆ nextLeft) (r : right ⊆ nextRight) : left ++ right ⊆ nextLeft ++ nextRight := by
  intro item member
  rcases List.mem_append.mp member with here | there
  · exact List.mem_append_left _ (l here)
  · exact List.mem_append_right _ (r there)

theorem without_subset (bound : left ⊆ right) (binder : Dependency) :
    without binder left ⊆ without binder right := by
  intro item member
  obtain ⟨present, different⟩ := mem_without.mp member
  exact mem_without.mpr ⟨bound present, different⟩

theorem effect_instantiation_keeps_atoms (effect : Effect) (environment : Environment) :
    effectAtoms effect ⊆ effectAtoms (effect.instantiate environment) := by
  intro identity member
  obtain ⟨name, present, atom⟩ := List.mem_filterMap.mp member
  cases name with
  | bound => cases atom
  | activation key =>
      cases atom
      apply List.mem_filterMap.mpr
      refine ⟨.activation identity, ?_, rfl⟩
      rw [effect_instantiation_resources]
      exact List.mem_map.mpr ⟨.activation identity, present, rfl⟩

theorem effect_instantiation_keeps_dependencies (effect : Effect) (environment : Environment) :
    (effectAtoms effect).map Dependency.resource ⊆
      (effectAtoms (effect.instantiate environment)).map Dependency.resource := by
  intro dependency member
  obtain ⟨identity, present, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨identity, effect_instantiation_keeps_atoms effect environment present, rfl⟩

mutual
/-- Opening may add resource atoms but cannot hide existing dependencies. -/
theorem Code.instantiation_keeps_dependencies (code : Code) (environment : Environment) :
    code.dependencies ⊆ (code.instantiate environment).dependencies := by
  cases code with
  | unit | boolean | integer | «variable» | discard => exact List.Subset.refl _
  | resourceRef name => cases name with
      | bound => exact List.nil_subset _
      | activation => exact List.Subset.refl _
  | pair left right | app left right | cleanup left right =>
      exact append_subset (left.instantiation_keeps_dependencies environment) (right.instantiation_keeps_dependencies environment)
  | lambda parameter body => exact without_subset (body.instantiation_keeps_dependencies environment) _
  | bind parameter initializer body =>
      exact append_subset (initializer.instantiation_keeps_dependencies environment)
        (without_subset (body.instantiation_keeps_dependencies environment) _)
  | branch condition yes no =>
      exact append_subset (append_subset (condition.instantiation_keeps_dependencies environment)
        (yes.instantiation_keeps_dependencies environment)) (no.instantiation_keeps_dependencies environment)
  | perform effect operation operand =>
      exact append_subset (effect_instantiation_keeps_dependencies effect environment)
        (operand.instantiation_keeps_dependencies environment)
  | handle effect body clauses =>
      exact append_subset (append_subset (effect_instantiation_keeps_dependencies effect environment)
        (body.instantiation_keeps_dependencies environment)) (clauses.instantiation_keeps_dependencies environment)
  | resume ticket operand =>
      intro dependency member
      rcases List.mem_cons.mp member with head | tail
      · exact List.mem_cons.mpr (Or.inl head)
      · exact List.mem_cons_of_mem _ (operand.instantiation_keeps_dependencies environment tail)
  | resource binder initializer body =>
      exact append_subset (initializer.instantiation_keeps_dependencies environment)
        (body.instantiation_keeps_dependencies (environment.mask binder))

theorem Clauses.instantiation_keeps_dependencies (clauses : Clauses) (environment : Environment) :
    clauses.dependencies ⊆ (clauses.instantiate environment).dependencies := by
  cases clauses with
  | nil => exact List.Subset.refl _
  | cons operation parameter ticket body rest =>
      exact append_subset (without_subset (without_subset (body.instantiation_keeps_dependencies environment) _) _)
        (rest.instantiation_keeps_dependencies environment)
end

end Ash.OneShot.ScopedExpressions

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (TypeEnv TicketType)

def TicketNames : TicketType → List Nat
  | .none => []
  | .bound binder _ _ _ _ => [binder]

def BoundDependency (environment : TypeEnv) (ticket : TicketType) : Dependency → Prop
  | .resource _ => True
  | .variable name => ∃ type, environment name = some type
  | .ticket name => name ∈ TicketNames ticket

def LexicallyBound (environment : TypeEnv) (ticket : TicketType) (dependencies : List Dependency) : Prop :=
  ∀ dependency ∈ dependencies, BoundDependency environment ticket dependency

theorem lexical_nil : LexicallyBound environment ticket [] := by
  intro dependency member; cases member

theorem lexical_append (left : LexicallyBound environment ticket before)
    (right : LexicallyBound environment ticket after) : LexicallyBound environment ticket (before ++ after) := by
  intro dependency member
  rcases List.mem_append.mp member with here | there
  · exact left _ here
  · exact right _ there

theorem lexical_subset (bound : LexicallyBound environment ticket right) (subset : left ⊆ right) :
    LexicallyBound environment ticket left := fun dependency member => bound dependency (subset member)

theorem lexical_remove_variable
    (bound : LexicallyBound (environment.extend parameter input) ticket dependencies) :
    LexicallyBound environment ticket (without (.variable parameter) dependencies) := by
  intro dependency member
  obtain ⟨present, different⟩ := mem_without.mp member
  have known := bound dependency present
  cases dependency with
  | resource => trivial
  | ticket => exact known
  | «variable» name =>
      have unequal : name ≠ parameter := by simpa using different
      simpa only [BoundDependency, TypeEnv.extend, if_neg unequal] using known

theorem lexical_none_ticket
    (bound : LexicallyBound environment .none dependencies) (ticket : TicketType) :
    LexicallyBound environment ticket dependencies := by
  intro dependency member
  have known := bound dependency member
  cases dependency with
  | resource => trivial
  | «variable» => exact known
  | ticket => cases known

theorem lexical_remove_ticket
    (bound : LexicallyBound environment (.bound binder input answer residual closing) dependencies) :
    LexicallyBound environment .none (without (.ticket binder) dependencies) := by
  intro dependency member
  obtain ⟨present, different⟩ := mem_without.mp member
  have known := bound dependency present
  cases dependency with
  | resource => trivial
  | «variable» => exact known
  | ticket name =>
      have same : name = binder := List.mem_singleton.mp known
      exact False.elim (different (congrArg Dependency.ticket same))

theorem lexical_effect (effect : Effect) :
    LexicallyBound environment ticket ((effectAtoms effect).map Dependency.resource) := by
  intro dependency member
  obtain ⟨identity, present, rfl⟩ := List.mem_map.mp member
  trivial

theorem typed_lexical_dependencies (typed : Typed signature world environment ticket allowed code type) :
    LexicallyBound environment ticket code.dependencies := by
  induction typed using Typed.rec
    (motive_2 := fun _ environment _ _ _ clauses _ => LexicallyBound environment .none clauses.dependencies) with
  | unit | boolean | integer => exact lexical_nil
  | «variable» known formed =>
      intro dependency member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_, known⟩
  | reference =>
      intro dependency member
      obtain rfl := List.mem_singleton.mp member
      trivial
  | pair _ _ left right | app _ _ _ left right | cleanup _ _ _ left right => exact lexical_append left right
  | lambda _ _ _ body => exact lexical_none_ticket (lexical_remove_variable body) _
  | bind _ _ initializer suffix => exact lexical_append initializer (lexical_remove_variable suffix)
  | branch _ _ _ condition yes no => exact lexical_append (lexical_append condition yes) no
  | perform _ _ _ _ operand => exact lexical_append (lexical_effect _) operand
  | handle _ _ _ _ _ body clauses => exact lexical_append (lexical_append (lexical_effect _) body) (lexical_none_ticket clauses _)
  | resume _ _ _ operand =>
      intro dependency member
      rcases List.mem_cons.mp member with head | tail
      · subst dependency; exact List.mem_cons_self
      · exact operand _ tail
  | discard =>
      intro dependency member
      obtain rfl := List.mem_singleton.mp member
      exact List.mem_cons_self
  | @resource currentWorld currentEnvironment currentTicket currentAllowed init residual answer binder source
      initTyped bodyTyped resultBound effectsBound effects initializer body =>
      obtain ⟨identity, fresh⟩ := fresh_world_name currentWorld
      exact lexical_append initializer
        (lexical_subset (body identity fresh) (source.instantiation_keeps_dependencies _))
  | nil => exact lexical_nil
  | cons _ _ _ body rest => exact lexical_append (lexical_remove_ticket (lexical_remove_variable body)) rest

end Ash.OneShot.ScopedTyping

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (TypeEnv TicketType)

theorem typed_variable_known (typed : Typed signature world environment ticket allowed code type)
    (member : Dependency.variable name ∈ code.dependencies) : ∃ input, environment name = some input :=
  typed_lexical_dependencies typed _ member

theorem typed_ticket_known (typed : Typed signature world environment ticket allowed code type)
    (member : Dependency.ticket binder ∈ code.dependencies) : binder ∈ TicketNames ticket :=
  typed_lexical_dependencies typed _ member

/-- Closed runtime values follow from empty-environment typing and value form.
    Resource access is not part of ClosedValue and remains separately checked. -/
theorem typed_value_closed
    (typed : Typed signature world TypeEnv.empty ticket allowed value type) (isValue : value.IsValue) :
    ScopedExpressions.ClosedValue value := by
  refine ⟨isValue, typed_resource_closed typed, ?_⟩
  have noTicket := typed_value_transport typed isValue .none []
  intro dependency member
  cases dependency with
  | resource => trivial
  | «variable» name =>
      obtain ⟨input, known⟩ := typed_variable_known typed member
      cases known
  | ticket binder =>
      have impossible := typed_ticket_known noTicket member
      cases impossible

theorem typed_suffix_ready
    (typed : Typed signature world (TypeEnv.empty.extend parameter input) ticket allowed suffix type) :
    ScopedExpressions.ClosedExcept parameter suffix := by
  intro name member
  obtain ⟨type, known⟩ := typed_variable_known typed member
  by_cases same : name = parameter
  · exact same
  · simp [TypeEnv.extend, TypeEnv.empty, same] at known

/-- A value-form initializer suffices: typing supplies both raw lexical checks. -/
theorem typed_bind_value_progress
    (typed : Typed signature world TypeEnv.empty ticket allowed (.bind parameter value suffix) type)
    (isValue : value.IsValue) (scope : Scope) (tail : Stack) :
    RawStep ⟨.bind parameter value suffix, scope, tail⟩ ⟨suffix.subst parameter value, scope, tail⟩ [] [] ∧
      Typed signature world TypeEnv.empty ticket allowed (suffix.subst parameter value) type := by
  cases typed with
  | bind initializer suffix =>
      exact typed_bind_step (.bind initializer suffix) (typed_value_closed initializer isValue)
        (typed_suffix_ready suffix) scope tail

theorem typed_function_value (typed : Typed signature world environment ticket allowed value (.function input output latent retained))
    (isValue : value.IsValue) : ∃ parameter body, value = .lambda parameter body := by
  cases typed <;> simp_all [Code.IsValue]

theorem typed_boolean_value (typed : Typed signature world environment ticket allowed value .boolean)
    (isValue : value.IsValue) : ∃ boolean, value = .boolean boolean := by
  cases typed <;> simp_all [Code.IsValue]

theorem typed_integer_value (typed : Typed signature world environment ticket allowed value .integer)
    (isValue : value.IsValue) : ∃ number, value = .integer number := by
  cases typed <;> simp_all [Code.IsValue]

theorem typed_application_value_progress
    (typed : Typed signature world TypeEnv.empty ticket allowed (.app function argument) type)
    (functionValue : function.IsValue) (argumentValue : argument.IsValue) (scope : Scope) (tail : Stack) :
    ∃ after, RawStep ⟨.app function argument, scope, tail⟩ ⟨after, .none, tail⟩ [] [] ∧
      Typed signature world TypeEnv.empty .none allowed after type := by
  cases typed with
  | app function argument effects =>
      obtain ⟨parameter, body, rfl⟩ := typed_function_value function functionValue
      exact ⟨_, typed_beta_step (.app function argument effects) (typed_value_closed argument argumentValue)
        (typed_value_closed function functionValue) scope tail⟩

theorem typed_branch_value_progress
    (typed : Typed signature world TypeEnv.empty ticket allowed (.branch condition yes no) type)
    (isValue : condition.IsValue) (scope : Scope) (tail : Stack) :
    ∃ after, RawStep ⟨.branch condition yes no, scope, tail⟩ ⟨after, scope, tail⟩ [] [] ∧
      Typed signature world TypeEnv.empty ticket allowed after type := by
  cases typed with
  | branch condition yes no =>
      obtain ⟨boolean, rfl⟩ := typed_boolean_value condition isValue
      cases boolean with
      | false => exact ⟨_, .ifFalse _ _ _ _, no⟩
      | true => exact ⟨_, .ifTrue _ _ _ _, yes⟩

/-- The fresh resource-entry theorem also applies when the initializer is only
    known to be a typed value: its integer form is derived canonically. -/
theorem typed_resource_value_progress
    (typed : Typed signature (resourceWorld issued) TypeEnv.empty ticket allowed (.resource binder initializer body) type)
    (isValue : initializer.IsValue) (scope : Scope) (tail : Stack)
    (ledger : Ledger (RunState.erase ⟨⟨.resource binder initializer body, scope, tail⟩, issued, completed⟩)) :
    ∃ after residual,
      RunStep ⟨⟨.resource binder initializer body, scope, tail⟩, issued, completed⟩ after ∧
      Typed signature (resourceWorld after.issued) TypeEnv.empty ticket residual after.configuration.expression type ∧
      Ledger after.erase := by
  have integerTyped : Typed signature (resourceWorld issued) TypeEnv.empty ticket allowed initializer .integer := by
    cases typed with | resource initializer _ _ _ _ => exact initializer
  obtain ⟨payload, rfl⟩ := typed_integer_value integerTyped isValue
  obtain ⟨identity, residual, fresh, step, bodyTyped, noEscape, noEffectEscape, effects, afterLedger⟩ :=
    typed_resource_entry_progress binder payload body scope type tail issued completed typed ledger
  exact ⟨_, .cell identity :: residual, step, bodyTyped, afterLedger⟩

end Ash.OneShot.ScopedTyping

#print axioms Ash.OneShot.ScopedExpressions.Code.instantiation_keeps_dependencies
#print axioms Ash.OneShot.ScopedTyping.typed_lexical_dependencies
#print axioms Ash.OneShot.ScopedTyping.typed_value_closed
#print axioms Ash.OneShot.ScopedTyping.typed_suffix_ready
#print axioms Ash.OneShot.ScopedTyping.typed_bind_value_progress
#print axioms Ash.OneShot.ScopedTyping.typed_application_value_progress
#print axioms Ash.OneShot.ScopedTyping.typed_branch_value_progress
#print axioms Ash.OneShot.ScopedTyping.typed_resource_value_progress

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (TypeEnv TicketType)

/-- Name correspondence only. The dynamic owner's existence, capability,
    ports, and consumption state remain separate configuration obligations. -/
inductive ScopeNamesMatch : TicketType → Scope → Prop where
  | none : ScopeNamesMatch .none .none
  | bound : ScopeNamesMatch (.bound binder input answer residual closing) (.ticket binder owner)

theorem lexical_translation_total
    (bound : LexicallyBound environment ticket dependencies) (matched : ScopeNamesMatch ticket scope) :
    ∃ pending, scope.translate dependencies = some pending := by
  induction dependencies with
  | nil => exact ⟨[], rfl⟩
  | cons dependency rest ih =>
      obtain ⟨pending, translated⟩ := ih (fun dep member => bound dep (List.mem_cons_of_mem _ member))
      cases dependency with
      | resource | «variable» => exact ⟨pending, translated⟩
      | ticket binder =>
          have known := bound (.ticket binder) List.mem_cons_self
          cases matched with
          | none => cases known
          | @bound localBinder input answer residual closing owner =>
              have same := List.mem_singleton.mp known
              subst binder
              exact ⟨owner :: pending, by simp [Execution.Scope.translate, Execution.Scope.resolve, translated]⟩

/-- An actual focus position gets its ports and pending-ticket translation
    from typing and structural scope-name correspondence. -/
theorem typed_focus_progress
    (focus : ScopedExecution.Focus whole child context)
    (typed : Typed signature world environment ticket allowed whole type)
    (matched : ScopeNamesMatch ticket scope) (tail : Stack) :
    ∃ plain : PlainData,
      RawStep ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ [] [] ∧
      Typed signature world environment ticket allowed child plain.input ∧
      ContextTyped signature world environment ticket allowed plain.context plain.input type ∧
      plain.output = type ∧ plain.context = context ∧ plain.scope = scope := by
  obtain ⟨input, childTyped, contextTyped⟩ := typed_focus_decomposition focus typed
  have contextBound : LexicallyBound environment ticket context.dependencies := by
    apply lexical_subset (typed_lexical_dependencies typed)
    intro dependency member
    rw [← focus_reconstructs focus]
    exact (context_dependency_membership context child dependency).mpr (Or.inl member)
  obtain ⟨pending, translated⟩ := lexical_translation_total contextBound matched
  let plain : PlainData := ⟨context, scope, input, type, pending, translated⟩
  exact ⟨plain, .focus plain focus tail, childTyped, contextTyped, rfl, rfl, rfl⟩

namespace ReadinessExamples

theorem unit_expression_type (typed : Typed signature world environment ticket allowed .unit type) : type = .unit := by
  cases typed
  rfl

theorem repeated_function_closed_from_typing : ScopedExpressions.ClosedValue ScopedExecution.Examples.function :=
  typed_value_closed (TypingExamples.repeated_function_template_typed (signature := fun _ _ => none)
    (environment := TypeEnv.empty) (ticket := .none) (allowed := []) []) trivial

theorem repeated_program_binding_progress :
    RawStep ScopedExecution.Examples.initial.configuration
      ⟨ScopedExecution.Examples.calls.subst 0 ScopedExecution.Examples.function, .none, .nil⟩ [] [] ∧
      Typed signature [] TypeEnv.empty .none []
        (ScopedExecution.Examples.calls.subst 0 ScopedExecution.Examples.function) .unit :=
  typed_bind_value_progress TypingExamples.repeated_program_typed_and_executes.1 trivial .none .nil

theorem missing_ordinary_binding_rejected :
    ¬ Typed signature world TypeEnv.empty ticket allowed (.variable 7) type := by
  intro typed
  obtain ⟨input, known⟩ := typed_variable_known typed List.mem_cons_self
  cases known

theorem unresolved_outer_ticket_rejected :
    ¬ Typed signature world environment .none allowed (.resume 9 .unit) type := by
  intro typed
  have impossible := typed_ticket_known typed List.mem_cons_self
  cases impossible

theorem wrong_runtime_binder_rejected :
    ¬ ScopeNamesMatch (.bound 9 .unit .unit [] []) (.ticket 8 3) := by
  intro matched
  cases matched

/-- The scope relation permits the actual owner 3; the pending list preserves
    repeated syntactic occurrences instead of inventing owner 9 from binder 9. -/
theorem matching_scope_translates_actual_owner :
    ScopeNamesMatch (.bound 9 .unit .unit [] []) (.ticket 9 3) ∧
      (Execution.Scope.ticket 9 3).translate [.ticket 9, .resource 4, .ticket 9] = some [3, 3] :=
  ⟨.bound, rfl⟩

theorem derived_focus_frame :
    ∃ plain : PlainData,
      RawStep
        ⟨.resume 9 (.bind 1 .unit .unit), .ticket 9 3, .nil⟩
        ⟨.bind 1 .unit .unit, .ticket 9 3, .push (.plain plain) .nil⟩ [] [] ∧
      plain.input = .unit ∧ plain.output = .unit ∧ plain.pending = [3] := by
  have typed : Typed (fun _ _ => none) [] TypeEnv.empty (.bound 9 .unit .unit [] []) []
      (.resume 9 (.bind 1 .unit .unit)) .unit :=
    .resume (.bind .unit .unit) (List.nil_subset _) (List.nil_subset _)
  obtain ⟨plain, step, child, context, output, shape, scope⟩ :=
    typed_focus_progress (.resume (by simp [Code.IsValue])) typed (.bound (owner := 3)) .nil
  have input : plain.input = .unit := by
    cases child with | bind initializer suffix => exact unit_expression_type suffix
  have pending : plain.pending = [3] := by
    have translated := plain.translated
    rw [shape, scope] at translated
    exact (Option.some.inj translated).symm
  exact ⟨plain, step, input, output, pending⟩

end ReadinessExamples
end Ash.OneShot.ScopedTyping

#print axioms Ash.OneShot.ScopedTyping.lexical_translation_total
#print axioms Ash.OneShot.ScopedTyping.typed_focus_progress
#print axioms Ash.OneShot.ScopedTyping.ReadinessExamples.repeated_function_closed_from_typing
#print axioms Ash.OneShot.ScopedTyping.ReadinessExamples.repeated_program_binding_progress
#print axioms Ash.OneShot.ScopedTyping.ReadinessExamples.missing_ordinary_binding_rejected
#print axioms Ash.OneShot.ScopedTyping.ReadinessExamples.unresolved_outer_ticket_rejected
#print axioms Ash.OneShot.ScopedTyping.ReadinessExamples.wrong_runtime_binder_rejected
#print axioms Ash.OneShot.ScopedTyping.ReadinessExamples.derived_focus_frame
