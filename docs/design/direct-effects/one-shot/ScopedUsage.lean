import ScopedAccess

/-!
Structural one-shot usage for scoped code. The projection forgets resource and
interpretation identities only for checking explicit ticket consumption. It is
not an operational erasure: it cannot establish dispatch, live support, or Core
correspondence. The structural rules are the existing Syntax.Uses judgment.
-/

namespace Ash.OneShot.ScopedExpressions
open Instantiation
open Syntax (TicketPolicy UseScope UseState UseAction OneShotRights UseProtocol)

mutual
/-- Retain the complete sequencing and ticket syntax; discard resource metadata. -/
def Code.usageShape : Code → Syntax.Expr
  | .unit => .unit
  | .boolean value => .boolean value
  | .integer value => .integer value
  | .variable name => .variable name
  | .resourceRef _ => .resourceRef 0
  | .pair left right => .pair left.usageShape right.usageShape
  | .lambda parameter body => .lambda parameter body.usageShape
  | .app function argument => .app function.usageShape argument.usageShape
  | .bind parameter initializer body => .bind parameter initializer.usageShape body.usageShape
  | .branch condition yes no => .branch condition.usageShape yes.usageShape no.usageShape
  | .perform _ operation operand => .perform (.user 0 []) operation operand.usageShape
  | .handle _ body clauses => .handle (.user 0 []) body.usageShape clauses.usageShape
  | .resume ticket operand => .resume ticket operand.usageShape
  | .discard ticket => .discard ticket
  | .resource _ initializer body => .resource 0 initializer.usageShape body.usageShape
  | .cleanup action body => .cleanup action.usageShape body.usageShape

def Clauses.usageShape : Clauses → Syntax.Clauses
  | .nil => .nil
  | .cons operation parameter ticket body rest =>
      .cons operation parameter ticket body.usageShape rest.usageShape
end

/-- A transparent application of the structural checker, not an admission oracle. -/
abbrev Uses (policy : TicketPolicy) (scope : UseScope) (before : UseState)
    (code : Code) (after : UseState) : Prop := Syntax.Uses policy scope before code.usageShape after
abbrev ClausesUse (policy : TicketPolicy) (clauses : Clauses) : Prop :=
  Syntax.ClausesUse policy clauses.usageShape
abbrev SyntaxPath (code : Code) (actions : List UseAction) : Prop :=
  Syntax.SyntaxPath code.usageShape actions

mutual
@[simp] theorem Code.instantiation_usage_shape (code : Code) (environment : Environment) :
    (code.instantiate environment).usageShape = code.usageShape := by
  cases code with
  | unit | boolean | integer | «variable» | resourceRef | discard => rfl
  | pair left right | app left right | bind _ left right | cleanup left right =>
      simp only [Code.instantiate, Code.usageShape, left.instantiation_usage_shape, right.instantiation_usage_shape]
  | lambda _ body | resume _ body | perform _ _ body =>
      simp only [Code.instantiate, Code.usageShape, body.instantiation_usage_shape]
  | branch condition yes no =>
      simp only [Code.instantiate, Code.usageShape, condition.instantiation_usage_shape,
        yes.instantiation_usage_shape, no.instantiation_usage_shape]
  | handle _ body clauses =>
      simp only [Code.instantiate, Code.usageShape, body.instantiation_usage_shape, clauses.instantiation_usage_shape]
  | resource _ initializer body =>
      simp only [Code.instantiate, Code.usageShape, initializer.instantiation_usage_shape, body.instantiation_usage_shape]

@[simp] theorem Clauses.instantiation_usage_shape (clauses : Clauses) (environment : Environment) :
    (clauses.instantiate environment).usageShape = clauses.usageShape := by
  cases clauses with
  | nil => rfl
  | cons _ _ _ body rest =>
      simp only [Clauses.instantiate, Clauses.usageShape, body.instantiation_usage_shape, rest.instantiation_usage_shape]
end

mutual
@[simp] theorem Code.substitution_usage_shape (code : Code) (name : Nat) (value : Code) :
    (code.subst name value).usageShape = code.usageShape.subst name value.usageShape := by
  cases code with
  | unit | boolean | integer | resourceRef | discard => rfl
  | «variable» => simp only [Code.subst, Code.usageShape, Syntax.Expr.subst]; split <;> rfl
  | pair left right | app left right | resource _ left right | cleanup left right =>
      simp only [Code.subst, Code.usageShape, Syntax.Expr.subst, left.substitution_usage_shape, right.substitution_usage_shape]
  | lambda _ body =>
      simp only [Code.subst, Code.usageShape, Syntax.Expr.subst]
      split <;> simp only [body.substitution_usage_shape]
  | bind _ initializer body =>
      simp only [Code.subst, Code.usageShape, Syntax.Expr.subst, initializer.substitution_usage_shape]
      split <;> simp only [body.substitution_usage_shape]
  | branch condition yes no =>
      simp only [Code.subst, Code.usageShape, Syntax.Expr.subst, condition.substitution_usage_shape,
        yes.substitution_usage_shape, no.substitution_usage_shape]
  | perform _ _ operand | resume _ operand =>
      simp only [Code.subst, Code.usageShape, Syntax.Expr.subst, operand.substitution_usage_shape]
  | handle _ body clauses =>
      simp only [Code.subst, Code.usageShape, Syntax.Expr.subst, body.substitution_usage_shape, clauses.substitution_usage_shape]

@[simp] theorem Clauses.substitution_usage_shape (clauses : Clauses) (name : Nat) (value : Code) :
    (clauses.subst name value).usageShape = clauses.usageShape.subst name value.usageShape := by
  cases clauses with
  | nil => rfl
  | cons _ _ _ body rest =>
      simp only [Clauses.subst, Clauses.usageShape, Syntax.Clauses.subst, rest.substitution_usage_shape]
      split <;> simp only [body.substitution_usage_shape]
end

open Syntax (ticketDependencies Dependency without)

theorem tickets_without_resource (items : List Dependency) (key : Nat) :
    ticketDependencies (without (.resource key) items) = ticketDependencies items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item <;> simp_all [without, ticketDependencies, List.filter_cons]
      all_goals split <;> simp_all

theorem tickets_without_variable (items : List Dependency) (name : Nat) :
    ticketDependencies (without (.variable name) items) = ticketDependencies items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item <;> simp_all [without, ticketDependencies, List.filter_cons]
      all_goals split <;> simp_all

theorem tickets_without_ticket (items : List Dependency) (name : Nat) :
    ticketDependencies (without (.ticket name) items) = (ticketDependencies items).filter (· != name) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item <;> simp_all [without, ticketDependencies, List.filter_cons]
      all_goals split <;> simp_all [eq_comm]

theorem tickets_resource_map (keys : List Nat) : ticketDependencies (keys.map Dependency.resource) = [] := by
  induction keys <;> simp_all [ticketDependencies]

theorem tickets_append (left right : List Dependency) :
    ticketDependencies (left ++ right) = ticketDependencies left ++ ticketDependencies right := by
  simp [ticketDependencies]

mutual
/-- Exact lists, including branch multiplicity and nested ticket masking. -/
theorem Code.usage_shape_tickets (code : Code) :
    ticketDependencies code.usageShape.dependencies = ticketDependencies code.dependencies := by
  cases code with
  | unit | boolean | integer | «variable» | discard => rfl
  | resourceRef name => cases name <;> rfl
  | pair left right | app left right | cleanup left right =>
      simp only [Code.usageShape, Code.dependencies, Syntax.Expr.dependencies, tickets_append,
        left.usage_shape_tickets, right.usage_shape_tickets]
  | lambda _ body =>
      simp only [Code.usageShape, Code.dependencies, Syntax.Expr.dependencies, tickets_without_variable, body.usage_shape_tickets]
  | bind _ initializer body =>
      simp only [Code.usageShape, Code.dependencies, Syntax.Expr.dependencies, tickets_append,
        tickets_without_variable, initializer.usage_shape_tickets, body.usage_shape_tickets]
  | branch condition yes no =>
      simp only [Code.usageShape, Code.dependencies, Syntax.Expr.dependencies, tickets_append,
        condition.usage_shape_tickets, yes.usage_shape_tickets, no.usage_shape_tickets]
  | perform _ _ operand =>
      simpa only [Code.usageShape, Code.dependencies, Syntax.Expr.dependencies, Syntax.instanceDependencies,
        Instance.resources, List.flatMap_nil, List.map_nil, List.nil_append, tickets_append, tickets_resource_map]
        using operand.usage_shape_tickets
  | handle _ body clauses =>
      simp only [Code.usageShape, Code.dependencies, Syntax.Expr.dependencies, Syntax.instanceDependencies,
        Instance.resources, List.flatMap_nil, List.map_nil, List.nil_append, tickets_append, tickets_resource_map,
        body.usage_shape_tickets, clauses.usage_shape_tickets]
  | resume _ operand =>
      change _ :: ticketDependencies operand.usageShape.dependencies = _ :: ticketDependencies operand.dependencies
      rw [operand.usage_shape_tickets]
  | resource _ initializer body =>
      simp only [Code.usageShape, Code.dependencies, Syntax.Expr.dependencies, tickets_append,
        tickets_without_resource, initializer.usage_shape_tickets, body.usage_shape_tickets]

theorem Clauses.usage_shape_tickets (clauses : Clauses) :
    ticketDependencies clauses.usageShape.dependencies = ticketDependencies clauses.dependencies := by
  cases clauses with
  | nil => rfl
  | cons _ _ _ body rest =>
      simp only [Clauses.usageShape, Clauses.dependencies, Syntax.Clauses.dependencies, tickets_append,
        tickets_without_ticket, tickets_without_variable, body.usage_shape_tickets, rest.usage_shape_tickets]
end

theorem instantiation_preserves_ticket_dependencies (code : Code) (environment : Environment) :
    ticketDependencies (code.instantiate environment).dependencies = ticketDependencies code.dependencies := by
  rw [← Code.usage_shape_tickets, Code.instantiation_usage_shape, Code.usage_shape_tickets]

theorem value_usage_shape {code : Code} (value : code.IsValue) : code.usageShape.IsValue := by
  cases code with
  | unit | boolean | integer | lambda => trivial
  | resourceRef name => cases name <;> trivial
  | pair left right => exact ⟨value_usage_shape value.1, value_usage_shape value.2⟩
  | «variable» | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases value
termination_by sizeOf code

theorem instantiation_preserves_usage_iff (code : Code) (environment : Environment) :
    Uses policy scope before (code.instantiate environment) after ↔ Uses policy scope before code after := by
  simp only [Uses, Code.instantiation_usage_shape]

theorem instantiation_preserves_clauses_usage_iff (clauses : Clauses) (environment : Environment) :
    ClausesUse policy (clauses.instantiate environment) ↔ ClausesUse policy clauses := by
  simp only [ClausesUse, Clauses.instantiation_usage_shape]

theorem instantiation_preserves_paths_iff (code : Code) (environment : Environment) :
    SyntaxPath (code.instantiate environment) actions ↔ SyntaxPath code actions := by
  simp only [SyntaxPath, Code.instantiation_usage_shape]

theorem usage_substitution (checked : Uses policy scope before code after)
    (value : replacement.IsValue) (replacementChecked : Uses policy .none .available replacement .available)
    (name : Nat) : Uses policy scope before (code.subst name replacement) after := by
  unfold Uses
  rw [Code.substitution_usage_shape]
  exact Syntax.usage_substitution checked (value_usage_shape value) replacementChecked name

theorem clauses_usage_substitution (checked : ClausesUse policy clauses)
    (value : replacement.IsValue) (replacementChecked : Uses policy .none .available replacement .available)
    (name : Nat) : ClausesUse policy (clauses.subst name replacement) := by
  unfold ClausesUse
  rw [Clauses.substitution_usage_shape]
  exact Syntax.clauses_usage_substitution checked (value_usage_shape value) replacementChecked name

theorem usage_path_sound (checked : Uses policy scope before code after)
    (path : SyntaxPath code actions) : UseProtocol scope before actions after :=
  Syntax.usage_path_sound checked path

theorem consuming_paths_exactly_once
    (checked : Uses policy (.ticket ticket rights) .available code .consumed)
    (path : SyntaxPath code actions) :
    (actions = [.resume ticket] ∧ rights.resume = true) ∨
      (actions = [.dispose ticket] ∧ rights.dispose = true) :=
  Syntax.consuming_paths_exactly_once checked path

theorem syntax_path_exists (code : Code) : ∃ actions, SyntaxPath code actions :=
  Syntax.syntax_path_exists code.usageShape

theorem free_ticket_requires_consumption (checked : Uses policy scope before code after)
    (used : Dependency.ticket binder ∈ code.dependencies) :
    ∃ rights, scope = .ticket binder rights ∧ after = .consumed := by
  apply Syntax.free_ticket_requires_consumption checked
  apply Syntax.mem_ticketDependencies.mp
  rw [Code.usage_shape_tickets]
  exact Syntax.mem_ticketDependencies.mpr used

theorem usage_clauses_ticket_closed (checked : ClausesUse policy clauses) :
    ticketDependencies clauses.dependencies = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro binder present
  apply Syntax.usage_clauses_ticket_closed checked (binder := binder)
  apply Syntax.mem_ticketDependencies.mp
  rwa [Clauses.usage_shape_tickets]

namespace UsageExamples

def rights : OneShotRights := ⟨true, true⟩
def policy : TicketPolicy := fun _ => rights

/-- Acquisition, ordinary sequencing, and either permitted consumption share one syntax. -/
def interleaved : Code :=
  .bind 1 (.resource 4 (.integer 17) (.perform (.cell (.bound 4)) 0 (.resourceRef (.bound 4))))
    (.branch (.boolean true) (.resume 9 .unit) (.discard 9))

theorem interleaved_checked : Uses policy (.ticket 9 rights) .available interleaved .consumed :=
  .bind (.resource .integer (.perform .resourceRef)) (.branch .boolean (.resume rfl .unit) (.discard rfl))

theorem interleaved_instantiation_checked (environment : Environment) :
    Uses policy (.ticket 9 rights) .available (interleaved.instantiate environment) .consumed :=
  (instantiation_preserves_usage_iff interleaved environment).mpr interleaved_checked

theorem interleaved_both_paths :
    SyntaxPath interleaved [.resume 9] ∧ SyntaxPath interleaved [.dispose 9] :=
  ⟨.bind (.resource .integer (.perform .resourceRef)) (.branchYes .boolean (.resume .unit)),
    .bind (.resource .integer (.perform .resourceRef)) (.branchNo .boolean .discard)⟩

theorem second_consumption_rejected :
    ¬ Uses policy (.ticket 9 rights) .available (.bind 1 (.discard 9) (.resume 9 .unit)) .consumed := by
  intro checked
  have bound := Syntax.usage_paths_at_most_once checked (Syntax.SyntaxPath.bind .discard (.resume .unit))
  have impossible : 2 ≤ 1 := bound
  omega

theorem function_cannot_capture_ticket :
    ¬ Uses policy (.ticket 9 rights) .available (.lambda 1 (.resume 9 .unit)) .available := by
  intro checked
  cases checked with
  | lambda body => cases body

theorem nested_clause_cannot_consume_outer_ticket :
    ¬ ClausesUse policy (.cons 0 1 10 (.resume 9 .unit) .nil) := by
  intro checked
  cases checked with
  | cons body rest => cases body

/-- Deliberate counterexample to interpreting usageShape as a runtime simulation. -/
theorem usage_does_not_resolve_names :
    Uses policy .none .available (.resourceRef (.bound 4)) .available ∧
    ¬ (Code.resourceRef (.bound 4)).ResourceClosed ∧
    ¬ (Code.resourceRef (.bound 4)).IsValue ∧
    (Code.resourceRef (.bound 4)).usageShape.IsValue :=
by
  refine ⟨.resourceRef, ?_, ?_, trivial⟩
  · simp [Code.ResourceClosed, Code.freeNames, ResourceName.freeNames]
  · intro impossible
    cases impossible

end UsageExamples

end Ash.OneShot.ScopedExpressions

namespace Ash.OneShot.ScopedExecution
open ScopedExpressions
open Syntax (UseScope UseState TicketPolicy)

def Context.usageShape : Context → Execution.Context
  | .pairLeft right => .pairLeft right.usageShape
  | .pairRight left => .pairRight left.usageShape
  | .appFunction argument => .appFunction argument.usageShape
  | .appArgument function => .appArgument function.usageShape
  | .bind parameter suffix => .bind parameter suffix.usageShape
  | .branch yes no => .branch yes.usageShape no.usageShape
  | .perform _ operation => .perform (.user 0 []) operation
  | .resume ticket => .resume ticket
  | .resource _ body => .resource 0 body.usageShape
  | .cleanup body => .cleanup body.usageShape

theorem context_plug_usage_shape (context : Context) (code : Code) :
    (context.plug code).usageShape = context.usageShape.plug code.usageShape := by
  cases context <;> rfl

abbrev ContextUses (policy : TicketPolicy) (scope : UseScope) (before : UseState)
    (context : Context) (after : UseState) : Prop :=
  Syntax.ContextUses policy scope before context.usageShape after

theorem context_plug_preserves_usage (context : ContextUses policy scope middle frame after)
    (child : Uses policy scope before code middle) : Uses policy scope before (frame.plug code) after := by
  unfold Uses
  rw [context_plug_usage_shape]
  exact Syntax.context_plug_preserves_usage context child

/-- Decomposition uses the actual scoped focus. It does not assume that the
    usage projection preserves non-values or operational focusing. -/
theorem focus_decomposes_usage (focus : Focus whole child context)
    (checked : Uses policy scope before whole after) :
    ∃ middle, Uses policy scope before child middle ∧ ContextUses policy scope middle context after := by
  cases focus with
  | pairLeft notValue => cases checked with
      | pair left right => exact ⟨_, left, .pairLeft right⟩
  | pairRight value notValue => cases checked with
      | pair left right =>
          have same := Syntax.value_use_preserves_state (value_usage_shape value) left
          subst same
          exact ⟨_, right, .pairRight (value_usage_shape value)
            (Syntax.value_use_transport (value_usage_shape value) left .none .available)⟩
  | appFunction notValue => cases checked with
      | app function argument => exact ⟨_, function, .appFunction argument⟩
  | appArgument value notValue => cases checked with
      | app function argument =>
          have same := Syntax.value_use_preserves_state (value_usage_shape value) function
          subst same
          exact ⟨_, argument, .appArgument (value_usage_shape value)
            (Syntax.value_use_transport (value_usage_shape value) function .none .available)⟩
  | bind notValue => cases checked with
      | bind initializer suffix => exact ⟨_, initializer, .bind suffix⟩
  | branch notValue => cases checked with
      | branch condition yes no => exact ⟨_, condition, .branch yes no⟩
  | perform notValue => cases checked with
      | perform operand => exact ⟨_, operand, .perform⟩
  | resume notValue => cases checked with
      | resume permitted operand => exact ⟨_, operand, .resume permitted⟩
  | resource notValue => cases checked with
      | resource initializer body => exact ⟨_, initializer, .resource body⟩
  | cleanup notValue => cases checked with
      | cleanup action body => exact ⟨_, action, .cleanup body⟩

/-- Fresh resource acquisition changes no ticket demand or clause permission. -/
theorem acquisition_preserves_usage
    (checked : Uses policy scope before (.resource binder (.integer payload) body) after)
    (environment : Instantiation.Environment) :
    Uses policy scope before (body.instantiate environment) after := by
  apply (instantiation_preserves_usage_iff body environment).mpr
  cases checked with
  | resource initializer body => cases initializer; exact body

abbrev CodeDemand (policy : TicketPolicy) (tickets : Syntax.UsageTickets) (scope : Scope)
    (code : Code) (demand : List Nat) : Prop := Syntax.CodeDemand policy tickets scope code.usageShape demand

theorem instantiation_preserves_code_demand_iff (code : Code) (environment : Instantiation.Environment) :
    CodeDemand policy tickets scope (code.instantiate environment) demand ↔ CodeDemand policy tickets scope code demand := by
  simp only [CodeDemand, Code.instantiation_usage_shape]

theorem bind_code_demand
    (checked : CodeDemand policy tickets scope (.bind parameter value body) demand) (isValue : value.IsValue) :
    CodeDemand policy tickets scope (body.subst parameter value) demand := by
  unfold CodeDemand
  rw [Code.substitution_usage_shape]
  exact Syntax.bind_code_demand checked (value_usage_shape isValue)

theorem beta_code_demand
    (checked : CodeDemand policy tickets scope (.app (.lambda parameter body) value) demand) (isValue : value.IsValue) :
    demand = [] ∧ CodeDemand policy tickets .none (body.subst parameter value) [] := by
  unfold CodeDemand
  rw [Code.substitution_usage_shape]
  exact Syntax.beta_code_demand checked (value_usage_shape isValue)

theorem acquisition_preserves_code_demand
    (checked : CodeDemand policy tickets scope (.resource binder (.integer payload) body) demand)
    (environment : Instantiation.Environment) :
    CodeDemand policy tickets scope (body.instantiate environment) demand := by
  apply (instantiation_preserves_code_demand_iff body environment).mpr
  exact Syntax.cell_code_demand checked

theorem focus_splits_code_demand (focus : Focus whole child context)
    (code : CodeDemand policy tickets scope whole demand) :
    ∃ childDemand frameDemand, demand = childDemand ++ frameDemand ∧
      CodeDemand policy tickets scope child childDemand ∧
      CodeDemand policy tickets scope (context.plug .unit) frameDemand := by
  cases code with
  | idle scope checked =>
      obtain ⟨middle, childUse, contextUse⟩ := focus_decomposes_usage focus checked
      cases middle with
      | available => exact ⟨[], [], rfl, .idle scope childUse, .idle scope (context_plug_preserves_usage contextUse .unit)⟩
      | consumed =>
          have impossible := Syntax.use_state_monotone (context_plug_preserves_usage (code := .unit) contextUse .unit) rfl
          cases impossible
  | consume known checked =>
      obtain ⟨middle, childUse, contextUse⟩ := focus_decomposes_usage focus checked
      cases middle with
      | available => exact ⟨[], [_], rfl, .idle (.bound known) childUse, .consume known (context_plug_preserves_usage contextUse .unit)⟩
      | consumed => exact ⟨[_], [], rfl, .consume known childUse,
          .idle (.bound known) (Syntax.usage_from_consumed_is_idle (context_plug_preserves_usage contextUse .unit))⟩

theorem scope_translate_ticket_list (scope : Scope) (items : List Syntax.Dependency) :
    scope.translate items = scope.translate ((Syntax.ticketDependencies items).map Syntax.Dependency.ticket) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item <;> simp only [Execution.Scope.translate, Syntax.ticketDependencies, List.filterMap_cons,
        List.map_cons, ih]

theorem usage_shape_scope_translation (scope : Scope) (code : Code) :
    scope.translate code.usageShape.dependencies = scope.translate code.dependencies := by
  rw [scope_translate_ticket_list scope code.usageShape.dependencies,
    scope_translate_ticket_list scope code.dependencies, Code.usage_shape_tickets]

end Ash.OneShot.ScopedExecution

#print axioms Ash.OneShot.ScopedExpressions.Code.instantiation_usage_shape
#print axioms Ash.OneShot.ScopedExpressions.Code.substitution_usage_shape
#print axioms Ash.OneShot.ScopedExpressions.instantiation_preserves_usage_iff
#print axioms Ash.OneShot.ScopedExpressions.usage_substitution
#print axioms Ash.OneShot.ScopedExpressions.consuming_paths_exactly_once
#print axioms Ash.OneShot.ScopedExecution.focus_decomposes_usage
#print axioms Ash.OneShot.ScopedExecution.context_plug_preserves_usage
#print axioms Ash.OneShot.ScopedExecution.acquisition_preserves_usage

#print axioms Ash.OneShot.ScopedExpressions.Code.usage_shape_tickets
#print axioms Ash.OneShot.ScopedExpressions.instantiation_preserves_ticket_dependencies
#print axioms Ash.OneShot.ScopedExpressions.free_ticket_requires_consumption
#print axioms Ash.OneShot.ScopedExpressions.usage_clauses_ticket_closed
#print axioms Ash.OneShot.ScopedExpressions.UsageExamples.interleaved_instantiation_checked
#print axioms Ash.OneShot.ScopedExpressions.UsageExamples.second_consumption_rejected
#print axioms Ash.OneShot.ScopedExpressions.UsageExamples.function_cannot_capture_ticket
#print axioms Ash.OneShot.ScopedExpressions.UsageExamples.nested_clause_cannot_consume_outer_ticket
#print axioms Ash.OneShot.ScopedExpressions.UsageExamples.usage_does_not_resolve_names
#print axioms Ash.OneShot.ScopedExecution.bind_code_demand
#print axioms Ash.OneShot.ScopedExecution.beta_code_demand
#print axioms Ash.OneShot.ScopedExecution.acquisition_preserves_code_demand
#print axioms Ash.OneShot.ScopedExecution.focus_splits_code_demand
#print axioms Ash.OneShot.ScopedExecution.usage_shape_scope_translation
