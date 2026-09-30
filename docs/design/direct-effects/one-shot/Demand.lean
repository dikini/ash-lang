import Effects

/-!
Scheduled continuation consumption derived from usage-checked code. Demands
count one consumption per path, rather than syntax occurrences in alternative
branches. Runtime ownership accounting and active visibility are separate from
the local code checks defined here.
-/

namespace Ash.OneShot.Syntax
open Execution Typing

mutual
theorem free_ticket_requires_consumption
    (checked : Uses policy scope before expression after)
    (used : Dependency.ticket binder ∈ expression.dependencies) :
    ∃ rights, scope = .ticket binder rights ∧ after = .consumed := by
  cases checked with
  | unit | boolean | integer | «variable» | resourceRef => simp_all [Expr.dependencies]
  | pair left right | app left right | bind left right | resource left right | cleanup left right =>
      rcases List.mem_append.mp used with used | used
      · obtain ⟨rights, same, consumed⟩ := free_ticket_requires_consumption left used
        exact ⟨rights, same, use_state_monotone right consumed⟩
      · first
        | exact free_ticket_requires_consumption right used
        | exact free_ticket_requires_consumption right (mem_without.mp used).1
  | lambda body =>
      obtain ⟨rights, impossible, consumed⟩ := free_ticket_requires_consumption body (mem_without.mp used).1
      cases impossible
  | branch condition yes no =>
      rcases List.mem_append.mp used with used | used
      · rcases List.mem_append.mp used with used | used
        · obtain ⟨rights, same, consumed⟩ := free_ticket_requires_consumption condition used
          exact ⟨rights, same, use_state_monotone yes consumed⟩
        · exact free_ticket_requires_consumption yes used
      · exact free_ticket_requires_consumption no used
  | perform operand =>
      rcases List.mem_append.mp used with used | used
      · exact False.elim (instance_has_no_ticket _ used)
      · exact free_ticket_requires_consumption operand used
  | handle body clauses =>
      rcases List.mem_append.mp used with used | used
      · rcases List.mem_append.mp used with used | used
        · exact False.elim (instance_has_no_ticket _ used)
        · exact free_ticket_requires_consumption body used
      · exact False.elim (usage_clauses_ticket_closed clauses used)
  | resume permitted operand =>
      rcases List.mem_cons.mp used with same | used
      · cases same
        exact ⟨_, rfl, rfl⟩
      · obtain ⟨rights, same, impossible⟩ := free_ticket_requires_consumption operand used
        cases impossible
  | discard permitted =>
      simp only [Expr.dependencies, List.mem_singleton, Dependency.ticket.injEq] at used
      subst binder
      exact ⟨_, rfl, rfl⟩
termination_by sizeOf expression

theorem usage_clauses_ticket_closed (checked : ClausesUse policy clauses)
    (used : Dependency.ticket binder ∈ clauses.dependencies) : False := by
  cases checked with
  | nil => cases used
  | cons body rest =>
      rcases List.mem_append.mp used with used | used
      · obtain ⟨withoutParameter, different⟩ := mem_without.mp used
        obtain ⟨rights, same, consumed⟩ := free_ticket_requires_consumption body (mem_without.mp withoutParameter).1
        cases same
        exact different rfl
      · exact usage_clauses_ticket_closed rest used
termination_by sizeOf clauses
end

theorem idle_usage_has_no_free_ticket
    (checked : Uses policy scope .available expression .available) :
    Dependency.ticket binder ∉ expression.dependencies := by
  intro used
  obtain ⟨rights, same, impossible⟩ := free_ticket_requires_consumption checked used
  cases impossible

theorem usage_from_consumed_is_idle
    (checked : Uses policy scope .consumed expression after) :
    Uses policy scope .available expression .available := by
  cases checked with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» => exact .variable
  | resourceRef => exact .resourceRef
  | pair left right | app left right | bind left right | resource left right | cleanup left right =>
      have same := use_state_monotone left rfl
      subst same
      first
      | exact .pair (usage_from_consumed_is_idle left) (usage_from_consumed_is_idle right)
      | exact .app (usage_from_consumed_is_idle left) (usage_from_consumed_is_idle right)
      | exact .bind (usage_from_consumed_is_idle left) (usage_from_consumed_is_idle right)
      | exact .resource (usage_from_consumed_is_idle left) (usage_from_consumed_is_idle right)
      | exact .cleanup (usage_from_consumed_is_idle left) (usage_from_consumed_is_idle right)
  | lambda body => exact .lambda body
  | branch condition yes no =>
      have same := use_state_monotone condition rfl
      subst same
      exact .branch (usage_from_consumed_is_idle condition) (usage_from_consumed_is_idle yes) (usage_from_consumed_is_idle no)
  | perform operand => exact .perform (usage_from_consumed_is_idle operand)
  | handle body clauses => exact .handle (usage_from_consumed_is_idle body) clauses
  | resume permitted operand => cases use_state_monotone operand rfl
termination_by sizeOf expression

inductive ContextUses (policy : TicketPolicy) : UseScope → UseState → Context → UseState → Prop where
  | pairLeft (right : Uses policy scope before expression after) :
      ContextUses policy scope before (.pairLeft expression) after
  | pairRight (value : expression.IsValue) (left : Uses policy .none .available expression .available) :
      ContextUses policy scope state (.pairRight expression) state
  | appFunction (argument : Uses policy scope before expression after) :
      ContextUses policy scope before (.appFunction expression) after
  | appArgument (value : expression.IsValue) (function : Uses policy .none .available expression .available) :
      ContextUses policy scope state (.appArgument expression) state
  | bind (suffix : Uses policy scope before expression after) :
      ContextUses policy scope before (.bind parameter expression) after
  | branch (yes : Uses policy scope before left after) (no : Uses policy scope before right after) :
      ContextUses policy scope before (.branch left right) after
  | perform : ContextUses policy scope state (.perform effectInst operation) state
  | resume (permitted : rights.resume = true) :
      ContextUses policy (.ticket binder rights) .available (.resume binder) .consumed
  | resource (body : Uses policy scope before expression after) :
      ContextUses policy scope before (.resource identity expression) after
  | cleanup (body : Uses policy scope before expression after) :
      ContextUses policy scope before (.cleanup expression) after

theorem context_plug_preserves_usage
    (context : ContextUses policy scope middle frame after)
    (child : Uses policy scope before expression middle) :
    Uses policy scope before (frame.plug expression) after := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight value left => exact .pair (value_use_transport value left scope before) child
  | appFunction argument => exact .app child argument
  | appArgument value function => exact .app (value_use_transport value function scope before) child
  | bind suffix => exact .bind child suffix
  | branch yes no => exact .branch child yes no
  | perform => exact .perform child
  | resume permitted => exact .resume permitted child
  | resource body => exact .resource child body
  | cleanup body => exact .cleanup child body

theorem focus_decomposes_usage (focus : Focus whole child context)
    (checked : Uses policy scope before whole after) :
    ∃ middle, Uses policy scope before child middle ∧ ContextUses policy scope middle context after := by
  cases focus with
  | pairLeft notValue => cases checked with
      | pair left right => exact ⟨_, left, .pairLeft right⟩
  | pairRight value notValue => cases checked with
      | pair left right =>
          have same := value_use_preserves_state value left
          subst same
          exact ⟨_, right, .pairRight value (value_use_transport value left .none .available)⟩
  | appFunction notValue => cases checked with
      | app function argument => exact ⟨_, function, .appFunction argument⟩
  | appArgument value notValue => cases checked with
      | app function argument =>
          have same := value_use_preserves_state value function
          subst same
          exact ⟨_, argument, .appArgument value (value_use_transport value function .none .available)⟩
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
      | cleanup callback body => exact ⟨_, callback, .cleanup body⟩

abbrev UsageTickets := Nat → Option OneShotRights

inductive UsageScope (tickets : UsageTickets) : Scope → UseScope → Prop where
  | none : UsageScope tickets .none .none
  | bound (known : tickets owner = some rights) :
      UsageScope tickets (.ticket binder owner) (.ticket binder rights)

def UsageScopeKnown (tickets : UsageTickets) (scope : Scope) : Prop :=
  ∃ useScope, UsageScope tickets scope useScope

/-- A checked fragment either has no outer demand or consumes its own lexical
    ticket once. Nested clauses and latent function bodies remain checked. -/
inductive CodeDemand (policy : TicketPolicy) (tickets : UsageTickets) : Scope → Expr → List Nat → Prop where
  | idle (scope : UsageScope tickets runtimeScope useScope)
      (checked : Uses policy useScope .available expression .available) :
      CodeDemand policy tickets runtimeScope expression []
  | consume (known : tickets owner = some rights)
      (checked : Uses policy (.ticket binder rights) .available expression .consumed) :
      CodeDemand policy tickets (.ticket binder owner) expression [owner]

theorem code_demand_scope (checked : CodeDemand policy tickets scope expression demand) :
    UsageScopeKnown tickets scope := by
  cases checked with
  | idle scope used => exact ⟨_, scope⟩
  | consume known used => exact ⟨_, .bound known⟩

theorem code_demand_is_unique (checked : CodeDemand policy tickets scope expression demand) : demand.Nodup := by
  cases checked <;> simp

theorem code_demand_value_is_empty
    (checked : CodeDemand policy tickets scope value demand) (isValue : value.IsValue) : demand = [] := by
  cases checked with
  | idle scope used => rfl
  | consume known used => cases value_use_preserves_state isValue used

theorem code_demand_value_transport
    (checked : CodeDemand policy tickets scope value demand) (isValue : value.IsValue)
    (destination : UsageScopeKnown tickets otherScope) : CodeDemand policy tickets otherScope value [] := by
  obtain ⟨useScope, scopeTyped⟩ := destination
  cases checked with
  | idle scope used => exact .idle scopeTyped (value_use_transport isValue used useScope .available)
  | consume known used => cases value_use_preserves_state isValue used

theorem code_demand_value_usage
    (checked : CodeDemand policy tickets scope value demand) (isValue : value.IsValue) :
    Uses policy .none .available value .available := by
  cases checked with
  | idle scope used => exact value_use_transport isValue used .none .available
  | consume known used => cases value_use_preserves_state isValue used

/-- Translation preserves ticket membership, without asserting multiplicity. -/
theorem scope_translate_membership {scope : Scope} {items : List Dependency}
    (translated : scope.translate items = some pending) (owner : Nat) :
    owner ∈ pending ↔ ∃ binder, Dependency.ticket binder ∈ items ∧ scope.resolve binder = some owner := by
  induction items generalizing pending with
  | nil =>
      simp only [Scope.translate, Option.some.injEq] at translated
      subst pending
      simp
  | cons dependency rest ih =>
      cases dependency with
      | «variable» name | resource name =>
          simpa using ih translated
      | ticket binder =>
          cases resolved : scope.resolve binder with
          | none => simp [Scope.translate, resolved] at translated
          | some selected =>
              cases remaining : scope.translate rest with
              | none => simp [Scope.translate, resolved, remaining] at translated
              | some tail =>
                  simp only [Scope.translate, resolved, remaining, Option.some.injEq] at translated
                  subst pending
                  simp [List.mem_cons, ih remaining, or_and_right, exists_or, resolved, eq_comm]

theorem translated_demand_membership
    (checked : CodeDemand policy tickets scope expression demand)
    (translated : scope.translate expression.dependencies = some pending) :
    ∀ owner, owner ∈ demand ↔ owner ∈ pending := by
  cases checked with
  | idle scope used =>
      intro owner
      rw [scope_translate_membership translated]
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨binder, present, resolved⟩
      exact idle_usage_has_no_free_ticket used present
  | consume known used =>
      rename_i owner rights binder
      intro name
      rw [scope_translate_membership translated]
      simp only [List.mem_singleton]
      constructor
      · intro same
        subst name
        exact ⟨binder, consuming_use_retains_ticket used, by simp [Scope.resolve]⟩
      · rintro ⟨other, present, resolved⟩
        obtain ⟨otherRights, same, consumed⟩ := free_ticket_requires_consumption used present
        have equal : other = binder := by cases same; rfl
        subst other
        simpa [Scope.resolve] using resolved.symm

namespace DemandExamples

def rights : OneShotRights := ⟨true, true⟩
def policy : TicketPolicy := fun _ => rights
def tickets : UsageTickets := fun owner => if owner = 3 then some rights else none

def alternatives : Expr := .branch (.boolean true) (.resume 9 .unit) (.discard 9)

theorem alternatives_have_one_demand :
    CodeDemand policy tickets (.ticket 9 3) alternatives [3] :=
  .consume rfl (.branch .boolean (.resume rfl .unit) (.discard rfl))

theorem alternatives_have_two_dependency_occurrences :
    (Scope.ticket 9 3).translate alternatives.dependencies = some [3, 3] := rfl

theorem sequential_double_consumption_rejected :
    ¬ Uses policy (.ticket 9 rights) .available (.pair (.resume 9 .unit) (.resume 9 .unit)) after := by
  intro checked
  cases checked with
  | pair left right =>
      cases left with
      | resume permitted operand =>
          cases right with
          | resume permitted operand => cases use_state_monotone operand rfl

end DemandExamples

end Ash.OneShot.Syntax

#print axioms Ash.OneShot.Syntax.free_ticket_requires_consumption
#print axioms Ash.OneShot.Syntax.context_plug_preserves_usage
#print axioms Ash.OneShot.Syntax.focus_decomposes_usage
#print axioms Ash.OneShot.Syntax.translated_demand_membership
