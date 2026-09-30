import OneShot

/-!
Expression-derived retained dependencies for the direct one-shot kernel.

These are administrative expressions with explicit instantiated resource and
ticket identities. They mirror the relevant Core forms, not its complete type
system. The module proves dependency transport and connects pending binding
suffixes to structural cut rejection. It does not yet prove expression-machine
preservation, infer residual cleanup effects, or validate Core elaboration.
-/

namespace Ash.OneShot.Syntax

inductive Dependency where
  | variable : Nat → Dependency
  | resource : Nat → Dependency
  | ticket : Nat → Dependency
  deriving DecidableEq, Repr

def without (name : Dependency) (items : List Dependency) : List Dependency :=
  items.filter (· != name)

def instanceDependencies (effectInst : Instance) : List Dependency :=
  effectInst.resources.map Dependency.resource

mutual
inductive Expr where
  | unit
  | boolean : Bool → Expr
  | integer : Int → Expr
  | variable : Nat → Expr
  | resourceRef : Nat → Expr
  | pair : Expr → Expr → Expr
  | lambda : Nat → Expr → Expr
  | app : Expr → Expr → Expr
  | bind : Nat → Expr → Expr → Expr
  | branch : Expr → Expr → Expr → Expr
  | perform : Instance → Nat → Expr → Expr
  | handle : Instance → Expr → Clauses → Expr
  | resume : Nat → Expr → Expr
  | discard : Nat → Expr
  | resource : Nat → Expr → Expr → Expr
  | cleanup : Expr → Expr → Expr
  deriving Repr

inductive Clauses where
  | nil
  | cons : Nat → Nat → Nat → Expr → Clauses → Clauses
  deriving Repr
end

mutual
def Expr.dependencies : Expr → List Dependency
  | .unit | .boolean _ | .integer _ => []
  | .variable name => [.variable name]
  | .resourceRef resource => [.resource resource]
  | .pair left right | .app left right | .cleanup left right =>
      left.dependencies ++ right.dependencies
  | .lambda parameter body => without (.variable parameter) body.dependencies
  | .bind name initializer body =>
      initializer.dependencies ++ without (.variable name) body.dependencies
  | .branch condition yes no =>
      condition.dependencies ++ yes.dependencies ++ no.dependencies
  | .perform effectInst _ operand => instanceDependencies effectInst ++ operand.dependencies
  | .handle effectInst body clauses =>
      instanceDependencies effectInst ++ body.dependencies ++ clauses.dependencies
  | .resume ticket operand => .ticket ticket :: operand.dependencies
  | .discard ticket => [.ticket ticket]
  | .resource resource initializer body =>
      initializer.dependencies ++ without (.resource resource) body.dependencies

def Clauses.dependencies : Clauses → List Dependency
  | .nil => []
  | .cons _ parameter ticket body rest =>
      without (.ticket ticket) (without (.variable parameter) body.dependencies) ++
      rest.dependencies
end

mutual
/-- Runtime substitution uses closed values: no free value variables or tickets.
    Resource identities are globally fresh owners, not value-variable binders. -/
def Expr.subst (expression : Expr) (name : Nat) (value : Expr) : Expr := match expression with
  | .variable other => if name = other then value else .variable other
  | .unit => .unit
  | .boolean value => .boolean value
  | .integer value => .integer value
  | .resourceRef resource => .resourceRef resource
  | .pair left right => .pair (left.subst name value) (right.subst name value)
  | .lambda parameter body =>
      .lambda parameter (if name = parameter then body else body.subst name value)
  | .app function argument => .app (function.subst name value) (argument.subst name value)
  | .bind parameter initializer body =>
      .bind parameter (initializer.subst name value)
        (if name = parameter then body else body.subst name value)
  | .branch condition yes no =>
      .branch (condition.subst name value) (yes.subst name value) (no.subst name value)
  | .perform effectInst operation operand => .perform effectInst operation (operand.subst name value)
  | .handle effectInst body clauses =>
      .handle effectInst (body.subst name value) (clauses.subst name value)
  | .resume ticket operand => .resume ticket (operand.subst name value)
  | .discard ticket => .discard ticket
  | .resource resource initializer body =>
      .resource resource (initializer.subst name value) (body.subst name value)
  | .cleanup action body => .cleanup (action.subst name value) (body.subst name value)

def Clauses.subst (clauses : Clauses) (name : Nat) (value : Expr) : Clauses := match clauses with
  | .nil => .nil
  | .cons operation parameter ticket body rest =>
      .cons operation parameter ticket
        (if name = parameter then body else body.subst name value) (rest.subst name value)
end

def Expr.IsValue : Expr → Prop
  | .unit | .boolean _ | .integer _ | .resourceRef _ | .lambda _ _ => True
  | .pair left right => left.IsValue ∧ right.IsValue
  | _ => False

/-- Closed in the value-variable and ticket namespaces; resource access may be retained. -/
def ClosedValue (value : Expr) : Prop :=
  value.IsValue ∧ ∀ dependency ∈ value.dependencies,
    match dependency with | .resource _ => True | _ => False

def ClosedExcept (parameter : Nat) (suffix : Expr) : Prop :=
  ∀ name, Dependency.variable name ∈ suffix.dependencies → name = parameter

mutual
def Expr.resourceBinders : Expr → List Nat
  | .unit | .boolean _ | .integer _ | .variable _ | .resourceRef _ | .discard _ => []
  | .pair left right | .app left right | .cleanup left right | .bind _ left right =>
      left.resourceBinders ++ right.resourceBinders
  | .lambda _ body | .perform _ _ body | .resume _ body => body.resourceBinders
  | .branch condition yes no => condition.resourceBinders ++ yes.resourceBinders ++ no.resourceBinders
  | .handle _ body clauses => body.resourceBinders ++ clauses.resourceBinders
  | .resource identity initializer body =>
      identity :: (initializer.resourceBinders ++ body.resourceBinders)

def Clauses.resourceBinders : Clauses → List Nat
  | .nil => []
  | .cons _ _ _ body rest => body.resourceBinders ++ rest.resourceBinders
end

/-- Administrative resource binders must be fresh for an inserted value.
    A full source machine must instantiate/freshen these names before substitution. -/
def ResourceFresh (value body : Expr) : Prop :=
  ∀ resource, Dependency.resource resource ∈ value.dependencies → resource ∉ body.resourceBinders

def resourceDependencies (items : List Dependency) : List Nat := items.filterMap fun item =>
  match item with | .resource resource => some resource | _ => none

def ticketDependencies (items : List Dependency) : List Nat := items.filterMap fun item =>
  match item with | .ticket ticket => some ticket | _ => none

/-- The suffix parameter is not retained before its initializer has returned.
    Request annotations are reserved for cleanup residual-effect evidence in
    this kernel; this constructor does not infer an effect row for the suffix. -/
def bindingFrame (parameter : Nat) (suffix : Expr) (input answer : Ty) : Frame :=
  let retained := without (.variable parameter) suffix.dependencies
  ⟨.bind, input, answer, resourceDependencies retained, ticketDependencies retained, []⟩

@[simp] theorem mem_without : item ∈ without name items ↔ item ∈ items ∧ item ≠ name := by
  simp [without]

theorem self_dependency_bound (items extra : List Dependency) : items ⊆ items ++ extra :=
  fun _ h => List.mem_append_left _ h

theorem append_dependency_bound {left right leftBase rightBase extra : List Dependency}
    (hl : left ⊆ leftBase ++ extra) (hr : right ⊆ rightBase ++ extra) :
    left ++ right ⊆ (leftBase ++ rightBase) ++ extra := by
  intro item h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp (hl h) with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · exact List.mem_append_right _ h
  · rcases List.mem_append.mp (hr h) with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h

theorem without_dependency_bound {items base extra : List Dependency}
    (h : items ⊆ base ++ extra) (name : Dependency) :
    without name items ⊆ without name base ++ extra := by
  intro item hi
  obtain ⟨inside, different⟩ := mem_without.mp hi
  rcases List.mem_append.mp (h inside) with original | inserted
  · exact List.mem_append_left _ (mem_without.mpr ⟨original, different⟩)
  · exact List.mem_append_right _ inserted

theorem cons_dependency_bound {items base extra : List Dependency}
    (h : items ⊆ base ++ extra) (name : Dependency) :
    name :: items ⊆ (name :: base) ++ extra := by
  intro item hi
  rcases List.mem_cons.mp hi with rfl | hi
  · exact List.mem_append_left _ List.mem_cons_self
  · rcases List.mem_append.mp (h hi) with hi | hi
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ hi)
    · exact List.mem_append_right _ hi

mutual
/-- Substitution cannot introduce a dependency absent from both the original
    expression and inserted value. This upper bound also holds for open syntax. -/
theorem Expr.subst_dependencies (expression : Expr) (name : Nat) (value : Expr) :
    (expression.subst name value).dependencies ⊆ expression.dependencies ++ value.dependencies := by
  cases expression with
  | unit | boolean _ | integer _ | resourceRef _ | discard _ =>
      exact self_dependency_bound _ _
  | «variable» other =>
      by_cases same : name = other
      · simp [Expr.subst, same, Expr.dependencies]
      · simpa only [Expr.subst, if_neg same] using
          self_dependency_bound (Expr.variable other).dependencies value.dependencies
  | pair left right | app left right | cleanup left right =>
      exact append_dependency_bound (left.subst_dependencies name value)
        (right.subst_dependencies name value)
  | lambda parameter body =>
      by_cases same : name = parameter
      · simpa only [Expr.subst, if_pos same] using
          self_dependency_bound (Expr.lambda parameter body).dependencies value.dependencies
      · simpa only [Expr.subst, if_neg same, Expr.dependencies] using
          without_dependency_bound (body.subst_dependencies name value) (.variable parameter)
  | bind parameter initializer body =>
      have hi := initializer.subst_dependencies name value
      by_cases same : name = parameter
      · simpa only [Expr.subst, if_pos same, Expr.dependencies] using
          append_dependency_bound hi
            (self_dependency_bound (without (.variable parameter) body.dependencies) value.dependencies)
      · simpa only [Expr.subst, if_neg same, Expr.dependencies] using
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
        (without_dependency_bound (body.subst_dependencies name value) (.resource resource))

theorem Clauses.subst_dependencies (clauses : Clauses) (name : Nat) (value : Expr) :
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

mutual
theorem Expr.subst_keeps_dependency (expression : Expr) (name : Nat) (value : Expr)
    (dependency : Dependency) (different : dependency ≠ .variable name)
    (retained : dependency ∈ expression.dependencies) :
    dependency ∈ (expression.subst name value).dependencies := by
  cases expression with
  | unit | boolean _ | integer _ => cases retained
  | resourceRef _ | discard _ => exact retained
  | «variable» other =>
      by_cases same : name = other
      · simp_all [Expr.dependencies]
      · simpa only [Expr.subst, if_neg same] using retained
  | pair left right | app left right | cleanup left right =>
      rcases List.mem_append.mp retained with hl | hr
      · exact List.mem_append_left _ (left.subst_keeps_dependency name value dependency different hl)
      · exact List.mem_append_right _ (right.subst_keeps_dependency name value dependency different hr)
  | lambda parameter body =>
      by_cases same : name = parameter
      · simpa only [Expr.subst, if_pos same] using retained
      · obtain ⟨inside, distinct⟩ := mem_without.mp retained
        simp only [Expr.subst, if_neg same, Expr.dependencies]
        exact mem_without.mpr ⟨body.subst_keeps_dependency name value dependency different inside,
          distinct⟩
  | bind parameter initializer body =>
      rcases List.mem_append.mp retained with hi | hb
      · exact List.mem_append_left _ (initializer.subst_keeps_dependency name value dependency different hi)
      · by_cases same : name = parameter
        · simpa only [Expr.subst, if_pos same, Expr.dependencies] using
            List.mem_append_right (initializer.subst name value).dependencies hb
        · obtain ⟨inside, distinct⟩ := mem_without.mp hb
          simp only [Expr.subst, if_neg same, Expr.dependencies]
          exact List.mem_append_right _ (mem_without.mpr
            ⟨body.subst_keeps_dependency name value dependency different inside, distinct⟩)
  | branch condition yes no =>
      rcases List.mem_append.mp retained with first | last
      · rcases List.mem_append.mp first with hc | hy
        · exact List.mem_append_left _ (List.mem_append_left _
            (condition.subst_keeps_dependency name value dependency different hc))
        · exact List.mem_append_left _ (List.mem_append_right _
            (yes.subst_keeps_dependency name value dependency different hy))
      · exact List.mem_append_right _ (no.subst_keeps_dependency name value dependency different last)
  | perform effectInst operation operand =>
      rcases List.mem_append.mp retained with direct | arg
      · exact List.mem_append_left _ direct
      · exact List.mem_append_right _ (operand.subst_keeps_dependency name value dependency different arg)
  | handle effectInst body clauses =>
      rcases List.mem_append.mp retained with first | last
      · rcases List.mem_append.mp first with direct | inside
        · exact List.mem_append_left _ (List.mem_append_left _ direct)
        · exact List.mem_append_left _ (List.mem_append_right _
            (body.subst_keeps_dependency name value dependency different inside))
      · exact List.mem_append_right _ (clauses.subst_keeps_dependency name value dependency different last)
  | resume ticket operand =>
      rcases List.mem_cons.mp retained with direct | inside
      · exact List.mem_cons.mpr (Or.inl direct)
      · exact List.mem_cons_of_mem _ (operand.subst_keeps_dependency name value dependency different inside)
  | resource resource initializer body =>
      rcases List.mem_append.mp retained with hi | hb
      · exact List.mem_append_left _ (initializer.subst_keeps_dependency name value dependency different hi)
      · obtain ⟨inside, distinct⟩ := mem_without.mp hb
        exact List.mem_append_right _ (mem_without.mpr
          ⟨body.subst_keeps_dependency name value dependency different inside, distinct⟩)

theorem Clauses.subst_keeps_dependency (clauses : Clauses) (name : Nat) (value : Expr)
    (dependency : Dependency) (different : dependency ≠ .variable name)
    (retained : dependency ∈ clauses.dependencies) :
    dependency ∈ (clauses.subst name value).dependencies := by
  cases clauses with
  | nil => cases retained
  | cons operation parameter ticket body rest =>
      rcases List.mem_append.mp retained with hb | hr
      · by_cases same : name = parameter
        · simpa only [Clauses.subst, if_pos same, Clauses.dependencies] using
            List.mem_append_left (rest.subst name value).dependencies hb
        · obtain ⟨notParameter, notTicket⟩ := mem_without.mp hb
          obtain ⟨inside, distinct⟩ := mem_without.mp notParameter
          simp only [Clauses.subst, if_neg same, Clauses.dependencies]
          exact List.mem_append_left _ (mem_without.mpr ⟨mem_without.mpr
            ⟨body.subst_keeps_dependency name value dependency different inside, distinct⟩, notTicket⟩)
      · exact List.mem_append_right _ (rest.subst_keeps_dependency name value dependency different hr)
end

theorem closedValue_no_ticket (h : ClosedValue value) :
    Dependency.ticket ticket ∉ value.dependencies := by
  intro present
  exact h.2 _ present

theorem substituted_ticket_iff (expression : Expr) (name : Nat) (h : ClosedValue value) :
    Dependency.ticket ticket ∈ (expression.subst name value).dependencies ↔
      Dependency.ticket ticket ∈ expression.dependencies := by
  constructor
  · intro retained
    rcases List.mem_append.mp (expression.subst_dependencies name value retained) with old | inserted
    · exact old
    · exact False.elim (closedValue_no_ticket h inserted)
  · exact expression.subst_keeps_dependency name value (.ticket ticket) (by simp)

theorem closedValue_no_variable (h : ClosedValue value) :
    Dependency.variable name ∉ value.dependencies := by
  intro present
  exact h.2 _ present

theorem without_preserves_absence {items : List Dependency} (absent : item ∉ items)
    (name : Dependency) : item ∉ without name items :=
  fun h => absent (mem_without.mp h).1

theorem instance_has_no_variable (effectInst : Instance) (name : Nat) :
    Dependency.variable name ∉ instanceDependencies effectInst := by
  intro present
  obtain ⟨resource, inside, equal⟩ := List.mem_map.mp present
  cases equal

theorem not_in_append {item : Dependency} {left right : List Dependency}
    (absent : item ∉ left ∧ item ∉ right) : item ∉ left ++ right := by
  simpa using absent

mutual
theorem Expr.subst_removes_variable (expression : Expr) (name : Nat) (value : Expr)
    (absent : Dependency.variable name ∉ value.dependencies) :
    Dependency.variable name ∉ (expression.subst name value).dependencies := by
  cases expression with
  | unit | boolean _ | integer _ | resourceRef _ | discard _ =>
      simp [Expr.subst, Expr.dependencies]
  | «variable» other =>
      by_cases same : name = other
      · simpa only [Expr.subst, if_pos same] using absent
      · simp [Expr.subst, same, Expr.dependencies]
  | pair left right | app left right | cleanup left right =>
      exact not_in_append ⟨left.subst_removes_variable name value absent,
        right.subst_removes_variable name value absent⟩
  | lambda parameter body =>
      by_cases same : name = parameter
      · simp [Expr.subst, same, Expr.dependencies]
      · simpa only [Expr.subst, if_neg same, Expr.dependencies] using
          without_preserves_absence (body.subst_removes_variable name value absent) (.variable parameter)
  | bind parameter initializer body =>
      have hi := initializer.subst_removes_variable name value absent
      by_cases same : name = parameter
      · simpa [Expr.subst, same, Expr.dependencies] using hi
      · simpa only [Expr.subst, if_neg same, Expr.dependencies] using
          not_in_append ⟨hi,
            without_preserves_absence (body.subst_removes_variable name value absent) (.variable parameter)⟩
  | branch condition yes no =>
      exact not_in_append
        ⟨not_in_append ⟨condition.subst_removes_variable name value absent,
          yes.subst_removes_variable name value absent⟩, no.subst_removes_variable name value absent⟩
  | perform effectInst operation operand =>
      exact not_in_append ⟨instance_has_no_variable effectInst name,
        operand.subst_removes_variable name value absent⟩
  | handle effectInst body clauses =>
      exact not_in_append
        ⟨not_in_append ⟨instance_has_no_variable effectInst name,
          body.subst_removes_variable name value absent⟩, clauses.subst_removes_variable name value absent⟩
  | resume ticket operand =>
      simpa [Expr.subst, Expr.dependencies] using operand.subst_removes_variable name value absent
  | resource resource initializer body =>
      exact not_in_append ⟨initializer.subst_removes_variable name value absent,
        without_preserves_absence (body.subst_removes_variable name value absent) (.resource resource)⟩

theorem Clauses.subst_removes_variable (clauses : Clauses) (name : Nat) (value : Expr)
    (absent : Dependency.variable name ∉ value.dependencies) :
    Dependency.variable name ∉ (clauses.subst name value).dependencies := by
  cases clauses with
  | nil => simp [Clauses.subst, Clauses.dependencies]
  | cons operation parameter ticket body rest =>
      have hr := rest.subst_removes_variable name value absent
      by_cases same : name = parameter
      · simpa [Clauses.subst, same, Clauses.dependencies] using hr
      · simpa only [Clauses.subst, if_neg same, Clauses.dependencies] using
          not_in_append
            ⟨without_preserves_absence
              (without_preserves_absence (body.subst_removes_variable name value absent)
                (.variable parameter)) (.ticket ticket), hr⟩
end

theorem substitution_bound_for_closed_value (expression : Expr) (name : Nat)
    (closed : ClosedValue value) :
    (expression.subst name value).dependencies ⊆
      without (.variable name) expression.dependencies ++ value.dependencies := by
  intro dependency retained
  rcases List.mem_append.mp (expression.subst_dependencies name value retained) with old | inserted
  · have different : dependency ≠ .variable name := by
      intro same
      subst dependency
      exact expression.subst_removes_variable name value (closedValue_no_variable closed) retained
    exact List.mem_append_left _ (mem_without.mpr ⟨old, different⟩)
  · exact List.mem_append_right _ inserted

@[simp] theorem mem_resourceDependencies :
    resource ∈ resourceDependencies items ↔ Dependency.resource resource ∈ items := by
  simp only [resourceDependencies, List.mem_filterMap]
  constructor
  · rintro ⟨item, inside, result⟩
    cases item <;> simp_all
  · intro inside
    exact ⟨.resource resource, inside, rfl⟩

@[simp] theorem mem_ticketDependencies :
    ticket ∈ ticketDependencies items ↔ Dependency.ticket ticket ∈ items := by
  simp only [ticketDependencies, List.mem_filterMap]
  constructor
  · rintro ⟨item, inside, result⟩
    cases item <;> simp_all
  · intro inside
    exact ⟨.ticket ticket, inside, rfl⟩

theorem binding_frame_records_ticket :
    ticket ∈ (bindingFrame parameter suffix input answer).pending ↔
      Dependency.ticket ticket ∈ suffix.dependencies := by
  simp [bindingFrame]

theorem binding_frame_records_resource :
    resource ∈ (bindingFrame parameter suffix input answer).access ↔
      Dependency.resource resource ∈ suffix.dependencies := by
  simp [bindingFrame]

theorem binding_substitution_support (suffix : Expr) (parameter : Nat)
    (closed : ClosedValue value) :
    resourceDependencies (suffix.subst parameter value).dependencies ⊆
      (bindingFrame parameter suffix input answer).access ++ resourceDependencies value.dependencies := by
  intro resource retained
  have bound := substitution_bound_for_closed_value suffix parameter closed
    (mem_resourceDependencies.mp retained)
  rcases List.mem_append.mp bound with old | inserted
  · exact List.mem_append_left _
      (binding_frame_records_resource.mpr (mem_without.mp old).1)
  · exact List.mem_append_right _ (mem_resourceDependencies.mpr inserted)

theorem binding_substitution_pending (suffix : Expr) (parameter : Nat)
    (closed : ClosedValue value) :
    ticket ∈ ticketDependencies (suffix.subst parameter value).dependencies ↔
      ticket ∈ (bindingFrame parameter suffix input answer).pending := by
  simp only [mem_ticketDependencies, binding_frame_records_ticket]
  exact substituted_ticket_iff suffix parameter closed

/-- This judgment describes the actual cut through a syntax-derived bind frame.
    It does not enumerate all reachable cuts of an arbitrary initializer. -/
theorem binding_cut_decomposes
    (cut : SourceCut effectInst (.push (bindingFrame parameter suffix input answer) rest) cap outer) :
    ∃ saved, cap = .push (bindingFrame parameter suffix input answer) saved ∧
      SourceCut effectInst rest saved outer := by
  cases cut with
  | hit f handlerId tail impossible => cases impossible
  | push f rest saved outer miss next => exact ⟨saved, rfl, next⟩

theorem pending_suffix_blocks_discard
    (cut : SourceCut effectInst (.push (bindingFrame parameter suffix input answer) rest) cap outer)
    (retained : Dependency.ticket ticket ∈ suffix.dependencies)
    (outside : ticket ∉ cap.liveTickets) : ¬ Discardable cap surviving plan := by
  intro admitted
  obtain ⟨saved, eq, next⟩ := binding_cut_decomposes cut
  have lost := discard_preserves_outside_consumption admitted outside
  apply lost
  rw [eq]
  exact List.mem_append_left _ (binding_frame_records_ticket.mpr retained)

def cleanupFrame (actionId : Nat) (action : Expr) (bodyType : Ty)
    (residualRequests : List Instance) : Frame :=
  ⟨.armed actionId, bodyType, bodyType, resourceDependencies action.dependencies,
    ticketDependencies action.dependencies, residualRequests⟩

theorem closed_value_has_no_pending_tickets (closed : ClosedValue value) :
    ticketDependencies value.dependencies = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro ticket retained
  exact closedValue_no_ticket closed (mem_ticketDependencies.mp retained)

theorem cleanup_frame_ticket_barrier (closed : ClosedValue action) :
    (cleanupFrame actionId action bodyType residualRequests).pending = [] :=
  closed_value_has_no_pending_tickets closed

theorem binding_substitution_resolves_environment
    (environmentReady : ClosedExcept parameter suffix)
    (closed : ClosedValue value) :
    ∀ name, Dependency.variable name ∉ (suffix.subst parameter value).dependencies := by
  intro name retained
  have bound := substitution_bound_for_closed_value suffix parameter closed retained
  rcases List.mem_append.mp bound with old | inserted
  · obtain ⟨inside, different⟩ := mem_without.mp old
    exact different (congrArg Dependency.variable (environmentReady name inside))
  · exact closedValue_no_variable closed inserted

theorem binding_return_preserves_support_and_environment
    (environmentReady : ClosedExcept parameter suffix)
    (stack : Supported (.push (bindingFrame parameter suffix input answer) outer) ambient)
    (closed : ClosedValue value)
    (valueSupport : resourceDependencies value.dependencies ⊆ outer.visible ++ ambient) :
    (resourceDependencies (suffix.subst parameter value).dependencies ⊆ outer.visible ++ ambient) ∧
    (∀ name, Dependency.variable name ∉ (suffix.subst parameter value).dependencies) := by
  constructor
  · cases stack with
    | push _ _ _ rest suffixSupport =>
        intro resource retained
        rcases List.mem_append.mp (binding_substitution_support suffix parameter closed retained) with
          fromSuffix | fromValue
        · exact suffixSupport fromSuffix
        · exact valueSupport fromValue
  · exact binding_substitution_resolves_environment environmentReady closed

mutual
/-- Freshness prevents a future resource binder from hiding resource access
    inserted at a free value-variable occurrence. -/
theorem Expr.subst_retains_inserted_resource (expression : Expr) (name : Nat) (value : Expr)
    (resource : Nat) (occurs : Dependency.variable name ∈ expression.dependencies)
    (inserted : Dependency.resource resource ∈ value.dependencies)
    (fresh : resource ∉ expression.resourceBinders) :
    Dependency.resource resource ∈ (expression.subst name value).dependencies := by
  cases expression with
  | unit | boolean _ | integer _ | resourceRef _ | discard _ =>
      simp [Expr.dependencies] at occurs
  | «variable» other =>
      have equal : name = other := by simpa [Expr.dependencies] using occurs
      simpa only [Expr.subst, if_pos equal] using inserted
  | pair left right | app left right | cleanup left right =>
      rcases List.mem_append.mp occurs with hl | hr
      · exact List.mem_append_left _ (left.subst_retains_inserted_resource name value resource hl inserted
          (fun bound => fresh (List.mem_append_left _ bound)))
      · exact List.mem_append_right _ (right.subst_retains_inserted_resource name value resource hr inserted
          (fun bound => fresh (List.mem_append_right _ bound)))
  | lambda parameter body =>
      obtain ⟨inside, distinct⟩ := mem_without.mp occurs
      have different : name ≠ parameter := fun eq => distinct (congrArg Dependency.variable eq)
      simp only [Expr.subst, if_neg different, Expr.dependencies]
      exact mem_without.mpr
        ⟨body.subst_retains_inserted_resource name value resource inside inserted fresh, by simp⟩
  | bind parameter initializer body =>
      rcases List.mem_append.mp occurs with hi | hb
      · exact List.mem_append_left _ (initializer.subst_retains_inserted_resource name value resource hi inserted
          (fun bound => fresh (List.mem_append_left _ bound)))
      · obtain ⟨inside, distinct⟩ := mem_without.mp hb
        have different : name ≠ parameter := fun eq => distinct (congrArg Dependency.variable eq)
        simp only [Expr.subst, if_neg different, Expr.dependencies]
        exact List.mem_append_right _ (mem_without.mpr
          ⟨body.subst_retains_inserted_resource name value resource inside inserted
            (fun bound => fresh (List.mem_append_right _ bound)), by simp⟩)
  | branch condition yes no =>
      rcases List.mem_append.mp occurs with first | last
      · rcases List.mem_append.mp first with hc | hy
        · exact List.mem_append_left _ (List.mem_append_left _
            (condition.subst_retains_inserted_resource name value resource hc inserted
              (fun bound => fresh (List.mem_append_left _ (List.mem_append_left _ bound)))))
        · exact List.mem_append_left _ (List.mem_append_right _
            (yes.subst_retains_inserted_resource name value resource hy inserted
              (fun bound => fresh (List.mem_append_left _ (List.mem_append_right _ bound)))))
      · exact List.mem_append_right _ (no.subst_retains_inserted_resource name value resource last inserted
          (fun bound => fresh (List.mem_append_right _ bound)))
  | perform effectInst operation operand =>
      rcases List.mem_append.mp occurs with direct | arg
      · exact False.elim (instance_has_no_variable effectInst name direct)
      · exact List.mem_append_right _ (operand.subst_retains_inserted_resource name value resource arg inserted fresh)
  | handle effectInst body clauses =>
      rcases List.mem_append.mp occurs with first | last
      · rcases List.mem_append.mp first with direct | inside
        · exact False.elim (instance_has_no_variable effectInst name direct)
        · exact List.mem_append_left _ (List.mem_append_right _
            (body.subst_retains_inserted_resource name value resource inside inserted
              (fun bound => fresh (List.mem_append_left _ bound))))
      · exact List.mem_append_right _ (clauses.subst_retains_inserted_resource name value resource last inserted
          (fun bound => fresh (List.mem_append_right _ bound)))
  | resume ticket operand =>
      rcases List.mem_cons.mp occurs with direct | inside
      · cases direct
      · exact List.mem_cons_of_mem _ (operand.subst_retains_inserted_resource name value resource inside inserted fresh)
  | resource identity initializer body =>
      rcases List.mem_append.mp occurs with hi | hb
      · exact List.mem_append_left _ (initializer.subst_retains_inserted_resource name value resource hi inserted
          (fun bound => fresh (List.mem_cons_of_mem _ (List.mem_append_left _ bound))))
      · have different : resource ≠ identity := fun eq => fresh (List.mem_cons.mpr (Or.inl eq))
        exact List.mem_append_right _ (mem_without.mpr
          ⟨body.subst_retains_inserted_resource name value resource (mem_without.mp hb).1 inserted
            (fun bound => fresh (List.mem_cons_of_mem _ (List.mem_append_right _ bound))),
            fun eq => different (Dependency.resource.inj eq)⟩)

theorem Clauses.subst_retains_inserted_resource (clauses : Clauses) (name : Nat) (value : Expr)
    (resource : Nat) (occurs : Dependency.variable name ∈ clauses.dependencies)
    (inserted : Dependency.resource resource ∈ value.dependencies)
    (fresh : resource ∉ clauses.resourceBinders) :
    Dependency.resource resource ∈ (clauses.subst name value).dependencies := by
  cases clauses with
  | nil => cases occurs
  | cons operation parameter ticket body rest =>
      rcases List.mem_append.mp occurs with hb | hr
      · obtain ⟨notParameter, notTicket⟩ := mem_without.mp hb
        obtain ⟨inside, distinct⟩ := mem_without.mp notParameter
        have different : name ≠ parameter := fun eq => distinct (congrArg Dependency.variable eq)
        simp only [Clauses.subst, if_neg different, Clauses.dependencies]
        exact List.mem_append_left _ (mem_without.mpr ⟨mem_without.mpr
          ⟨body.subst_retains_inserted_resource name value resource inside inserted
            (fun bound => fresh (List.mem_append_left _ bound)), by simp⟩, by simp⟩)
      · exact List.mem_append_right _ (rest.subst_retains_inserted_resource name value resource hr inserted
          (fun bound => fresh (List.mem_append_right _ bound)))
end

/-- These are the local expression rules only. Effect dispatch, owned scope
    transitions, and cleanup execution still require the control machine. -/
inductive LocalStep : Expr → Expr → Prop where
  | bind (parameter : Nat) (value suffix : Expr) (closed : ClosedValue value)
      (environmentReady : ClosedExcept parameter suffix) (fresh : ResourceFresh value suffix) :
      LocalStep (.bind parameter value suffix) (suffix.subst parameter value)
  | beta (parameter : Nat) (body value : Expr) (closed : ClosedValue value)
      (closureReady : ClosedValue (.lambda parameter body)) (fresh : ResourceFresh value body) :
      LocalStep (.app (.lambda parameter body) value) (body.subst parameter value)
  | ifTrue (yes no : Expr) : LocalStep (.branch (.boolean true) yes no) yes
  | ifFalse (yes no : Expr) : LocalStep (.branch (.boolean false) yes no) no
  | pairLeft (step : LocalStep left left') (right : Expr) :
      LocalStep (.pair left right) (.pair left' right)
  | pairRight (left : Expr) (closed : ClosedValue left) (step : LocalStep right right') :
      LocalStep (.pair left right) (.pair left right')
  | appFunction (step : LocalStep function function') (argument : Expr) :
      LocalStep (.app function argument) (.app function' argument)
  | appArgument (function : Expr) (closed : ClosedValue function) (step : LocalStep argument argument') :
      LocalStep (.app function argument) (.app function argument')
  | bindInitializer (parameter : Nat) (step : LocalStep initializer initializer') (suffix : Expr) :
      LocalStep (.bind parameter initializer suffix) (.bind parameter initializer' suffix)
  | branchCondition (step : LocalStep condition condition') (yes no : Expr) :
      LocalStep (.branch condition yes no) (.branch condition' yes no)
  | performOperand (effectInst : Instance) (operation : Nat) (step : LocalStep operand operand') :
      LocalStep (.perform effectInst operation operand) (.perform effectInst operation operand')
  | resumeOperand (ticket : Nat) (step : LocalStep operand operand') :
      LocalStep (.resume ticket operand) (.resume ticket operand')
  | handlerBody (effectInst : Instance) (step : LocalStep body body') (clauses : Clauses) :
      LocalStep (.handle effectInst body clauses) (.handle effectInst body' clauses)
  | resourceInitializer (resource : Nat) (step : LocalStep initializer initializer') (body : Expr) :
      LocalStep (.resource resource initializer body) (.resource resource initializer' body)
  | cleanupInitializer (step : LocalStep action action') (body : Expr) :
      LocalStep (.cleanup action body) (.cleanup action' body)

theorem append_dependency_mono {left right left' right' : List Dependency}
    (hl : left ⊆ left') (hr : right ⊆ right') : left ++ right ⊆ left' ++ right' := by
  intro item retained
  rcases List.mem_append.mp retained with hl' | hr'
  · exact List.mem_append_left _ (hl hl')
  · exact List.mem_append_right _ (hr hr')

theorem local_step_dependencies (step : LocalStep before after) :
    after.dependencies ⊆ before.dependencies := by
  induction step with
  | bind parameter value suffix closed environmentReady fresh =>
      intro dependency retained
      have bound := substitution_bound_for_closed_value suffix parameter closed retained
      simpa only [Expr.dependencies, List.mem_append, or_comm] using bound
  | beta parameter body value closed closureReady fresh =>
      exact substitution_bound_for_closed_value body parameter closed
  | ifTrue yes no =>
      intro dependency retained
      exact List.mem_append_left _ (List.mem_append_right _ retained)
  | ifFalse yes no => exact fun _ retained => List.mem_append_right _ retained
  | pairLeft step right ih | appFunction step right ih | cleanupInitializer step right ih =>
      exact append_dependency_mono ih (fun _ h => h)
  | pairRight left closed step ih | appArgument left closed step ih =>
      exact append_dependency_mono (fun _ h => h) ih
  | bindInitializer parameter step suffix ih | resourceInitializer parameter step suffix ih =>
      exact append_dependency_mono ih (fun _ h => h)
  | branchCondition step yes no ih =>
      exact append_dependency_mono (append_dependency_mono ih (fun _ h => h)) (fun _ h => h)
  | performOperand effectInst operation step ih =>
      exact append_dependency_mono (fun _ h => h) ih
  | resumeOperand ticket step ih =>
      intro dependency retained
      rcases List.mem_cons.mp retained with equal | arg
      · exact List.mem_cons.mpr (Or.inl equal)
      · exact List.mem_cons_of_mem _ (ih arg)
  | handlerBody effectInst step clauses ih =>
      exact append_dependency_mono (append_dependency_mono (fun _ h => h) ih) (fun _ h => h)

namespace Examples

/-- A closure can retain resource access without retaining a structural ticket. -/
theorem resource_closure_is_closed : ClosedValue (.lambda 0 (.resourceRef 4)) := by
  simp [ClosedValue, Expr.IsValue, Expr.dependencies, without]

theorem outer_ticket_closure_is_rejected :
    ¬ ClosedValue (.lambda 0 (.resume 9 .unit)) := by
  simp [ClosedValue, Expr.IsValue, Expr.dependencies, without]

/-- This is a free-dependency fact, not a proof of the clause's usage protocol. -/
theorem handler_local_ticket_is_bound :
    ClosedValue (.lambda 0 (.handle (.user 1 []) .unit
      (.cons 0 1 9 (.resume 9 .unit) .nil))) := by
  simp [ClosedValue, Expr.IsValue, Expr.dependencies, Clauses.dependencies,
    instanceDependencies, Instance.resources, without]

theorem nested_effect_argument_retains_resource :
    resourceDependencies (Expr.perform
      (.user 1 [.apply (.nominal 2) (.resource 4)]) 0 .unit).dependencies = [4] := rfl

theorem unresolved_environment_is_rejected :
    ¬ ClosedExcept 0 (.pair (.variable 0) (.variable 1)) := by
  intro ready
  have impossible := ready 1 (by simp [Expr.dependencies])
  omega

/-- An unrestricted raw substitution can hide an inserted resource dependency. -/
theorem raw_substitution_can_capture_resource :
    ((Expr.resource 4 .unit (.variable 0)).subst 0 (.resourceRef 4)).dependencies = [] := rfl

theorem capturing_substitution_is_rejected :
    ¬ ResourceFresh (.resourceRef 4) (.resource 4 .unit (.variable 0)) := by
  intro fresh
  exact fresh 4 (by simp [Expr.dependencies]) (by simp [Expr.resourceBinders])

theorem fresh_substitution_retains_resource :
    Dependency.resource 4 ∈
      ((Expr.resource 5 .unit (.variable 0)).subst 0 (.resourceRef 4)).dependencies := by
  exact Expr.subst_retains_inserted_resource _ _ _ 4
    (by simp [Expr.dependencies, without]) (by simp [Expr.dependencies])
    (by simp [Expr.resourceBinders])

theorem resource_binding_reduces :
    LocalStep (.bind 0 (.resourceRef 4) (.pair (.variable 0) .unit))
      (.pair (.resourceRef 4) .unit) := by
  apply LocalStep.bind
  · simp [ClosedValue, Expr.IsValue, Expr.dependencies]
  · intro name retained
    simpa [Expr.dependencies] using retained
  · simp [ResourceFresh, Expr.dependencies, Expr.resourceBinders]

/-- The free resume in this actual suffix forbids a cut's disposal when its
    ticket is owned outside the capture. Reachability of the cut is separate. -/
theorem resume_suffix_rejects_outside_disposal
    (cut : SourceCut effectInst
      (.push (bindingFrame 0 (.resume 9 (.variable 0)) input answer) rest) cap outer)
    (outside : 9 ∉ cap.liveTickets) : ¬ Discardable cap surviving plan := by
  exact pending_suffix_blocks_discard cut (by simp [Expr.dependencies]) outside

end Examples

end Ash.OneShot.Syntax

#print axioms Ash.OneShot.Syntax.Expr.subst_dependencies
#print axioms Ash.OneShot.Syntax.Clauses.subst_dependencies
#print axioms Ash.OneShot.Syntax.substituted_ticket_iff
#print axioms Ash.OneShot.Syntax.binding_substitution_support
#print axioms Ash.OneShot.Syntax.binding_substitution_pending
#print axioms Ash.OneShot.Syntax.pending_suffix_blocks_discard
#print axioms Ash.OneShot.Syntax.cleanup_frame_ticket_barrier
#print axioms Ash.OneShot.Syntax.binding_return_preserves_support_and_environment
#print axioms Ash.OneShot.Syntax.local_step_dependencies
#print axioms Ash.OneShot.Syntax.Expr.subst_retains_inserted_resource
