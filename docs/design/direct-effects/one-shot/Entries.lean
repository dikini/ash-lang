import Retained

/-!
Type-directed construction of administrative entries and preservation for
ordinary computation and builtin cell operations. The judgments check value
types; the common effect/usage/source admission invariant remains separate.
-/

namespace Ash.OneShot.Typing
open Syntax Execution

def TicketType.binders : TicketType → List Nat
  | .none => []
  | .bound binder _ _ _ _ => [binder]

theorem instance_has_no_ticket (effectInst : Instance) :
    Dependency.ticket binder ∉ instanceDependencies effectInst := by
  simp [instanceDependencies]

mutual
theorem typed_tickets_scoped
    (typed : Typed signature environment ticket allowed expression type)
    (used : Dependency.ticket binder ∈ expression.dependencies) : binder ∈ ticket.binders := by
  cases typed with
  | unit | boolean | integer | «variable» | reference => simp_all [Expr.dependencies]
  | pair left right | app left right effects | cleanup left right effects =>
      rcases List.mem_append.mp used with used | used
      · exact typed_tickets_scoped left used
      · exact typed_tickets_scoped right used
  | lambda body retained =>
      have impossible := typed_tickets_scoped body (mem_without.mp used).1
      cases impossible
  | bind initializer suffix =>
      rcases List.mem_append.mp used with used | used
      · exact typed_tickets_scoped initializer used
      · exact typed_tickets_scoped suffix (mem_without.mp used).1
  | branch condition yes no =>
      rcases List.mem_append.mp used with used | used
      · rcases List.mem_append.mp used with used | used
        · exact typed_tickets_scoped condition used
        · exact typed_tickets_scoped yes used
      · exact typed_tickets_scoped no used
  | perform operation available operand =>
      rcases List.mem_append.mp used with used | used
      · exact False.elim (instance_has_no_ticket _ used)
      · exact typed_tickets_scoped operand used
  | handle body clauses coverage unique effects =>
      rcases List.mem_append.mp used with used | used
      · rcases List.mem_append.mp used with used | used
        · exact False.elim (instance_has_no_ticket _ used)
        · exact typed_tickets_scoped body used
      · exact False.elim (typed_clauses_ticket_closed clauses used)
  | resume operand effects =>
      rcases List.mem_cons.mp used with same | used
      · cases same
        simp [TicketType.binders]
      · exact typed_tickets_scoped operand used
  | discard effects => simpa [Expr.dependencies, TicketType.binders] using used
  | resource initializer body noEscape noEffectEscape effects =>
      rcases List.mem_append.mp used with used | used
      · exact typed_tickets_scoped initializer used
      · exact typed_tickets_scoped body (mem_without.mp used).1
termination_by sizeOf expression

theorem typed_clauses_ticket_closed
    (typed : ClausesTyped signature environment effectInst answer residual clauses)
    (used : Dependency.ticket binder ∈ clauses.dependencies) : False := by
  cases typed with
  | nil => cases used
  | cons operation body rest =>
      rcases List.mem_append.mp used with used | used
      · obtain ⟨withoutParameter, different⟩ := mem_without.mp used
        have within := typed_tickets_scoped body (mem_without.mp withoutParameter).1
        simp only [TicketType.binders, List.mem_singleton] at within
        exact different (congrArg Dependency.ticket within)
      · exact typed_clauses_ticket_closed rest used
termination_by sizeOf clauses
end

theorem typed_clauses_have_barrier
    (typed : ClausesTyped signature environment effectInst answer residual clauses) :
    ticketDependencies clauses.dependencies = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro binder used
  exact typed_clauses_ticket_closed typed (mem_ticketDependencies.mp used)

theorem instance_has_no_variable (effectInst : Instance) :
    Dependency.variable name ∉ instanceDependencies effectInst := by
  simp [instanceDependencies]

theorem bound_outside_parameter {environment : TypeEnv}
    (found : (environment.extend parameter input) name = some type)
    (different : Dependency.variable name ≠ .variable parameter) : environment name = some type := by
  simpa [TypeEnv.extend, show name ≠ parameter from fun same => different (congrArg Dependency.variable same)] using found

mutual
theorem typed_variables_bound
    (typed : Typed signature environment ticket allowed expression type)
    (used : Dependency.variable name ∈ expression.dependencies) : ∃ input, environment name = some input := by
  cases typed with
  | unit | boolean | integer | reference => simp_all [Expr.dependencies]
  | «variable» found =>
      simp only [Expr.dependencies, List.mem_singleton, Dependency.variable.injEq] at used
      subst name
      exact ⟨_, found⟩
  | pair left right | app left right effects | cleanup left right effects =>
      rcases List.mem_append.mp used with used | used
      · exact typed_variables_bound left used
      · exact typed_variables_bound right used
  | lambda body retained =>
      obtain ⟨used, different⟩ := mem_without.mp used
      obtain ⟨input, found⟩ := typed_variables_bound body used
      exact ⟨input, bound_outside_parameter found different⟩
  | bind initializer suffix =>
      rcases List.mem_append.mp used with used | used
      · exact typed_variables_bound initializer used
      · obtain ⟨used, different⟩ := mem_without.mp used
        obtain ⟨input, found⟩ := typed_variables_bound suffix used
        exact ⟨input, bound_outside_parameter found different⟩
  | branch condition yes no =>
      rcases List.mem_append.mp used with used | used
      · rcases List.mem_append.mp used with used | used
        · exact typed_variables_bound condition used
        · exact typed_variables_bound yes used
      · exact typed_variables_bound no used
  | perform operation available operand =>
      rcases List.mem_append.mp used with used | used
      · exact False.elim (instance_has_no_variable _ used)
      · exact typed_variables_bound operand used
  | handle body clauses coverage unique effects =>
      rcases List.mem_append.mp used with used | used
      · rcases List.mem_append.mp used with used | used
        · exact False.elim (instance_has_no_variable _ used)
        · exact typed_variables_bound body used
      · exact typed_clauses_variables_bound clauses used
  | resume operand effects =>
      rcases List.mem_cons.mp used with impossible | used
      · cases impossible
      · exact typed_variables_bound operand used
  | discard effects => simp [Expr.dependencies] at used
  | resource initializer body noEscape noEffectEscape effects =>
      rcases List.mem_append.mp used with used | used
      · exact typed_variables_bound initializer used
      · exact typed_variables_bound body (mem_without.mp used).1
termination_by sizeOf expression

theorem typed_clauses_variables_bound
    (typed : ClausesTyped signature environment effectInst answer residual clauses)
    (used : Dependency.variable name ∈ clauses.dependencies) : ∃ input, environment name = some input := by
  cases typed with
  | nil => cases used
  | cons operation body rest =>
      rcases List.mem_append.mp used with used | used
      · obtain ⟨used, different⟩ := mem_without.mp (mem_without.mp used).1
        obtain ⟨input, found⟩ := typed_variables_bound body used
        exact ⟨input, bound_outside_parameter found different⟩
      · exact typed_clauses_variables_bound rest used
termination_by sizeOf clauses
end

/-- A value in an empty lexical environment is closed in both ordinary and
    ticket namespaces. Resource references can remain; their availability is
    checked separately. -/
theorem typed_value_is_closed
    (typed : Typed signature TypeEnv.empty ticket allowed value type) (isValue : value.IsValue) :
    ClosedValue value := by
  refine ⟨isValue, ?_⟩
  intro dependency retained
  cases dependency with
  | resource identity => trivial
  | «variable» name =>
      obtain ⟨input, found⟩ := typed_variables_bound typed retained
      cases found
  | ticket binder =>
      have noneTyped := typed_value_transport typed isValue .none []
      exact List.not_mem_nil (typed_tickets_scoped noneTyped retained)

theorem typed_body_is_closed_except
    (typed : Typed signature (TypeEnv.empty.extend parameter input) ticket allowed body type) :
    ClosedExcept parameter body := by
  intro name used
  obtain ⟨type, found⟩ := typed_variables_bound typed used
  by_cases same : name = parameter
  · exact same
  · simp [TypeEnv.extend, TypeEnv.empty, same] at found

theorem scope_translates_scoped_dependencies
    (scope : ScopeTyped tickets runtimeScope ticket)
    (within : ∀ binder, Dependency.ticket binder ∈ dependencies → binder ∈ ticket.binders) :
    ∃ pending, runtimeScope.translate dependencies = some pending := by
  induction dependencies with
  | nil => exact ⟨[], rfl⟩
  | cons dependency rest ih =>
      obtain ⟨pending, translated⟩ := ih (fun binder used => within binder (List.mem_cons_of_mem _ used))
      cases dependency with
      | «variable» name | resource name => exact ⟨pending, translated⟩
      | ticket binder =>
          have known := within binder (by simp)
          cases scope with
          | none => cases known
          | bound found =>
              simp only [TicketType.binders, List.mem_singleton] at known
              subst binder
              exact ⟨_ :: pending, by simp [Scope.translate, Scope.resolve, translated]; rfl⟩

theorem focus_constructs_typed_configuration
    (typed : ConfigurationTyped signature tickets ⟨whole, scope, tail⟩ result)
    (focus : Focus whole child context) :
    ∃ plain : PlainData,
      plain.context = context ∧ plain.scope = scope ∧
      RawStep ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ [] [] ∧
      ConfigurationTyped signature tickets ⟨child, scope, .push (.plain plain) tail⟩ result := by
  obtain ⟨output, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped wholeTyped =>
      obtain ⟨input, childTyped, contextTyped⟩ := typed_focus_decomposition focus wholeTyped
      have contextBound : context.dependencies ⊆ whole.dependencies := by
        cases focus <;> simp_all [Context.dependencies, Context.plug, Expr.dependencies, List.subset_def]
      obtain ⟨pending, translated⟩ := scope_translates_scoped_dependencies scopeTyped
        (fun binder used => typed_tickets_scoped wholeTyped (contextBound used))
      let plain : PlainData := ⟨context, scope, input, output, pending, translated⟩
      exact ⟨plain, rfl, rfl, .focus plain focus tail,
        input, .checked scopeTyped childTyped, .push (.plain scopeTyped contextTyped) stack⟩

theorem handler_entry_constructs_typed_configuration
    (typed : ConfigurationTyped signature tickets ⟨.handle effectInst body clauses, scope, tail⟩ result)
    (activation : Nat) :
    ∃ handler : HandlerData,
      handler.activation = activation ∧
      RawStep ⟨.handle effectInst body clauses, scope, tail⟩
        ⟨body, scope, .push (.handler handler) tail⟩ [] [] ∧
      ConfigurationTyped signature tickets ⟨body, scope, .push (.handler handler) tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | handle bodyTyped clausesTyped coverage unique effects =>
          let handler : HandlerData := ⟨activation, effectInst, clauses, scope, answer,
            typed_clauses_have_barrier clausesTyped⟩
          exact ⟨handler, rfl, .enterHandler handler body tail,
            answer, .checked scopeTyped bodyTyped,
            .push (.handler ⟨_, scopeTyped⟩ clausesTyped coverage unique) stack⟩

theorem cell_entry_constructs_typed_configuration
    (typed : ConfigurationTyped signature tickets ⟨.resource identity (.integer payload) body, scope, tail⟩ result) :
    ∃ answer : Ty,
      RawStep ⟨.resource identity (.integer payload) body, scope, tail⟩
        ⟨body, scope, .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
      ConfigurationTyped signature tickets ⟨body, scope, .push (.cell identity payload scope answer) tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | resource initializer bodyTyped noEscape noEffectEscape effects =>
          exact ⟨answer, .enterCell identity payload body scope answer tail,
            answer, .checked scopeTyped bodyTyped, .push (.cell ⟨_, scopeTyped⟩ noEscape) stack⟩

theorem cleanup_entry_constructs_typed_configuration
    (typed : ConfigurationTyped signature tickets ⟨.cleanup callback body, scope, tail⟩ result)
    (isValue : callback.IsValue) (identity : Nat) :
    ∃ action : ActionData,
      RawStep ⟨.cleanup callback body, scope, tail⟩
        ⟨body, scope, .push (.armed action) tail⟩ [.cleanup identity] [] ∧
      ConfigurationTyped signature tickets ⟨body, scope, .push (.armed action) tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | @cleanup _ _ _ _ latent retained _ _ callbackTyped bodyTyped effects =>
          have closed := typed_value_is_closed callbackTyped isValue
          let action : ActionData := ⟨identity, callback, closed, scope, answer, latent⟩
          exact ⟨action, .enterCleanup action body tail,
            answer, .checked scopeTyped bodyTyped,
            .push (.armed ⟨_, scopeTyped⟩ (typed_value_transport callbackTyped closed.1 .none [])) stack⟩

theorem bind_preserves_configuration_typing
    (typed : ConfigurationTyped signature tickets ⟨.bind parameter value body, scope, tail⟩ result)
    (closed : ClosedValue value) :
    ConfigurationTyped signature tickets ⟨body.subst parameter value, scope, tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | bind initializer suffix =>
          exact ⟨answer, .checked scopeTyped
            (typed_substitution suffix (typed_value_transport initializer closed.1 .none []) closed), stack⟩

theorem beta_preserves_configuration_typing
    (typed : ConfigurationTyped signature tickets ⟨.app (.lambda parameter body) value, scope, tail⟩ result)
    (closed : ClosedValue value) :
    ConfigurationTyped signature tickets ⟨body.subst parameter value, .none, tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | app function argument effects => cases function with
          | lambda bodyTyped retained =>
              exact ⟨answer, .checked .none
                (typed_substitution bodyTyped (typed_value_transport argument closed.1 .none []) closed), stack⟩

theorem branch_preserves_configuration_typing
    (typed : ConfigurationTyped signature tickets ⟨.branch (.boolean condition) yes no, scope, tail⟩ result) :
    ConfigurationTyped signature tickets ⟨if condition then yes else no, scope, tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | branch test yesTyped noTyped =>
          cases condition
          · exact ⟨answer, .checked scopeTyped noTyped, stack⟩
          · exact ⟨answer, .checked scopeTyped yesTyped, stack⟩

theorem bind_constructs_typed_step
    (typed : ConfigurationTyped signature tickets ⟨.bind parameter value body, scope, tail⟩ result)
    (isValue : value.IsValue) (fresh : ResourceFresh value body) :
    RawStep ⟨.bind parameter value body, scope, tail⟩ ⟨body.subst parameter value, scope, tail⟩ [] [] ∧
      ConfigurationTyped signature tickets ⟨body.subst parameter value, scope, tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | bind initializer suffix =>
          have closed := typed_value_is_closed initializer isValue
          exact ⟨.bind parameter value body scope tail closed (typed_body_is_closed_except suffix) fresh,
            answer, .checked scopeTyped
              (typed_substitution suffix (typed_value_transport initializer isValue .none []) closed), stack⟩

theorem beta_constructs_typed_step
    (typed : ConfigurationTyped signature tickets ⟨.app (.lambda parameter body) value, scope, tail⟩ result)
    (isValue : value.IsValue) (fresh : ResourceFresh value body) :
    RawStep ⟨.app (.lambda parameter body) value, scope, tail⟩
      ⟨body.subst parameter value, .none, tail⟩ [] [] ∧
      ConfigurationTyped signature tickets ⟨body.subst parameter value, .none, tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | app function argument effects =>
          have argumentClosed := typed_value_is_closed argument isValue
          have functionClosed := typed_value_is_closed function trivial
          cases function with
          | lambda bodyTyped retained =>
              exact ⟨.beta parameter body value scope tail argumentClosed functionClosed fresh,
                answer, .checked .none
                  (typed_substitution bodyTyped (typed_value_transport argument isValue .none []) argumentClosed), stack⟩

/-- Actual source and retained-handler typing supply the lexical premises of
    capture. Resource-name freshness and outward support are separate checks. -/
theorem typed_capture_lexical_admission
    (typed : ConfigurationTyped signature tickets ⟨.perform requested operation operand, scope, whole⟩ result)
    (cut : HandlerCut requested whole cap tail handler) (isValue : operand.IsValue) :
    ClosedValue operand ∧
      ∀ parameter binder body, ClauseAt operation handler.clauses parameter binder body → ClosedExcept parameter body := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | perform operationType available operandTyped =>
          refine ⟨typed_value_is_closed operandTyped isValue, ?_⟩
          intro parameter binder body selected
          obtain ⟨saved, outside, handlerTyped⟩ := handler_cut_retains_typing cut stack
          cases handlerTyped with
          | handler caller clauses coverage unique =>
              obtain ⟨input, output, operation, bodyTyped⟩ := selected_clause_typed selected clauses
              exact typed_body_is_closed_except bodyTyped

/-- Updating a selected integer cell preserves the types of all active and
    dormant code. Selection already accounts for nearer source overrides. -/
theorem cell_update_preserves_stack_typing
    (update : CellUpdate identity old new before after)
    (typed : StackTyped signature tickets before input result) :
    StackTyped signature tickets after input result := by
  induction update generalizing input result with
  | hit => cases typed with
      | push frame rest => cases frame with
          | cell caller noEscape => exact .push (.cell caller noEscape) rest
  | push miss next ih => cases typed with
      | push frame rest => exact .push frame (ih rest)
  | live next ih => cases typed with
      | live known caller saved rest => exact .live known caller saved (ih rest)
  | spent next ih => cases typed with
      | spent known caller rest => exact .spent known caller (ih rest)

theorem cell_read_preserves_configuration_typing
    (typed : ConfigurationTyped (withCellSignatures users) tickets
      ⟨.perform (.cell identity) 0 (.resourceRef identity), scope, before⟩ result)
    (selected : CellUpdate identity payload payload before after) :
    ConfigurationTyped (withCellSignatures users) tickets ⟨.integer payload, scope, after⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | perform operation available operand =>
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
          obtain ⟨rfl, rfl⟩ := operation
          exact ⟨.integer, .checked scopeTyped (Typed.integer (allowed := [])),
            cell_update_preserves_stack_typing selected stack⟩

theorem cell_write_preserves_configuration_typing
    (typed : ConfigurationTyped (withCellSignatures users) tickets
      ⟨.perform (.cell identity) 1 (.pair (.resourceRef identity) (.integer new)), scope, before⟩ result)
    (selected : CellUpdate identity old new before after) :
    ConfigurationTyped (withCellSignatures users) tickets ⟨.unit, scope, after⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | perform operation available operand =>
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
          obtain ⟨rfl, rfl⟩ := operation
          exact ⟨.unit, .checked scopeTyped (Typed.unit (allowed := [])),
            cell_update_preserves_stack_typing selected stack⟩

namespace EntryExamples
open Ash.OneShot.Execution.Examples

/-- Focus through a live clause retains the actual outer owner's pending use;
    runtime translation is derived, rather than assumed by the example. -/
theorem focus_retains_pending_owner :
    ∃ plain : PlainData,
      plain.pending = [3] ∧
      RawStep
        ⟨.bind 0 (.perform (.user 1 []) 0 .unit) (.resume 9 .unit), .ticket 9 3,
          .live 3 .unit .integer captureStack .none .nil⟩
        ⟨.perform (.user 1 []) 0 .unit, .ticket 9 3,
          .push (.plain plain) (.live 3 .unit .integer captureStack .none .nil)⟩ [] [] ∧
      ConfigurationTyped Examples.unitRequestSignature RetainedExamples.withCapturedTicket
        ⟨.perform (.user 1 []) 0 .unit, .ticket 9 3,
          .push (.plain plain) (.live 3 .unit .integer captureStack .none .nil)⟩ .integer := by
  have known : RetainedExamples.withCapturedTicket 3 = some (.unit, .integer) := rfl
  have typed : ConfigurationTyped Examples.unitRequestSignature RetainedExamples.withCapturedTicket
      ⟨.bind 0 (.perform (.user 1 []) 0 .unit) (.resume 9 .unit), .ticket 9 3,
        .live 3 .unit .integer captureStack .none .nil⟩ .integer := by
    refine ⟨.integer, .checked (allowed := [.user 1 []]) (.bound (residual := []) (closing := []) known) ?_,
      .live known ⟨_, .none⟩ RetainedExamples.running_capture_has_typed_code .nil⟩
    apply Typed.bind (input := .unit) (allowed := [.user 1 []])
    · exact .perform rfl (by simp) .unit
    · exact .resume .unit (by simp)
  obtain ⟨plain, context, scope, step, after⟩ := focus_constructs_typed_configuration typed
    (Focus.bind (by simp [Expr.IsValue]))
  have pending := plain.translated
  rw [context, scope] at pending
  simp [Context.dependencies, Context.plug, Expr.dependencies, without, Scope.translate, Scope.resolve] at pending
  exact ⟨plain, pending.symm, step, after⟩

theorem wrong_ticket_is_not_typed :
    ¬ Typed Examples.unitRequestSignature TypeEnv.empty (.bound 9 .unit .integer [] []) []
      (.resume 10 .unit) .integer := by
  intro typed
  have bound := typed_tickets_scoped typed (binder := 10) (by simp [Expr.dependencies])
  simp [TicketType.binders] at bound

def wrongHandler : HandlerData := ⟨8, .user 1 [], .nil, .none, .boolean, rfl⟩
def noOperations : Signature := fun _ _ => none

/-- A raw entry can carry the wrong answer annotation despite a typed source.
    The type-directed entry construction eliminates this freedom. -/
theorem raw_handler_annotations_need_checking :
    ConfigurationTyped noOperations RetainedExamples.noTickets
      ⟨.handle (.user 1 []) (.integer 42) .nil, .none, .nil⟩ .integer ∧
    RawStep ⟨.handle (.user 1 []) (.integer 42) .nil, .none, .nil⟩
      ⟨.integer 42, .none, .push (.handler wrongHandler) .nil⟩ [] [] ∧
    ¬ ConfigurationTyped noOperations RetainedExamples.noTickets
      ⟨.integer 42, .none, .push (.handler wrongHandler) .nil⟩ .integer := by
  refine ⟨?_, .enterHandler wrongHandler (.integer 42) .nil, ?_⟩
  · exact ⟨.integer, .checked .none (.handle (residual := []) (allowed := []) .integer .nil
      (by intro operation input output found; cases found) (by simp [clauseKeys]) (by simp)), .nil⟩
  · rintro ⟨input, expression, stack⟩
    cases stack with
    | push frame rest => cases rest

def wrongCellSignature : Signature
  | .cell 4, 0 => some (.reference 4, .boolean)
  | _, _ => none

/-- Arbitrary declarations cannot redefine a builtin result while retaining
    the machine's integer read rule. -/
theorem builtin_signature_must_match_execution :
    let stack := Stack.push (.cell 4 17 .none .boolean) .nil
    ConfigurationTyped wrongCellSignature RetainedExamples.noTickets
      ⟨.perform (.cell 4) 0 (.resourceRef 4), .none, stack⟩ .boolean ∧
    RawStep ⟨.perform (.cell 4) 0 (.resourceRef 4), .none, stack⟩
      ⟨.integer 17, .none, stack⟩ [] [] ∧
    ¬ ConfigurationTyped wrongCellSignature RetainedExamples.noTickets
      ⟨.integer 17, .none, stack⟩ .boolean := by
  let cell := Stack.push (.cell 4 17 .none .boolean) .nil
  refine ⟨?_, .readCell 4 17 .none cell cell .hit, ?_⟩
  · exact ⟨.boolean, .checked .none (.perform (allowed := [.cell 4]) rfl (by simp) .reference),
      .push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) .nil⟩
  · rintro ⟨input, expression, stack⟩
    cases expression with
    | checked scope typed => cases typed with
        | integer => cases stack

theorem builtin_write_retains_typed_cell :
    ConfigurationTyped (withCellSignatures noOperations) RetainedExamples.noTickets
      ⟨.unit, .none, .push (.cell 4 23 .none .unit) .nil⟩ .unit := by
  apply cell_write_preserves_configuration_typing (identity := 4) (old := 17) (new := 23)
    (before := .push (.cell 4 17 .none .unit) .nil)
  · exact ⟨.unit, .checked .none (.perform (allowed := [.cell 4]) rfl (by simp)
      (.pair .reference .integer)), .push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) .nil⟩
  · exact .hit

end EntryExamples

end Ash.OneShot.Typing

#print axioms Ash.OneShot.Typing.typed_tickets_scoped
#print axioms Ash.OneShot.Typing.focus_constructs_typed_configuration
#print axioms Ash.OneShot.Typing.handler_entry_constructs_typed_configuration
#print axioms Ash.OneShot.Typing.cleanup_entry_constructs_typed_configuration
#print axioms Ash.OneShot.Typing.beta_preserves_configuration_typing
#print axioms Ash.OneShot.Typing.cell_update_preserves_stack_typing
#print axioms Ash.OneShot.Typing.cell_read_preserves_configuration_typing
#print axioms Ash.OneShot.Typing.cell_write_preserves_configuration_typing
#print axioms Ash.OneShot.Typing.EntryExamples.focus_retains_pending_owner
#print axioms Ash.OneShot.Typing.EntryExamples.builtin_write_retains_typed_cell
#print axioms Ash.OneShot.Typing.typed_value_is_closed
#print axioms Ash.OneShot.Typing.bind_constructs_typed_step
#print axioms Ash.OneShot.Typing.beta_constructs_typed_step
#print axioms Ash.OneShot.Typing.typed_capture_lexical_admission
