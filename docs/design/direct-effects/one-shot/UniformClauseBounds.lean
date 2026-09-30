import EffectBounds

/-!
Shared clause contracts across capture occurrences. Structural induction proves
coverage transport through the same ordered interpretation context and clause
schema. A table evaluated at upper bounds certifies every covered occurrence;
it need not be specialized again to that occurrence's exact rows.
-/

namespace Ash.OneShot.UniformClauseBounds
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open EffectBounds (Covers)
open ParametricClauseRows

theorem merge_parts (merged : merge first second = some row) :
    ∃ a b, first = some a ∧ second = some b ∧ row = a ++ b := by
  cases first <;> cases second <;> simp [merge] at merged
  case some.some a b => exact ⟨a, b, rfl, rfl, merged.symm⟩

theorem layer_member (evaluated : throughLayer layer bound = some output)
    (member : request ∈ bound) :
    ∃ actual, demandThrough layer request = some actual ∧ Covers output actual := by
  induction bound generalizing output with
  | nil => cases member
  | cons first rest ih =>
      obtain ⟨a, b, head, tail, same⟩ := merge_parts evaluated
      rcases List.mem_cons.mp member with equal | next
      · cases equal
        exact ⟨a, head, by rw [same]; exact List.subset_append_left _ _⟩
      · obtain ⟨actual, found, covered⟩ := ih tail next
        refine ⟨actual, found, ?_⟩
        intro demand present
        rw [same]
        exact List.mem_append_right _ (covered present)

theorem layer_coverage (covered : Covers bound actual)
    (evaluated : throughLayer layer bound = some output) :
    ∃ result, throughLayer layer actual = some result ∧ Covers output result := by
  induction actual with
  | nil => exact ⟨[], rfl, by simp [Covers]⟩
  | cons request rest ih =>
      obtain ⟨a, head, first⟩ := layer_member (request := request) evaluated (covered List.mem_cons_self)
      obtain ⟨b, tail, second⟩ := ih (fun _ present => covered (List.mem_cons_of_mem _ present))
      exact ⟨a ++ b, by simp only [throughLayer, head, tail, merge], EffectBounds.covers_append first second⟩

/-- The context is fixed: barriers, exact targets and first-match clause tables
    occur at the same positions on both sides. -/
theorem residual_coverage (covered : Covers bound actual)
    (evaluated : residualize context bound = some output) :
    ∃ result, residualize context actual = some result ∧ Covers output result := by
  induction context generalizing bound actual output with
  | nil => cases Option.some.inj evaluated; exact ⟨actual, rfl, covered⟩
  | cons layer rest ih =>
      cases next : throughLayer layer bound with
      | none => simp [residualize, next] at evaluated
      | some middle =>
          obtain ⟨actualMiddle, first, included⟩ := layer_coverage covered next
          obtain ⟨result, tail, final⟩ := ih included (by simpa only [residualize, next] using evaluated)
          exact ⟨result, by simpa only [residualize, first] using tail, final⟩

/-- A successful upper evaluation must have a successful covered lower result.
    A failed upper evaluation offers no admission guarantee. -/
def SuccessBelow (actual bound : Option Footprint) : Prop :=
  ∀ upper, bound = some upper → ∃ lower, actual = some lower ∧ Covers upper lower

theorem success_refl (result : Option Footprint) : SuccessBelow result result := by
  intro upper same
  exact ⟨upper, same, EffectBounds.covers_refl upper⟩

theorem success_some (covered : Covers bound actual) : SuccessBelow (some actual) (some bound) := by
  intro upper same
  cases Option.some.inj same
  exact ⟨actual, rfl, covered⟩

theorem success_none (actual : Option Footprint) : SuccessBelow actual none := by
  intro upper same
  cases same

theorem merge_coverage (left : SuccessBelow actualA boundA) (right : SuccessBelow actualB boundB) :
    SuccessBelow (merge actualA actualB) (merge boundA boundB) := by
  intro upper evaluated
  obtain ⟨a, b, first, second, same⟩ := merge_parts evaluated
  obtain ⟨actualFirst, foundFirst, coveredFirst⟩ := left _ first
  obtain ⟨actualSecond, foundSecond, coveredSecond⟩ := right _ second
  refine ⟨actualFirst ++ actualSecond, by simp only [foundFirst, foundSecond, merge], ?_⟩
  rw [same]
  exact EffectBounds.covers_append_bounds coveredFirst coveredSecond

theorem eval_coverage (resume : Covers resumeBound resumeRow) (closing : SuccessBelow closeRow closeBound)
    (expression : RowExpr) : SuccessBelow (expression.eval resumeRow closeRow) (expression.eval resumeBound closeBound) := by
  induction expression with
  | literal row => exact success_refl (some row)
  | resume => exact success_some resume
  | disposal => exact closing
  | append first second ihFirst ihSecond => exact merge_coverage ihFirst ihSecond
  | through context expression ih =>
      intro upper evaluated
      cases boundResult : expression.eval resumeBound closeBound with
      | none => simp [RowExpr.eval, boundResult] at evaluated
      | some raw =>
          obtain ⟨actualRaw, actualResult, included⟩ := ih _ boundResult
          obtain ⟨output, found, covered⟩ := residual_coverage included (by simpa only [RowExpr.eval, boundResult] using evaluated)
          exact ⟨output, by simpa only [RowExpr.eval, actualResult] using found, covered⟩

/-- Instantiation retains exact source evidence and the existing phase judgment.
    Only the connection to the shared effect contract uses coverage. -/
theorem instantiate_bounded
    (schema : Schema operations policy header inside environment before code after contract expression)
    (resume : Covers resumeBound resumeRow) (closing : SuccessBelow closeRow closeBound)
    (evaluated : expression.eval resumeBound closeBound = some bound) :
    ∃ actual, ClauseProtection.Derives operations policy (header.ticket resumeRow closeRow) inside environment
      before code after contract actual ∧ Covers bound actual := by
  obtain ⟨actual, found, covered⟩ := eval_coverage resume closing expression _ evaluated
  exact ⟨actual, instantiate schema found, covered⟩

theorem uniform_offer
    (offer : Offer operations policy environment parameter binder argument input answer body held expression)
    (resume : Covers resumeBound resumeRow) (closing : SuccessBelow closeRow closeBound) :
    EffectBounds.Offer operations policy (CaptureInterfaces.localRows resumeRow closeRow) environment operation parameter binder
      argument input answer body held (evalOffer resumeBound closeBound expression) := by
  cases offer with
  | unavailable => exact .unavailable
  | offered supported schema =>
      rename_i expression
      cases evaluated : expression.eval resumeBound closeBound with
      | none => simp only [evalOffer, evaluated]; exact .unavailable
      | some bound =>
          obtain ⟨actual, source, covered⟩ := instantiate_bounded schema resume closing evaluated
          simp only [evalOffer, evaluated]
          exact .offered supported source covered

/-- The advertised table is evaluated once at shared bounds. Its certificate
    applies to all covered row inputs, without replacing that table. -/
theorem uniform_clauses
    (schemas : ClausesSchema operations policy environment requested answer clauses schemaTable)
    (resume : Covers resumeBound resumeRow) (closing : SuccessBelow closeRow closeBound) :
    EffectBounds.Certified operations policy (CaptureInterfaces.localRows resumeRow closeRow) environment requested answer clauses
      (specializeTable schemaTable resumeBound closeBound) := by
  induction schemas with
  | nil => exact .nil
  | cons known ordinary protectedMode rest ih =>
      exact .cons known (uniform_offer ordinary resume closing) (uniform_offer protectedMode resume closing) ih

theorem uniform_at_interface {handler : HandlerData} {tables : CallableProtectionFrames.Tables}
    (schemas : ClausesSchema operations policy environment requested answer handler.clauses schemaTable)
    (same : tables handler = specializeTable schemaTable resumeBound closeBound)
    (resume : Covers resumeBound resumeRow) (closing : SuccessBelow closeRow closeBound) :
    EffectBounds.Certified operations policy (CaptureInterfaces.localRows resumeRow closeRow) environment requested answer
      handler.clauses (tables handler) := by
  rw [same]
  exact uniform_clauses schemas resume closing

theorem capture_preserves
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing runtimeBound)
    (interface : CaptureInterfaces.Interface operations tables capture resumeRow closeRow)
    (schemas : ClausesSchema operations policy clauseEnvironment requested answer handler.clauses schemaTable)
    (same : tables handler = specializeTable schemaTable resumeBound closeBound)
    (resume : Covers resumeBound resumeRow) (closing : SuccessBelow closeRow closeBound)
    (cut : HandlerCut requested whole capture tail handler)
    (checked : CallableProtectionFrames.Checked operations tables operandEnvironment whole
      (.perform (Instantiation.freezeEffect requested) operation operand) output)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (parameter binder : Nat) (body : Code) (port : ScopedPorts.Port) (record : CallableJoint.TicketRecord)
      (input : Contract) (row : Footprint),
      ClauseAt operation handler.clauses parameter binder body ∧
      (∃ argument, DeclarationResults.signature declarations requested operation = some (argument, port)) ∧
      (∃ argument, operations requested operation = some (argument, input)) ∧
      CallableJoint.RegistryExtends registry (registry.insert owner record) ∧
      let newTicket := CaptureInterfaces.ticketFor capture resumeRow closeRow binder input answer
      let before : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let base := Stack.live owner (ScopedPorts.embedPort port) handler.answer capture handler.scope tail
      let next := ScopedPortJoint.advanceState before ⟨body.subst parameter operand, .ticket binder owner, base⟩
        [.ticket owner] []
      NamedAccessStep ambient before next ∧
      CompletionJoint.Valid declarations policy (registry.insert owner record) ambient next result outgoing runtimeBound ∧
      PhaseBoundaries.Boundary newTicket owner .available base tail handler.answer ∧
      ClauseProtection.Derives operations policy newTicket [] clauseEnvironment .available (body.subst parameter operand) .consumed answer row ∧
      checkFootprint (CallableProtectionFrames.contextOf tables tail) row = true ∧
      CaptureInterfaces.Interface operations tables capture resumeRow closeRow := by
  have certified := uniform_at_interface schemas same resume closing
  obtain ⟨parameter, binder, body, port, record, input, row, selected, rawKnown, sourceKnown,
      extension, step, nextValid, boundary, source, accepted, _⟩ :=
    EffectBounds.capture_preserves valid (EffectBounds.interface_exact interface) certified cut checked isValue fresh
  exact ⟨parameter, binder, body, port, record, input, row, selected, rawKnown, sourceKnown,
    extension, step, nextValid, boundary, source, accepted, interface⟩

namespace Examples
open CaptureInterfaces.Examples (actualRow pending capturedChoice)
open ParametricClauseRows.Examples (schemaTable clause_list_schema)
open CallableFrames.Examples (handler clauses)
open CallableJoint.CaptureExample (policy)
open PhaseBoundaries.Examples (operations functionContract)
open ContinuationBounds.Examples (family)

def shared : Footprint := actualRow true ++ actualRow false
def table : List (Nat × ClauseContract) := specializeTable schemaTable shared (some [])
def tables : CallableProtectionFrames.Tables := fun _ => table

theorem both_rows_covered (choice : Bool) : Covers shared (actualRow choice) := by
  cases choice <;> decide

theorem saved_under_shared_table (choice : Bool) :
    SavedFrameRequirements.Rows operations tables (capturedChoice choice) (actualRow choice) := by
  have frame : SavedFrameRequirements.FrameSource operations (.plain (pending choice)) (actualRow choice) :=
    SavedFrameRequirements.FrameSource.plain (environment := .empty) (input := .scalar) (output := functionContract)
      (.bind (.bind (.perform rfl .unit) (.lambda (.variable rfl))))
  have suffix : SavedFrameRequirements.Rows operations tables (.push (.handler handler) .nil) [] := .push .handler rfl .nil
  have through : residualize (CallableProtectionFrames.contextOf tables (.push (.handler handler) .nil))
      (actualRow choice) = some (actualRow choice) := by cases choice <;> rfl
  exact .push frame through suffix

/-- Both actual captures are derived under the very same advertised table.
    This is structural capture evidence, not two complete runtime executions. -/
theorem both_captures_one_table (choice : Bool) :
    CaptureInterfaces.Interface operations tables (capturedChoice choice) (actualRow choice) (some []) ∧
      EffectBounds.Certified operations policy (CaptureInterfaces.localRows (actualRow choice) (some []))
        CallableProtection.Environment.empty family functionContract clauses (tables handler) :=
  ⟨.closable (saved_under_shared_table choice) rfl .nil,
    uniform_at_interface (handler := handler) (tables := tables)
      (clause_list_schema (environment := .empty)) rfl (both_rows_covered choice) (success_refl _)⟩

theorem resume_only_table_ignores_closing (closeRow : Option Footprint) :
    specializeTable schemaTable shared closeRow = table := by
  simp only [table, schemaTable, specializeTable, List.map_cons, List.map_nil,
    ClauseSchema.specialize, evalOffer, ParametricClauseRows.Examples.clause_expression_eval]

/-- A resume-only schema can be checked with an unavailable disposal parameter.
    Its resulting table also covers captures with an available disposal plan. -/
theorem resume_only_any_closing (choice : Bool) (closeRow : Option Footprint) :
    EffectBounds.Certified operations policy (CaptureInterfaces.localRows (actualRow choice) closeRow)
      CallableProtection.Environment.empty family functionContract clauses (tables handler) := by
  apply uniform_at_interface (handler := handler) (tables := tables)
    (clause_list_schema (environment := .empty)) (resume_only_table_ignores_closing none).symm
    (both_rows_covered choice) (success_none closeRow)

def protectedCapture (choice : Bool) : Stack := .live 9 .unit .unit
  (.push (.running DisposalProtection.Examples.cellAction .unit CallableProtection.Examples.unit_closed) .nil)
  .none (capturedChoice choice)

theorem protected_capture_same_table (choice : Bool) :
    CaptureInterfaces.Interface operations tables (protectedCapture choice) (actualRow choice) none ∧
      EffectBounds.Certified operations policy (CaptureInterfaces.localRows (actualRow choice) none)
        CallableProtection.Environment.empty family functionContract clauses (tables handler) := by
  have rows : SavedFrameRequirements.Rows operations tables (protectedCapture choice) (actualRow choice) :=
    .live (.push (.running (environment := .empty) (contract := .scalar) .unit) .nil) (saved_under_shared_table choice)
  exact ⟨.protectedCapture rows rfl, resume_only_any_closing choice none⟩

theorem failed_disposal_cannot_cover_available : ¬ SuccessBelow none (some []) := by
  intro assumed
  obtain ⟨row, impossible, _⟩ := assumed [] rfl
  cases impossible

theorem protected_demand_cannot_use_unprotected_bound :
    ¬ Covers [⟨family, 0, false⟩] [⟨family, 0, true⟩] := by decide

theorem order_remains_observable :
    let handler := ProtectionResiduals.Examples.disposableE
    let row := ProtectionResiduals.Examples.demandE
    residualize [handler, .barrier true] row = some [] ∧
      residualize [.barrier true, handler] row = none := by decide

end Examples

end Ash.OneShot.UniformClauseBounds

#print axioms Ash.OneShot.UniformClauseBounds.merge_parts
#print axioms Ash.OneShot.UniformClauseBounds.layer_member
#print axioms Ash.OneShot.UniformClauseBounds.layer_coverage
#print axioms Ash.OneShot.UniformClauseBounds.residual_coverage
#print axioms Ash.OneShot.UniformClauseBounds.success_refl
#print axioms Ash.OneShot.UniformClauseBounds.success_some
#print axioms Ash.OneShot.UniformClauseBounds.success_none
#print axioms Ash.OneShot.UniformClauseBounds.merge_coverage
#print axioms Ash.OneShot.UniformClauseBounds.eval_coverage
#print axioms Ash.OneShot.UniformClauseBounds.instantiate_bounded
#print axioms Ash.OneShot.UniformClauseBounds.uniform_offer
#print axioms Ash.OneShot.UniformClauseBounds.uniform_clauses
#print axioms Ash.OneShot.UniformClauseBounds.uniform_at_interface
#print axioms Ash.OneShot.UniformClauseBounds.capture_preserves
#print axioms Ash.OneShot.UniformClauseBounds.Examples.both_rows_covered
#print axioms Ash.OneShot.UniformClauseBounds.Examples.saved_under_shared_table
#print axioms Ash.OneShot.UniformClauseBounds.Examples.both_captures_one_table
#print axioms Ash.OneShot.UniformClauseBounds.Examples.resume_only_table_ignores_closing
#print axioms Ash.OneShot.UniformClauseBounds.Examples.resume_only_any_closing
#print axioms Ash.OneShot.UniformClauseBounds.Examples.protected_capture_same_table
#print axioms Ash.OneShot.UniformClauseBounds.Examples.failed_disposal_cannot_cover_available
#print axioms Ash.OneShot.UniformClauseBounds.Examples.protected_demand_cannot_use_unprotected_bound
#print axioms Ash.OneShot.UniformClauseBounds.Examples.order_remains_observable
