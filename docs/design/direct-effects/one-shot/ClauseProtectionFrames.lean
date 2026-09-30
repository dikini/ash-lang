import CleanupProtection

/-!
Source continuation phases at actual pending evaluation contexts. Focus and
plug preserve exact residual rows and full callable contracts within this
judgment. Historical owner/scope realization and full machine preservation
remain separate obligations.
-/

namespace Ash.OneShot.ClauseProtectionFrames
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open ClauseProtection (Ticket Derives exportAt)
open Syntax (UseState)
open Instantiation (freezeEffect)

variable {ticket : Ticket}

theorem split_export
    (exported : exportAt ticket inside state (first ++ second) = some row) :
    ∃ left right, exportAt ticket inside state first = some left ∧
      exportAt ticket inside state second = some right ∧ row = left ++ right := by
  rw [exportAt, residual_rows_append] at exported
  cases a : residualize (ClauseProtection.phaseContext ticket inside state) first <;>
    cases b : residualize (ClauseProtection.phaseContext ticket inside state) second <;>
    simp [merge, a, b] at exported
  case some.some left right => exact ⟨left, right, a, b, exported.symm⟩

inductive ContextDerives (operations : Operations) (policy : Syntax.TicketPolicy) (ticket : Ticket)
    (inside : ProtectionContracts.Context) (environment : CallableProtection.Environment) :
    ScopedExecution.Context → UseState → Contract → UseState → Contract → Footprint → Prop where
  | pairLeft (right : Derives operations policy ticket inside environment middle code after output row) :
      ContextDerives operations policy ticket inside environment (.pairLeft code) middle input after (.pair input output) row
  | pairRight (left : Summarizes operations environment code input []) :
      ContextDerives operations policy ticket inside environment (.pairRight code) state output state (.pair input output) []
  | appFunction (argument : Derives operations policy ticket inside environment middle code after input argumentRow)
      (exported : exportAt ticket inside after latent = some invocationRow) :
      ContextDerives operations policy ticket inside environment (.appFunction code) middle (.function input output latent)
        after output (argumentRow ++ invocationRow)
  | appArgument (function : Summarizes operations environment code (.function input output latent) [])
      (exported : exportAt ticket inside state latent = some invocationRow) :
      ContextDerives operations policy ticket inside environment (.appArgument code) state input state output invocationRow
  | bind (body : Derives operations policy ticket inside (environment.extend name input) middle code after output row) :
      ContextDerives operations policy ticket inside environment (.bind name code) middle input after output row
  | branch (yes : Derives operations policy ticket inside environment middle a after output yesRow)
      (no : Derives operations policy ticket inside environment middle b after output noRow) :
      ContextDerives operations policy ticket inside environment (.branch a b) middle .scalar after output (yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output))
      (exported : exportAt ticket inside state [⟨effect, operation, false⟩] = some row) :
      ContextDerives operations policy ticket inside environment (.perform (freezeEffect effect) operation)
        state input state output row
  | resume (allowed : (policy ticket.binder).resume = true)
      (exported : residualize inside ticket.resumeRow = some row) :
      ContextDerives operations policy ticket inside environment (.resume ticket.binder)
        .available ticket.input .consumed ticket.answer row
  | cleanup (body : Derives operations policy ticket inside environment middle code after output bodyRow)
      (exported : residualize (.barrier true :: ClauseProtection.phaseContext ticket inside after) latent = some invocationRow) :
      ContextDerives operations policy ticket inside environment (.cleanup code) middle (.function .scalar .scalar latent)
        after output (bodyRow ++ invocationRow)
  | resource {world : List Nat} {bodyRow : Nat → Footprint}
      (body : ∀ identity, identity ∉ world → Summarizes operations environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (outward : ∀ identity, identity ∉ world → outsideCell identity (bodyRow identity) = raw)
      (exported : exportAt ticket inside state raw = some row) :
      ContextDerives operations policy ticket inside environment (.resource binder code) state .scalar state output row

theorem context_plug (context : ContextDerives operations policy ticket inside environment position middle input after output remainder)
    (child : Derives operations policy ticket inside environment before code middle input row) :
    Derives operations policy ticket inside environment before (position.plug code) after output (row ++ remainder) := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left =>
      simpa [ScopedExecution.Context.plug] using Derives.pair
        (Derives.stable (ticket := ticket) (outside := []) left (by simp [exportAt, residual_empty])) child
  | appFunction argument exported =>
      simpa [ScopedExecution.Context.plug, List.append_assoc] using Derives.app child argument exported
  | appArgument function exported =>
      simpa [ScopedExecution.Context.plug] using Derives.app
        (Derives.stable (ticket := ticket) (outside := []) function (by simp [exportAt, residual_empty])) child exported
  | bind body => exact .bind child body
  | branch yes no => simpa [ScopedExecution.Context.plug, List.append_assoc] using Derives.branch child yes no
  | perform known exported => exact .perform known child exported
  | resume allowed exported => exact .resume allowed child exported
  | cleanup body exported =>
      simpa [ScopedExecution.Context.plug, List.append_assoc] using Derives.cleanup child body exported
  | resource body outward exported => exact .resource child body outward exported

/-- Unit is only a placeholder for the hole's ticket usage here; this projection
    does not assert that Unit has the hole's ordinary or callable type. -/
theorem context_usage (context : ContextDerives operations policy ticket inside environment position middle input after output row) :
    Uses policy (.ticket ticket.binder (policy ticket.binder)) middle (position.plug .unit) after := by
  cases context with
  | pairLeft right => exact .pair .unit (ClauseProtection.derives_usage right)
  | pairRight left => exact .pair (ClauseProtection.stable_usage left policy _ _) .unit
  | appFunction argument exported => exact .app .unit (ClauseProtection.derives_usage argument)
  | appArgument function exported => exact .app (ClauseProtection.stable_usage function policy _ _) .unit
  | bind body => exact .bind .unit (ClauseProtection.derives_usage body)
  | branch yes no => exact .branch .unit (ClauseProtection.derives_usage yes) (ClauseProtection.derives_usage no)
  | perform => exact .perform .unit
  | resume allowed exported => exact .resume allowed .unit
  | cleanup body exported => exact .cleanup .unit (ClauseProtection.derives_usage body)
  | resource body outward exported =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource .unit ((instantiation_preserves_usage_iff _ _).mp (ClauseProtection.stable_usage (body identity fresh) policy _ _))

theorem context_phase_monotone
    (context : ContextDerives operations policy ticket inside environment position middle input after output row) :
    middle = .consumed → after = .consumed := Syntax.use_state_monotone (context_usage context)

theorem stable_context
    (context : CallableProtectionFrames.ContextSummarizes operations environment position input output raw)
    (exported : exportAt ticket inside state raw = some row) :
    ContextDerives operations policy ticket inside environment position state input state output row := by
  cases context with
  | pairLeft right => exact .pairLeft (.stable right exported)
  | pairRight left =>
      have empty : row = [] := by simpa [exportAt, residual_empty] using exported.symm
      subst row
      exact .pairRight left
  | appFunction argument =>
      obtain ⟨argumentRow, invocationRow, argumentExport, invocationExport, same⟩ := split_export exported
      subst row
      exact .appFunction (.stable argument argumentExport) invocationExport
  | appArgument function => exact .appArgument function exported
  | bind body => exact .bind (.stable body exported)
  | branch yes no =>
      obtain ⟨yesRow, noRow, yesExport, noExport, same⟩ := split_export exported
      subst row
      exact .branch (.stable yes yesExport) (.stable no noExport)
  | perform known => exact .perform known exported
  | cleanup body =>
      obtain ⟨bodyRow, invocationRow, bodyExport, invocationExport, same⟩ := split_export exported
      subst row
      exact .cleanup (.stable body bodyExport) (by
        simp only [residualize, DisposalProtection.through_barrier]
        exact invocationExport)
  | resource body outward => exact .resource body outward exported

theorem focus_decompose
    (checked : Derives operations policy ticket inside environment before whole after output row)
    (focus : Focus whole child position) :
    ∃ middle input childRow remainder,
      Derives operations policy ticket inside environment before child middle input childRow ∧
      ContextDerives operations policy ticket inside environment position middle input after output remainder ∧
      row = childRow ++ remainder := by
  cases checked with
  | stable summary exported =>
      obtain ⟨input, childRaw, remainingRaw, childSummary, context, same⟩ :=
        CallableProtectionFrames.focus_decompose summary focus
      rw [same] at exported
      obtain ⟨childRow, remainder, childExport, remainderExport, same⟩ := split_export exported
      exact ⟨_, input, childRow, remainder, .stable childSummary childExport, stable_context context remainderExport, same⟩
  | pair left right => cases focus with
      | pairLeft => exact ⟨_, _, _, _, left, .pairLeft right, rfl⟩
      | pairRight value =>
          obtain ⟨summary, same, empty⟩ := ClauseProtection.value_summary left value
          subst_vars
          exact ⟨_, _, _, _, right, .pairRight summary, by simp⟩
  | app function argument exported => cases focus with
      | appFunction => exact ⟨_, _, _, _, function, .appFunction argument exported, List.append_assoc ..⟩
      | appArgument value =>
          obtain ⟨summary, same, empty⟩ := ClauseProtection.value_summary function value
          subst_vars
          exact ⟨_, _, _, _, argument, .appArgument summary exported, by simp⟩
  | bind initializer body => cases focus with
      | bind => exact ⟨_, _, _, _, initializer, .bind body, rfl⟩
  | branch condition yes no => cases focus with
      | branch => exact ⟨_, _, _, _, condition, .branch yes no, List.append_assoc ..⟩
  | perform known operand exported => cases focus with
      | perform => exact ⟨_, _, _, _, operand, .perform known exported, rfl⟩
  | resume allowed operand exported => cases focus with
      | resume => exact ⟨_, _, _, _, operand, .resume allowed exported, rfl⟩
  | discard => cases focus
  | cleanup callback body exported => cases focus with
      | cleanup => exact ⟨_, _, _, _, callback, .cleanup body exported, List.append_assoc ..⟩
  | resource initializer body outward exported => cases focus with
      | resource notValue => exact ⟨_, _, _, _, initializer, .resource body outward exported, rfl⟩

/-- The frame retains its suffix's analysis environment and the phase/contract
    expected when the focused child returns. Earlier child effects are absent. -/
def Pending (operations : Operations) (policy : Syntax.TicketPolicy) (ticket : Ticket)
    (inside outside : ProtectionContracts.Context) (environment : CallableProtection.Environment)
    (plain : PlainData) (middle : UseState) (input : Contract) (after : UseState) (output : Contract)
    (remainder : Footprint) : Prop :=
  ContextDerives operations policy ticket inside environment plain.context middle input after output remainder ∧
    checkFootprint outside remainder = true

theorem plain_context (tables : CallableProtectionFrames.Tables) (plain : PlainData) (front : Stack) :
    CallableProtectionFrames.contextOf tables (.push (.plain plain) front) =
      .barrier false :: CallableProtectionFrames.contextOf tables front := rfl

theorem focus_step
    (checked : Derives operations policy ticket inside environment before whole after output row)
    (accepted : checkFootprint outside row = true) (focus : Focus whole child plain.context) :
    ∃ middle input childRow remainder,
      RawStep ⟨whole, plain.scope, tail⟩ ⟨child, plain.scope, .push (.plain plain) tail⟩ [] [] ∧
      Derives operations policy ticket (.barrier false :: inside) environment before child middle input childRow ∧
      checkFootprint outside childRow = true ∧
      Pending operations policy ticket inside outside environment plain middle input after output remainder := by
  obtain ⟨middle, input, childRow, remainder, childChecked, context, same⟩ := focus_decompose checked focus
  rw [same, check_footprint_append, Bool.and_eq_true_iff] at accepted
  exact ⟨middle, input, childRow, remainder, .focus plain focus tail, CleanupProtection.under_armed childChecked,
    accepted.1, context, accepted.2⟩

theorem plug_step
    (pending : Pending operations policy ticket inside outside savedEnvironment plain middle input after output remainder)
    (returned : Derives operations policy ticket (.barrier false :: inside) currentEnvironment
      current value middle input row)
    (closed : ClosedValue value) :
    current = middle ∧
      RawStep ⟨value, scope, .push (.plain plain) tail⟩ ⟨plain.context.plug value, plain.scope, tail⟩ [] [] ∧
      Derives operations policy ticket inside savedEnvironment middle (plain.context.plug value) after output remainder ∧
      checkFootprint outside remainder = true := by
  obtain ⟨context, accepted⟩ := pending
  obtain ⟨summary, same, empty⟩ := ClauseProtection.value_summary returned closed.1
  have moved := closed_value_environment summary closed savedEnvironment
  refine ⟨same, .plug plain value closed scope tail, ?_, accepted⟩
  simpa using context_plug context
    (Derives.stable (ticket := ticket) (outside := []) moved (by simp [exportAt, residual_empty]))

theorem bind_step
    (checked : Derives operations policy ticket inside environment before (.bind parameter value body) after result row)
    (closed : ClosedValue value) (ready : ClosedExcept parameter body) :
    RawStep ⟨.bind parameter value body, scope, tail⟩ ⟨body.subst parameter value, scope, tail⟩ [] [] ∧
      Derives operations policy ticket inside environment before (body.subst parameter value) after result row :=
  ⟨.bind parameter value body scope tail closed ready, ClauseProtection.bind_summary checked closed⟩

theorem beta_step
    (checked : Derives operations policy ticket inside environment before (.app (.lambda parameter body) value) after result row)
    (closed : ClosedValue value) (functionClosed : ClosedValue (.lambda parameter body)) :
    RawStep ⟨.app (.lambda parameter body) value, scope, tail⟩ ⟨body.subst parameter value, .none, tail⟩ [] [] ∧
      Derives operations policy ticket inside environment before (body.subst parameter value) after result row :=
  ⟨.beta parameter body value scope tail closed functionClosed, ClauseProtection.beta_summary checked closed⟩

theorem selected_branch
    (checked : Derives operations policy ticket inside environment before (.branch (.boolean choice) yes no) after result row)
    (accepted : checkFootprint outside row = true) :
    ∃ selectedRow, Derives operations policy ticket inside environment before (if choice then yes else no) after result selectedRow ∧
      checkFootprint outside selectedRow = true := by
  cases checked with
  | stable summary exported =>
      cases summary with
      | branch condition yesSummary noSummary =>
          cases condition
          simp only [List.nil_append] at exported
          obtain ⟨yesRow, noRow, yesExport, noExport, same⟩ := split_export exported
          rw [same, check_footprint_append, Bool.and_eq_true_iff] at accepted
          cases choice with
          | false => exact ⟨noRow, .stable noSummary noExport, accepted.2⟩
          | true => exact ⟨yesRow, .stable yesSummary yesExport, accepted.1⟩
  | branch condition yesChecked noChecked =>
      obtain ⟨_, same, empty⟩ := ClauseProtection.value_summary condition trivial
      subst_vars
      simp only [List.nil_append, check_footprint_append, Bool.and_eq_true_iff] at accepted
      cases choice with
      | false => exact ⟨_, noChecked, accepted.2⟩
      | true => exact ⟨_, yesChecked, accepted.1⟩

theorem branch_step
    (checked : Derives operations policy ticket inside environment before (.branch (.boolean choice) yes no) after result row)
    (accepted : checkFootprint outside row = true) :
    ∃ selectedRow, RawStep ⟨.branch (.boolean choice) yes no, scope, tail⟩
      ⟨if choice then yes else no, scope, tail⟩ [] [] ∧
      Derives operations policy ticket inside environment before (if choice then yes else no) after result selectedRow ∧
      checkFootprint outside selectedRow = true := by
  obtain ⟨selectedRow, selected, admitted⟩ := selected_branch checked accepted
  refine ⟨selectedRow, ?_, selected, admitted⟩
  cases choice with
  | false => exact .ifFalse yes no scope tail
  | true => exact .ifTrue yes no scope tail

namespace Examples
open ClauseProtection.Examples (effectF effectG operations policy capturedTicket requestF unit_summary request_summary resume_summary)
open CallableProtection.Examples (unit_closed)

def outside : ProtectionContracts.Context :=
  [.handler effectF 11 [(0, ⟨true, some [], none⟩)], .handler effectG 22 [(0, ⟨false, some [], some []⟩)]]
def afterResume : Code := .bind 1 (.resume 0 .unit) requestF
def afterResumeFrame : PlainData := ⟨.bind 1 requestF, .ticket 0 7, .unit, .unit, [], rfl⟩
def resumedThenF : Footprint := [⟨effectG, 0, true⟩, ⟨effectF, 0, false⟩]
def remainingF : Footprint := [⟨effectF, 0, false⟩]

theorem resume_then_suffix : Derives operations policy capturedTicket [] environment
    .available afterResume .consumed .scalar resumedThenF :=
  .bind resume_summary (request_summary .consumed)

theorem focus_actual_bind : ∃ middle input childRow remainder,
    RawStep ⟨afterResume, .ticket 0 7, tail⟩
      ⟨.resume 0 .unit, .ticket 0 7, .push (.plain afterResumeFrame) tail⟩ [] [] ∧
    Derives operations policy capturedTicket [.barrier false] environment
      .available (.resume 0 .unit) middle input childRow ∧
    checkFootprint outside childRow = true ∧
    Pending operations policy capturedTicket [] outside environment afterResumeFrame
      middle input .consumed .scalar remainder :=
  focus_step (plain := afterResumeFrame) (outside := outside) resume_then_suffix (by decide)
    (show Focus afterResume (.resume 0 .unit) afterResumeFrame.context from
      .bind (by intro impossible; cases impossible))

theorem pending_after_consumption : Pending operations policy capturedTicket [] outside environment afterResumeFrame
    .consumed .scalar .consumed .scalar remainingF := ⟨.bind (request_summary .consumed), by decide⟩

theorem plug_keeps_only_suffix :
    RawStep ⟨.unit, .none, .push (.plain afterResumeFrame) tail⟩
      ⟨.bind 1 .unit requestF, .ticket 0 7, tail⟩ [] [] ∧
    Derives operations policy capturedTicket [] savedEnvironment .consumed
      (.bind 1 .unit requestF) .consumed .scalar remainingF ∧ checkFootprint outside remainingF = true := by
  exact (plug_step (pending_after_consumption (environment := savedEnvironment))
    (unit_summary (environment := CallableProtection.Environment.empty) .consumed) unit_closed).2

theorem suffix_does_not_replay_resume :
    checkFootprint outside remainingF = true ∧
      checkFootprint outside [⟨effectF, 0, true⟩] = false ∧
      ⟨effectG, 0, true⟩ ∉ remainingF := by decide

theorem resume_operand_context : ContextDerives operations policy capturedTicket [] environment (.resume 0)
    .available .scalar .consumed .scalar [⟨effectG, 0, true⟩] := .resume rfl rfl

theorem consumed_resume_context_rejected :
    ¬ ContextDerives operations policy capturedTicket inside environment (.resume 0)
      .consumed input after output row := by intro context; cases context

def forwardF : ProtectionContracts.Context := [.handler effectF 33 [(0, ⟨false, some [⟨effectG, 0, false⟩], none⟩)]]

theorem stable_context_exports_selected_rows : ContextDerives operations policy capturedTicket forwardF environment
    (.appFunction requestF) .available (.function .scalar .scalar [⟨effectG, 1, false⟩]) .available .scalar
      [⟨effectG, 0, true⟩, ⟨effectG, 1, true⟩] := by
  exact stable_context (.appFunction (.perform rfl .unit)) (by decide)

def identity : Code := .lambda 0 (.variable 0)
def identityContract : Contract := .function .scalar .scalar []
def applyBound : Code := .app (.variable 5) .unit
def savedEnvironment : CallableProtection.Environment := CallableProtection.Environment.empty.extend 9 .scalar
def callableFrame : PlainData := ⟨.bind 5 applyBound, .ticket 0 7, .function .unit .unit [] [], .unit, [], rfl⟩

theorem identity_summary : Summarizes operations environment identity identityContract [] :=
  .lambda (.variable (by simp [CallableProtection.Environment.extend]))

theorem identity_closed : ClosedValue identity :=
  ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem callable_pending : Pending operations policy capturedTicket [] outside savedEnvironment callableFrame
    .consumed identityContract .consumed .scalar [] := by
  have body : Summarizes operations (savedEnvironment.extend 5 identityContract) applyBound .scalar [] :=
    .app (.variable (by simp [CallableProtection.Environment.extend, identityContract])) .unit
  exact ⟨.bind (.stable body rfl), rfl⟩

theorem callable_plug_saved_environment :
    RawStep ⟨identity, .none, .push (.plain callableFrame) tail⟩
      ⟨.bind 5 identity applyBound, .ticket 0 7, tail⟩ [] [] ∧
    Derives operations policy capturedTicket [] savedEnvironment .consumed
      (.bind 5 identity applyBound) .consumed .scalar [] ∧ checkFootprint outside [] = true := by
  exact (plug_step callable_pending
    (show Derives operations policy capturedTicket [.barrier false] CallableProtection.Environment.empty
      .consumed identity .consumed identityContract [] from .stable identity_summary rfl) identity_closed).2

theorem callable_bind_preserves_result : Derives operations policy capturedTicket [] savedEnvironment
    .consumed (.app identity .unit) .consumed .scalar [] :=
  ClauseProtection.bind_summary (callable_plug_saved_environment (tail := .nil)).2.1 identity_closed

theorem cleanup_context_uses_body_final_phase : ContextDerives operations policy capturedTicket [] environment
    (.cleanup (.resume 0 .unit)) .available (.function .scalar .scalar [⟨effectF, 0, false⟩])
    .consumed .scalar [⟨effectG, 0, true⟩, ⟨effectF, 0, true⟩] :=
  .cleanup resume_summary rfl

theorem actual_callable_beta :
    RawStep ⟨.app identity .unit, .ticket 0 7, tail⟩ ⟨.unit, .none, tail⟩ [] [] ∧
      Derives operations policy capturedTicket [] savedEnvironment .consumed .unit .consumed .scalar [] :=
  beta_step callable_bind_preserves_result unit_closed identity_closed

theorem branch_selects_remaining_requirements : ∃ row,
    RawStep ⟨.branch (.boolean true) requestF (.perform (freezeEffect effectG) 0 .unit), .ticket 0 7, tail⟩
      ⟨requestF, .ticket 0 7, tail⟩ [] [] ∧
    Derives operations policy capturedTicket [] environment .consumed requestF .consumed .scalar row ∧
      checkFootprint outside row = true := by
  have checked : Derives operations policy capturedTicket [] environment .consumed
      (.branch (.boolean true) requestF (.perform (freezeEffect effectG) 0 .unit)) .consumed .scalar
      [⟨effectF, 0, false⟩, ⟨effectG, 0, false⟩] :=
    .stable (.branch .boolean (.perform rfl .unit) (.perform rfl .unit)) rfl
  exact branch_step checked (by decide)

end Examples

end Ash.OneShot.ClauseProtectionFrames

#print axioms Ash.OneShot.ClauseProtectionFrames.split_export
#print axioms Ash.OneShot.ClauseProtectionFrames.context_plug
#print axioms Ash.OneShot.ClauseProtectionFrames.context_usage
#print axioms Ash.OneShot.ClauseProtectionFrames.context_phase_monotone
#print axioms Ash.OneShot.ClauseProtectionFrames.stable_context
#print axioms Ash.OneShot.ClauseProtectionFrames.focus_decompose
#print axioms Ash.OneShot.ClauseProtectionFrames.plain_context
#print axioms Ash.OneShot.ClauseProtectionFrames.focus_step
#print axioms Ash.OneShot.ClauseProtectionFrames.plug_step
#print axioms Ash.OneShot.ClauseProtectionFrames.bind_step
#print axioms Ash.OneShot.ClauseProtectionFrames.beta_step
#print axioms Ash.OneShot.ClauseProtectionFrames.selected_branch
#print axioms Ash.OneShot.ClauseProtectionFrames.branch_step
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.resume_then_suffix
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.focus_actual_bind
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.pending_after_consumption
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.plug_keeps_only_suffix
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.suffix_does_not_replay_resume
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.resume_operand_context
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.consumed_resume_context_rejected
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.stable_context_exports_selected_rows
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.identity_summary
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.identity_closed
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.callable_pending
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.callable_plug_saved_environment
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.callable_bind_preserves_result
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.cleanup_context_uses_body_final_phase
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.actual_callable_beta
#print axioms Ash.OneShot.ClauseProtectionFrames.Examples.branch_selects_remaining_requirements
