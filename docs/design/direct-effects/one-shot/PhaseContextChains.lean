import PhaseFrameUsage

/-!
Phase and full-contract composition through contiguous pending plain frames.
The source invariant records the current computation and the exact remaining
context chain. Other frame kinds and multiple source ticket environments still
require integration; this is not complete source admission or progress.
-/

namespace Ash.OneShot.PhaseContextChains
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open ClauseProtection (Ticket Derives)
open ClauseProtectionFrames (ContextDerives)
open CallableProtectionFrames (Tables contextOf)
open Syntax (UseState)

def stackOf : List PlainData → Stack → Stack
  | [], tail => tail
  | frame :: rest, tail => .push (.plain frame) (stackOf rest tail)

def plug : List PlainData → Code → Code
  | [], code => code
  | frame :: rest, code => plug rest (frame.context.plug code)

theorem stack_append (first second : List PlainData) (tail : Stack) :
    stackOf (first ++ second) tail = stackOf first (stackOf second tail) := by
  induction first with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append, stackOf, ih]

theorem stack_tail_append (frames : List PlainData) (inside tail : Stack) :
    (stackOf frames inside).append tail = stackOf frames (inside.append tail) := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => simp only [stackOf, Stack.append, ih]

theorem plug_append (first second : List PlainData) (code : Code) :
    plug (first ++ second) code = plug second (plug first code) := by
  induction first generalizing code with
  | nil => rfl
  | cons frame rest ih => exact ih _

/-- Contiguous plain frames add only inert false barriers to interpretation.
    This does not permit removing handler, resource or protected frames. -/
theorem plain_prefix_residual (tables : Tables) (frames : List PlainData) (inside : Stack) (row : Footprint) :
    residualize (contextOf tables (stackOf frames inside)) row = residualize (contextOf tables inside) row := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      change residualize (.barrier false :: contextOf tables (stackOf rest inside)) row = _
      simpa [residualize, DisposalProtection.through_barrier, qualify] using ih

inductive Chain (operations : Operations) (policy : Syntax.TicketPolicy) (ticket : Ticket)
    (inside : ProtectionContracts.Context) (environment : CallableProtection.Environment) :
    List PlainData → UseState → Contract → UseState → Contract → Footprint → Prop where
  | nil : Chain operations policy ticket inside environment [] phase contract phase contract []
  | cons (head : ContextDerives operations policy ticket inside environment frame.context before input middle intermediate headRow)
      (rest : Chain operations policy ticket inside environment frames middle intermediate after output restRow) :
      Chain operations policy ticket inside environment (frame :: frames) before input after output (headRow ++ restRow)

variable {ticket : Ticket}

theorem chain_append
    (first : Chain operations policy ticket inside environment frames before input middle intermediate firstRow)
    (second : Chain operations policy ticket inside environment rest middle intermediate after output secondRow) :
    Chain operations policy ticket inside environment (frames ++ rest) before input after output (firstRow ++ secondRow) := by
  induction first with
  | nil => exact second
  | cons head remaining ih => simpa only [List.cons_append, List.append_assoc] using Chain.cons head (ih second)

theorem chain_decompose
    (chain : Chain operations policy ticket inside environment (frames ++ rest) before input after output row) :
    ∃ middle intermediate firstRow secondRow,
      Chain operations policy ticket inside environment frames before input middle intermediate firstRow ∧
      Chain operations policy ticket inside environment rest middle intermediate after output secondRow ∧
      row = firstRow ++ secondRow := by
  induction frames generalizing before input row with
  | nil => exact ⟨before, input, [], row, .nil, chain, rfl⟩
  | cons frame remaining ih => cases chain with
      | cons head tail =>
          obtain ⟨middle, intermediate, firstRow, secondRow, first, second, same⟩ := ih tail
          exact ⟨middle, intermediate, _, secondRow, .cons head first, second, by simp [same, List.append_assoc]⟩

theorem chain_plug
    (chain : Chain operations policy ticket inside environment frames middle input after output remainder)
    (child : Derives operations policy ticket inside environment before code middle input row) :
    Derives operations policy ticket inside environment before (plug frames code) after output (row ++ remainder) := by
  induction chain generalizing before code row with
  | nil => simpa only [plug, List.append_nil] using child
  | cons head rest ih =>
      simpa only [plug, List.append_assoc] using ih (ClauseProtectionFrames.context_plug head child)

theorem chain_phase_monotone
    (chain : Chain operations policy ticket inside environment frames before input after output row) :
    before = .consumed → after = .consumed := by
  induction chain with
  | nil => exact id
  | cons head rest ih => exact fun spent => ih (ClauseProtectionFrames.context_phase_monotone head spent)

/-- Current code promises a particular return phase and full contract. The
    first pending context must accept both, and each following context must
    accept its predecessor's output. Earlier effects are not replayed. -/
inductive Source (operations : Operations) (policy : Syntax.TicketPolicy) (ticket : Ticket)
    (inside outside : ProtectionContracts.Context) (environment : CallableProtection.Environment) :
    Code → List PlainData → UseState → UseState → Contract → Footprint → Prop where
  | checked (current : Derives operations policy ticket inside environment before code middle input currentRow)
      (pending : Chain operations policy ticket inside environment frames middle input after output remaining)
      (accepted : checkFootprint outside (currentRow ++ remaining) = true) :
      Source operations policy ticket inside outside environment code frames before after output (currentRow ++ remaining)

theorem source_reconstruct
    (source : Source operations policy ticket inside outside environment code frames before after output row) :
    Derives operations policy ticket inside environment before (plug frames code) after output row ∧
      checkFootprint outside row = true := by
  cases source with
  | checked current pending accepted => exact ⟨chain_plug pending current, accepted⟩

theorem source_focus
    (source : Source operations policy ticket inside outside environment whole frames before after output row)
    (focus : Focus whole child plain.context) :
    Source operations policy ticket inside outside environment child (plain :: frames) before after output row := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨middle, input, childRow, frameRow, childSource, context, same⟩ :=
        ClauseProtectionFrames.focus_decompose current focus
      rw [same, List.append_assoc] at accepted ⊢
      exact .checked childSource (.cons context pending) accepted

theorem source_return
    (source : Source operations policy ticket inside outside environment value frames before after output row)
    (isValue : value.IsValue) :
    ∃ input, Summarizes operations environment value input [] ∧
      Chain operations policy ticket inside environment frames before input after output row ∧
      checkFootprint outside row = true := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨summary, same, empty⟩ := ClauseProtection.value_summary current isValue
      cases same
      subst_vars
      exact ⟨_, summary, pending, accepted⟩

theorem pending_after_resume
    (source : Source operations policy ticket inside outside environment (.resume ticket.binder value)
      frames before after output row) :
    ∃ remaining, Chain operations policy ticket inside environment frames .consumed ticket.answer after output remaining ∧
      checkFootprint outside remaining = true := by
  cases source with
  | checked current pending accepted => cases current with
      | stable summary exported => cases summary
      | resume allowed operand exported =>
          exact ⟨_, pending, (Bool.and_eq_true_iff.mp (by rwa [check_footprint_append] at accepted)).2⟩

theorem source_plug
    (source : Source operations policy ticket inside outside environment value (plain :: frames) before after output row)
    (closed : ClosedValue value) :
    Source operations policy ticket inside outside environment (plain.context.plug value) frames before after output row := by
  obtain ⟨input, summary, pending, accepted⟩ := source_return source closed.1
  cases pending with
  | cons head rest =>
      have current : Derives operations policy ticket inside environment before value before input [] :=
        .stable summary (by simp [ClauseProtection.exportAt, residual_empty])
      exact .checked (ClauseProtectionFrames.context_plug head current) rest accepted

theorem source_bind
    (source : Source operations policy ticket inside outside environment (.bind parameter value body) frames before after output row)
    (closed : ClosedValue value) :
    Source operations policy ticket inside outside environment (body.subst parameter value) frames before after output row := by
  cases source with
  | checked current pending accepted => exact .checked (ClauseProtection.bind_summary current closed) pending accepted

theorem source_beta
    (source : Source operations policy ticket inside outside environment (.app (.lambda parameter body) value) frames before after output row)
    (closed : ClosedValue value) :
    Source operations policy ticket inside outside environment (body.subst parameter value) frames before after output row := by
  cases source with
  | checked current pending accepted => exact .checked (ClauseProtection.beta_summary current closed) pending accepted

theorem source_branch
    (source : Source operations policy ticket inside outside environment (.branch (.boolean choice) yes no)
      frames before after output row) :
    ∃ selectedRow, Source operations policy ticket inside outside environment (if choice then yes else no)
      frames before after output selectedRow := by
  cases source with
  | checked current pending accepted =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      obtain ⟨selectedRow, selected, admitted⟩ := ClauseProtectionFrames.selected_branch current accepted.1
      exact ⟨_, .checked selected pending (by simp only [check_footprint_append, admitted, accepted.2, Bool.and_self])⟩

theorem current_at_actual_prefix
    (source : Source operations policy ticket (contextOf tables inside) (contextOf tables tail) environment
      code frames before after output row) :
    ∃ middle input currentRow remaining,
      Derives operations policy ticket (contextOf tables (stackOf frames inside)) environment
        before code middle input currentRow ∧
      Chain operations policy ticket (contextOf tables inside) environment frames middle input after output remaining ∧
      checkFootprint (contextOf tables tail) currentRow = true ∧
      checkFootprint (contextOf tables tail) remaining = true := by
  cases source with
  | checked current pending accepted =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      refine ⟨_, _, _, _, CleanupProtection.inside_congr current ?_, pending, accepted.1, accepted.2⟩
      intro demands
      exact (plain_prefix_residual tables frames inside demands).symm

theorem current_request_checked
    (source : Source operations policy ticket (contextOf tables inside) (contextOf tables tail) environment
      (.perform effect operation operand) frames before after output row)
    (boundary : PhaseBoundaries.Boundary ticket owner before base tail answer)
    (isValue : operand.IsValue) :
    ∃ input, CallableProtectionFrames.Checked operations tables environment
      (stackOf frames (inside.append base)) (.perform effect operation operand) input := by
  obtain ⟨middle, input, currentRow, remaining, current, pending, accepted, restAccepted⟩ :=
    current_at_actual_prefix source
  obtain ⟨_, request⟩ := PhaseBoundaries.request_checked boundary current accepted isValue
  exact ⟨input, by simpa only [stack_tail_append] using request⟩

/-- Ordinary typing chooses the actual frame ports and scope. The source
    invariant is preserved on the same named focus step. -/
theorem focus_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨whole, scope, stackOf frames (inside.append base)⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy ticket (contextOf tables inside) (contextOf tables tail) environment whole frames before after output row)
    (boundary : PhaseBoundaries.Boundary ticket owner before base tail answer)
    (focus : Focus whole child context) :
    ∃ plain : PlainData, plain.context = context ∧ plain.scope = scope ∧
      let initial : NamedState := ⟨⟨⟨whole, scope, stackOf frames (inside.append base)⟩, issued, completed⟩, activations⟩
      let next := ScopedPortJoint.advanceState initial ⟨child, scope, stackOf (plain :: frames) (inside.append base)⟩ [] []
      NamedAccessStep ambient initial next ∧
      CompletionJoint.Valid declarations policy registry ambient next result outgoing bound ∧
      PhaseBoundaries.Boundary ticket owner before base tail answer ∧
      Source operations policy ticket (contextOf tables inside) (contextOf tables tail) environment child (plain :: frames) before after output row := by
  obtain ⟨plain, shape, saved, step, nextValid⟩ := CompletionJoint.focus_preserves valid focus
  exact ⟨plain, shape, saved, step, nextValid, boundary, source_focus source (shape ▸ focus)⟩

theorem plug_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, stackOf (plain :: frames) (inside.append base)⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy ticket (contextOf tables inside) (contextOf tables tail) environment value (plain :: frames) before after output row)
    (boundary : PhaseBoundaries.Boundary ticket owner before base tail answer)
    (isValue : value.IsValue) :
    let initial : NamedState := ⟨⟨⟨value, scope, stackOf (plain :: frames) (inside.append base)⟩, issued, completed⟩, activations⟩
    let next := ScopedPortJoint.advanceState initial ⟨plain.context.plug value, plain.scope, stackOf frames (inside.append base)⟩ [] []
    NamedAccessStep ambient initial next ∧
      CompletionJoint.Valid declarations policy registry ambient next result outgoing bound ∧
      PhaseBoundaries.Boundary ticket owner before base tail answer ∧
      Source operations policy ticket (contextOf tables inside) (contextOf tables tail) environment (plain.context.plug value) frames before after output row := by
  obtain ⟨step, nextValid⟩ := CompletionJoint.plug_preserves valid isValue
  exact ⟨step, nextValid, boundary, source_plug source (CompletionJoint.current_closed_value valid isValue)⟩

namespace Examples
open ClauseProtection.Examples (effectF effectG operations policy)
open ClauseProtectionFrames.Examples (outside)

def callable : Contract := .function .scalar .scalar [⟨effectF, 0, false⟩]
def callTicket : Ticket := ⟨0, .scalar, callable, true, [⟨effectG, 0, true⟩], []⟩
def functionType : Ty := .function .unit .unit [effectF] []
def resumeFrame : PlainData := ⟨.resume 0, .ticket 0 7, .unit, functionType, [7], by decide⟩
def applyFrame : PlainData := ⟨.appFunction .unit, .none, functionType, .unit, [], rfl⟩
def bindFrame : PlainData := ⟨.bind 4 (.variable 4), .ticket 0 7, functionType, functionType, [], rfl⟩
def remaining : Footprint := [⟨effectF, 0, false⟩]
def completeRow : Footprint := [⟨effectG, 0, true⟩, ⟨effectF, 0, false⟩]
def returned : Code := .lambda 9 (.perform (Instantiation.freezeEffect effectF) 0 (.variable 9))

theorem resume_then_apply : Chain operations policy callTicket [] CallableProtection.Environment.empty
    [resumeFrame, applyFrame] .available .scalar .consumed .scalar completeRow := by
  have argument : Derives operations policy callTicket [] CallableProtection.Environment.empty
      .consumed .unit .consumed .scalar [] := .stable .unit rfl
  have application : ContextDerives operations policy callTicket [] CallableProtection.Environment.empty
      applyFrame.context .consumed callable .consumed .scalar remaining := .appFunction argument rfl
  exact Chain.cons (frame := resumeFrame) (.resume rfl rfl)
    (Chain.cons (frame := applyFrame) application .nil)

theorem composition_uses_final_phase : checkFootprint outside completeRow = true ∧
    checkFootprint outside [⟨effectF, 0, true⟩] = false := by decide

theorem two_resumes_cannot_compose :
    ¬ Chain operations policy callTicket inside environment [resumeFrame, resumeFrame] before input after output row := by
  intro chain
  cases chain with
  | cons first rest => cases first with
      | resume allowed exported => cases rest with
          | cons second tail => cases second

def scalarRequestFrame : PlainData :=
  ⟨.perform (Instantiation.freezeEffect effectF) 0, .none, .unit, .unit, [], rfl⟩

theorem callable_cannot_fill_scalar_request_hole :
    ¬ Chain operations policy callTicket inside environment [resumeFrame, scalarRequestFrame] before input after output row := by
  have incompatible {position after output row}
      (context : ContextDerives operations policy callTicket inside environment position .consumed callable after output row)
      (shape : position = scalarRequestFrame.context) : False := by
    cases context <;> simp only [scalarRequestFrame, Context.perform.injEq, reduceCtorEq] at shape
    case perform effect operation output row known exported =>
      change some (Contract.scalar, Contract.scalar) = some (callable, _) at known
      have impossible := (Prod.mk.inj (Option.some.inj known)).1
      cases impossible
  intro chain
  cases chain with
  | cons first rest => cases first with
      | resume allowed exported => cases rest with
          | cons second tail => exact incompatible second rfl

theorem returned_callable_summary : Summarizes operations CallableProtection.Environment.empty returned callable [] :=
  .lambda (.perform rfl (.variable rfl))

theorem after_return_source : Source operations policy callTicket [] outside CallableProtection.Environment.empty
    returned [bindFrame, applyFrame] .consumed .consumed .scalar remaining := by
  have argument : Derives operations policy callTicket [] CallableProtection.Environment.empty
      .consumed .unit .consumed .scalar [] := .stable .unit rfl
  have application : ContextDerives operations policy callTicket [] CallableProtection.Environment.empty
      applyFrame.context .consumed callable .consumed .scalar remaining := .appFunction argument rfl
  have binding : ContextDerives operations policy callTicket [] CallableProtection.Environment.empty
      bindFrame.context .consumed callable .consumed callable [] := .bind (.stable (.variable rfl) rfl)
  have pending : Chain operations policy callTicket [] CallableProtection.Environment.empty
      [bindFrame, applyFrame] .consumed callable .consumed .scalar remaining :=
    Chain.cons (frame := bindFrame) binding (Chain.cons (frame := applyFrame) application .nil)
  exact Source.checked (outside := outside) (.stable returned_callable_summary rfl) pending (by decide)

theorem returned_callable_closed : ClosedValue returned := ⟨trivial, rfl, by intro _ present; cases present⟩

theorem returning_then_applying_keeps_only_suffix : Source operations policy callTicket [] outside CallableProtection.Environment.empty
    (.perform (Instantiation.freezeEffect effectF) 0 .unit) [] .consumed .consumed .scalar remaining := by
  have bindReady := source_plug after_return_source returned_callable_closed
  have returnedAgain := source_bind bindReady returned_callable_closed
  have application := source_plug returnedAgain returned_callable_closed
  exact source_beta application CallableProtection.Examples.unit_closed

namespace Joint
open CallableFrames.Examples (s1 clauseBody captured handler pendingFunction spent)
open CallableJoint.CaptureExample (liveState)
open GenerativeFrames.Examples (declarations)
open CallableContracts.Examples (identity scalar)
open PhaseBoundaries.Examples (phaseTicket functionContract)

theorem resume_return_preserves_pending_chain
    (valid : CompletionJoint.Valid declarations CallableJoint.CaptureExample.policy registry []
      (liveState s1) .integer [] scalar) :
    NamedAccessSteps [] (liveState s1) PhaseBoundaries.Examples.afterClausePlug ∧
    CompletionJoint.Valid declarations CallableJoint.CaptureExample.policy registry []
      PhaseBoundaries.Examples.afterClausePlug .integer [] scalar ∧
    ∃ row, Source PhaseBoundaries.Examples.operations CallableJoint.CaptureExample.policy (phaseTicket false)
      [] (contextOf PhaseBoundaries.Examples.tables CallableFrames.Examples.outside) CallableProtection.Environment.empty
      (.bind 4 identity (.variable 4)) [] .consumed .consumed functionContract row := by
  have initialSource : Source PhaseBoundaries.Examples.operations CallableJoint.CaptureExample.policy (phaseTicket false)
      [] (contextOf PhaseBoundaries.Examples.tables CallableFrames.Examples.outside) CallableProtection.Environment.empty
      clauseBody [] .available .consumed functionContract [] :=
    .checked PhaseBoundaries.Examples.clause_checked .nil (by decide)
  have position : Focus clauseBody (.resume 10 (.integer 17)) (.bind 4 (.variable 4)) :=
    .bind (by intro impossible; cases impossible)
  obtain ⟨plain, shape, savedScope, e1, c2, _, focused⟩ := focus_joint (inside := .nil)
    (tables := PhaseBoundaries.Examples.tables) valid initialSource (PhaseBoundaries.Boundary.live rfl) position
  obtain ⟨remaining, pending, accepted⟩ := pending_after_resume focused
  obtain ⟨e2, c3⟩ := CompletionJoint.resume_preserves (front := .push (.plain plain) .nil) c2 rfl trivial
  obtain ⟨e3, c4⟩ := CompletionJoint.plug_preserves c3 trivial
  obtain ⟨e4, c5⟩ := CompletionJoint.bind_preserves c4 trivial
  obtain ⟨e5, c6⟩ := CompletionJoint.handler_return_preserves c5 trivial
  have identitySource : Derives PhaseBoundaries.Examples.operations CallableJoint.CaptureExample.policy (phaseTicket false)
      [] CallableProtection.Environment.empty .consumed identity .consumed functionContract [] :=
    .stable (.lambda (.variable rfl)) rfl
  have returnedSource : Source PhaseBoundaries.Examples.operations CallableJoint.CaptureExample.policy (phaseTicket false)
      [] (contextOf PhaseBoundaries.Examples.tables CallableFrames.Examples.outside) CallableProtection.Environment.empty
      identity [plain] .consumed .consumed functionContract remaining :=
    .checked identitySource pending accepted
  obtain ⟨e6, c7, _, finalSource⟩ := plug_joint (inside := .nil) (tables := PhaseBoundaries.Examples.tables)
    c6 returnedSource PhaseBoundaries.Boundary.spent trivial
  refine ⟨?_, ?_, remaining, ?_⟩
  · simpa [ScopedPortJoint.advanceState, liveState, s1, PhaseBoundaries.Examples.afterClausePlug,
      CallableJoint.CaptureExample.spentState, captured, handler, pendingFunction, spent, shape, savedScope,
      ScopedExecution.Context.plug, Code.subst, enteredActivations, clauseBody, identity, Stack.append, stackOf] using
      (NamedAccessSteps.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.refl _)))))))
  · simpa [ScopedPortJoint.advanceState, liveState, s1, PhaseBoundaries.Examples.afterClausePlug,
      CallableJoint.CaptureExample.spentState, captured, handler, pendingFunction, spent, shape, savedScope,
      ScopedExecution.Context.plug, Code.subst, enteredActivations, clauseBody, identity, Stack.append, stackOf] using c7
  · simpa [shape, ScopedExecution.Context.plug, identity, Code.subst, contextOf] using finalSource

end Joint
end Examples

end Ash.OneShot.PhaseContextChains

#print axioms Ash.OneShot.PhaseContextChains.stack_append
#print axioms Ash.OneShot.PhaseContextChains.stack_tail_append
#print axioms Ash.OneShot.PhaseContextChains.plug_append
#print axioms Ash.OneShot.PhaseContextChains.plain_prefix_residual
#print axioms Ash.OneShot.PhaseContextChains.chain_append
#print axioms Ash.OneShot.PhaseContextChains.chain_decompose
#print axioms Ash.OneShot.PhaseContextChains.chain_plug
#print axioms Ash.OneShot.PhaseContextChains.chain_phase_monotone
#print axioms Ash.OneShot.PhaseContextChains.source_reconstruct
#print axioms Ash.OneShot.PhaseContextChains.source_focus
#print axioms Ash.OneShot.PhaseContextChains.source_plug
#print axioms Ash.OneShot.PhaseContextChains.source_bind
#print axioms Ash.OneShot.PhaseContextChains.source_beta
#print axioms Ash.OneShot.PhaseContextChains.source_branch
#print axioms Ash.OneShot.PhaseContextChains.current_at_actual_prefix
#print axioms Ash.OneShot.PhaseContextChains.focus_joint
#print axioms Ash.OneShot.PhaseContextChains.plug_joint

#print axioms Ash.OneShot.PhaseContextChains.source_return
#print axioms Ash.OneShot.PhaseContextChains.current_request_checked
#print axioms Ash.OneShot.PhaseContextChains.pending_after_resume
#print axioms Ash.OneShot.PhaseContextChains.Examples.resume_then_apply
#print axioms Ash.OneShot.PhaseContextChains.Examples.composition_uses_final_phase
#print axioms Ash.OneShot.PhaseContextChains.Examples.two_resumes_cannot_compose
#print axioms Ash.OneShot.PhaseContextChains.Examples.callable_cannot_fill_scalar_request_hole
#print axioms Ash.OneShot.PhaseContextChains.Examples.returned_callable_summary
#print axioms Ash.OneShot.PhaseContextChains.Examples.after_return_source
#print axioms Ash.OneShot.PhaseContextChains.Examples.returned_callable_closed
#print axioms Ash.OneShot.PhaseContextChains.Examples.returning_then_applying_keeps_only_suffix
#print axioms Ash.OneShot.PhaseContextChains.Examples.Joint.resume_return_preserves_pending_chain
