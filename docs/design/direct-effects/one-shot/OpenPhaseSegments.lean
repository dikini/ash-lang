import OwnerPhases

/-!
Phase-indexed pending source segments with an owner outside the segment.
The existing direct expression judgment is retained. Every frame checks its
code at its actual remaining interpretation suffix, and composition threads
full contracts and the exposed owner's phase. Interior live-owner groups and
complete machine source preservation remain separate integration obligations.
-/

namespace Ash.OneShot.OpenPhaseSegments
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open CallableProtectionFrames (Tables contextOf)
open ClauseProtection (Ticket Derives exportAt)
open ClauseProtectionFrames (ContextDerives)
open Syntax (UseState)

/-- The phase parameter describes one exposed outside owner. Other retained
    code is checked with the existing ticket-free callable summaries. -/
inductive FrameSource (operations : Operations) (policy : Syntax.TicketPolicy) (ticket : Ticket)
    (owner : Nat) (inside : ProtectionContracts.Context) :
    ExecFrame → UseState → Contract → UseState → Contract → Footprint → Prop where
  | plain (source : ContextDerives operations policy ticket inside environment plain.context before input after output row)
      (resolved : before = .available → after = .consumed → plain.scope.resolve ticket.binder = some owner) :
      FrameSource operations policy ticket owner inside (.plain plain) before input after output row
  | handler : FrameSource operations policy ticket owner inside (.handler handler) phase contract phase contract []
  | cell : FrameSource operations policy ticket owner inside (.cell identity payload scope answer) phase contract phase contract []
  | armed (callback : Summarizes operations environment action.action (.function .scalar .scalar latent) [])
      (exported : exportAt ticket inside phase (qualify true latent) = some row) :
      FrameSource operations policy ticket owner inside (.armed action) phase contract phase contract row
  | running (saved : Summarizes operations environment value contract []) :
      FrameSource operations policy ticket owner inside (.running action value closed) phase .scalar phase contract []
  | closing : FrameSource operations policy ticket owner inside (.closing identity scope) phase .scalar phase .scalar []
  | retiring : FrameSource operations policy ticket owner inside (.retiring other) phase .scalar phase .scalar []

/-- `fixed` lies beyond this segment and before the exposed owner. Keeping it
    explicit makes splitting and recomposition preserve interpretation order. -/
inductive Segment (operations : Operations) (policy : Syntax.TicketPolicy) (ticket : Ticket)
    (owner : Nat) (tables : Tables) (fixed : Stack) :
    Stack → UseState → Contract → UseState → Contract → Footprint → Prop where
  | nil : Segment operations policy ticket owner tables fixed .nil phase contract phase contract []
  | push (head : FrameSource operations policy ticket owner (contextOf tables (rest.append fixed))
        frame before input middle intermediate headRow)
      (tail : Segment operations policy ticket owner tables fixed rest middle intermediate after output tailRow) :
      Segment operations policy ticket owner tables fixed (.push frame rest) before input after output (headRow ++ tailRow)
  | spent (tail : Segment operations policy ticket owner tables fixed rest before input after output row) :
      Segment operations policy ticket owner tables fixed (.spent other answer caller rest) before input after output row

theorem frame_phase_monotone
    (source : FrameSource operations policy ticket owner inside frame before input after output row) :
    before = .consumed → after = .consumed := by
  cases source with
  | plain source resolved => exact ClauseProtectionFrames.context_phase_monotone source
  | handler | cell | armed | running | closing | retiring => exact id

theorem segment_phase_monotone
    (source : Segment operations policy ticket owner tables fixed segment before input after output row) :
    before = .consumed → after = .consumed := by
  induction source with
  | nil => exact id
  | push head tail ih => exact fun spent => ih (frame_phase_monotone head spent)
  | spent tail ih => exact ih

theorem segment_no_active_owner
    (source : Segment operations policy ticket owner tables fixed segment before input after output row) :
    activeTickets segment = [] := by
  induction source <;> simp_all [activeTickets]

theorem segment_fixed_context
    (source : Segment operations policy ticket owner tables fixed segment before input after output row)
    (same : contextOf tables fixed = contextOf tables replacement) :
    Segment operations policy ticket owner tables replacement segment before input after output row := by
  induction source with
  | nil => exact .nil
  | push head tail ih =>
      refine .push ?_ ih
      simpa only [ProtectionResiduals.context_append, same] using head
  | spent tail ih => exact .spent ih

section Composition

variable {front middle fixed : Stack}

theorem segment_append
    (first : Segment operations policy ticket owner tables (middle.append fixed) front before input phase intermediate firstRow)
    (second : Segment operations policy ticket owner tables fixed middle phase intermediate after output secondRow) :
    Segment operations policy ticket owner tables fixed (front.append middle) before input after output (firstRow ++ secondRow) := by
  induction first with
  | nil => exact second
  | push head tail ih =>
      simpa only [Stack.append, List.append_assoc] using
        Segment.push (by simpa only [stack_append_assoc] using head) (ih second)
  | spent tail ih => exact .spent (ih second)

theorem segment_decompose
    (source : Segment operations policy ticket owner tables fixed (front.append middle) before input after output row) :
    ∃ phase intermediate firstRow secondRow,
      Segment operations policy ticket owner tables (middle.append fixed) front before input phase intermediate firstRow ∧
      Segment operations policy ticket owner tables fixed middle phase intermediate after output secondRow ∧
      row = firstRow ++ secondRow := by
  induction front generalizing before input row with
  | nil => exact ⟨_, _, [], row, .nil, source, rfl⟩
  | push frame rest ih => cases source with
      | push head tail =>
          obtain ⟨phase, intermediate, firstRow, secondRow, first, second, same⟩ := ih tail
          exact ⟨phase, intermediate, _, secondRow,
            .push (by simpa only [stack_append_assoc] using head) first,
            second, by simp only [same, List.append_assoc]⟩
  | live owner input answer saved scope rest ihSaved ihRest => cases source
  | spent other answer caller rest ih => cases source with
      | spent tail =>
          obtain ⟨phase, intermediate, firstRow, secondRow, first, second, same⟩ := ih tail
          exact ⟨phase, intermediate, firstRow, secondRow, .spent first, second, same⟩

theorem capture_segment (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy ticket owner tables fixed whole before input after output row) :
    ∃ phase intermediate firstRow secondRow,
      Segment operations policy ticket owner tables (tail.append fixed) capture before input phase intermediate firstRow ∧
      Segment operations policy ticket owner tables fixed tail phase intermediate after output secondRow ∧
      row = firstRow ++ secondRow := by
  rw [handler_cut_reconstructs cut] at source
  exact segment_decompose source

/-- Source composition checks effects on each side of a split at the same
    outside context; each row already accounts for its local owner phase. -/
theorem checked_recompose
    (first : Segment operations policy ticket owner tables (middle.append fixed) front before input phase intermediate firstRow)
    (second : Segment operations policy ticket owner tables fixed middle phase intermediate after output secondRow)
    (left : checkFootprint outside firstRow = true) (right : checkFootprint outside secondRow = true) :
    Segment operations policy ticket owner tables fixed (front.append middle) before input after output (firstRow ++ secondRow) ∧
      checkFootprint outside (firstRow ++ secondRow) = true :=
  ⟨segment_append first second, by simp only [check_footprint_append, left, right, Bool.and_self]⟩

/-- A consuming source frame is tied to its actual lexical scope. Neutral
    retirement belongs to the segment and cannot masquerade as its outside owner. -/
theorem frame_protocol
    (source : FrameSource operations policy ticket owner inside frame before input after output row)
    (runtime : FrameDemand policy tickets frame demand)
    (separate : owner ∉ ownedTickets (.push frame .nil)) :
    OwnedPhaseRows.Protocol owner before after (demand.filter (· == owner)) := by
  cases source with
  | plain source resolved =>
      have monotone := ClauseProtectionFrames.context_phase_monotone source
      cases before <;> cases after
      · rw [PhaseFrameUsage.unchanged_frame_demand_empty source runtime]; exact .idle
      · rw [PhaseFrameUsage.consuming_frame_demand source runtime (resolved rfl rfl)]
        simpa using OwnedPhaseRows.Protocol.consume (owner := owner)
      · cases monotone rfl
      · rw [PhaseFrameUsage.unchanged_frame_demand_empty source runtime]; exact .idle
  | handler | cell | armed | running | closing => cases runtime; exact .idle
  | retiring =>
      cases runtime
      simp only [ownedTickets, List.mem_cons, List.not_mem_nil, or_false] at separate
      have different := Ne.symm separate
      simpa only [List.filter_cons, beq_iff_eq, different, ↓reduceIte, List.filter_nil] using
        OwnedPhaseRows.Protocol.idle (owner := owner) (phase := before)

theorem segment_protocol
    (source : Segment operations policy ticket owner tables fixed segment before input after output row)
    (runtime : StackUsage policy tickets segment outside demand)
    (separate : owner ∉ ownedTickets segment) :
    OwnedPhaseRows.Protocol owner before after (demand.filter (· == owner)) := by
  induction source generalizing demand with
  | nil => cases runtime; exact .idle
  | push head tail ih => cases runtime with
      | push frame accessible rest =>
          rw [OpenOwnerUses.frame_owned] at separate
          have first := frame_protocol head frame (fun member => separate (List.mem_append_left _ member))
          have second := ih rest (fun member => separate (List.mem_append_right _ member))
          simpa only [List.filter_append] using OwnedPhaseRows.protocol_compose first second
  | spent tail ih => cases runtime with
      | spent known scope rest => exact ih rest separate

theorem exposed_owner_consumed_once
    (source : Segment operations policy ticket owner tables fixed segment .available input .consumed output row)
    (runtime : StackUsage policy tickets segment outside demand)
    (separate : owner ∉ ownedTickets segment) : demand.filter (· == owner) = [owner] := by
  have protocol := segment_protocol source runtime separate
  generalize same : demand.filter (· == owner) = selected at protocol
  cases protocol
  rfl

theorem consumed_owner_is_external
    (source : Segment operations policy ticket owner tables fixed segment .available input .consumed output row)
    (interface : OpenOwnerUses.Interface policy tickets segment outside)
    (separate : owner ∉ ownedTickets segment) : owner ∈ interface.external := by
  apply OpenOwnerUses.external_member.mpr
  refine ⟨?_, separate⟩
  have present : owner ∈ interface.demand.filter (· == owner) := by
    rw [exposed_owner_consumed_once source interface.source separate]
    exact List.mem_cons_self
  exact (List.mem_filter.mp present).1

/-- The old disposal ownership test cannot admit a segment whose source must
    consume its outside owner, even if its physical close plan is empty. -/
theorem consuming_segment_not_disposable
    (source : Segment operations policy ticket owner tables fixed segment .available input .consumed output row)
    (interface : OpenOwnerUses.Interface policy tickets segment outside)
    (separate : owner ∉ ownedTickets segment) : ¬ InternalUses segment.erase.liveTickets segment.erase.pending :=
  OpenOwnerUses.outside_use_blocks_internal interface (consumed_owner_is_external source interface separate)

end Composition

/-- Current code and pending frames agree on the exposed owner's phase and
    full return contract. Source names are authenticated at consuming sites. -/
inductive Source (operations : Operations) (policy : Syntax.TicketPolicy) (ticket : Ticket)
    (owner : Nat) (tables : Tables) (fixed : Stack) (outside : ProtectionContracts.Context) :
    Scope → Code → Stack → UseState → UseState → Contract → Footprint → Prop where
  | checked (current : Derives operations policy ticket (contextOf tables (segment.append fixed))
        environment before code middle input currentRow)
      (resolved : before = .available → middle = .consumed → scope.resolve ticket.binder = some owner)
      (pending : Segment operations policy ticket owner tables fixed segment middle input after output remaining)
      (accepted : checkFootprint outside (currentRow ++ remaining) = true) :
      Source operations policy ticket owner tables fixed outside scope code segment before after output (currentRow ++ remaining)

theorem false_prefix_residual (inside : ProtectionContracts.Context) (row : Footprint) :
    residualize (.barrier false :: inside) row = residualize inside row := by
  simp [residualize, DisposalProtection.through_barrier, qualify]

theorem derives_false_prefix
    (source : Derives operations policy ticket inside environment before code after contract row) :
    Derives operations policy ticket (.barrier false :: inside) environment before code after contract row :=
  CleanupProtection.inside_congr source (fun demands => (false_prefix_residual inside demands).symm)

theorem source_focus
    (source : Source operations policy ticket owner tables fixed outside plain.scope whole segment before after output row)
    (focus : Focus whole child plain.context) :
    Source operations policy ticket owner tables fixed outside plain.scope child (.push (.plain plain) segment)
      before after output row := by
  cases source with
  | checked current resolved pending accepted =>
      obtain ⟨middle, input, childRow, remainder, childSource, context, same⟩ :=
        ClauseProtectionFrames.focus_decompose current focus
      rw [same, List.append_assoc] at accepted ⊢
      refine .checked (derives_false_prefix childSource) ?_ (.push (.plain context ?_) pending) accepted
      · intro available consumed
        exact resolved available (ClauseProtectionFrames.context_phase_monotone context consumed)
      · intro available consumed
        have initial : before = .available := by
          cases before
          · rfl
          · have impossible := ClauseProtection.phase_monotone childSource rfl
            rw [available] at impossible
            cases impossible
        exact resolved initial consumed

theorem source_return
    (source : Source operations policy ticket owner tables fixed outside scope value segment before after output row)
    (isValue : value.IsValue) :
    ∃ environment input, Summarizes operations environment value input [] ∧
      Segment operations policy ticket owner tables fixed segment before input after output row ∧
      checkFootprint outside row = true := by
  cases source with
  | checked current resolved pending accepted =>
      obtain ⟨summary, same, empty⟩ := ClauseProtection.value_summary current isValue
      cases same
      subst_vars
      exact ⟨_, _, summary, pending, accepted⟩

theorem source_current_request
    (source : Source operations policy ticket owner tables fixed (contextOf tables tail) scope
      (.perform effect operation operand) segment before after output row)
    (boundary : PhaseBoundaries.Boundary ticket owner before base tail answer)
    (isValue : operand.IsValue) :
    ∃ environment input remaining,
      CallableProtectionFrames.Checked operations tables environment ((segment.append fixed).append base)
        (.perform effect operation operand) input ∧
      Segment operations policy ticket owner tables fixed segment before input after output remaining ∧
      checkFootprint (contextOf tables tail) remaining = true := by
  cases source with
  | checked current resolved pending accepted =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      obtain ⟨same, checked⟩ := PhaseBoundaries.request_checked boundary current accepted.1 isValue
      cases same
      exact ⟨_, _, _, checked, pending, accepted.2⟩

theorem source_plug
    (source : Source operations policy ticket owner tables fixed outside scope value (.push (.plain plain) segment)
      before after output row) (closed : ClosedValue value) :
    Source operations policy ticket owner tables fixed outside plain.scope (plain.context.plug value) segment
      before after output row := by
  obtain ⟨environment, input, summary, pending, accepted⟩ := source_return source closed.1
  cases pending with
  | push head rest => cases head with
      | plain context resolved =>
          have current := ClauseProtectionFrames.context_plug context
            (Derives.stable (outside := []) (CallableProtection.closed_value_environment summary closed _)
              (by simp [exportAt, residual_empty]))
          simpa only [List.nil_append] using Source.checked current resolved rest accepted

theorem source_bind
    (source : Source operations policy ticket owner tables fixed outside scope (.bind parameter value body) segment
      before after output row) (closed : ClosedValue value) :
    Source operations policy ticket owner tables fixed outside scope (body.subst parameter value) segment
      before after output row := by
  cases source with
  | checked current resolved pending accepted =>
      exact .checked (ClauseProtection.bind_summary current closed) resolved pending accepted

theorem application_values_phase
    (source : Derives operations policy ticket inside environment before (.app function argument) after contract row)
    (functionValue : function.IsValue) (argumentValue : argument.IsValue) : before = after := by
  cases source with
  | stable => rfl
  | app function argument exported =>
      exact (ClauseProtection.value_summary function functionValue).2.1.trans
        (ClauseProtection.value_summary argument argumentValue).2.1

theorem source_beta
    (source : Source operations policy ticket owner tables fixed outside scope (.app (.lambda parameter body) value) segment
      before after output row) (closed : ClosedValue value) :
    Source operations policy ticket owner tables fixed outside .none (body.subst parameter value) segment
      before after output row := by
  cases source with
  | checked current resolved pending accepted =>
      have same := application_values_phase current (by trivial) closed.1
      cases same
      exact .checked (ClauseProtection.beta_summary current closed)
        (by intro first second; cases first; cases second) pending accepted

theorem source_branch
    (source : Source operations policy ticket owner tables fixed outside scope (.branch (.boolean choice) yes no) segment
      before after output row) :
    ∃ selectedRow, Source operations policy ticket owner tables fixed outside scope (if choice then yes else no) segment
      before after output selectedRow := by
  cases source with
  | checked current resolved pending accepted =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      obtain ⟨selectedRow, selected, admitted⟩ := ClauseProtectionFrames.selected_branch current accepted.1
      exact ⟨_, .checked selected resolved pending
        (by simp only [check_footprint_append, admitted, accepted.2, Bool.and_self])⟩

theorem source_handler_return
    (source : Source operations policy ticket owner tables fixed outside scope value (.push (.handler handler) segment)
      before after output row) (closed : ClosedValue value) :
    Source operations policy ticket owner tables fixed outside handler.scope value segment before after output row := by
  obtain ⟨environment, input, summary, pending, accepted⟩ := source_return source closed.1
  cases pending with
  | push head rest => cases head with
      | handler =>
          exact .checked (.stable summary (by simp [exportAt, residual_empty]))
            (by intro first second; cases first; cases second) rest accepted

theorem source_start_cleanup
    (source : Source operations policy ticket owner tables fixed outside scope value (.push (.armed action) segment)
      before after output row) (closed : ClosedValue value) :
    Source operations policy ticket owner tables fixed outside .none (.app action.action .unit)
      (.push (.running action value closed) segment) before after output row := by
  obtain ⟨environment, input, summary, pending, accepted⟩ := source_return source closed.1
  cases pending with
  | push head rest => cases head with
      | armed callback exported =>
          refine .checked (.stable (Summarizes.app callback Summarizes.unit) ?_)
            (by intro first second; cases first; cases second) (.push (.running summary) rest) ?_
          · simpa only [Stack.append, contextOf, CallableProtectionFrames.pushContext,
              ProtectionContexts.frameProtected, ExecFrame.erase, ActionData.erase,
              exportAt, ClauseProtection.phaseContext, List.cons_append, residualize,
              DisposalProtection.through_barrier, List.nil_append, List.append_nil] using exported
          · simpa only [List.nil_append] using accepted

theorem source_finish_cleanup
    (source : Source operations policy ticket owner tables fixed outside scope .unit
      (.push (.running action saved closed) segment) before after output row) :
    Source operations policy ticket owner tables fixed outside action.scope saved segment before after output row := by
  obtain ⟨environment, input, summary, pending, accepted⟩ := source_return source (by trivial)
  cases pending with
  | push head rest => cases head with
      | running savedSource =>
          exact .checked (.stable savedSource (by simp [exportAt, residual_empty]))
            (by intro first second; cases first; cases second) rest accepted

section Restoration

variable {segment fixed : Stack} {issued completed : List Owner}

/-- A spent caller boundary has no interpretation layer. The exposed outside
    owner's phase is retained across restoration of the captured segment. -/
theorem restore_spent
    (source : Segment operations policy ticket owner tables fixed segment before input after output row) :
    Segment operations policy ticket owner tables fixed
      (segment.append (.spent consumed answer caller .nil)) before input after output row := by
  have inside := segment_fixed_context source (replacement := (Stack.spent consumed answer caller .nil).append fixed) rfl
  simpa only [List.append_nil] using segment_append inside (Segment.spent Segment.nil)

theorem focus_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨whole, scope, (segment.append fixed).append base⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy ticket owner tables fixed (contextOf tables outside) scope whole segment
      phase finalPhase output row)
    (boundary : PhaseBoundaries.Boundary ticket owner phase base outside ownerAnswer)
    (focus : Focus whole child context) :
    ∃ plain : PlainData, plain.context = context ∧ plain.scope = scope ∧
      let initial : NamedState := ⟨⟨⟨whole, scope, (segment.append fixed).append base⟩, issued, completed⟩, activations⟩
      let next := ScopedPortJoint.advanceState initial
        ⟨child, scope, ((Stack.push (.plain plain) segment).append fixed).append base⟩ [] []
      NamedAccessStep ambient initial next ∧
      CompletionJoint.Valid declarations policy registry ambient next result outgoing bound ∧
      PhaseBoundaries.Boundary ticket owner phase base outside ownerAnswer ∧
      Source operations policy ticket owner tables fixed (contextOf tables outside) scope child (.push (.plain plain) segment)
        phase finalPhase output row := by
  obtain ⟨plain, shape, saved, step, nextValid⟩ := CompletionJoint.focus_preserves valid focus
  refine ⟨plain, shape, saved, step, nextValid, boundary, ?_⟩
  have focused := source_focus (plain := plain) (saved ▸ source) (shape ▸ focus)
  exact saved ▸ focused

theorem plug_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, ((Stack.push (.plain plain) segment).append fixed).append base⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy ticket owner tables fixed (contextOf tables outside) scope value
      (.push (.plain plain) segment) phase finalPhase output row)
    (boundary : PhaseBoundaries.Boundary ticket owner phase base outside ownerAnswer)
    (isValue : value.IsValue) :
    let initial : NamedState := ⟨⟨⟨value, scope, ((Stack.push (.plain plain) segment).append fixed).append base⟩,
      issued, completed⟩, activations⟩
    let next := ScopedPortJoint.advanceState initial
      ⟨plain.context.plug value, plain.scope, (segment.append fixed).append base⟩ [] []
    NamedAccessStep ambient initial next ∧
      CompletionJoint.Valid declarations policy registry ambient next result outgoing bound ∧
      PhaseBoundaries.Boundary ticket owner phase base outside ownerAnswer ∧
      Source operations policy ticket owner tables fixed (contextOf tables outside) plain.scope
        (plain.context.plug value) segment phase finalPhase output row := by
  obtain ⟨step, nextValid⟩ := CompletionJoint.plug_preserves valid isValue
  exact ⟨step, nextValid, boundary, source_plug source (CompletionJoint.current_closed_value valid isValue)⟩

/-- Both segments are checked in their actual future suffix. The saved
    segment's return phase and full contract feed the waiting caller. -/
theorem restore_recompose {waiting : Stack}
    (savedSource : Segment operations policy ticket owner tables
      (waiting.append (.spent consumed answer caller fixed)) segment phase input middle intermediate savedRow)
    (waitingSource : Segment operations policy ticket owner tables (.spent consumed answer caller fixed)
      waiting middle intermediate finalPhase output waitingRow) :
    Segment operations policy ticket owner tables fixed
      (segment.append (waiting.append (.spent consumed answer caller .nil))) phase input finalPhase output
      (savedRow ++ waitingRow) := by
  have waitingAtFixed := segment_fixed_context waitingSource (replacement := fixed) rfl
  have restored := restore_spent (consumed := consumed) (answer := answer) (caller := caller) waitingAtFixed
  have savedAtRestored := segment_fixed_context savedSource
    (replacement := (waiting.append (.spent consumed answer caller .nil)).append fixed) (by
      simp only [ProtectionResiduals.context_append, contextOf, List.append_nil])
  exact segment_append savedAtRestored restored

theorem restore_joint {waiting : Stack}
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, waiting.append (.live consumed operationResult answer segment caller (fixed.append base))⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (resolved : scope.resolve binder = some consumed) (isValue : value.IsValue)
    (boundary : PhaseBoundaries.Boundary ticket owner phase base outside ownerAnswer)
    (savedSource : Segment operations policy ticket owner tables
      (waiting.append (.spent consumed answer caller fixed)) segment phase input middle intermediate savedRow)
    (waitingSource : Segment operations policy ticket owner tables (.spent consumed answer caller fixed)
      waiting middle intermediate finalPhase output waitingRow) :
    let before : NamedState := ⟨⟨⟨.resume binder value, scope,
      waiting.append (.live consumed operationResult answer segment caller (fixed.append base))⟩,
      issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, scope,
      segment.append (waiting.append (.spent consumed answer caller (fixed.append base)))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket consumed]) ∧
    CompletionJoint.Valid declarations policy registry ambient
      (ScopedPortJoint.advanceState before after [] [.ticket consumed]) result outgoing bound ∧
    Segment operations policy ticket owner tables fixed
      (segment.append (waiting.append (.spent consumed answer caller .nil))) phase input finalPhase output
      (savedRow ++ waitingRow) ∧
    ∀ demands, checkFootprint
      (ClauseProtection.phaseContext ticket
        (contextOf tables ((segment.append (waiting.append (.spent consumed answer caller .nil))).append fixed)) phase ++
        contextOf tables outside) demands = checkFootprint (contextOf tables after.stack) demands := by
  obtain ⟨step, preserved⟩ := CompletionJoint.resume_preserves (front := waiting) valid resolved isValue
  refine ⟨step, preserved, restore_recompose savedSource waitingSource, ?_⟩
  intro demands
  simpa only [stack_append_assoc, Stack.append] using
    PhaseBoundaries.boundary_check (tables := tables)
      (front := (segment.append (waiting.append (.spent consumed answer caller .nil))).append fixed) (row := demands) boundary

end Restoration
namespace Examples

open OpenOwnerUses.Examples (operations policy tickets tables callTicket waiting localHandler capture saved)

/-- This is the same open capture rejected by the preceding closed row system. -/
theorem open_segment : Segment operations policy callTicket 9 tables .nil capture
    .available .scalar .consumed .scalar [] :=
  .push (.plain OpenOwnerUses.Examples.waiting_source (by intro _ _; rfl)) (.push .handler .nil)

theorem open_saved_rows : SavedFrameRequirements.Rows operations tables saved [] := by
  have head : CallableProtectionFrames.ContextSummarizes operations CallableProtection.Environment.empty
      OpenOwnerUses.Examples.return17.context .scalar .scalar [] := .bind .integer
  exact .push (.plain head) rfl (.push .handler rfl .nil)

theorem open_saved_interface : CaptureInterfaces.Interface operations tables saved [] (some []) :=
  .closable open_saved_rows rfl .nil

theorem outside_use_from_source : 9 ∈ OpenOwnerUses.Examples.interface.external :=
  consumed_owner_is_external open_segment OpenOwnerUses.Examples.interface (by decide)

theorem outside_consumption_exact : OpenOwnerUses.Examples.interface.demand.filter (· == 9) = [9] :=
  exposed_owner_consumed_once open_segment OpenOwnerUses.Examples.captured_usage (by decide)

theorem discard_rejected_from_source : ¬ InternalUses capture.erase.liveTickets capture.erase.pending :=
  consuming_segment_not_disposable open_segment OpenOwnerUses.Examples.interface (by decide)

theorem request_source : Source operations policy callTicket 9 tables .nil [] (.ticket 10 9)
    OpenOwnerUses.Examples.request capture .available .consumed .scalar [] := by
  have current : Derives operations policy callTicket (contextOf tables (capture.append .nil))
      CallableProtection.Environment.empty .available OpenOwnerUses.Examples.request .available .scalar [] := by
    unfold OpenOwnerUses.Examples.request
    have operand : Derives operations policy callTicket (contextOf tables (capture.append .nil))
        CallableProtection.Environment.empty .available .unit .available .scalar [] := .stable .unit rfl
    exact .perform (requestRow := []) rfl operand rfl
  exact .checked current (by intro _ impossible; cases impossible) open_segment rfl

theorem request_checked_at_actual_stack :
    ∃ environment input remaining,
      CallableProtectionFrames.Checked operations tables environment OpenOwnerUses.Examples.whole
        OpenOwnerUses.Examples.request input ∧
      Segment operations policy callTicket 9 tables .nil capture .available input .consumed .scalar remaining ∧
      checkFootprint [] remaining = true :=
  source_current_request (effect := Instantiation.freezeEffect OpenOwnerUses.Examples.handled)
    (operand := .unit) (base := OpenOwnerUses.Examples.tail) (tail := .nil)
    request_source (PhaseBoundaries.Boundary.live rfl) trivial

theorem restored_open_segment : Segment operations policy callTicket 9 tables .nil
    (capture.append (.spent 19 .integer (.ticket 10 9) .nil)) .available .scalar .consumed .scalar [] :=
  restore_spent open_segment

theorem restored_actual_shape : OpenOwnerUses.Examples.afterResume.stack =
    (capture.append (.spent 19 .integer (.ticket 10 9) .nil)).append OpenOwnerUses.Examples.tail := by
  rw [stack_append_assoc]
  rfl

/-- Effects after resumption use the consumed phase. The saved running cleanup
    is separately retained in the actual restored context until it completes. -/
def protectedTicket : Ticket := CaptureInterfaces.ticketFor OwnerPhases.Examples.capture [] none 10 .scalar .scalar

theorem protected_saved_interface : CaptureInterfaces.Interface operations tables OwnerPhases.Examples.capture [] none :=
  .protectedCapture (.push (.running (environment := CallableProtection.Environment.empty) .integer) rfl .nil) rfl

def laterRequest : Code := .perform (Instantiation.freezeEffect (.user 71 [])) 0 .unit
def laterBody : Code := .bind 5 (.resume 10 .unit) laterRequest
def laterFrame : PlainData := ⟨.bind 4 laterBody, .ticket 10 9, .unit, .integer, [9], rfl⟩
def laterCapture : Stack := .push (.plain laterFrame) (.push (.handler localHandler) .nil)
def laterRow : Footprint := [⟨.user 71 [], 0, false⟩]
def earlyRow : Footprint := [⟨.user 71 [], 0, true⟩]

theorem later_frame_source : ContextDerives operations policy protectedTicket
    (contextOf tables (.push (.handler localHandler) .nil)) CallableProtection.Environment.empty
    laterFrame.context .available .scalar .consumed .scalar laterRow := by
  let inside := contextOf tables (.push (.handler localHandler) .nil)
  let environment := CallableProtection.Environment.empty.extend 4 .scalar
  have unitAt (env : CallableProtection.Environment) (phase : UseState) :
      Derives operations policy protectedTicket inside env phase .unit phase .scalar [] := .stable .unit rfl
  have resumed : Derives operations policy protectedTicket inside environment .available
      (.resume 10 .unit) .consumed .scalar [] := .resume rfl (unitAt _ _) rfl
  have later : Derives operations policy protectedTicket inside (environment.extend 5 .scalar) .consumed
      laterRequest .consumed .scalar laterRow := .perform (requestRow := laterRow) rfl (unitAt _ _) rfl
  exact .bind (.bind resumed later)

theorem later_segment : Segment operations policy protectedTicket 9 tables .nil laterCapture
    .available .scalar .consumed .scalar laterRow := by
  simpa only [List.append_nil, laterCapture] using Segment.push (.plain later_frame_source (by intro _ _; rfl))
    (Segment.push FrameSource.handler Segment.nil)

theorem later_effect_accepted : checkFootprint (contextOf OwnerPhases.Examples.tables OwnerPhases.Examples.tail) laterRow = true := by decide

theorem earlier_effect_rejected : checkFootprint (contextOf OwnerPhases.Examples.tables OwnerPhases.Examples.tail) earlyRow = false := by decide

theorem earlier_effect_export : exportAt protectedTicket (contextOf tables (.push (.handler localHandler) .nil))
    .available laterRow = some earlyRow := rfl

theorem later_effect_export : exportAt protectedTicket (contextOf tables (.push (.handler localHandler) .nil))
    .consumed laterRow = some laterRow := rfl

end Examples

end Ash.OneShot.OpenPhaseSegments

#print axioms Ash.OneShot.OpenPhaseSegments.frame_phase_monotone
#print axioms Ash.OneShot.OpenPhaseSegments.segment_phase_monotone
#print axioms Ash.OneShot.OpenPhaseSegments.segment_no_active_owner
#print axioms Ash.OneShot.OpenPhaseSegments.segment_fixed_context
#print axioms Ash.OneShot.OpenPhaseSegments.segment_append
#print axioms Ash.OneShot.OpenPhaseSegments.segment_decompose
#print axioms Ash.OneShot.OpenPhaseSegments.capture_segment
#print axioms Ash.OneShot.OpenPhaseSegments.checked_recompose
#print axioms Ash.OneShot.OpenPhaseSegments.frame_protocol
#print axioms Ash.OneShot.OpenPhaseSegments.segment_protocol
#print axioms Ash.OneShot.OpenPhaseSegments.exposed_owner_consumed_once
#print axioms Ash.OneShot.OpenPhaseSegments.consumed_owner_is_external
#print axioms Ash.OneShot.OpenPhaseSegments.consuming_segment_not_disposable
#print axioms Ash.OneShot.OpenPhaseSegments.false_prefix_residual
#print axioms Ash.OneShot.OpenPhaseSegments.derives_false_prefix
#print axioms Ash.OneShot.OpenPhaseSegments.source_focus
#print axioms Ash.OneShot.OpenPhaseSegments.source_return
#print axioms Ash.OneShot.OpenPhaseSegments.source_current_request
#print axioms Ash.OneShot.OpenPhaseSegments.source_plug
#print axioms Ash.OneShot.OpenPhaseSegments.source_bind
#print axioms Ash.OneShot.OpenPhaseSegments.application_values_phase
#print axioms Ash.OneShot.OpenPhaseSegments.source_beta
#print axioms Ash.OneShot.OpenPhaseSegments.source_branch
#print axioms Ash.OneShot.OpenPhaseSegments.source_handler_return
#print axioms Ash.OneShot.OpenPhaseSegments.source_start_cleanup
#print axioms Ash.OneShot.OpenPhaseSegments.source_finish_cleanup
#print axioms Ash.OneShot.OpenPhaseSegments.restore_spent
#print axioms Ash.OneShot.OpenPhaseSegments.focus_joint
#print axioms Ash.OneShot.OpenPhaseSegments.plug_joint
#print axioms Ash.OneShot.OpenPhaseSegments.restore_recompose
#print axioms Ash.OneShot.OpenPhaseSegments.restore_joint
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.open_segment
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.open_saved_rows
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.open_saved_interface
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.outside_use_from_source
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.outside_consumption_exact
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.discard_rejected_from_source
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.request_source
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.request_checked_at_actual_stack
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.restored_open_segment
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.restored_actual_shape
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.protected_saved_interface
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.later_frame_source
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.later_segment
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.later_effect_accepted
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.earlier_effect_rejected
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.earlier_effect_export
#print axioms Ash.OneShot.OpenPhaseSegments.Examples.later_effect_export
