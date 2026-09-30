import Substitution

/-!
Typed operation dispatch connects actual handler selection, annotated stack
ports, independently checked clause usage, and the new runtime ticket scope.
These are transition-local results. Source admission of every reachable cut,
residual effect contracts of saved control, and full machine preservation remain
separate obligations.
-/

namespace Ash.OneShot.Typing
open Syntax Execution

/-- A selected executable handler fixes the cut's answer port. The answer is
    derived from the actual boundary, not an independently supplied witness. -/
theorem handler_cut_ports
    (cut : HandlerCut requested whole cap tail handler)
    (ports : Fits whole.erase input result) :
    Fits cap.erase input handler.answer ∧ Fits tail.erase handler.answer result := by
  induction cut generalizing input result with
  | hit handler tail same =>
      cases ports with
      | push _ _ _ next => exact ⟨.push _ _ _ (.nil _), next⟩
  | push frame rest cap tail handler miss next ih =>
      cases ports with
      | push _ _ _ restPorts =>
          obtain ⟨saved, outside⟩ := ih restPorts
          exact ⟨.push _ _ _ saved, outside⟩
  | live ticket q a saved scope rest cap tail handler next ih =>
      cases ports with
      | live _ _ _ _ _ _ savedPorts restPorts =>
          obtain ⟨inside, outside⟩ := ih restPorts
          exact ⟨.live _ _ _ _ _ _ savedPorts inside, outside⟩
  | spent ticket a scope rest cap tail handler next ih =>
      cases ports with
      | spent _ _ _ _ restPorts =>
          obtain ⟨inside, outside⟩ := ih restPorts
          exact ⟨.spent _ _ _ _ inside, outside⟩

theorem handler_cut_instance (cut : HandlerCut requested whole cap tail handler) :
    handler.effectInst = requested := by
  induction cut with
  | hit handler tail same => exact same
  | push frame rest cap tail handler miss next ih => exact ih
  | live ticket q a saved scope rest cap tail handler next ih => exact ih
  | spent ticket a scope rest cap tail handler next ih => exact ih

theorem selected_clause_usage
    (selected : ClauseAt operation clauses parameter binder body)
    (checked : ClausesUse policy clauses) :
    Uses policy (.ticket binder (policy binder)) .available body .consumed := by
  induction selected with
  | hit => cases checked with
      | cons body rest => exact body
  | pass different next ih => cases checked with
      | cons body rest => exact ih rest

theorem selected_clause_substitution_usage
    (selected : ClauseAt operation clauses parameter binder body)
    (checked : ClausesUse policy clauses)
    (operandUse : Uses policy useScope before operand after)
    (closed : ClosedValue operand) :
    Uses policy (.ticket binder (policy binder)) .available
      (body.subst parameter operand) .consumed :=
  usage_substitution (selected_clause_usage selected checked) closed.1
    (value_use_transport closed.1 operandUse .none .available) parameter

/-- Static type and usage scopes name the same lexical binder. Runtime scope
    maps that binder to a dynamic owner. This relation does not certify the
    saved continuation's effects or its disposal plan. -/
inductive ScopeAgreement : TicketType → UseScope → Scope → Prop where
  | none : ScopeAgreement .none .none .none
  | bound : ScopeAgreement (.bound binder input answer residual closing)
      (.ticket binder rights) (.ticket binder owner)

theorem scope_agreement_resolves
    (agreement : ScopeAgreement (.bound binder input answer residual closing) useScope scope) :
    ∃ rights owner, useScope = .ticket binder rights ∧
      scope = .ticket binder owner ∧ scope.resolve binder = some owner := by
  cases agreement
  exact ⟨_, _, rfl, rfl, by simp [Scope.resolve]⟩

/-- The static binder and protocol state refer to an actual active clause
    boundary with matching ports. Prefixes may contain other live or spent
    clauses; dormant captures are not searched. Effects remain contracts to be
    validated by a future whole-stack typing judgment. -/
inductive TicketBinding : TicketType → UseScope → Scope → UseState → Stack → Prop where
  | none : TicketBinding .none .none .none .available stack
  | live {front saved tail : Stack} {callerScope : Scope} :
      TicketBinding (.bound binder input answer residual closing)
      (.ticket binder rights) (.ticket binder owner) .available
      (front.append (.live owner input answer saved callerScope tail))
  | spent {front tail : Stack} {callerScope : Scope} :
      TicketBinding (.bound binder input answer residual closing)
      (.ticket binder rights) (.ticket binder owner) .consumed
      (front.append (.spent owner answer callerScope tail))

theorem ticket_binding_scope
    (binding : TicketBinding ticket useScope scope state stack) :
    ScopeAgreement ticket useScope scope := by
  cases binding with
  | none => exact .none
  | live | spent => exact .bound

/-- Entry installs a live owner with the same input/answer ports as the static
    ticket. Lexical binder and dynamic owner need not have the same numeral. -/
theorem capture_ticket_binding :
    TicketBinding (.bound binder input answer residual closing)
      (.ticket binder rights) (.ticket binder owner) .available
      (.live owner input answer saved callerScope tail) :=
  .live (front := .nil)

/-- Include dormant clause occurrences and retirement names when checking
    uniqueness. Retirement is marked consumed here only as a name occurrence;
    it does not provide a TicketBinding or complete its outstanding owner. -/
def _root_.Ash.OneShot.Control.ticketStates : Control → List (Nat × UseState)
  | .nil => []
  | .push frame rest =>
      (match frame.kind with | .retiring owner => [(owner, .consumed)] | _ => []) ++ rest.ticketStates
  | .live owner _ _ saved rest => (owner, .available) :: (saved.ticketStates ++ rest.ticketStates)
  | .spent owner _ rest => (owner, .consumed) :: rest.ticketStates

theorem ticket_states_names (control : Control) :
    control.ticketStates.map Prod.fst = control.ticketNames := by
  induction control with
  | nil => rfl
  | push frame rest ih =>
      cases kind : frame.kind <;> simp_all [Control.ticketStates, Control.ticketNames]
  | live owner input answer saved rest ihSaved ihRest =>
      simp [Control.ticketStates, Control.ticketNames, ihSaved, ihRest]
  | spent owner answer rest ih => simp [Control.ticketStates, Control.ticketNames, ih]

theorem ticket_states_append (front tail : Control) :
    (front.append tail).ticketStates = front.ticketStates ++ tail.ticketStates := by
  induction front with
  | nil => rfl
  | push frame rest ih => simp [Control.append, Control.ticketStates, ih, List.append_assoc]
  | live owner input answer saved rest ihSaved ihRest =>
      simp [Control.append, Control.ticketStates, ihRest, List.append_assoc]
  | spent owner answer rest ih => simp [Control.append, Control.ticketStates, ih]

theorem ticket_binding_occurs
    (binding : TicketBinding ticket useScope (.ticket binder owner) state stack) :
    (owner, state) ∈ stack.erase.ticketStates := by
  cases binding with
  | live => simp [erase_append, Stack.erase, ticket_states_append, Control.ticketStates]
  | spent => simp [erase_append, Stack.erase, ticket_states_append, Control.ticketStates]

theorem unique_ticket_state_in_list {entries : List (Nat × UseState)}
    (names : (entries.map Prod.fst).Nodup)
    (left : (owner, state) ∈ entries) (right : (owner, otherState) ∈ entries) :
    state = otherState := by
  induction entries with
  | nil => cases left
  | cons entry entries ih =>
      have split := List.nodup_cons.mp names
      rcases List.mem_cons.mp left with same | later
      · subst entry
        rcases List.mem_cons.mp right with same | later
        · exact (Prod.mk.inj same).2.symm
        · exact False.elim (split.1 (List.mem_map.mpr ⟨_, later, rfl⟩))
      · rcases List.mem_cons.mp right with same | otherLater
        · subst entry
          exact False.elim (split.1 (List.mem_map.mpr ⟨_, later, rfl⟩))
        · exact ih split.2 later otherLater

/-- The name component of the existing control invariant turns occurrence
    correspondence into an exclusive protocol state for a runtime owner. -/
theorem ticket_binding_state_unique
    (names : stack.erase.ticketNames.Nodup)
    (left : TicketBinding ticket useScope (.ticket binder owner) state stack)
    (right : TicketBinding otherTicket otherUse (.ticket otherBinder owner) otherState stack) :
    state = otherState :=
  unique_ticket_state_in_list (by simpa only [ticket_states_names] using names)
    (ticket_binding_occurs left) (ticket_binding_occurs right)

theorem spent_binding_blocks_available
    (names : stack.erase.ticketNames.Nodup)
    (spent : TicketBinding ticket useScope (.ticket binder owner) .consumed stack) :
    ¬ TicketBinding otherTicket otherUse (.ticket otherBinder owner) .available stack := by
  intro available
  have impossible := ticket_binding_state_unique names spent available
  cases impossible

/-- Independently supplied type and usage checks agree on a concrete capture
    transition. Operation result, clause answer and ticket binder are derived
    from the operation signature, actual boundary and selected clause. -/
theorem capture_instantiates_clause
    (cut : HandlerCut requested whole cap tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (requestType : signature requested operation = some (input, output))
    (clausesTyped : ClausesTyped signature environment handler.effectInst handler.answer residual handler.clauses)
    (clausesUsed : ClausesUse policy handler.clauses)
    (operandTyped : Typed signature environment oldTicket allowed operand input)
    (operandUsed : Uses policy oldUse before operand after)
    (closed : ClosedValue operand)
    (ready : ClosedExcept parameter body) (fresh : ResourceFresh operand body)
    (ports : Fits whole.erase output result) :
    RawStep ⟨.perform requested operation operand, scope, whole⟩
      ⟨body.subst parameter operand, .ticket binder owner,
        .live owner output handler.answer cap handler.scope tail⟩ [.ticket owner] [] ∧
    Typed signature environment (.bound binder output handler.answer residual residual) residual
      (body.subst parameter operand) handler.answer ∧
    Uses policy (.ticket binder (policy binder)) .available
      (body.subst parameter operand) .consumed ∧
    ScopeAgreement (.bound binder output handler.answer residual residual)
      (.ticket binder (policy binder)) (.ticket binder owner) ∧
    Fits (Stack.live owner output handler.answer cap handler.scope tail).erase handler.answer result := by
  have known : signature handler.effectInst operation = some (input, output) := by
    rw [handler_cut_instance cut]
    exact requestType
  obtain ⟨savedPorts, outsidePorts⟩ := handler_cut_ports cut ports
  exact ⟨.capture requested operation parameter binder owner operand body scope whole cap tail handler
      output cut selected closed ready fresh,
    selected_clause_substitution_typed selected clausesTyped known operandTyped closed,
    selected_clause_substitution_usage selected clausesUsed operandUsed closed,
    .bound, .live _ _ _ _ _ _ savedPorts outsidePorts⟩

/-- Type support at the actual boundary supplies the capture payload check.
    This includes callable payloads with retained resources absent from the
    effect instance; no global instance-bounded signature restriction is used. -/
theorem capture_access_from_types
    (cut : HandlerCut requested whole cap tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (operandTyped : Typed signature environment oldTicket allowed operand input)
    (closed : ClosedValue operand)
    (boundary : input.resources ⊆ tail.erase.visible ++ ambient)
    (support : Supported whole.erase ambient) :
    AccessValid ⟨body.subst parameter operand, .ticket binder owner,
      .live owner output handler.answer cap handler.scope tail⟩ ambient := by
  have provider := selected_handler_access cut support
  constructor
  · exact capture_preserves_support (sourceCut_is_cut (handler_cut_erases cut)) support
  · intro resource retained
    have bound := substitution_bound_for_closed_value body parameter closed
      (mem_resourceDependencies.mp retained)
    rcases List.mem_append.mp bound with fromBody | fromOperand
    · apply provider
      exact List.mem_append_right _ (mem_resourceDependencies.mpr
        (clause_resource_retained selected (mem_without.mp fromBody).1))
    · exact typed_payload_at_boundary operandTyped closed boundary
        (mem_resourceDependencies.mpr fromOperand)

/-- A covered request has an actual fresh capture step, with typed and
    usage-checked clause entry, derived ports, supported retained resources and
    the lifetime ledger. Hygiene is still supplied for selected administrative
    bodies; the theorem does not infer all future capture or close contracts. -/
theorem typed_capture_step
    (cut : HandlerCut requested whole cap tail handler)
    (requestType : signature requested operation = some (input, output))
    (clausesTyped : ClausesTyped signature environment handler.effectInst handler.answer residual handler.clauses)
    (clausesUsed : ClausesUse policy handler.clauses)
    (covered : Covers signature handler.effectInst handler.clauses)
    (operandTyped : Typed signature environment oldTicket allowed operand input)
    (operandUsed : Uses policy oldUse before operand after)
    (closed : ClosedValue operand)
    (hygiene : ∀ parameter binder body, ClauseAt operation handler.clauses parameter binder body →
      ClosedExcept parameter body ∧ ResourceFresh operand body)
    (ports : Fits whole.erase output result)
    (support : Supported whole.erase ambient)
    (boundary : input.resources ⊆ tail.erase.visible ++ ambient)
    (ledger : Ledger ⟨whole.erase, issued, completed⟩)
    (freshOwner : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ parameter binder body,
      ClauseAt operation handler.clauses parameter binder body ∧
      let next : RunState := ⟨⟨body.subst parameter operand, .ticket binder owner,
        .live owner output handler.answer cap handler.scope tail⟩,
        issued ++ [.ticket owner], completed⟩
      RunStep ⟨⟨.perform requested operation operand, scope, whole⟩, issued, completed⟩ next ∧
      Typed signature environment (.bound binder output handler.answer residual residual) residual
        next.configuration.expression handler.answer ∧
      Uses policy (.ticket binder (policy binder)) .available next.configuration.expression .consumed ∧
      TicketBinding (.bound binder output handler.answer residual residual)
        (.ticket binder (policy binder)) next.configuration.scope .available next.configuration.stack ∧
      Fits next.configuration.stack.erase handler.answer result ∧
      AccessValid next.configuration ambient ∧ Ledger next.erase := by
  have known : signature handler.effectInst operation = some (input, output) := by
    rw [handler_cut_instance cut]
    exact requestType
  obtain ⟨parameter, binder, body, selected⟩ := covered_operation_selects_clause covered known
  obtain ⟨ready, fresh⟩ := hygiene parameter binder body selected
  obtain ⟨raw, typed, used, _, nextPorts⟩ :=
    capture_instantiates_clause (owner := owner) (scope := scope) cut selected requestType
      clausesTyped clausesUsed operandTyped operandUsed closed ready fresh ports
  have step := RunStep.event
    ⟨⟨.perform requested operation operand, scope, whole⟩, issued, completed⟩ _ _ _ raw freshOwner
  exact ⟨parameter, binder, body, selected, step, typed, used, capture_ticket_binding, nextPorts,
    capture_access_from_types cut selected operandTyped closed boundary support,
    run_step_preserves_ledger step ledger⟩

/-- The structural binding selects an active live owner with the exact static
    ports. Checked resumption consumes its permission, restores the full clause
    prefix, and leaves a spent binding under the restored capture. -/
theorem typed_resume_step
    (binding : TicketBinding (.bound binder input answer residual closing)
      (.ticket binder rights) scope .available stack)
    (typed : Typed signature environment (.bound binder input answer residual closing) allowed
      (.resume binder value) answer)
    (used : Uses policy (.ticket binder rights) .available (.resume binder value) .consumed)
    (closed : ClosedValue value)
    (ports : Fits stack.erase answer result)
    (support : AccessValid ⟨.resume binder value, scope, stack⟩ ambient)
    (ledger : Ledger ⟨stack.erase, issued, completed⟩) :
    ∃ owner nextStack,
      let next : RunState := ⟨⟨value, scope, nextStack⟩, issued, .ticket owner :: completed⟩
      RunStep ⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩ next ∧
      rights.resume = true ∧ scope.resolve binder = some owner ∧
      Typed signature environment (.bound binder input answer residual closing) allowed value input ∧
      Uses policy (.ticket binder rights) .consumed value .consumed ∧
      TicketBinding (.bound binder input answer residual closing)
        (.ticket binder rights) scope .consumed nextStack ∧
      Fits nextStack.erase input result ∧ AccessValid next.configuration ambient ∧ Ledger next.erase := by
  cases binding with
  | live =>
      rename_i owner front saved tail callerScope
      cases typed with
      | resume valueTyped effects =>
          cases used with
          | resume permission operandUsed =>
              have raw := RawStep.resume binder owner (.ticket binder owner) callerScope input answer
                front saved tail value closed (by simp [Scope.resolve])
              have step := RunStep.event
                ⟨⟨.resume binder value, .ticket binder owner,
                  front.append (.live owner input answer saved callerScope tail)⟩, issued, completed⟩
                _ _ _ raw (by simpa using ledger.2)
              simp only [List.append_nil] at step
              have nextPorts : Fits
                  (saved.append (front.append (.spent owner answer callerScope tail))).erase input result := by
                simpa only [erase_append, Stack.erase] using resume_full_type_recomposition
                  (by simpa only [erase_append, Stack.erase] using ports)
              have nextAccess : AccessValid
                  ⟨value, .ticket binder owner, saved.append (front.append (.spent owner answer callerScope tail))⟩
                  ambient := by
                constructor
                · simpa only [erase_append, Stack.erase] using resume_preserves_support
                    (by simpa only [erase_append, Stack.erase] using support.control)
                · intro resource retained
                  have previous : resource ∈ (front.erase.visible ++ tail.erase.visible) ++ ambient := by
                    have old := support.expression (by simpa [Expr.dependencies, resourceDependencies] using retained)
                    simpa [erase_append, Stack.erase, Control.visible] using old
                  simpa [erase_append, Stack.erase, Control.visible, List.append_assoc] using
                    List.mem_append_right saved.erase.visible previous
              refine ⟨owner, _, step, permission, by simp [Scope.resolve], valueTyped,
                value_use_transport closed.1 operandUsed _ .consumed, ?_, nextPorts,
                nextAccess, run_step_preserves_ledger step ledger⟩
              rw [← stack_append_assoc]
              exact .spent

/-- Disposal checks the actual abandoned capture and surviving clause prefix.
    The result preserves a spent binding and retains the checked close plan;
    callbacks have not yet run when this transition returns. -/
theorem typed_discard_step {front saved tail : Stack}
    (typed : Typed signature environment (.bound binder input answer residual closing) allowed
      (.discard binder) .unit)
    (used : Uses policy (.ticket binder rights) .available (.discard binder) .consumed)
    (disposal : DisposalTyped signature closing saved
      (front.append (.spent owner answer callerScope tail)) plan)
    (ports : Fits (front.append (.live owner input answer saved callerScope tail)).erase .unit result)
    (support : Supported (front.append (.live owner input answer saved callerScope tail)).erase ambient)
    (ledger : Ledger ⟨(front.append (.live owner input answer saved callerScope tail)).erase, issued, completed⟩)
    (fresh : (issued ++ [Owner.close closeId]).Nodup) :
    let scope := Scope.ticket binder owner
    let nextStack := (closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer callerScope tail)))
    let next : RunState := ⟨⟨.unit, scope, nextStack⟩,
      issued ++ [.close closeId], .ticket owner :: completed⟩
    RunStep ⟨⟨.discard binder, scope, front.append (.live owner input answer saved callerScope tail)⟩,
      issued, completed⟩ next ∧
    rights.dispose = true ∧ closing ⊆ allowed ∧ PlanTyped signature closing plan ∧
    TicketBinding (.bound binder input answer residual closing)
      (.ticket binder rights) scope .consumed nextStack ∧
    Typed signature environment (.bound binder input answer residual closing) allowed .unit .unit ∧
    Uses policy (.ticket binder rights) .consumed .unit .consumed ∧
    Fits nextStack.erase .unit result ∧ AccessValid next.configuration ambient ∧ Ledger next.erase := by
  cases typed with
  | discard effects =>
      cases used with
      | discard permission =>
          have raw := RawStep.discard binder owner closeId (.ticket binder owner) callerScope input answer
            front saved tail plan (by simp [Scope.resolve]) disposal.build
          have step := RunStep.event
            ⟨⟨.discard binder, .ticket binder owner,
              front.append (.live owner input answer saved callerScope tail)⟩, issued, completed⟩
            _ _ _ raw fresh
          refine ⟨step, permission, effects, disposal.calls, ?_, .unit, .unit, ?_, ?_,
            run_step_preserves_ledger step ledger⟩
          · have spent : TicketBinding (.bound binder input answer residual closing)
                (.ticket binder rights) (.ticket binder owner) .consumed
                (((closeControl (.ticket binder owner) plan).append
                  (.push (.closing closeId (.ticket binder owner)) front)).append
                  (.spent owner answer callerScope tail)) := .spent
            simpa only [stack_append_assoc, Stack.append] using spent
          · simpa only [erase_append, Stack.erase, close_control_erases, ExecFrame.erase] using
              discard_type_recomposition (plan := plan.map CloseEntry.erase) (closeId := closeId)
                (by simpa only [erase_append, Stack.erase] using ports)
          · constructor
            · simpa only [erase_append, Stack.erase, close_control_erases, ExecFrame.erase] using
                discard_control_preserves_support
                  (by simpa only [erase_append, Stack.erase] using support)
                  (by simpa only [erase_append, Stack.erase] using disposal.close) (closeId := closeId)
            · simp [Expr.dependencies, resourceDependencies]

namespace DispatchExamples
open Execution.Examples

def resumePolicy : TicketPolicy := fun _ => ⟨true, false⟩

theorem cleanup_capture_ports : Fits captureStack.erase .unit .integer :=
  .push _ _ _ (.push _ _ _ (.nil _))

theorem cleanup_capture_support : Supported captureStack.erase [] := by
  apply Supported.push _ _ _
  · apply Supported.push _ _ _ (.nil _)
    simp [ExecFrame.erase, HandlerData.erase, handler, clauses,
      Clauses.dependencies, Expr.dependencies, resourceDependencies, without, Instance.resources]
  · simp [ExecFrame.erase, ActionData.erase, action, callback, callbackBody,
      Expr.dependencies, resourceDependencies, without, instanceDependencies, Instance.resources]

theorem cleanup_clauses_typed :
    ClausesTyped Examples.unitRequestSignature TypeEnv.empty handler.effectInst handler.answer [] handler.clauses := by
  apply ClausesTyped.cons (input := .unit) (output := .unit)
  · simp [Examples.unitRequestSignature, handler]
  · exact .resume .unit (fun _ used => used)
  · exact .nil

theorem cleanup_clauses_used : ClausesUse resumePolicy handler.clauses :=
  .cons (.resume rfl .unit) .nil

/-- A real running cleanup is captured under lexical binder 9 and dynamic
    owner 3, with Unit input and Integer answer, then resumed. The checks in
    this example come from the general dispatch/resume constructions. -/
theorem cleanup_capture_resume_checked :
    let before : RunState := ⟨⟨.perform (.user 1 []) 0 .unit, .none, captureStack⟩, [.cleanup 7], []⟩
    let entered : RunState := ⟨capturedState, [.cleanup 7, .ticket 3], []⟩
    ∃ nextStack, let resumed : RunState := ⟨⟨.unit, .ticket 9 3, nextStack⟩,
      [.cleanup 7, .ticket 3], [.ticket 3]⟩
    RunStep before entered ∧ RunStep entered resumed ∧
      Typed Examples.unitRequestSignature TypeEnv.empty (.bound 9 .unit .integer [] []) []
        entered.configuration.expression .integer ∧
      TicketBinding (.bound 9 .unit .integer [] []) (.ticket 9 (resumePolicy 9))
        resumed.configuration.scope .consumed resumed.configuration.stack ∧
      Fits resumed.configuration.stack.erase .unit .integer ∧
      AccessValid resumed.configuration [] ∧ Ledger resumed.erase := by
  have cut : HandlerCut (.user 1 []) captureStack captureStack .nil handler :=
    .push _ _ _ _ _ (by simp [ExecFrame.erase, Frame.target]) (.hit handler .nil rfl)
  have covered : Covers Examples.unitRequestSignature handler.effectInst handler.clauses := by
    intro operation input output known
    simp only [Examples.unitRequestSignature, handler] at known
    split at known
    · rename_i equal
      simp [handler, clauseKeys, clauses, equal.2]
    · cases known
  have hygiene : ∀ parameter binder body, ClauseAt 0 handler.clauses parameter binder body →
      ClosedExcept parameter body ∧ ResourceFresh Expr.unit body := by
    intro parameter binder body selected
    cases selected with
    | hit => simp [ClosedExcept, Expr.dependencies, ResourceFresh]
    | pass different next => exact False.elim (different rfl)
  have initialLedger : Ledger ⟨captureStack.erase, [.cleanup 7], []⟩ := by
    constructor
    · exact List.Perm.refl _
    · decide
  obtain ⟨parameter, binder, body, selected, step, typed, used, binding, ports, access, ledger⟩ :=
    typed_capture_step (owner := 3) (scope := .none) (result := .integer)
      cut (by simp [Examples.unitRequestSignature]) cleanup_clauses_typed cleanup_clauses_used
      covered (Typed.unit (ticket := .none) (allowed := []))
      (Uses.unit (scope := .none) (state := .available)) closed_unit hygiene
      cleanup_capture_ports cleanup_capture_support (by simp [Ty.resources]) initialLedger (by decide)
  cases selected with
  | hit =>
      obtain ⟨owner, nextStack, resumedStep, permission, resolved, valueTyped,
        valueUsed, spentBinding, resumedPorts, resumedAccess, resumedLedger⟩ :=
        typed_resume_step binding typed used closed_unit ports access ledger
      have ownerSame : owner = 3 := (Option.some.inj resolved).symm
      subst owner
      exact ⟨nextStack, step, resumedStep, typed, spentBinding,
        resumedPorts, resumedAccess, resumedLedger⟩
  | pass different next => exact False.elim (different rfl)

theorem wrong_capture_input_port_rejected :
    ¬ Fits (Stack.live 3 .boolean .integer captureStack .none .nil).erase .integer .integer := by
  intro ports
  cases ports with
  | live _ _ _ _ _ _ saved outside => cases saved

theorem mismatched_lexical_scopes_rejected :
    ¬ ScopeAgreement (.bound 9 .unit .integer [] []) (.ticket 4 (resumePolicy 4)) (.ticket 9 3) := by
  intro agreement
  cases agreement

def disposePolicy : TicketPolicy := fun _ => ⟨false, true⟩

def aliasedTicketStack : Stack := .spent 3 .unit .none (.live 3 .unit .unit .nil .none .nil)

theorem ledger_alone_allows_conflicting_ticket_states :
    Ledger ⟨aliasedTicketStack.erase, [.ticket 3], []⟩ ∧
    TicketBinding (.bound 9 .unit .unit [] []) (.ticket 9 (resumePolicy 9))
      (.ticket 9 3) .available aliasedTicketStack ∧
    TicketBinding (.bound 9 .unit .unit [] []) (.ticket 9 (resumePolicy 9))
      (.ticket 9 3) .consumed aliasedTicketStack ∧
    ¬ aliasedTicketStack.erase.ticketNames.Nodup := by
  refine ⟨⟨.refl _, by decide⟩,
    .live (front := .spent 3 .unit .none .nil), .spent (front := .nil), ?_⟩
  simp [aliasedTicketStack, Stack.erase, Control.ticketNames]

theorem cell_discard_entry_checked :
    let before : RunState := ⟨⟨.discard 9, closeScope, .live 3 .unit .unit abandoned .none .nil⟩,
      [.ticket 3, .cleanup 7, .resource 4], []⟩
    let nextStack := (closeControl closeScope closePlan).append closeTail
    let next : RunState := ⟨⟨.unit, closeScope, nextStack⟩,
      [.ticket 3, .cleanup 7, .resource 4, .close 8], [.ticket 3]⟩
    RunStep before next ∧ PlanTyped Examples.cellOnly [] closePlan ∧
      TicketBinding (.bound 9 .unit .unit [] []) (.ticket 9 (disposePolicy 9))
        closeScope .consumed nextStack ∧ AccessValid next.configuration [] ∧ Ledger next.erase := by
  have ports : Fits (Stack.live 3 .unit .unit abandoned .none .nil).erase .unit .unit :=
    .live _ _ _ _ _ _ (.push _ _ _ (.push _ _ _ (.push _ _ _ (.nil _)))) (.nil _)
  have support : Supported (Stack.live 3 .unit .unit abandoned .none .nil).erase [] := by
    apply Supported.live _ _ _ _ _ _ _ (.nil _)
    apply Supported.push _ _ _
    · apply Supported.push _ _ _
      · apply Supported.push _ _ _ (.nil _)
        simp [ExecFrame.erase, HandlerData.erase, discardHandler, Clauses.dependencies,
          Expr.dependencies, resourceDependencies, without, Instance.resources]
      · simp [ExecFrame.erase]
    · simp [ExecFrame.erase, ActionData.erase, readAction, readCallback, readBody,
        Expr.dependencies, instanceDependencies, Instance.resources, resourceDependencies,
        without, Stack.erase, Control.visible, Frame.visible, HandlerData.erase, discardHandler]
  have ledger : Ledger ⟨(Stack.live 3 .unit .unit abandoned .none .nil).erase,
      [.ticket 3, .cleanup 7, .resource 4], []⟩ := ⟨.refl _, by decide⟩
  obtain ⟨step, _, _, plan, binding, _, _, _, access, nextLedger⟩ :=
    typed_discard_step (binder := 9) (front := .nil) (closeId := 8) (input := .unit) (residual := [])
      (Typed.discard (environment := TypeEnv.empty) (allowed := []) (fun _ used => used))
      (Uses.discard (policy := disposePolicy) (rights := disposePolicy 9) rfl)
      Examples.pure_cell_disposal_typed ports support ledger (by decide)
  exact ⟨step, plan, binding, access, nextLedger⟩

end DispatchExamples

end Ash.OneShot.Typing

#print axioms Ash.OneShot.Typing.handler_cut_ports
#print axioms Ash.OneShot.Typing.capture_instantiates_clause
#print axioms Ash.OneShot.Typing.typed_capture_step
#print axioms Ash.OneShot.Typing.typed_resume_step
#print axioms Ash.OneShot.Typing.typed_discard_step
#print axioms Ash.OneShot.Typing.DispatchExamples.cleanup_capture_resume_checked
#print axioms Ash.OneShot.Typing.DispatchExamples.cell_discard_entry_checked
#print axioms Ash.OneShot.Typing.ticket_binding_state_unique
#print axioms Ash.OneShot.Typing.DispatchExamples.ledger_alone_allows_conflicting_ticket_states
