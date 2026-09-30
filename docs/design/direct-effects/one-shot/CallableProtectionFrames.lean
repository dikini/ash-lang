import CallableProtection

/-!
Source protection summaries at actual retained evaluation frames. Runtime
contexts are derived from the stack; handler tables remain supplied annotations.
These local transition certificates do not yet form a full machine invariant.
-/

namespace Ash.OneShot.CallableProtectionFrames
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts
open Instantiation (freezeEffect)

abbrev Tables := HandlerData → List (Nat × ClauseContract)

def pushContext (tables : Tables) (frame : ExecFrame) (tail : ProtectionContracts.Context) :
    ProtectionContracts.Context := match frame with
  | .handler data => .handler data.effectInst data.activation (tables data) :: tail
  | .cell identity _ _ _ => .builtin identity :: tail
  | _ => .barrier (ProtectionContexts.frameProtected frame.erase) :: tail

def contextOf (tables : Tables) : Stack → ProtectionContracts.Context
  | .nil => []
  | .push frame rest => pushContext tables frame (contextOf tables rest)
  | .live _ _ _ saved _ rest => .barrier (ProtectionContexts.protectedMode saved.erase) :: contextOf tables rest
  | .spent _ _ _ rest => contextOf tables rest

theorem erase_push_context (tables : Tables) (frame : ExecFrame) (tail : ProtectionContracts.Context) :
    erase (pushContext tables frame tail) = ProtectionContexts.pushFrame frame.erase (erase tail) := by
  cases frame <;> rfl

theorem context_realizes (tables : Tables) (stack : Stack) :
    erase (contextOf tables stack) = ProtectionContexts.contextOf stack.erase := by
  induction stack with
  | nil => rfl
  | push frame rest ih => simp only [contextOf, erase_push_context, Stack.erase, ProtectionContexts.contextOf, ih]
  | live owner input answer saved scope rest ihSaved ihRest =>
      simp only [contextOf, erase, Stack.erase, ProtectionContexts.contextOf, ihRest]
  | spent owner answer scope rest ih => exact ih

@[simp] theorem check_plain_context (tables : Tables) (plain : PlainData) (tail : Stack) (row : Footprint) :
    checkFootprint (contextOf tables (.push (.plain plain) tail)) row = checkFootprint (contextOf tables tail) row := by
  simp [contextOf, pushContext, ProtectionContexts.frameProtected, ExecFrame.erase, PlainData.erase,
    checkFootprint, checkRequest]

def Checked (operations : Operations) (tables : Tables) (environment : CallableProtection.Environment)
    (stack : Stack) (code : Code) (contract : Contract) : Prop :=
  CheckedAt operations environment (contextOf tables stack) code contract

inductive ContextSummarizes (operations : Operations) (environment : CallableProtection.Environment) :
    ScopedExecution.Context → Contract → Contract → Footprint → Prop where
  | pairLeft (right : Summarizes operations environment code output row) :
      ContextSummarizes operations environment (.pairLeft code) input (.pair input output) row
  | pairRight (left : Summarizes operations environment code input []) :
      ContextSummarizes operations environment (.pairRight code) output (.pair input output) []
  | appFunction (argument : Summarizes operations environment code input row) :
      ContextSummarizes operations environment (.appFunction code) (.function input output latent) output (row ++ latent)
  | appArgument (function : Summarizes operations environment code (.function input output latent) []) :
      ContextSummarizes operations environment (.appArgument code) input output latent
  | bind (body : Summarizes operations (environment.extend name input) code output row) :
      ContextSummarizes operations environment (.bind name code) input output row
  | branch (yes : Summarizes operations environment a output yesRow)
      (no : Summarizes operations environment b output noRow) :
      ContextSummarizes operations environment (.branch a b) .scalar output (yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output)) :
      ContextSummarizes operations environment (.perform (freezeEffect effect) operation) input output [⟨effect, operation, false⟩]
  | cleanup (body : Summarizes operations environment code output row) :
      ContextSummarizes operations environment (.cleanup code) (.function .scalar .scalar latent) output (row ++ qualify true latent)
  | resource {world : List Nat} {bodyRow : Nat → Footprint}
      (body : ∀ identity, identity ∉ world →
        Summarizes operations environment
          (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (outward : ∀ identity, identity ∉ world → outsideCell identity (bodyRow identity) = row) :
      ContextSummarizes operations environment (.resource binder code) .scalar output row

theorem context_plug (context : ContextSummarizes operations environment position input output remainder)
    (child : Summarizes operations environment code input row) :
    Summarizes operations environment (position.plug code) output (row ++ remainder) := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left => simpa [ScopedExecution.Context.plug] using Summarizes.pair left child
  | appFunction argument => simpa [ScopedExecution.Context.plug, List.append_assoc] using Summarizes.app child argument
  | appArgument function => simpa [ScopedExecution.Context.plug] using Summarizes.app function child
  | bind body => exact .bind child body
  | branch yes no => simpa [ScopedExecution.Context.plug, List.append_assoc] using Summarizes.branch child yes no
  | perform known => exact .perform known child
  | cleanup body => simpa [ScopedExecution.Context.plug, List.append_assoc] using Summarizes.cleanup child body
  | resource body outward => exact .resource child body outward

theorem focus_decompose (summary : Summarizes operations environment whole output row)
    (focus : Focus whole child position) :
    ∃ input childRow remainder, Summarizes operations environment child input childRow ∧
      ContextSummarizes operations environment position input output remainder ∧ row = childRow ++ remainder := by
  cases summary with
  | unit | boolean | integer | reference | «variable» | lambda => cases focus
  | pair left right => cases focus with
      | pairLeft => exact ⟨_, _, _, left, .pairLeft right, rfl⟩
      | pairRight value =>
          have empty := value_has_no_immediate_demands left value
          subst_vars
          exact ⟨_, _, _, right, .pairRight left, by simp⟩
  | app function argument => cases focus with
      | appFunction => exact ⟨_, _, _, function, .appFunction argument, List.append_assoc ..⟩
      | appArgument value =>
          have empty := value_has_no_immediate_demands function value
          subst_vars
          exact ⟨_, _, _, argument, .appArgument function, by simp⟩
  | bind initializer body => cases focus with
      | bind => exact ⟨_, _, _, initializer, .bind body, rfl⟩
  | branch condition yes no => cases focus with
      | branch => exact ⟨_, _, _, condition, .branch yes no, List.append_assoc ..⟩
  | perform known operand => cases focus with
      | perform => exact ⟨_, _, _, operand, .perform known, rfl⟩
  | cleanup callback body => cases focus with
      | cleanup => exact ⟨_, _, _, callback, .cleanup body, List.append_assoc ..⟩
  | resource initializer body outward => cases focus with
      | resource notValue => exact ⟨_, _, _, initializer, .resource body outward, rfl⟩

/-- A retained evaluation frame carries the residual source requirement at its
    actual tail. Its hole's callable contract is retained without approximation. -/
def Pending (operations : Operations) (tables : Tables) (environment : CallableProtection.Environment)
    (plain : PlainData) (tail : Stack) (input output : Contract) : Prop :=
  ∃ remainder, ContextSummarizes operations environment plain.context input output remainder ∧
    checkFootprint (contextOf tables tail) remainder = true

theorem focus_step (checked : Checked operations tables environment tail whole output)
    (focus : Focus whole child plain.context) :
    ∃ input, RawStep ⟨whole, plain.scope, tail⟩ ⟨child, plain.scope, .push (.plain plain) tail⟩ [] [] ∧
      Checked operations tables environment (.push (.plain plain) tail) child input ∧
      Pending operations tables environment plain tail input output := by
  obtain ⟨row, summary, admitted⟩ := checked
  obtain ⟨input, childRow, remainder, childSummary, contextSummary, same⟩ := focus_decompose summary focus
  rw [same, check_footprint_append, Bool.and_eq_true_iff] at admitted
  exact ⟨input, .focus plain focus tail,
    ⟨childRow, childSummary, by simpa using admitted.1⟩, remainder, contextSummary, admitted.2⟩

theorem plug_step (pending : Pending operations tables environment plain tail input output)
    (checked : Checked operations tables currentEnvironment (.push (.plain plain) tail) value input)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.plain plain) tail⟩ ⟨plain.context.plug value, plain.scope, tail⟩ [] [] ∧
      Checked operations tables environment tail (plain.context.plug value) output := by
  obtain ⟨remainder, context, admitted⟩ := pending
  obtain ⟨row, summary, _⟩ := checked
  have empty := value_has_no_immediate_demands summary closed.1
  subst row
  have moved := closed_value_environment summary closed environment
  exact ⟨.plug plain value closed scope tail, remainder,
    by simpa using context_plug context moved, admitted⟩

theorem beta_step (checked : Checked operations tables environment tail (.app (.lambda parameter body) argument) result)
    (argumentClosed : ClosedValue argument) (functionClosed : ClosedValue (.lambda parameter body)) :
    RawStep ⟨.app (.lambda parameter body) argument, scope, tail⟩ ⟨body.subst parameter argument, .none, tail⟩ [] [] ∧
      Checked operations tables environment tail (body.subst parameter argument) result :=
  CallableProtection.beta_step checked argumentClosed functionClosed

theorem bind_step (checked : Checked operations tables environment tail (.bind parameter value body) result)
    (closed : ClosedValue value) (ready : ClosedExcept parameter body) :
    RawStep ⟨.bind parameter value body, scope, tail⟩ ⟨body.subst parameter value, scope, tail⟩ [] [] ∧
      Checked operations tables environment tail (body.subst parameter value) result :=
  CallableProtection.bind_step checked closed ready

theorem protected_request_denies_summary_disposal
    (checked : Checked operations tables environment whole (.perform (freezeEffect requested) operation operand) result)
    (cut : HandlerCut requested whole capture tail handler) (held : capture.erase.protected ≠ []) :
    ∃ contract, Selected (contextOf tables whole) ⟨requested, operation, false⟩ handler.activation contract true ∧
      contract.dispose = false :=
  checked_capture_contract cut (context_realizes tables whole) (actual_request_admitted checked) held

/-- The callback is checked for its future running phase. This certificate does
    not move the outside continuation beneath that barrier. -/
def Armed (operations : Operations) (tables : Tables) (action : ActionData) (tail : Stack) : Prop :=
  ∃ environment latent,
    Summarizes operations environment action.action (.function .scalar .scalar latent) [] ∧
    checkFootprint (.barrier true :: contextOf tables tail) latent = true

/-- A returned value retains its full contract independently of ambient handlers. -/
def Saved (operations : Operations) (value : Code) (contract : Contract) : Prop :=
  ∃ environment, Summarizes operations environment value contract []

theorem enter_cleanup_step
    (checked : Checked operations tables environment tail (.cleanup action.action body) result) :
    RawStep ⟨.cleanup action.action body, action.scope, tail⟩
      ⟨body, action.scope, .push (.armed action) tail⟩ [.cleanup action.identity] [] ∧
      Checked operations tables environment (.push (.armed action) tail) body result ∧
      Armed operations tables action tail := by
  obtain ⟨row, summary, admitted⟩ := checked
  cases summary with
  | cleanup callback bodySummary =>
      have empty := value_has_no_immediate_demands callback action.closed.1
      subst_vars
      simp only [List.nil_append, check_footprint_append, Bool.and_eq_true_iff] at admitted
      refine ⟨.enterCleanup action _ tail, ⟨_, bodySummary, ?_⟩, _, _, callback, ?_⟩
      · simpa [contextOf, pushContext, ProtectionContexts.frameProtected, ExecFrame.erase, ActionData.erase,
          checkFootprint, checkRequest] using admitted.1
      · exact (check_qualified).symm.trans admitted.2

theorem start_cleanup_step (armed : Armed operations tables action tail)
    (checked : Checked operations tables environment (.push (.armed action) tail) value result)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.armed action) tail⟩
      ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩ [] [] ∧
      Checked operations tables environment (.push (.running action value closed) tail)
        (.app action.action .unit) .scalar ∧ Saved operations value result := by
  obtain ⟨callbackEnvironment, latent, callback, admitted⟩ := armed
  obtain ⟨row, summary, _⟩ := checked
  have empty := value_has_no_immediate_demands summary closed.1
  subst row
  have moved := closed_value_environment callback action.closed environment
  refine ⟨.startCleanup action value closed scope tail, ⟨latent, ?_, ?_⟩, environment, summary⟩
  · simpa using Summarizes.app moved Summarizes.unit
  · exact admitted

theorem finish_cleanup_step (saved : Saved operations value result) (closed : ClosedValue value) :
    RawStep ⟨.unit, scope, .push (.running action value closed) tail⟩
      ⟨value, action.scope, tail⟩ [] [.cleanup action.identity] ∧
      Checked operations tables environment tail value result := by
  obtain ⟨savedEnvironment, summary⟩ := saved
  exact ⟨.finishCleanup action value closed scope tail,
    [], closed_value_environment summary closed environment, rfl⟩

/-- Source-bound rows remain supplied, but disposal permission is read directly
    from the same fixed ticket policy used at runtime allocation. -/
abbrev ClauseRows := Nat → Nat → Nat → Code → Option Footprint × Option Footprint

def clauseTable (policy : Syntax.TicketPolicy) (rows : ClauseRows) : Clauses → List (Nat × ClauseContract)
  | .nil => []
  | .cons operation parameter binder body rest =>
      (operation, ⟨(policy binder).dispose, (rows operation parameter binder body).1,
        (rows operation parameter binder body).2⟩) :: clauseTable policy rows rest

def policyTables (policy : Syntax.TicketPolicy) (rows : HandlerData → ClauseRows) : Tables :=
  fun handler => clauseTable policy (rows handler) handler.clauses

theorem clause_lookup (selected : ClauseAt operation clauses parameter binder body) :
    lookup operation (clauseTable policy rows clauses) =
      some ⟨(policy binder).dispose, (rows operation parameter binder body).1,
        (rows operation parameter binder body).2⟩ := by
  induction selected with
  | hit => simp [clauseTable, lookup]
  | pass different next ih => simpa [clauseTable, lookup, different] using ih

theorem check_push_miss (tables : Tables) (frame : ExecFrame) (context : ProtectionContracts.Context)
    (miss : frame.erase.target ≠ some requested) :
    checkRequest (pushContext tables frame context) ⟨requested, operation, incoming⟩ =
      checkRequest context ⟨requested, operation, incoming || ProtectionContexts.frameProtected frame.erase⟩ := by
  cases frame <;> simp_all [pushContext, checkRequest, ExecFrame.erase, HandlerData.erase, Frame.target,
    ProtectionContexts.frameProtected, PlainData.erase, ActionData.erase, eq_comm]

theorem cut_contract (cut : HandlerCut requested whole capture tail handler)
    (checked : checkRequest (contextOf tables whole) ⟨requested, operation, incoming⟩ = true) :
    ∃ contract, lookup operation (tables handler) = some contract ∧
      modeCheck contract.dispose (incoming || ProtectionContexts.protectedMode capture.erase) = true := by
  induction cut generalizing incoming with
  | hit handler tail same =>
      simp only [contextOf, pushContext, checkRequest, same, ↓reduceIte] at checked
      cases known : lookup operation (tables handler) with
      | none => simp [known] at checked
      | some contract =>
          refine ⟨contract, rfl, ?_⟩
          have permitted : modeCheck contract.dispose incoming = true := by
            by_cases permitted : modeCheck contract.dispose incoming = true
            · exact permitted
            · simp [known, permitted] at checked
          simpa [Stack.erase, ExecFrame.erase, HandlerData.erase, ProtectionContexts.protectedMode,
            ProtectionContexts.frameProtected] using permitted
  | push frame rest capture tail handler miss next ih =>
      rw [contextOf, check_push_miss tables frame _ miss] at checked
      obtain ⟨contract, known, permitted⟩ := ih checked
      exact ⟨contract, known, by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using permitted⟩
  | live owner input answer saved scope rest capture tail handler next ih =>
      change checkRequest (contextOf tables rest)
        ⟨requested, operation, incoming || ProtectionContexts.protectedMode saved.erase⟩ = true at checked
      obtain ⟨contract, known, permitted⟩ := ih checked
      exact ⟨contract, known, by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using permitted⟩
  | spent owner answer scope rest capture tail handler next ih => exact ih checked

theorem protected_request_denies_policy_disposal
    (checked : Checked operations (policyTables policy rows) environment whole
      (.perform (freezeEffect requested) operation operand) result)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (held : capture.erase.protected ≠ []) : (policy binder).dispose = false := by
  obtain ⟨contract, known, permitted⟩ := cut_contract cut (actual_request_admitted checked)
  have same := (clause_lookup (policy := policy) (rows := rows handler) clause).symm.trans known
  cases Option.some.inj same
  apply (mode_check_iff.mp permitted)
  simp [ProtectionContexts.protected_mode_iff.mpr held]

namespace Examples
open CallableProtection.Examples (effect operations function functionContract function_summary function_closed unit_closed)

def handler : HandlerData :=
  ⟨11, effect, .cons 0 0 0 (.resume 0 .unit) .nil, .none, .unit, rfl⟩
def tail : Stack := .push (.handler handler) .nil
def rows : HandlerData → ClauseRows := fun _ _ _ _ _ => (some [], some [])
def resumePolicy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly
def disposePolicy : Syntax.TicketPolicy := fun _ => ActionRequirements.disposeOnly
def action : ActionData := ⟨7, function, function_closed, .none, .unit, [effect]⟩
def running : Stack := .push (.running action .unit unit_closed) tail
def disposeHandler : HandlerData :=
  ⟨11, effect, .cons 0 0 0 (.discard 0) .nil, .none, .unit, rfl⟩
def disposeRunning : Stack :=
  .push (.running action .unit unit_closed) (.push (.handler disposeHandler) .nil)

theorem actual_context : contextOf (policyTables resumePolicy rows) running =
    [.barrier true, .handler effect 11 [(0, ⟨false, some [], some []⟩)]] := rfl

theorem running_cut : HandlerCut effect running running .nil handler :=
  .push _ _ _ _ _ (by decide) (.hit handler .nil rfl)

theorem actual_dispose_policy_rejected :
    ¬ Checked operations (policyTables disposePolicy rows) environment disposeRunning
      (.perform (freezeEffect effect) 0 .unit) .scalar := by
  intro checked
  have cut : HandlerCut effect disposeRunning disposeRunning .nil disposeHandler :=
    .push _ _ _ _ _ (by decide) (.hit disposeHandler .nil rfl)
  have denied := protected_request_denies_policy_disposal checked cut ClauseAt.hit (by decide)
  cases denied

theorem callable_cleanup_entry :
    Checked operations (policyTables resumePolicy rows) environment (.push (.armed action) tail) function functionContract ∧
      Armed operations (policyTables resumePolicy rows) action tail := by
  have checked : Checked operations (policyTables resumePolicy rows) environment tail
      (.cleanup action.action function) functionContract :=
    ⟨_, Summarizes.cleanup function_summary function_summary, by decide⟩
  exact (enter_cleanup_step checked).2

theorem callable_cleanup_start :
    Checked operations (policyTables resumePolicy rows) environment
      (.push (.running action function function_closed) tail) (.app action.action .unit) .scalar ∧
      Saved operations function functionContract := by
  obtain ⟨checked, armed⟩ := callable_cleanup_entry (environment := environment)
  exact (start_cleanup_step armed checked function_closed (scope := .none)).2

theorem callable_cleanup_finish :
    RawStep ⟨.unit, .none, .push (.running action function function_closed) tail⟩
      ⟨function, action.scope, tail⟩ [] [.cleanup action.identity] ∧
      Checked operations (policyTables resumePolicy rows) environment tail function functionContract :=
  finish_cleanup_step ⟨environment, function_summary⟩ function_closed

end Examples

end Ash.OneShot.CallableProtectionFrames

#print axioms Ash.OneShot.CallableProtectionFrames.erase_push_context
#print axioms Ash.OneShot.CallableProtectionFrames.context_realizes
#print axioms Ash.OneShot.CallableProtectionFrames.check_plain_context
#print axioms Ash.OneShot.CallableProtectionFrames.context_plug
#print axioms Ash.OneShot.CallableProtectionFrames.focus_decompose
#print axioms Ash.OneShot.CallableProtectionFrames.focus_step
#print axioms Ash.OneShot.CallableProtectionFrames.plug_step
#print axioms Ash.OneShot.CallableProtectionFrames.beta_step
#print axioms Ash.OneShot.CallableProtectionFrames.bind_step
#print axioms Ash.OneShot.CallableProtectionFrames.protected_request_denies_summary_disposal
#print axioms Ash.OneShot.CallableProtectionFrames.enter_cleanup_step
#print axioms Ash.OneShot.CallableProtectionFrames.start_cleanup_step
#print axioms Ash.OneShot.CallableProtectionFrames.finish_cleanup_step

#print axioms Ash.OneShot.CallableProtectionFrames.clause_lookup
#print axioms Ash.OneShot.CallableProtectionFrames.check_push_miss
#print axioms Ash.OneShot.CallableProtectionFrames.cut_contract
#print axioms Ash.OneShot.CallableProtectionFrames.protected_request_denies_policy_disposal

#print axioms Ash.OneShot.CallableProtectionFrames.Examples.actual_context
#print axioms Ash.OneShot.CallableProtectionFrames.Examples.running_cut
#print axioms Ash.OneShot.CallableProtectionFrames.Examples.actual_dispose_policy_rejected
#print axioms Ash.OneShot.CallableProtectionFrames.Examples.callable_cleanup_entry
#print axioms Ash.OneShot.CallableProtectionFrames.Examples.callable_cleanup_start
#print axioms Ash.OneShot.CallableProtectionFrames.Examples.callable_cleanup_finish
