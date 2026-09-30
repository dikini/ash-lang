import ScopedEffects

/-!
Scoped effect interfaces for entry, fresh world extension and materialized
closing. Structural close readiness constructs the executable plan; resource
access, interpretation agreement, permissions and joint admission remain
independent obligations.
-/

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (Signature TypeEnv TicketType EffectTickets ContinuationContract EffectScope EffectScopeKnown
  effect_scope_has_types effect_scope_known_has_types effect_ticket_from_types withCellSignatures)

theorem effect_frame_world_weaken
    (typed : EffectFrame signature tickets world frame incoming outgoing) (larger : world ⊆ next) :
    EffectFrame signature tickets next frame incoming outgoing := by
  cases typed with
  | plain scope context => exact .plain scope (context_world_weaken context larger)
  | handler scope clauses coverage unique => exact .handler scope (clauses_world_weaken clauses larger) coverage unique
  | cell scope noEscape => exact .cell scope noEscape
  | armed scope callable requests => exact .armed scope (typed_world_weaken callable next larger) requests
  | running scope callable saved requests =>
      exact .running scope (typed_world_weaken callable next larger) (typed_world_weaken saved next larger) requests
  | closing scope => exact .closing scope
  | retiring known => exact .retiring known

theorem effect_stack_world_weaken
    (typed : EffectStack signature tickets world stack incoming outgoing) (larger : world ⊆ next) :
    EffectStack signature tickets next stack incoming outgoing := by
  induction typed with
  | nil bound => exact .nil bound
  | push frame rest bound ih => exact .push (effect_frame_world_weaken frame larger) ih bound
  | live known scope saved rest resume close bound ihSaved ihRest =>
      exact .live known scope ihSaved ihRest resume close bound
  | spent known scope rest bound ih => exact .spent known scope ih bound

theorem effect_configuration_world_weaken
    (typed : EffectConfigurationTyped signature tickets world configuration result outgoing) (larger : world ⊆ next) :
    EffectConfigurationTyped signature tickets next configuration result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scope expression =>
      exact ⟨input, effects, .checked scope (typed_world_weaken expression next larger),
        stack_world_weaken stack larger, effect_stack_world_weaken effectStack larger⟩

theorem focus_constructs_effect_configuration
    (typed : EffectConfigurationTyped signature tickets world ⟨whole, scope, tail⟩ result outgoing)
    (focus : ScopedExecution.Focus whole child context) :
    ∃ plain : PlainData,
      RawStep ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ [] [] ∧
      EffectConfigurationTyped signature tickets world ⟨child, scope, .push (.plain plain) tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨plain, step, childTyped, contextTyped, output, shape, savedScope⟩ :=
        typed_focus_progress focus expression (scope_typed_names_match (effect_scope_has_types scopeTyped)) tail
      have frame : EffectFrame signature tickets world (.plain plain) effects effects :=
        .plain (by rw [savedScope]; exact scopeTyped) (by rw [output]; exact contextTyped)
      exact ⟨plain, step, plain.input, effects, .checked scopeTyped childTyped,
        .push (effect_frame_has_types frame) (by simpa only [ExecFrame.erase, PlainData.erase, output] using stack),
        .push frame effectStack (List.Subset.refl _)⟩

theorem handler_entry_constructs_effect_configuration
    (typed : EffectConfigurationTyped signature tickets world ⟨.handle source body clauses, scope, tail⟩ result outgoing)
    (activation : Nat) :
    ∃ handler : HandlerData, handler.activation = activation ∧
      RawStep ⟨.handle source body clauses, scope, tail⟩ ⟨body, scope, .push (.handler handler) tail⟩ [] [] ∧
      EffectConfigurationTyped signature tickets world ⟨body, scope, .push (.handler handler) tail⟩ result outgoing := by
  obtain ⟨answer, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | @handle _ _ _ effect _ _ _ _ _ bodyTyped clausesTyped coverage unique available =>
          let handler : HandlerData := ⟨activation, effect, clauses, scope, answer, clauses_have_ticket_barrier clausesTyped⟩
          have frame : EffectFrame signature tickets world (.handler handler) _ _ :=
            .handler ⟨_, scopeTyped⟩ clausesTyped coverage unique
          exact ⟨handler, rfl, .enterHandler handler body tail,
            answer, _, .checked scopeTyped bodyTyped, .push (effect_frame_has_types frame) stack,
            .push frame (effect_stack_input_weaken effectStack available) (List.Subset.refl _)⟩

theorem cleanup_entry_constructs_effect_configuration
    (typed : EffectConfigurationTyped signature tickets world ⟨.cleanup callback body, scope, tail⟩ result outgoing)
    (isValue : callback.IsValue) (identity : Nat) :
    ∃ action : ActionData, action.identity = identity ∧
      RawStep ⟨.cleanup callback body, scope, tail⟩ ⟨body, scope, .push (.armed action) tail⟩ [.cleanup identity] [] ∧
      EffectConfigurationTyped signature tickets world ⟨body, scope, .push (.armed action) tail⟩ result outgoing := by
  obtain ⟨answer, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | @cleanup _ _ _ _ _ latent retained _ _ callbackTyped bodyTyped available =>
          have closed := typed_value_closed callbackTyped isValue
          let action : ActionData := ⟨identity, callback, closed, scope, answer, latent⟩
          have frame : EffectFrame signature tickets world (.armed action) effects effects :=
            .armed ⟨_, scopeTyped⟩ (typed_value_transport callbackTyped isValue .none []) available
          exact ⟨action, rfl, .enterCleanup action body tail,
            answer, effects, .checked scopeTyped bodyTyped, .push (effect_frame_has_types frame) stack,
            .push frame effectStack (List.Subset.refl _)⟩

theorem branch_preserves_effect_configuration
    (typed : EffectConfigurationTyped signature tickets world ⟨.branch (.boolean condition) yes no, scope, tail⟩ result outgoing) :
    EffectConfigurationTyped signature tickets world ⟨if condition then yes else no, scope, tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | branch test yesTyped noTyped =>
          cases condition
          · exact ⟨input, effects, .checked scopeTyped noTyped, stack, effectStack⟩
          · exact ⟨input, effects, .checked scopeTyped yesTyped, stack, effectStack⟩

/-- Each entry opens the source body at a fresh activation and grows the world
    in current code, every retained frame and every dormant capture. -/
theorem resource_entry_effect_progress
    (typed : EffectConfigurationTyped signature tickets (resourceWorld issued)
      ⟨.resource binder initializer body, scope, tail⟩ result outgoing)
    (isValue : initializer.IsValue)
    (ledger : Ledger (RunState.erase ⟨⟨.resource binder initializer body, scope, tail⟩, issued, completed⟩)) :
    ∃ after,
      RunStep ⟨⟨.resource binder initializer body, scope, tail⟩, issued, completed⟩ after ∧
      EffectConfigurationTyped signature tickets (resourceWorld after.issued) after.configuration result outgoing ∧
      Ledger after.erase := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      rename_i ticket
      have integerTyped : Typed signature (resourceWorld issued) TypeEnv.empty ticket effects initializer .integer := by
        cases expression with | resource initializer _ _ _ _ => exact initializer
      obtain ⟨payload, rfl⟩ := typed_integer_value integerTyped isValue
      obtain ⟨identity, residual, fresh, step, bodyTyped, noEscape, noEffectEscape, available, afterLedger⟩ :=
        typed_resource_entry_progress binder payload body scope input tail issued completed expression ledger
      have larger : resourceWorld issued ⊆ resourceWorld (issued ++ [.resource identity]) := by
        rw [resource_world_append]
        exact fun _ member => List.mem_append_left _ member
      have frame : EffectFrame signature tickets (resourceWorld (issued ++ [.resource identity]))
          (.cell identity payload scope input) (.cell identity :: residual) residual :=
        .cell ⟨_, scopeTyped⟩ noEscape
      exact ⟨_, step, ⟨input, _, .checked scopeTyped bodyTyped,
        .push (effect_frame_has_types frame) (stack_world_weaken stack larger),
        .push frame (effect_stack_input_weaken (effect_stack_world_weaken effectStack larger) available)
          (List.Subset.refl _)⟩, afterLedger⟩

def planProvides : List CloseEntry → List Instance
  | [] => []
  | .release identity _ :: rest => .cell identity :: planProvides rest
  | .invoke _ :: rest | .retire _ :: rest => planProvides rest

inductive InvocationAt (action : ActionData) : List CloseEntry → List CloseEntry → Prop where
  | here : InvocationAt action (.invoke action :: suffix) suffix
  | later : InvocationAt action rest suffix → InvocationAt action (entry :: rest) suffix

/-- The close contract bounds outward requests. An invocation may additionally
    use a builtin provided by its actual remaining materialized suffix. -/
inductive PlanTyped (signature : Signature) (world : World) (closing : List Instance) : List CloseEntry → Prop where
  | nil : PlanTyped signature world closing []
  | release : PlanTyped signature world closing rest → PlanTyped signature world closing (.release identity payload :: rest)
  | retire : PlanTyped signature world closing rest → PlanTyped signature world closing (.retire ticket :: rest)
  | invoke (typed : Typed signature world TypeEnv.empty .none [] action.action
      (.function .unit .unit action.requests retained))
      (effects : action.requests ⊆ planProvides tail ++ closing) (rest : PlanTyped signature world closing tail) :
      PlanTyped signature world closing (.invoke action :: tail)

theorem plan_invocation_contract (position : InvocationAt action plan suffix)
    (typed : PlanTyped signature world closing plan) :
    ∃ retained, Typed signature world TypeEnv.empty .none [] action.action
      (.function .unit .unit action.requests retained) ∧ action.requests ⊆ planProvides suffix ++ closing := by
  induction position with
  | here => cases typed with
      | invoke typed effects rest => exact ⟨_, typed, effects⟩
  | later next ih => cases typed with
      | release rest | retire rest | invoke _ _ rest => exact ih rest

/-- Each invocation is typed in its local interpretation context. Its request
    bound may be larger than the whole close plan's outward row. -/
theorem disposal_invocation_typed (typed : PlanTyped signature world closing plan)
    (position : InvocationAt action plan suffix) :
    Typed signature world TypeEnv.empty .none (planProvides suffix ++ closing) (.app action.action .unit) .unit := by
  obtain ⟨retained, callable, effects⟩ := plan_invocation_contract position typed
  exact .app (typed_value_transport callable action.closed.1 .none _) .unit effects

/-- Every effect discharged by planProvides resolves to the corresponding
    actual builtin even when arbitrary surviving outer control is appended. -/
theorem plan_provided_resolves {plan : List CloseEntry}
    (provided : effectInst ∈ planProvides plan) (scope : Scope) (outer : Control) :
    ∃ identity, effectInst = .cell identity ∧
      ((closeControl scope plan).erase.append outer).resolve effectInst = some (.builtin identity) := by
  induction plan with
  | nil => simp [planProvides] at provided
  | cons entry rest ih => cases entry with
      | release identity payload =>
          rcases List.mem_cons.mp provided with same | later
          · subst effectInst
            exact ⟨identity, rfl, by simp [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
              Control.append, Control.resolve, Frame.resolve]⟩
          · obtain ⟨target, rfl, resolves⟩ := ih later
            refine ⟨target, rfl, ?_⟩
            by_cases same : target = identity
            · subst target
              simp [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
                Control.append, Control.resolve, Frame.resolve]
            · simpa [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
                Control.append, Control.resolve, Frame.resolve, same] using resolves
      | invoke action =>
          obtain ⟨target, rfl, resolves⟩ := ih provided
          exact ⟨target, rfl, by simpa [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
            ActionData.erase, Control.append, Control.resolve, Frame.resolve] using resolves⟩
      | retire ticket =>
          obtain ⟨target, rfl, resolves⟩ := ih provided
          exact ⟨target, rfl, by simpa [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
            CloseItem.frame, Control.append, Control.resolve, Frame.resolve] using resolves⟩

theorem plan_request_is_outward_or_interpreted
    (typed : PlanTyped signature world closing plan) (position : InvocationAt action plan suffix)
    (request : effectInst ∈ action.requests) (scope : Scope) (outer : Control) :
    effectInst ∈ closing ∨ ∃ identity, effectInst = .cell identity ∧
      ((closeControl scope suffix).erase.append outer).resolve effectInst = some (.builtin identity) := by
  obtain ⟨retained, callable, bound⟩ := plan_invocation_contract position typed
  rcases List.mem_append.mp (bound request) with provided | outward
  · exact Or.inr (plan_provided_resolves provided scope outer)
  · exact Or.inl outward

@[simp] theorem plan_provides_append (left right : List ScopedExecution.CloseEntry) :
    planProvides (left ++ right) = planProvides left ++ planProvides right := by
  induction left with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp_all [planProvides]

/-- A prefix closes with the resources retained by the suffix still available.
    This is sequential plan composition, not a commutation of cleanup order. -/
theorem plan_typed_append
    (inside : PlanTyped signature world (planProvides right ++ closing) left)
    (outside : PlanTyped signature world closing right) :
    PlanTyped signature world closing (left ++ right) := by
  induction inside with
  | nil => exact outside
  | release rest ih => exact .release ih
  | retire rest ih => exact .retire ih
  | @invoke retained tail action callable effects rest ih =>
      apply PlanTyped.invoke callable (rest := ih)
      change action.requests ⊆ planProvides (tail ++ right) ++ closing
      rw [plan_provides_append, List.append_assoc]
      exact effects

/-- Resources in the executable disposal order, including recursively captured
    live records. This function alone neither constructs nor admits a plan. -/
def closeProvides : Stack → List Instance
  | .nil => []
  | .push (.cell identity _ _ _) tail => .cell identity :: closeProvides tail
  | .push _ tail => closeProvides tail
  | .live _ _ _ capture _ tail => closeProvides capture ++ closeProvides tail
  | .spent _ _ _ tail => closeProvides tail

/-- Structural effect readiness of a captured stack. Protected frames have no
    constructor. For a nested live record, its capture closes before retirement
    and the outside suffix; that suffix remains available to its callbacks.
    This judgment does not grant any ticket's disposal permission. -/
inductive CloseReady (signature : Signature) (world : World) : List Instance → Stack → Prop where
  | nil : CloseReady signature world closing .nil
  | plain : CloseReady signature world closing tail → CloseReady signature world closing (.push (.plain data) tail)
  | handler : CloseReady signature world closing tail → CloseReady signature world closing (.push (.handler data) tail)
  | cell : CloseReady signature world closing tail → CloseReady signature world closing (.push (.cell identity payload scope answer) tail)
  | armed (callable : Typed signature world TypeEnv.empty .none [] action.action
      (.function .unit .unit action.requests retained))
      (effects : action.requests ⊆ closeProvides tail ++ closing)
      (rest : CloseReady signature world closing tail) :
      CloseReady signature world closing (.push (.armed action) tail)
  | live (inside : CloseReady signature world (closeProvides tail ++ closing) capture)
      (outside : CloseReady signature world closing tail) :
      CloseReady signature world closing (.live owner input answer capture scope tail)
  | spent : CloseReady signature world closing tail → CloseReady signature world closing (.spent owner answer scope tail)

theorem make_plan_provides (stack : Stack) (built : makePlan stack = some plan) :
    planProvides plan = closeProvides stack := by
  induction stack generalizing plan with
  | nil => cases built; rfl
  | push frame tail ih => cases frame with
      | plain | handler => exact ih built
      | cell =>
          cases tailPlan : makePlan tail with
          | none => simp [makePlan, tailPlan] at built
          | some rest =>
              simp only [makePlan, tailPlan, Option.some.injEq] at built
              subst plan
              exact congrArg (List.cons _) (ih tailPlan)
      | armed =>
          cases tailPlan : makePlan tail with
          | none => simp [makePlan, tailPlan] at built
          | some rest =>
              simp only [makePlan, tailPlan, Option.some.injEq] at built
              subst plan
              simpa only [planProvides, closeProvides] using (ih (plan := rest) tailPlan)
      | running | unwinding | closing | retiring => simp [makePlan] at built
  | live owner input answer capture scope tail ihCapture ihTail =>
      cases capturePlan : makePlan capture <;> cases tailPlan : makePlan tail <;>
        simp [makePlan, capturePlan, tailPlan] at built
      case some.some inside outside =>
        subst plan
        simp only [plan_provides_append, planProvides, closeProvides, ihCapture capturePlan, ihTail tailPlan]
  | spent owner answer scope tail ih => exact ih built

/-- No successful-plan premise: the structural derivation constructs both the
    actual makePlan result and the ordered callback effect derivation. -/
theorem close_ready_constructs_plan (ready : CloseReady signature world closing stack) :
    ∃ plan, makePlan stack = some plan ∧ PlanTyped signature world closing plan := by
  induction ready with
  | nil => exact ⟨[], rfl, .nil⟩
  | plain rest ih | handler rest ih | spent rest ih => exact ih
  | @cell closing tail identity payload scope answer rest ih =>
      obtain ⟨plan, built, typed⟩ := ih
      exact ⟨.release identity payload :: plan, by simp [makePlan, built], .release typed⟩
  | armed callable effects rest ih =>
      obtain ⟨plan, built, typed⟩ := ih
      exact ⟨_, by simp [makePlan, built], .invoke callable (by rw [make_plan_provides _ built]; exact effects) typed⟩
  | @live closing tail capture owner input answer scope inside outside ihInside ihOutside =>
      obtain ⟨inner, builtInner, typedInner⟩ := ihInside
      obtain ⟨outer, builtOuter, typedOuter⟩ := ihOutside
      refine ⟨inner ++ .retire owner :: outer, by simp [makePlan, builtInner, builtOuter], ?_⟩
      apply plan_typed_append (right := .retire owner :: outer) (outside := .retire typedOuter)
      simpa only [planProvides, make_plan_provides _ builtOuter] using typedInner

theorem plan_typed_world_weaken (typed : PlanTyped signature world closing plan) (larger : world ⊆ next) :
    PlanTyped signature next closing plan := by
  induction typed with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire rest ih => exact .retire ih
  | invoke callable effects rest ih => exact .invoke (typed_world_weaken callable next larger) effects ih

theorem close_ready_world_weaken (ready : CloseReady signature world closing stack) (larger : world ⊆ next) :
    CloseReady signature next closing stack := by
  induction ready with
  | nil => exact .nil
  | plain rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | armed callable effects rest ih => exact .armed (typed_world_weaken callable next larger) effects ih
  | live inside outside ihInside ihOutside => exact .live ihInside ihOutside
  | spent rest ih => exact .spent ih

theorem effect_live_to_spent
    (typed : EffectStack signature tickets world (.live owner input answer cap callerScope tail) incoming outgoing) :
    EffectStack signature tickets world (.spent owner answer callerScope tail) incoming outgoing := by
  cases typed with
  | live known scope saved rest resume close bound => exact .spent known scope rest bound

theorem close_plan_has_effect_interface
    (contents : PlanContentsTyped signature tickets.types world plan)
    (typed : PlanTyped signature world closing plan) (scope : EffectScopeKnown tickets runtimeScope) :
    EffectStack signature tickets world (closeControl runtimeScope plan) (planProvides plan ++ closing) closing := by
  induction typed with
  | nil => exact .nil (fun _ used => used)
  | release rest ih => cases contents with
      | release remaining =>
          exact .push (.cell scope (by simp [Ty.resources])) (ih remaining) (fun _ used => used)
  | retire rest ih => cases contents with
      | retire known remaining =>
          obtain ⟨contract, known⟩ := effect_ticket_from_types known
          exact .push (.retiring known) (ih remaining) (fun _ used => used)
  | invoke callable effects rest ih => cases contents with
      | invoke oldCallable remaining => exact .push (.armed scope callable effects) (ih remaining) (fun _ used => used)

theorem discard_preserves_effect_configuration {front cap tail : Stack}
    (known : tickets owner = some contract) (resolved : scope.resolve binder = some owner)
    (typed : EffectConfigurationTyped signature tickets world
      ⟨.discard binder, scope, front.append (.live owner contract.input contract.answer cap callerScope tail)⟩ result outgoing)
    (built : makePlan cap = some plan) (planTyped : PlanTyped signature world contract.closeEffects plan) :
    EffectConfigurationTyped signature tickets world
      ⟨.unit, scope, (closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner contract.answer callerScope tail)))⟩ result outgoing := by
  have oldAfter := discard_preserves_configuration_typing (closeId := closeId) resolved built (effect_configuration_has_types typed)
  obtain ⟨oldInput, oldExpression, oldStack⟩ := oldAfter
  cases oldExpression with
  | checked oldScope oldExpression => cases oldExpression with
      | unit =>
          obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
          cases expression with
          | checked scopeTyped expression => cases expression with
              | discard closeAllowed => cases scopeTyped with
                  | bound actual =>
                      simp [Execution.Scope.resolve] at resolved
                      subst owner
                      have same := Option.some.inj (known.symm.trans actual)
                      cases same
                      obtain ⟨middleType, frontTypes, liveTypes⟩ := stack_typed_decompose front stack
                      cases liveTypes with
                      | live oldKnown oldCaller capturedTypes outsideTypes =>
                          have contents := make_plan_retains_types capturedTypes built
                          have closeEffects := close_plan_has_effect_interface contents planTyped ⟨_, .bound (binder := binder) actual⟩
                          obtain ⟨middle, inside, outside⟩ := effect_stack_decompose front effectStack
                          refine ⟨.unit, [], .checked (.bound actual) .unit, oldStack, ?_⟩
                          apply effect_stack_input_weaken (effect_stack_append
                            (effect_stack_output_weaken closeEffects closeAllowed)
                            (.push (.closing ⟨_, .bound actual⟩)
                              (effect_stack_append inside (effect_live_to_spent outside)) (fun _ used => used)))
                          simp

/-- The structural capture judgment supplies the plan; finite ownership history
    supplies a fresh close owner. This proves effect/ledger progress at a known
    live boundary, not access or disposal-permission admission. -/
theorem ready_disposal_effect_progress {front cap tail : Stack}
    (known : tickets owner = some contract) (resolved : scope.resolve binder = some owner)
    (typed : EffectConfigurationTyped signature tickets (resourceWorld issued)
      ⟨.discard binder, scope, front.append (.live owner contract.input contract.answer cap callerScope tail)⟩ result outgoing)
    (ready : CloseReady signature (resourceWorld issued) contract.closeEffects cap)
    (ledger : Ledger (RunState.erase
      ⟨⟨.discard binder, scope, front.append (.live owner contract.input contract.answer cap callerScope tail)⟩,
        issued, completed⟩)) :
    ∃ after,
      RunStep ⟨⟨.discard binder, scope, front.append (.live owner contract.input contract.answer cap callerScope tail)⟩,
        issued, completed⟩ after ∧
      EffectConfigurationTyped signature tickets (resourceWorld after.issued) after.configuration result outgoing ∧
      Ledger after.erase := by
  obtain ⟨plan, built, planTyped⟩ := close_ready_constructs_plan ready
  obtain ⟨closeId, fresh⟩ := Progress.fresh_close_exists ledger.2
  have raw := RawStep.discard binder owner closeId scope callerScope contract.input contract.answer front cap tail plan resolved built
  have step := RunStep.event
    ⟨⟨.discard binder, scope, front.append (.live owner contract.input contract.answer cap callerScope tail)⟩, issued, completed⟩
    _ _ _ raw fresh
  have afterTyped := discard_preserves_effect_configuration (closeId := closeId) known resolved typed built planTyped
  exact ⟨_, step, by simpa [resource_world_append, resourceWorld] using afterTyped,
    run_step_preserves_ledger step ledger⟩

namespace CompletionExamples

def signature : Signature := withCellSignatures (fun _ _ => none)
def noTickets : EffectTickets := fun _ => none
def contract : ContinuationContract := ⟨.unit, .unit, [], []⟩
def tickets : EffectTickets := noTickets.insert 3 contract

def callback : Code := .lambda 0 (.bind 1
  (.perform (freezeEffect (.cell 4)) 0 (.resourceRef (.activation 4))) .unit)

theorem callback_typed : Typed signature [4] TypeEnv.empty .none [] callback
    (.function .unit .unit [.cell 4] [4]) := by
  apply Typed.lambda (retained := [4])
  · exact .bind (.perform rfl (by simp) (.reference (by simp)) (List.nil_subset _)) .unit
  · simp [Code.dependencies, effectAtoms, freezeEffect, Effect.resources, without, Typing.retainedSupport]
  · simp [InWorld, Ty.resources, Instance.resources]

def action : ActionData := ⟨7, callback, typed_value_closed callback_typed trivial, .none, .unit, [.cell 4]⟩
def captured : Stack := .push (.armed action) (.push (.cell 4 17 .none .unit) .nil)
def plan : List ScopedExecution.CloseEntry := [.invoke action, .release 4 17]

theorem captured_ready : CloseReady signature [4] [] captured :=
  .armed callback_typed (by simp [action, closeProvides]) (.cell .nil)

theorem generated_plan : makePlan captured = some plan ∧ PlanTyped signature [4] [] plan := by
  obtain ⟨actual, built, typed⟩ := close_ready_constructs_plan captured_ready
  have same : actual = plan := by simpa [captured, makePlan, plan] using built.symm
  subst actual
  exact ⟨built, typed⟩

theorem captured_effects : EffectStack signature registry [4] captured [] [] :=
  .push (.armed ⟨_, .none⟩ callback_typed (List.Subset.refl _))
    (.push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) (.nil (List.Subset.refl _)) (List.Subset.refl _))
    (List.nil_subset _)

theorem captured_types {registry : EffectTickets} : StackTyped signature registry.types [4] captured .unit .unit :=
  .push (.armed ⟨_, .none⟩ callback_typed) (.push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) .nil)

def initial : RunState :=
  ⟨⟨.discard 9, .ticket 9 3, .live 3 .unit .unit captured .none .nil⟩,
    [.ticket 3, .cleanup 7, .resource 4], []⟩

theorem initial_typed : EffectConfigurationTyped signature tickets (resourceWorld initial.issued)
    initial.configuration .unit [] := by
  have known : tickets 3 = some contract := rfl
  exact ⟨.unit, [], .checked (.bound known) (.discard (List.Subset.refl _)),
    .live (by simp [EffectTickets.types, known, contract]) ⟨_, .none⟩ captured_types .nil,
    .live known ⟨_, .none⟩ captured_effects (.nil (List.Subset.refl _))
      (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)⟩

theorem initial_ledger : Ledger initial.erase := ⟨.refl _, by decide⟩

theorem derived_disposal_step :
    ∃ after, RunStep initial after ∧
      EffectConfigurationTyped signature tickets (resourceWorld after.issued) after.configuration .unit [] ∧
      Ledger after.erase :=
  ready_disposal_effect_progress (front := .nil) (contract := contract) rfl rfl
    initial_typed captured_ready initial_ledger

theorem callback_has_actual_remaining_builtin :
    Typed signature [4] TypeEnv.empty .none [.cell 4] (.app callback .unit) .unit ∧
      ((closeControl (.ticket 9 3) [.release 4 17]).erase.append outer).resolve (.cell 4) = some (.builtin 4) := by
  have invocation : InvocationAt action plan [.release 4 17] := .here
  exact ⟨disposal_invocation_typed generated_plan.2 invocation, by
    simp [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase, Control.append, Control.resolve, Frame.resolve]⟩

/-- Releasing the only provider before invoking its callback is rejected. -/
theorem release_before_callback_rejected :
    ¬ CloseReady signature [4] [] (.push (.cell 4 17 .none .unit) (.push (.armed action) .nil)) := by
  intro ready
  cases ready with
  | cell rest => cases rest with
      | armed callable effects rest =>
          have impossible := effects (show Instance.cell 4 ∈ action.requests from by simp [action])
          cases impossible

theorem running_cleanup_rejected :
    ¬ CloseReady signature [4] closing (.push (.running action .unit ScopedExecution.Examples.unit_closed) tail) := by
  intro ready
  cases ready

def nested : Stack := .live 6 .unit .unit (.push (.armed action) .nil) .none
  (.push (.cell 4 17 .none .unit) .nil)

theorem nested_ready : CloseReady signature [4] [] nested :=
  .live (.armed callback_typed (by simp [action, closeProvides]) .nil) (.cell .nil)

/-- The nested callback uses a resource retained by the outside suffix; the
    inner ticket retires between callback completion and resource release. -/
theorem nested_plan_order :
    makePlan nested = some [.invoke action, .retire 6, .release 4 17] ∧
      PlanTyped signature [4] [] [.invoke action, .retire 6, .release 4 17] := by
  obtain ⟨actual, built, typed⟩ := close_ready_constructs_plan nested_ready
  have same : actual = [.invoke action, .retire 6, .release 4 17] := by
    simpa [nested, makePlan] using built.symm
  subst actual
  exact ⟨built, typed⟩

def overrideClauses : ScopedExpressions.Clauses :=
  .cons 0 1 10 (.resume 10 (.integer 0)) (.cons 1 2 11 (.resume 11 .unit) .nil)

theorem override_clauses_typed : ClausesTyped signature [4] TypeEnv.empty (.cell 4) .unit [] overrideClauses :=
  .cons rfl (.resume .integer (List.Subset.refl _) (List.nil_subset _))
    (.cons rfl (.resume .unit (List.Subset.refl _) (List.nil_subset _)) .nil)

def override : HandlerData :=
  ⟨20, .cell 4, overrideClauses, .none, .unit, clauses_have_ticket_barrier override_clauses_typed⟩

theorem override_frame_effects : EffectFrame signature registry [4] (.handler override) [.cell 4] [] := by
  apply EffectFrame.handler ⟨_, .none⟩ override_clauses_typed
  · intro operation input output found
    cases operation with
    | zero => simp [override, overrideClauses, clauseKeys]
    | succ operation => cases operation with
        | zero => simp [override, overrideClauses, clauseKeys]
        | succ operation => simp [override, signature, withCellSignatures] at found
  · decide

def overridden : Stack := .push (.armed action) (.push (.handler override) (.push (.cell 4 17 .none .unit) .nil))

theorem overridden_ready : CloseReady signature [4] [] overridden :=
  .armed callback_typed (by simp [action, closeProvides]) (.handler (.cell .nil))

theorem overridden_typed {registry : EffectTickets} : StackTyped signature registry.types [4] overridden .unit .unit ∧
    EffectStack signature registry [4] overridden [] [] :=
  ⟨.push (.armed ⟨_, .none⟩ callback_typed)
    (.push (effect_frame_has_types override_frame_effects) (.push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) .nil)),
   .push (.armed ⟨_, .none⟩ callback_typed (List.Subset.refl _))
    (.push override_frame_effects
      (.push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) (.nil (List.Subset.refl _)) (List.nil_subset _))
      (List.Subset.refl _)) (List.nil_subset _)⟩

/-- Available effects do not preserve interpreter identity. This value/effect
    typed capture and structurally ready plan lose a source override; the
    independent SameRequests check must reject that change. -/
theorem readiness_does_not_imply_interpretation_agreement :
    CloseReady signature [4] [] overridden ∧ makePlan overridden = some plan ∧
      overridden.erase.resolve (.cell 4) = some (.source 20) ∧
      (closeControl .none plan).erase.resolve (.cell 4) = some (.builtin 4) ∧
      ¬ SameRequests overridden.erase (closeControl .none plan).erase [.cell 4] := by
  refine ⟨overridden_ready, rfl, rfl, rfl, ?_⟩
  intro agreement
  cases agreement with
  | cons request rest target before after next =>
      have first : some (Target.source 20) = some target := before
      have second : some (Target.builtin 4) = some target := after
      cases first.trans second.symm

def caller : Scope := .ticket 9 3
def surviving : Stack := .push (.closing 100 caller) (.spent 3 .unit .none .nil)
def cellTail : Stack := .push (.cell 4 17 caller .unit) surviving
def preparedAction : ActionData := { action with scope := caller, answer := .unit }
def runningStack : Stack := .push (.running preparedAction .unit ScopedExecution.Examples.unit_closed) cellTail
def readContext : PlainData := ⟨.bind 1 .unit, .none, .integer, .unit, [], rfl⟩
def readRequest : Code := .perform (freezeEffect (.cell 4)) 0 (.resourceRef (.activation 4))
def terminal : RunState :=
  ⟨⟨.unit, .none, .nil⟩, [.ticket 3, .cleanup 7, .resource 4, .close 100],
    [.close 100, .resource 4, .cleanup 7, .ticket 3]⟩

/-- Disposal starts the actual callback, reads its still-live cell, completes
    the callback, then releases the cell and completes the close owner. -/
theorem disposal_callback_trace :
    RawTrace initial.configuration terminal.configuration [.close 100]
      [.close 100, .resource 4, .cleanup 7, .ticket 3] := by
  have discard := RawStep.discard 9 3 100 caller .none .unit .unit .nil captured .nil plan rfl generated_plan.1
  have start := RawStep.startCleanup preparedAction .unit ScopedExecution.Examples.unit_closed caller cellTail
  have beta := RawStep.beta 0 (.bind 1 readRequest .unit) .unit .none runningStack
    ScopedExecution.Examples.unit_closed preparedAction.closed
  have focus := RawStep.focus readContext (Focus.bind (initializer := readRequest) (by simp [readRequest, Code.IsValue])) runningStack
  have read := RawStep.readCell 4 17 .none (.push (.plain readContext) runningStack) (.push (.plain readContext) runningStack)
    (.push (by simp [ExecFrame.erase, PlainData.erase, Frame.target])
      (.push (by simp [ExecFrame.erase, ActionData.erase, Frame.target]) .hit))
  have plug := RawStep.plug readContext (.integer 17)
    (typed_value_closed (Typed.integer (signature := signature) (world := [4]) (ticket := .none) (allowed := [])) trivial)
    .none runningStack
  have bind := RawStep.bind 1 (.integer 17) .unit .none runningStack
    (typed_value_closed (Typed.integer (signature := signature) (world := [4]) (ticket := .none) (allowed := [])) trivial)
    (by intro name member; cases member)
  have finish := RawStep.finishCleanup preparedAction .unit ScopedExecution.Examples.unit_closed .none cellTail
  have release := RawStep.leaveCell 4 17 .unit caller caller .unit ScopedExecution.Examples.unit_closed surviving
  have close := RawStep.finishClose 100 caller caller (.spent 3 .unit .none .nil)
  have leave := RawStep.leaveClause 3 .unit .unit ScopedExecution.Examples.unit_closed caller .none .nil
  exact .next discard (.next start (.next beta (.next focus (.next read (.next plug
    (.next bind (.next finish (.next release (.next close (.next leave (.refl _)))))))))))

theorem disposal_callback_execution : RunSteps initial terminal :=
  raw_trace_enacts disposal_callback_trace (by decide)

theorem disposal_callback_ledger : Ledger terminal.erase :=
  run_steps_preserve_ledger disposal_callback_execution initial_ledger

def afterDisposal : Configuration := ⟨.unit, caller, .push (.armed preparedAction) cellTail⟩
def afterStart : Configuration := ⟨.app callback .unit, .none, runningStack⟩
def afterBeta : Configuration := ⟨.bind 1 readRequest .unit, .none, runningStack⟩
def afterFocus : Configuration := ⟨readRequest, .none, .push (.plain readContext) runningStack⟩
def afterRead : Configuration := ⟨.integer 17, .none, .push (.plain readContext) runningStack⟩
def afterPlug : Configuration := ⟨.bind 1 (.integer 17) .unit, .none, runningStack⟩
def afterBind : Configuration := ⟨.unit, .none, runningStack⟩
def afterFinish : Configuration := ⟨.unit, caller, cellTail⟩
def afterRelease : Configuration := ⟨.unit, caller, surviving⟩
def afterClose : Configuration := ⟨.unit, caller, .spent 3 .unit .none .nil⟩
def traceConfigurations : List Configuration :=
  [initial.configuration, afterDisposal, afterStart, afterBeta, afterFocus, afterRead,
    afterPlug, afterBind, afterFinish, afterRelease, afterClose, terminal.configuration]

/-- All twelve configurations in the eleven-step example have connected value
    and effect typing. This is a concrete derivation, not universal preservation
    of readiness for arbitrary future captures. -/
theorem disposal_trace_configurations_typed :
    ∀ configuration ∈ traceConfigurations,
      EffectConfigurationTyped signature tickets [4] configuration .unit [] := by
  have t0 := initial_typed
  have t1 : EffectConfigurationTyped signature tickets [4] afterDisposal .unit [] :=
    discard_preserves_effect_configuration (front := .nil) (contract := contract) (closeId := 100)
      rfl rfl initial_typed generated_plan.1 generated_plan.2
  have t2 : EffectConfigurationTyped signature tickets [4] afterStart .unit [] :=
    raw_value_step_preserves_effect_configuration
      (RawStep.startCleanup preparedAction .unit ScopedExecution.Examples.unit_closed caller cellTail)
      ScopedExecution.Examples.unit_closed t1
  have t3 : EffectConfigurationTyped signature tickets [4] afterBeta .unit [] :=
    beta_preserves_effect_configuration (parameter := 0) (body := .bind 1 readRequest .unit) t2 trivial
  have t4 : EffectConfigurationTyped signature tickets [4] afterFocus .unit [] := by
    obtain ⟨input, effects, expression, stack, control⟩ := t3
    cases expression with
    | checked scopeTyped expression => cases expression with
        | bind initializer suffix => cases suffix with
            | unit =>
                obtain ⟨operandType, known, available, operandTyped⟩ := typed_perform_inversion initializer
                simp only [signature, withCellSignatures, Option.some.injEq, Prod.mk.injEq] at known
                obtain ⟨rfl, rfl⟩ := known
                exact ⟨.integer, effects, .checked scopeTyped initializer,
                  .push (.plain (allowed := effects) (effect_scope_has_types scopeTyped) (.bind .unit)) stack,
                  .push (.plain scopeTyped (.bind .unit)) control (List.Subset.refl _)⟩
  have selected : CellUpdate 4 17 17 afterFocus.stack afterRead.stack :=
    .push (by simp [ExecFrame.erase, PlainData.erase, Frame.target])
      (.push (by simp [ExecFrame.erase, ActionData.erase, Frame.target]) .hit)
  have t5 : EffectConfigurationTyped signature tickets [4] afterRead .unit [] :=
    cell_read_preserves_effect_configuration t4 selected
  have integerClosed : ScopedExpressions.ClosedValue (.integer 17) := typed_value_closed
    (Typed.integer (signature := signature) (world := [4]) (ticket := .none) (allowed := [])) trivial
  have t6 : EffectConfigurationTyped signature tickets [4] afterPlug .unit [] :=
    raw_value_step_preserves_effect_configuration
      (RawStep.plug readContext (.integer 17) integerClosed .none runningStack) integerClosed t5
  have t7 : EffectConfigurationTyped signature tickets [4] afterBind .unit [] :=
    bind_preserves_effect_configuration t6 trivial
  have t8 : EffectConfigurationTyped signature tickets [4] afterFinish .unit [] :=
    raw_value_step_preserves_effect_configuration
      (RawStep.finishCleanup preparedAction .unit ScopedExecution.Examples.unit_closed .none cellTail)
      ScopedExecution.Examples.unit_closed t7
  have t9 : EffectConfigurationTyped signature tickets [4] afterRelease .unit [] :=
    raw_value_step_preserves_effect_configuration
      (RawStep.leaveCell 4 17 .unit caller caller .unit ScopedExecution.Examples.unit_closed surviving)
      ScopedExecution.Examples.unit_closed t8
  have t10 : EffectConfigurationTyped signature tickets [4] afterClose .unit [] :=
    raw_value_step_preserves_effect_configuration
      (RawStep.finishClose 100 caller caller (.spent 3 .unit .none .nil)) ScopedExecution.Examples.unit_closed t9
  have t11 : EffectConfigurationTyped signature tickets [4] terminal.configuration .unit [] :=
    raw_value_step_preserves_effect_configuration
      (RawStep.leaveClause 3 .unit .unit ScopedExecution.Examples.unit_closed caller .none .nil)
      ScopedExecution.Examples.unit_closed t10
  intro configuration member
  simp only [traceConfigurations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact t0
  · exact t1
  · exact t2
  · exact t3
  · exact t4
  · exact t5
  · exact t6
  · exact t7
  · exact t8
  · exact t9
  · exact t10
  · exact t11

theorem fresh_resource_entry_with_effects :
    ∃ after, RunStep
      ⟨⟨.resource 4 (.integer 17) (ScopedExecution.Examples.readBody 4), .none, .nil⟩, [], []⟩ after ∧
      EffectConfigurationTyped signature noTickets (resourceWorld after.issued) after.configuration .integer [] ∧
      Ledger after.erase :=
  resource_entry_effect_progress
    ⟨.integer, [], .checked .none (TypingExamples.resource_read_typed [] 4 17), .nil, .nil (List.Subset.refl _)⟩
    trivial ⟨.refl _, by decide⟩

end CompletionExamples

end Ash.OneShot.ScopedTyping

#print axioms Ash.OneShot.ScopedTyping.effect_frame_world_weaken
#print axioms Ash.OneShot.ScopedTyping.effect_stack_world_weaken
#print axioms Ash.OneShot.ScopedTyping.effect_configuration_world_weaken
#print axioms Ash.OneShot.ScopedTyping.focus_constructs_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.handler_entry_constructs_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.cleanup_entry_constructs_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.branch_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.resource_entry_effect_progress
#print axioms Ash.OneShot.ScopedTyping.plan_invocation_contract
#print axioms Ash.OneShot.ScopedTyping.disposal_invocation_typed
#print axioms Ash.OneShot.ScopedTyping.plan_request_is_outward_or_interpreted
#print axioms Ash.OneShot.ScopedTyping.plan_typed_append
#print axioms Ash.OneShot.ScopedTyping.make_plan_provides
#print axioms Ash.OneShot.ScopedTyping.close_ready_constructs_plan
#print axioms Ash.OneShot.ScopedTyping.plan_typed_world_weaken
#print axioms Ash.OneShot.ScopedTyping.close_ready_world_weaken
#print axioms Ash.OneShot.ScopedTyping.close_plan_has_effect_interface
#print axioms Ash.OneShot.ScopedTyping.discard_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.ready_disposal_effect_progress
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.derived_disposal_step
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.callback_has_actual_remaining_builtin
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.release_before_callback_rejected
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.running_cleanup_rejected
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.nested_plan_order
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.overridden_typed
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.readiness_does_not_imply_interpretation_agreement
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.disposal_callback_trace
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.disposal_callback_execution
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.disposal_callback_ledger
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.disposal_trace_configurations_typed
#print axioms Ash.OneShot.ScopedTyping.CompletionExamples.fresh_resource_entry_with_effects
