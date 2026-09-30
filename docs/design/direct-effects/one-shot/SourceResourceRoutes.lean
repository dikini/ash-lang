import SourceCleanupRoutes

/-! Extend source cleanup routing to retained cells and resource-bearing
callbacks. Ordinary resource support is reused from Supported. The source
annotation inspects nearest interpretation scopes, not a future close plan.
Dormant captures and the full hereditary source integration remain separate. -/
namespace Ash.OneShot.SourceResourceRoutes
open ScopedExpressions ScopedExecution ProtectionContracts

inductive Entry where
  | handler : Instance → Entry
  | cell : Nat → Entry
  | cleanup : List Instance → Entry
  deriving DecidableEq, Repr

abbrev Context := List Entry

/-- A local builtin survives closing. A matching source handler has no rule.
An unresolved requirement is exported through the stated outward row. -/
inductive Route (outward : List Instance) : Context → Instance → Option Nat → Prop where
  | outside (included : requested ∈ outward) : Route outward [] requested none
  | cell (same : requested = .cell identity) : Route outward (.cell identity :: rest) requested (some identity)
  | cellMiss (different : requested ≠ .cell identity) (tail : Route outward rest requested target) :
      Route outward (.cell identity :: rest) requested target
  | handler (different : requested ≠ effect) (tail : Route outward rest requested target) :
      Route outward (.handler effect :: rest) requested target
  | cleanup (tail : Route outward rest requested target) : Route outward (.cleanup requests :: rest) requested target

inductive Closing (outward : List Instance) : Context → Prop where
  | nil : Closing outward []
  | handler (tail : Closing outward rest) : Closing outward (.handler effect :: rest)
  | cell (tail : Closing outward rest) : Closing outward (.cell identity :: rest)
  | cleanup (requests : ∀ effect ∈ needs, ∃ target, Route outward rest effect target)
      (tail : Closing outward rest) : Closing outward (.cleanup needs :: rest)

/-- Align source scopes and callback annotations with an actual stack. Plan
construction is structural; there is no admission or access premise here. -/
inductive Realizes : Context → Stack → List CloseEntry → Prop where
  | nil : Realizes [] .nil []
  | handler (tail : Realizes rest stack plan) :
      Realizes (.handler handler.effectInst :: rest) (.push (.handler handler) stack) plan
  | cell (tail : Realizes rest stack plan) :
      Realizes (.cell identity :: rest) (.push (.cell identity payload scope answer) stack) (.release identity payload :: plan)
  | cleanup (tail : Realizes rest stack plan) :
      Realizes (.cleanup action.requests :: rest) (.push (.armed action) stack) (.invoke action :: plan)

theorem Realizes.built (realized : Realizes context stack plan) : makePlan stack = some plan := by
  induction realized with
  | nil => rfl
  | handler tail ih => exact ih
  | cell tail ih | cleanup tail ih => simp [makePlan, ih]

/-- Closing leaves the same accessible cells in the same suffix. Reuse this
equation with existing source support, including captured access handles. -/
theorem Realizes.visible (realized : Realizes context stack plan) :
    (planControl (plan.map CloseEntry.erase)).visible = stack.erase.visible := by
  induction realized with
  | nil => rfl
  | handler tail ih | cleanup tail ih => exact ih
  | cell tail ih => simpa only [List.map_cons, CloseEntry.erase, planControl, CloseItem.frame,
      Control.visible, Frame.visible, Stack.erase, ExecFrame.erase, List.singleton_append] using congrArg (List.cons _) ih

theorem Realizes.pending_empty (realized : Realizes context stack plan) : stack.erase.pending = [] := by
  induction realized with
  | nil => rfl
  | handler tail ih | cell tail ih | cleanup tail ih => exact ih

/-- The source route supplies the same exact builtin, or no local target on
either side of closing. The effect bound is obtained at the same time. -/
theorem Realizes.route (realized : Realizes context stack plan)
    (route : Route outward context requested target) :
    stack.erase.resolve requested = target.map Target.builtin ∧
      (planControl (plan.map CloseEntry.erase)).resolve requested = target.map Target.builtin ∧
      requested ∈ ScopedPorts.planProvides plan ++ outward := by
  induction realized generalizing target with
  | nil => cases route with
      | outside included => exact ⟨rfl, rfl, included⟩
  | @handler rest stack plan handler tail ih =>
      cases route with
      | handler different next =>
          obtain ⟨before, after, included⟩ := ih next
          exact ⟨by simpa [Stack.erase, ExecFrame.erase, HandlerData.erase, Control.resolve,
            Frame.resolve, different] using before, after, included⟩
  | @cell rest stack plan identity payload scope answer tail ih =>
      cases route with
      | cell same =>
          subst requested
          exact ⟨by simp [Stack.erase, ExecFrame.erase, Control.resolve, Frame.resolve],
            by simp [CloseEntry.erase, planControl, CloseItem.frame, Control.resolve, Frame.resolve],
            by simp [ScopedPorts.planProvides]⟩
      | cellMiss different next =>
          obtain ⟨before, after, included⟩ := ih next
          exact ⟨by simpa [Stack.erase, ExecFrame.erase, Control.resolve, Frame.resolve, different] using before,
            by simpa [CloseEntry.erase, planControl, CloseItem.frame, Control.resolve, Frame.resolve, different] using after,
            List.mem_cons_of_mem _ included⟩
  | cleanup tail ih => cases route with
      | cleanup next => exact ih next

theorem Realizes.interfaces (realized : Realizes context stack plan)
    (closing : Closing outward context)
    (supported : Supported stack.erase resources)
    (contents : ScopedPorts.PlanContentsTyped signature tickets world plan) :
    ScopedPorts.PlanTyped signature world outward plan ∧
      Admission.OpenCloses stack.erase .nil .nil resources outward (plan.map CloseEntry.erase) := by
  induction realized with
  | nil => exact ⟨.nil, .nil _ _ _ _⟩
  | handler tail ih =>
      cases closing with
      | handler closing =>
          cases supported with
          | push frame rest resources support access =>
              obtain ⟨typed, routes⟩ := ih closing support contents
              exact ⟨typed, .handler _ _ _ _ _ _ _ _ _ rfl routes⟩
  | cell tail ih =>
      cases closing with
      | cell closing =>
          cases supported with
          | push frame rest resources support access =>
              cases contents with
              | release contents =>
                  obtain ⟨typed, routes⟩ := ih closing support contents
                  exact ⟨.release typed, .resource _ _ _ _ _ _ _ _ rfl routes⟩
  | @cleanup rest stack plan action tail ih =>
      cases closing with
      | cleanup requests closing =>
          cases supported with
          | push frame rest resources support access =>
              cases contents with
              | invoke callable contents =>
                  obtain ⟨typed, remaining⟩ := ih closing support contents
                  have effects : action.requests ⊆ ScopedPorts.planProvides plan ++ outward := by
                    intro effect member
                    obtain ⟨target, selected⟩ := requests effect member
                    exact (tail.route selected).2.2
                  have routes : Admission.OpenRequests stack.erase (planControl (plan.map CloseEntry.erase))
                      outward action.requests := by
                    have each : ∀ effect ∈ action.requests,
                        ∃ target, Route outward rest effect target := requests
                    generalize same : action.requests = needs at each ⊢
                    clear same
                    induction needs with
                    | nil => exact .nil
                    | cons effect needs ih =>
                        obtain ⟨target, selected⟩ := each effect List.mem_cons_self
                        obtain ⟨before, after, provided⟩ := tail.route selected
                        have next := ih (fun next member => each next (List.mem_cons_of_mem _ member))
                        cases target with
                        | some identity => exact .localTarget effect needs (.builtin identity) before after next
                        | none =>
                            have outside : effect ∈ outward := by
                              rcases List.mem_append.mp provided with retained | outside
                              · obtain ⟨identity, same, resolved⟩ := ScopedPorts.plan_provided_resolves retained .none .nil
                                rw [close_control_erases, append_nil, after] at resolved
                                cases resolved
                              · exact outside
                            exact .outside effect needs before after outside next
                  exact ⟨.invoke callable effects typed,
                    .armed _ _ _ _ _ _ _ _ rfl rfl
                      (by simpa only [append_nil, tail.visible] using access)
                      (by simpa only [append_nil, ExecFrame.erase, ActionData.erase] using routes) remaining⟩

def Realizes.certificate (realized : Realizes context stack plan)
    (closing : Closing record.annotation.closeEffects context)
    (supported : Supported stack.erase (Admission.outsideResources stack.erase))
    (contents : ScopedPorts.PlanContentsTyped signature tickets world plan) :
    DeclaredClosingInvariant.Certificate signature world record stack :=
  let checked := realized.interfaces closing supported contents
  ⟨plan, realized.built, checked.1, checked.2, realized.pending_empty.symm ▸ InternalUses.nil⟩

namespace Examples
open ScopedPorts.CompletionExamples (action captured plan signature callback_typed)

theorem retained_cell : Closing [] [.cleanup [.cell 4], .cell 4] :=
  .cleanup (by intro effect member; cases List.mem_singleton.mp member; exact ⟨some 4, .cell rfl⟩) (.cell .nil)

/-- A retained nearer builtin makes a later source handler irrelevant. This
is why the earlier all-handlers membership test cannot simply be reused. -/
theorem builtin_shadows_handler : Closing [] [.cleanup [.cell 4], .cell 4, .handler (.cell 4)] :=
  .cleanup (by intro effect member; cases List.mem_singleton.mp member; exact ⟨some 4, .cell rfl⟩) (.cell (.handler .nil))

theorem handler_shadows_builtin : ¬ Closing [] [.cleanup [.cell 4], .handler (.cell 4), .cell 4] := by
  intro closing
  cases closing with
  | cleanup requests tail =>
      obtain ⟨target, route⟩ := requests (.cell 4) List.mem_cons_self
      cases route with
      | handler different tail => exact different rfl

theorem release_before_callback_rejected : ¬ Closing [] [.cell 4, .cleanup [.cell 4]] := by
  intro closing
  cases closing with
  | cell tail => cases tail with
      | cleanup requests tail =>
          obtain ⟨target, route⟩ := requests (.cell 4) List.mem_cons_self
          cases route with
          | outside included => cases included

theorem realized_cell : Realizes [.cleanup [.cell 4], .cell 4] captured plan :=
  .cleanup (action := action) (.cell .nil)

theorem supported_cell : Supported captured.erase [] := by
  refine .push _ _ _ (.push _ _ _ (.nil _) (by simp [ExecFrame.erase])) ?_
  change Syntax.resourceDependencies action.action.dependencies ⊆ [4]
  decide

/-- Reuse the existing real cell-reading callback and its retained type. -/
theorem cell_closing_interfaces :
    ScopedPorts.PlanTyped signature [4] [] plan ∧
      Admission.OpenCloses captured.erase .nil .nil [] [] (plan.map CloseEntry.erase) :=
  realized_cell.interfaces retained_cell supported_cell
    (.invoke (tickets := fun _ => none) callback_typed (.release .nil))

end Examples

end Ash.OneShot.SourceResourceRoutes

#print axioms Ash.OneShot.SourceResourceRoutes.Realizes.built
#print axioms Ash.OneShot.SourceResourceRoutes.Realizes.visible
#print axioms Ash.OneShot.SourceResourceRoutes.Realizes.pending_empty
#print axioms Ash.OneShot.SourceResourceRoutes.Realizes.route
#print axioms Ash.OneShot.SourceResourceRoutes.Realizes.interfaces
#print axioms Ash.OneShot.SourceResourceRoutes.Realizes.certificate
#print axioms Ash.OneShot.SourceResourceRoutes.Examples.retained_cell
#print axioms Ash.OneShot.SourceResourceRoutes.Examples.builtin_shadows_handler
#print axioms Ash.OneShot.SourceResourceRoutes.Examples.handler_shadows_builtin
#print axioms Ash.OneShot.SourceResourceRoutes.Examples.release_before_callback_rejected
#print axioms Ash.OneShot.SourceResourceRoutes.Examples.realized_cell
#print axioms Ash.OneShot.SourceResourceRoutes.Examples.supported_cell
#print axioms Ash.OneShot.SourceResourceRoutes.Examples.cell_closing_interfaces

/- Bounded experiment: an installation-bound operation reference retains the
   existing operation ports. Dispatch semantics and lifetime preservation are
   intentionally not claimed by these binding lemmas. -/
namespace Ash.OneShot.ExplicitCleanupReference
open ScopedExpressions ScopedExecution ScopedPorts
variable {signature : Signature}

def frameBinding (frame : Frame) (target : Target) : Option Instance :=
  match frame.kind, target with
  | .handler effect installed, .source requested => if installed = requested then some effect else none
  | .resource identity, .builtin requested => if identity = requested then some (.cell identity) else none
  | _, _ => none

def lookup (target : Target) : Control → Option Instance
  | .nil => none
  | .push frame rest => match frameBinding frame target with
    | some effect => some effect
    | none => lookup target rest
  | .live _ _ _ _ rest => lookup target rest
  | .spent _ _ rest => lookup target rest

/-- The operation's input/output types remain those of the existing signature.
    The reference additionally records the particular installation to use. -/
structure Ref (signature : Signature) (effect : Instance) (operation : Nat)
    (input output : Port) where
  target : Target
  operationType : signature effect operation = some (input, output)

def Ref.Live (reference : Ref signature effect operation input output) (control : Control) : Prop :=
  lookup reference.target control = some effect

def installed (handler : HandlerData)
    (known : signature handler.effectInst operation = some (input, output)) :
    Ref signature handler.effectInst operation input output :=
  ⟨.source handler.activation, known⟩

theorem installed_live (handler : HandlerData)
    (known : signature handler.effectInst operation = some (input, output)) :
    (installed handler known).Live (.push handler.erase rest) := by
  simp [Ref.Live, installed, lookup, frameBinding, HandlerData.erase]

/-- A distinct installation cannot redirect this reference, even when it
    interprets exactly the same effect. No effect-name lookup occurs here. -/
theorem install_preserves_reference (handler : HandlerData)
    (reference : Ref signature effect operation input output)
    (live : reference.Live rest)
    (different : reference.target ≠ .source handler.activation) :
    reference.Live (.push handler.erase rest) := by
  cases reference with
  | mk target known =>
    cases target with
    | source identity =>
        have fresh : handler.activation ≠ identity := by
          intro same
          exact different (congrArg Target.source same.symm)
        simpa [Ref.Live, lookup, frameBinding, HandlerData.erase, fresh] using live
    | builtin identity => exact live

/-- Existing expression typing is recovered without changing either port,
    the callback result type, or the operation's effect instance. -/
theorem typing_erasure
    (reference : Ref signature effect operation input output)
    (argument : Typed signature world environment ticket allowed value input)
    (permitted : effect ∈ allowed) (formed : InWorld world output) :
    Typed signature world environment ticket allowed
      (.perform (Instantiation.freezeEffect effect) operation value) output :=
  .perform reference.operationType permitted argument formed

/-- Concrete witness: nearest-effect dispatch changes, but a reference bound
    to the original installation continues to name that installation. -/
def effect : Instance := .user 910 []
def frame (identity : Nat) : Frame := ⟨.handler effect identity, .unit, .unit, [], [], []⟩
def original := Control.push (frame 19) .nil
def shadowed := Control.push (frame 37) original

theorem distinct_installations : shadowed.activations.Nodup := by decide

theorem fixed_binding :
    original.resolve effect = some (.source 19) ∧
    shadowed.resolve effect = some (.source 37) ∧
    lookup (.source 19) original = some effect ∧
    lookup (.source 19) shadowed = some effect := by decide

/-- Identity binding does not manufacture lifetime: a removed installation
    is unavailable, even though its operation signature still exists. -/
theorem removed_unavailable : lookup (.source 19) .nil = none := rfl

#print axioms Ash.OneShot.ExplicitCleanupReference.installed_live
#print axioms Ash.OneShot.ExplicitCleanupReference.install_preserves_reference
#print axioms Ash.OneShot.ExplicitCleanupReference.typing_erasure
#print axioms Ash.OneShot.ExplicitCleanupReference.distinct_installations
#print axioms Ash.OneShot.ExplicitCleanupReference.fixed_binding
#print axioms Ash.OneShot.ExplicitCleanupReference.removed_unavailable
end Ash.OneShot.ExplicitCleanupReference


/- Administrative fragment of lexical unwinding. Callback evaluation and
   return to unwind mode are defined below. No cleanup plan is constructed. -/
namespace Ash.OneShot.LexicalUnwind
open ScopedExpressions ScopedExecution

inductive Advance : Stack → Stack → List Owner → Prop where
  | plain : Advance (.push (.plain frame) rest) rest []
  | handler : Advance (.push (.handler installation) rest) rest []
  | cell : Advance (.push (.cell identity payload scope answer) rest) rest [.resource identity]
  | spent : Advance (.spent owner answer scope rest) rest []
  | live : Advance (.live owner input answer saved scope rest)
      (saved.append (.push (.retiring owner) rest)) []
  | retire : Advance (.push (.retiring owner) rest) rest [.ticket owner]

/-- The next cleanup cannot be skipped to release an enclosing resource or
    remove an enclosing interpretation. It must be evaluated first. -/
theorem callback_not_skipped : ¬ Advance (.push (.armed action) rest) next discharged := by
  intro step
  cases step

/-- Unwinding cannot cancel a callback which is already executing. -/
theorem running_not_skipped : ¬ Advance (.push (.running action saved closed) rest) next discharged := by
  intro step
  cases step

/-- Each administrative decision is local. Adding an enclosing scope leaves
    that decision and its completed owners unchanged. -/
theorem append (step : Advance before after discharged) (outside : Stack) :
    Advance (before.append outside) (after.append outside) discharged := by
  cases step with
  | plain => exact .plain
  | handler => exact .handler
  | cell => exact .cell
  | spent => exact .spent
  | @live owner input answer saved scope rest =>
      simpa only [Stack.append, stack_append_assoc] using
        (Advance.live (owner := owner) (input := input) (answer := answer)
          (scope := scope) (saved := saved) (rest := rest.append outside))
  | retire => exact .retire

/-- Only a topmost scope is removed. A captured live owner becomes a pending
    retirement behind its saved scopes, rather than being silently dropped. -/
theorem accounting (step : Advance before after discharged) :
    before.erase.owners.Perm (after.erase.owners ++ discharged) := by
  cases step with
  | plain | handler | spent =>
      simp [Stack.erase, ExecFrame.erase, PlainData.erase, HandlerData.erase, Control.owners, Frame.owners]
  | @cell identity payload scope answer rest =>
      simpa [Stack.erase, ExecFrame.erase, Control.owners, Frame.owners] using
        (show ([Owner.resource identity] ++ after.erase.owners).Perm
          (after.erase.owners ++ [.resource identity]) from List.perm_append_comm)
  | @retire owner rest =>
      simpa [Stack.erase, ExecFrame.erase, Control.owners, Frame.owners, CloseItem.frame] using
        (show ([Owner.ticket owner] ++ after.erase.owners).Perm
          (after.erase.owners ++ [.ticket owner]) from List.perm_append_comm)
  | @live owner input answer saved scope rest =>
      have moved : ([Owner.ticket owner] ++ saved.erase.owners).Perm
          (saved.erase.owners ++ [.ticket owner]) := List.perm_append_comm
      simpa [Stack.erase, erase_append, owners_append, ExecFrame.erase, Control.owners,
        Frame.owners, CloseItem.frame, List.append_assoc] using moved.append_right rest.erase.owners

/-- Reuse the same structural ledger as ordinary execution. No future-safe
    state, generated plan, or successful callback premise appears here. -/
theorem preserves_ledger (step : Advance before after discharged)
    (valid : Ledger ⟨before.erase, issued, completed⟩) :
    Ledger ⟨after.erase, issued, discharged ++ completed⟩ := by
  obtain ⟨balance, unique⟩ := valid
  refine ⟨?_, unique⟩
  have moved := balance.trans ((accounting step).append_right completed)
  simpa only [List.append_assoc] using moved

/-- Fresh linear ownership plus the local transition implies that every
    owner completed by this step was still live, not previously completed. -/
theorem no_double_completion (step : Advance before after discharged)
    (valid : Ledger ⟨before.erase, issued, completed⟩) :
    (discharged ++ completed).Nodup := by
  have after := preserves_ledger step valid
  exact (List.nodup_append.mp (after.1.nodup_iff.mp after.2)).2.1

namespace Example
open InitialCleanupRouteGap

/-- The existing source example has a live lexical interpretation for the
    callback. The old disposal planner removes it. -/
theorem disposal_scope_mismatch :
    capture.erase.resolve inner = some (.source 101) ∧
    (closeControl .none plan).erase.resolve inner = none := by decide

/-- No administrative unwind step may bypass the callback in that example. -/
theorem cleanup_first : ¬ Advance capture next discharged := callback_not_skipped

/-- Existing ordinary scope-exit rules run the callback and its one-shot
    handler before leaving either interpretation. This is reference behavior,
    not yet an execution theorem for an unwind-mode callback. -/
theorem cleanup_runs :
    RawTrace ⟨.unit, .none, capture⟩ ⟨.unit, .none, .nil⟩
      [.ticket 104] [.cleanup 102, .ticket 104] := by
  let running : ExecFrame := .running action .unit ⟨trivial, rfl, by intro dependency member; cases member⟩
  let saved : Stack := .push running (.push (.handler innerHandler) .nil)
  have cut : HandlerCut inner (.push running innerStack) saved outerStack innerHandler :=
    .push _ _ _ _ _ (by decide) (.hit innerHandler outerStack rfl)
  have selected : ClauseAt 0 innerHandler.clauses 1 8 (.resume 8 .unit) := .hit
  have closedUnit : ClosedValue Code.unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
  have ready : ClosedExcept 1 (.resume 8 .unit) := by intro dependency member; simp [Code.dependencies] at member
  have last := RawTrace.next (.leaveHandler outerHandler .unit closedUnit .none .nil) (.refl _)
  have exited := RawTrace.next (.leaveClause 104 .unit .unit closedUnit .none .none outerStack) last
  have left := RawTrace.next (.leaveHandler innerHandler .unit closedUnit .none
    (.spent 104 .unit .none outerStack)) exited
  have finished := RawTrace.next (.finishCleanup action .unit closedUnit (.ticket 8 104)
    (.push (.handler innerHandler) (.spent 104 .unit .none outerStack))) left
  have resumed := RawTrace.next (.resume 8 104 (.ticket 8 104) .none .unit .unit .nil saved outerStack
    .unit closedUnit rfl) finished
  have captured := RawTrace.next (.capture inner 0 1 8 104 .unit (.resume 8 .unit) .none
    (.push running innerStack) saved outerStack innerHandler .unit cut selected closedUnit ready) resumed
  have applied := RawTrace.next (.beta 0 (.perform (Instantiation.freezeEffect inner) 0 .unit) .unit .none
    (.push running innerStack) closedUnit action.closed) captured
  exact RawTrace.next (.startCleanup action .unit closedUnit .none innerStack) applied


theorem cleanup_run : RunSteps
    ⟨⟨.unit, .none, capture⟩, [.cleanup 102], []⟩
    ⟨⟨.unit, .none, .nil⟩, [.cleanup 102, .ticket 104], [.cleanup 102, .ticket 104]⟩ :=
  raw_trace_enacts cleanup_runs (by decide)

end Example

#print axioms Ash.OneShot.LexicalUnwind.Example.disposal_scope_mismatch
#print axioms Ash.OneShot.LexicalUnwind.Example.cleanup_first
#print axioms Ash.OneShot.LexicalUnwind.Example.cleanup_runs
#print axioms Ash.OneShot.LexicalUnwind.Example.cleanup_run
#print axioms Ash.OneShot.LexicalUnwind.callback_not_skipped
#print axioms Ash.OneShot.LexicalUnwind.running_not_skipped
#print axioms Ash.OneShot.LexicalUnwind.append
#print axioms Ash.OneShot.LexicalUnwind.accounting
#print axioms Ash.OneShot.LexicalUnwind.preserves_ledger
#print axioms Ash.OneShot.LexicalUnwind.no_double_completion
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open ScopedExpressions ScopedExecution

/-- Ordinary evaluation or abandonment of the current scopes. Abandonment has
    no value and does not change a handler's declared answer type. -/
inductive Machine where
  | eval (configuration : Configuration)
  | unwind (scope : Scope) (stack : Stack)

def Machine.stack : Machine → Stack
  | .eval configuration => configuration.stack
  | .unwind _ stack => stack

/-- The old plan-based discard is excluded from the reused evaluator. -/
def ordinary : Code → Prop
  | .discard _ => False
  | _ => True

inductive Transition : Machine → Machine → List Owner → List Owner → Prop where
  | evaluate (step : RawStep before after created discharged) (allowed : ordinary before.expression) :
      Transition (.eval before) (.eval after) created discharged
  | advance (step : Advance before after discharged) :
      Transition (.unwind scope before) (.unwind scope after) [] discharged
  | startCleanup :
      Transition (.unwind scope (.push (.armed action) rest))
        (.eval ⟨.app action.action .unit, .none, .push (.unwinding action) rest⟩) [] []
  | finishCleanup :
      Transition (.eval ⟨.unit, scope, .push (.unwinding action) rest⟩)
        (.unwind action.scope rest) [] [.cleanup action.identity]
  | discard (binder owner identity : Nat) (scope callerScope : Scope) (input answer : Ty)
      (front captured tail : Stack) (resolve : scope.resolve binder = some owner)
      (unprotected : ProtectionContexts.protectedMode captured.erase = false) :
      Transition (.eval ⟨.discard binder, scope,
          front.append (.live owner input answer captured callerScope tail)⟩)
        (.unwind scope (captured.append (.push (.closing identity scope)
          (front.append (.spent owner answer callerScope tail))))) [.close identity] [.ticket owner]
  | finishClose :
      Transition (.unwind scope (.push (.closing identity callerScope) tail))
        (.eval ⟨.unit, callerScope, tail⟩) [] [.close identity]
  | retireValue (closed : ClosedValue value) :
      Transition (.eval ⟨value, scope, .push (.retiring owner) tail⟩)
        (.eval ⟨value, scope, tail⟩) [] [.ticket owner]
  | closeValue (closed : ClosedValue value) :
      Transition (.eval ⟨value, scope, .push (.closing identity callerScope) tail⟩)
        (.eval ⟨.unit, callerScope, tail⟩) [] [.close identity]

/-- Unwind-mode completion is explicit in the frame and survives capture and
    resumption through the same stack representation as ordinary frames. -/
theorem callback_keeps_interpretation :
    (.push (.unwinding action) rest : Stack).erase.resolve effect = rest.erase.resolve effect := rfl

theorem callback_protected :
    ProtectionContexts.protectedMode (.push (.unwinding action) rest : Stack).erase = true := rfl

/-- Unchanged handler records and unchanged operation ports: the callback
    return marker has the existing running-cleanup ownership and protection. -/
theorem callback_cut
    (cut : HandlerCut effect rest captured tail handler) :
    HandlerCut effect (.push (.unwinding action) rest)
      (.push (.unwinding action) captured) tail handler :=
  .push _ _ _ _ _ (by simp [ExecFrame.erase, ActionData.erase, Frame.target]) cut

/-- The call uses the existing Unit-to-Unit callback type. Its return marker
    retains the abandoned scope's original output annotation; no enclosing
    handler is retyped and no value of that output type is constructed. -/
theorem cleanup_entry_ports
    (callable : ScopedPorts.Typed signature world ScopedPorts.TypeEnv.empty .none []
      action.action (.function .unit .unit action.requests)) :
    ScopedPorts.Typed signature world ScopedPorts.TypeEnv.empty .none action.requests
      (.app action.action .unit) .unit ∧
      (ExecFrame.unwinding action).erase.input = .unit ∧
      (ExecFrame.unwinding action).erase.output = action.answer := by
  exact ⟨.app (ScopedPorts.typed_value_transport callable action.closed.1 .none action.requests)
    .unit (List.Subset.refl _), rfl, rfl⟩

theorem transition_accounting (step : Transition before after created discharged) :
    (before.stack.erase.owners ++ created).Perm (after.stack.erase.owners ++ discharged) := by
  cases step with
  | evaluate raw allowed => exact flow_accounting (raw_step_erases raw)
  | advance localStep => simpa only [Machine.stack, List.append_nil] using accounting localStep
  | startCleanup => simp [Machine.stack, Stack.erase, ExecFrame.erase, ActionData.erase, Control.owners, Frame.owners]
  | finishCleanup =>
      simpa [Machine.stack, Stack.erase, ExecFrame.erase, ActionData.erase, Control.owners, Frame.owners] using
        (List.perm_append_comm (l₁ := [Owner.cleanup _]) (l₂ := _))
  | discard =>
      apply List.perm_iff_count.mpr
      intro owner
      simp only [Machine.stack, erase_append, Stack.erase, owners_append, Control.owners,
        ExecFrame.erase, closeFrame, Frame.owners, List.count_append, List.count_cons, List.count_nil]
      omega
  | finishClose | closeValue =>
      simpa [Machine.stack, Stack.erase, ExecFrame.erase, closeFrame, Control.owners, Frame.owners] using
        (List.perm_append_comm (l₁ := [Owner.close _]) (l₂ := _))
  | retireValue =>
      simpa [Machine.stack, Stack.erase, ExecFrame.erase, CloseItem.frame, Control.owners, Frame.owners] using
        (List.perm_append_comm (l₁ := [Owner.ticket _]) (l₂ := _))

/-- Same ledger equation as ordinary execution, supplied with this machine's
    local accounting theorem. Freshness is checked against lifetime history. -/
theorem transition_preserves_ledger (step : Transition before after created discharged)
    (valid : Ledger ⟨before.stack.erase, issued, completed⟩)
    (fresh : (issued ++ created).Nodup) :
    Ledger ⟨after.stack.erase, issued ++ created, discharged ++ completed⟩ := by
  refine ⟨?_, fresh⟩
  have old := valid.1.append_right created
  have moved := (transition_accounting step).append_right completed
  have regroup : ((before.stack.erase.owners ++ completed) ++ created).Perm
      ((before.stack.erase.owners ++ created) ++ completed) := by
    apply List.perm_iff_count.mpr
    intro owner
    simp only [List.count_append]
    omega
  simpa only [List.append_assoc] using old.trans (regroup.trans moved)

structure RunState where
  machine : Machine
  issued : List Owner
  completed : List Owner

def RunState.erase (state : RunState) : Ash.OneShot.State :=
  ⟨state.machine.stack.erase, state.issued, state.completed⟩

inductive Event : RunState → RunState → Prop where
  | step (transition : Transition before.machine after created discharged)
      (fresh : (before.issued ++ created).Nodup) :
      Event before ⟨after, before.issued ++ created, discharged ++ before.completed⟩

theorem event_preserves_ledger (step : Event before after) (valid : Ledger before.erase) :
    Ledger after.erase := by
  cases step with
  | step transition fresh => exact transition_preserves_ledger transition valid fresh

/-- Reuse the library's finite-trace induction. Empty execution retains its
    initial ledger; every nonempty execution is covered by this statement. -/
theorem execution_preserves_ledger (steps : Relation.TransGen Event before after)
    (valid : Ledger before.erase) : Ledger after.erase := by
  induction steps with
  | single step => exact event_preserves_ledger step valid
  | tail steps step ih => exact event_preserves_ledger step ih

theorem execution_no_double_completion (steps : Relation.TransGen Event before after)
    (valid : Ledger before.erase) : after.completed.Nodup :=
  ledger_no_double_completion (execution_preserves_ledger steps valid)

namespace DisposalExample
open InitialCleanupRouteGap

def caller : Stack := .spent 103 .unit .none .nil
def boundary : Stack := .push (.closing 105 (.ticket 9 103)) caller
def outside : Stack := outerStack.append boundary
def inside : Stack := innerStack.append boundary

def initial : RunState :=
  ⟨.eval ⟨.discard 9, .ticket 9 103, .live 103 .unit .unit capture .none .nil⟩,
    [.ticket 103, .cleanup 102], []⟩
def final : RunState :=
  ⟨.eval ⟨.unit, .none, .nil⟩, [.ticket 103, .cleanup 102, .close 105, .ticket 104],
    [.close 105, .cleanup 102, .ticket 104, .ticket 103]⟩

/-- Disposal of the existing counterexample now executes its effectful
    callback under the original handler, then exits the captured scopes and
    returns to the disposing caller. No plan or changed handler is used. -/
theorem execution : Relation.TransGen Event initial final := by
  let running : ExecFrame := .unwinding action
  let saved : Stack := .push running (.push (.handler innerHandler) .nil)
  have cut : HandlerCut inner (.push running inside) saved outside innerHandler :=
    .push _ _ _ _ _ (by decide) (.hit innerHandler outside rfl)
  have selected : ClauseAt 0 innerHandler.clauses 1 8 (.resume 8 .unit) := .hit
  have closedUnit : ClosedValue Code.unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
  have ready : ClosedExcept 1 (.resume 8 .unit) := by intro dependency member; simp [Code.dependencies] at member
  have first : Transition initial.machine
      (.unwind (.ticket 9 103) (capture.append boundary)) [.close 105] [.ticket 103] :=
    .discard 9 103 105 (.ticket 9 103) .none .unit .unit .nil capture .nil rfl disposal_selected.1
  have trace := Relation.TransGen.single (Event.step (before := initial) first (by decide))
  have trace := trace.tail (Event.step Transition.startCleanup (by decide))
  have trace := trace.tail (Event.step (.evaluate
    (.beta 0 (.perform (Instantiation.freezeEffect inner) 0 .unit) .unit .none
      (.push running inside) closedUnit action.closed) trivial) (by decide))
  have trace := trace.tail (Event.step (.evaluate
    (.capture inner 0 1 8 104 .unit (.resume 8 .unit) .none
      (.push running inside) saved outside innerHandler .unit cut selected closedUnit ready) trivial) (by decide))
  have trace := trace.tail (Event.step (.evaluate
    (.resume 8 104 (.ticket 8 104) .none .unit .unit .nil saved outside .unit closedUnit rfl) trivial) (by decide))
  have trace := trace.tail (Event.step Transition.finishCleanup (by decide))
  have trace := trace.tail (Event.step (.advance Advance.handler) (by decide))
  have trace := trace.tail (Event.step (.advance Advance.spent) (by decide))
  have trace := trace.tail (Event.step (.advance Advance.handler) (by decide))
  have trace := trace.tail (Event.step Transition.finishClose (by decide))
  have trace := trace.tail (Event.step (.evaluate
    (.leaveClause 103 .unit .unit closedUnit (.ticket 9 103) .none .nil) trivial) (by decide))
  exact trace

theorem initial_ledger : Ledger initial.erase := by
  constructor
  · exact List.Perm.refl _
  · decide

theorem final_ledger : Ledger final.erase := execution_preserves_ledger execution initial_ledger

theorem exactly_once : final.issued.Perm final.completed ∧ final.completed.Nodup := by
  refine ⟨?_, execution_no_double_completion execution initial_ledger⟩
  simpa [final, RunState.erase, Machine.stack, Stack.erase, Control.owners] using final_ledger.1

end DisposalExample

#print axioms Ash.OneShot.LexicalUnwind.event_preserves_ledger
#print axioms Ash.OneShot.LexicalUnwind.execution_preserves_ledger
#print axioms Ash.OneShot.LexicalUnwind.execution_no_double_completion
#print axioms Ash.OneShot.LexicalUnwind.DisposalExample.execution
#print axioms Ash.OneShot.LexicalUnwind.DisposalExample.final_ledger
#print axioms Ash.OneShot.LexicalUnwind.DisposalExample.exactly_once
#print axioms Ash.OneShot.LexicalUnwind.cleanup_entry_ports
#print axioms Ash.OneShot.LexicalUnwind.callback_keeps_interpretation
#print axioms Ash.OneShot.LexicalUnwind.callback_protected
#print axioms Ash.OneShot.LexicalUnwind.callback_cut
#print axioms Ash.OneShot.LexicalUnwind.transition_accounting
#print axioms Ash.OneShot.LexicalUnwind.transition_preserves_ledger
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open ScopedExpressions ScopedExecution ScopedPorts

/-- Local port rules for the shared runtime frames. Unwind return points carry
    no saved value. Internal retirement and close boundaries do not require an
    abandoned scope's answer to be Unit. -/
inductive FramePorts (signature : Signature) (tickets : TicketSignatures) (world : ScopedTyping.World) :
    ExecFrame → Port → Port → Prop where
  | ordinary (typed : ScopedPorts.FrameTyped signature tickets world frame) :
      FramePorts signature tickets world frame (eraseType frame.erase.input) (eraseType frame.erase.output)
  | unwinding (scope : ScopeKnown tickets action.scope)
      (callable : Typed signature world TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests)) :
      FramePorts signature tickets world (.unwinding action) .unit (eraseType action.answer)
  | closing (scope : ScopeKnown tickets runtimeScope) :
      FramePorts signature tickets world (.closing identity runtimeScope) input .unit
  | retiring (known : tickets owner = some (argument, answer)) :
      FramePorts signature tickets world (.retiring owner) input input

inductive StackPorts (signature : Signature) (tickets : TicketSignatures) (world : ScopedTyping.World) :
    Stack → Port → Port → Prop where
  | nil : StackPorts signature tickets world .nil input input
  | push (frame : FramePorts signature tickets world entry input middle)
      (rest : StackPorts signature tickets world tail middle result) :
      StackPorts signature tickets world (.push entry tail) input result
  | live (known : tickets owner = some (eraseType input, eraseType answer))
      (scope : ScopeKnown tickets callerScope)
      (saved : StackPorts signature tickets world captured (eraseType input) (eraseType answer))
      (rest : StackPorts signature tickets world tail (eraseType answer) result) :
      StackPorts signature tickets world (.live owner input answer captured callerScope tail) (eraseType answer) result
  | spent (known : tickets owner = some (argument, eraseType answer))
      (scope : ScopeKnown tickets callerScope)
      (rest : StackPorts signature tickets world tail (eraseType answer) result) :
      StackPorts signature tickets world (.spent owner answer callerScope tail) (eraseType answer) result

theorem ordinary_stack_ports (typed : StackTyped signature tickets world stack input result) :
    StackPorts signature tickets world stack input result := by
  induction typed with
  | nil => exact .nil
  | push frame rest ih => exact .push (.ordinary frame) ih
  | live known scope saved rest ihSaved ihRest => exact .live known scope ihSaved ihRest
  | spent known scope rest ih => exact .spent known scope ih

theorem stack_ports_append
    (front : StackPorts signature tickets world left input middle)
    (tail : StackPorts signature tickets world right middle result) :
    StackPorts signature tickets world (left.append right) input result := by
  induction front with
  | nil => exact tail
  | push frame rest ih => exact .push frame (ih tail)
  | live known scope saved rest ihSaved ihRest => exact .live known scope saved (ihRest tail)
  | spent known scope rest ih => exact .spent known scope (ih tail)

inductive MachinePorts (signature : Signature) (tickets : TicketSignatures) (world : ScopedTyping.World) :
    Machine → Port → Prop where
  | eval (expression : AtType signature tickets world scope code input)
      (stack : StackPorts signature tickets world frames input result) :
      MachinePorts signature tickets world (.eval ⟨code, scope, frames⟩) result
  | unwind (scope : ScopeKnown tickets runtimeScope)
      (stack : StackPorts signature tickets world frames input result) :
      MachinePorts signature tickets world (.unwind runtimeScope frames) result

theorem administrative_ports (step : Advance before after discharged)
    (typed : StackPorts signature tickets world before input result) :
    ∃ nextInput, StackPorts signature tickets world after nextInput result := by
  cases step with
  | plain | handler | cell | retire => cases typed with
      | push frame rest => exact ⟨_, rest⟩
  | spent => cases typed with
      | spent known scope rest => exact ⟨_, rest⟩
  | live => cases typed with
      | live known scope saved rest =>
          exact ⟨_, stack_ports_append saved (.push (.retiring known) rest)⟩

theorem start_cleanup_ports
    (typed : MachinePorts signature tickets world (.unwind scope (.push (.armed action) rest)) result) :
    MachinePorts signature tickets world
      (.eval ⟨.app action.action .unit, .none, .push (.unwinding action) rest⟩) result := by
  cases typed with
  | unwind current stack => cases stack with
      | push frame tail => cases frame with
          | ordinary frame => cases frame with
              | armed scope callable =>
                  exact .eval (.checked .none (cleanup_entry_ports callable).1)
                    (.push (.unwinding scope callable) tail)

theorem finish_cleanup_ports
    (typed : MachinePorts signature tickets world
      (.eval ⟨.unit, scope, .push (.unwinding action) rest⟩) result) :
    MachinePorts signature tickets world (.unwind action.scope rest) result := by
  cases typed with
  | eval expression stack => cases stack with
      | push frame tail => cases frame with
          | ordinary impossible => cases impossible
          | unwinding scope callable => exact .unwind scope tail

theorem finish_close_ports
    (typed : MachinePorts signature tickets world
      (.unwind scope (.push (.closing identity callerScope) tail)) result) :
    MachinePorts signature tickets world (.eval ⟨.unit, callerScope, tail⟩) result := by
  cases typed with
  | unwind current stack => cases stack with
      | push frame rest => cases frame with
          | ordinary frame => cases frame with
              | closing scope =>
                  obtain ⟨ticket, scope⟩ := scope
                  exact .eval (.checked (allowed := []) scope .unit) rest
          | closing scope =>
              obtain ⟨ticket, scope⟩ := scope
              exact .eval (.checked (allowed := []) scope .unit) rest

/-- Normal return through a retirement marker preserves its value and port. -/
theorem retire_value_ports
    (typed : MachinePorts signature tickets world
      (.eval ⟨value, scope, .push (.retiring owner) tail⟩) result) :
    MachinePorts signature tickets world (.eval ⟨value, scope, tail⟩) result := by
  cases typed with
  | eval expression stack => cases stack with
      | push frame rest => cases frame with
          | ordinary frame => cases frame with
              | retiring known => exact .eval expression rest
          | retiring known => exact .eval expression rest

/-- A completed disposal returns Unit to its caller, independent of the
    abandoned scope's ordinary answer port. -/
theorem close_value_ports
    (typed : MachinePorts signature tickets world
      (.eval ⟨value, scope, .push (.closing identity callerScope) tail⟩) result) :
    MachinePorts signature tickets world (.eval ⟨.unit, callerScope, tail⟩) result := by
  cases typed with
  | eval expression stack => cases stack with
      | push frame rest => cases frame with
          | ordinary frame => cases frame with
              | closing scope =>
                  obtain ⟨ticket, scope⟩ := scope
                  exact .eval (.checked (allowed := []) scope .unit) rest
          | closing scope =>
              obtain ⟨ticket, scope⟩ := scope
              exact .eval (.checked (allowed := []) scope .unit) rest

#print axioms Ash.OneShot.LexicalUnwind.retire_value_ports
#print axioms Ash.OneShot.LexicalUnwind.close_value_ports
#print axioms Ash.OneShot.LexicalUnwind.ordinary_stack_ports
#print axioms Ash.OneShot.LexicalUnwind.stack_ports_append
#print axioms Ash.OneShot.LexicalUnwind.administrative_ports
#print axioms Ash.OneShot.LexicalUnwind.start_cleanup_ports
#print axioms Ash.OneShot.LexicalUnwind.finish_cleanup_ports
#print axioms Ash.OneShot.LexicalUnwind.finish_close_ports
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open Instantiation ScopedExpressions ScopedExecution ScopedPorts

/-- Split the retained stack at an explicit lexical boundary. This is the
    existing stack decomposition induction, with explicit adjacent ports. -/
theorem stack_ports_decompose (front : Stack)
    (typed : StackPorts signature tickets world (front.append tail) input result) :
    ∃ middle, StackPorts signature tickets world front input middle ∧
      StackPorts signature tickets world tail middle result := by
  induction front generalizing input with
  | nil => exact ⟨_, .nil, typed⟩
  | push entry rest ih => cases typed with
      | push frame tail =>
          obtain ⟨middle, frontTyped, outside⟩ := ih tail
          exact ⟨middle, .push frame frontTyped, outside⟩
  | live owner q a saved scope rest ihSaved ihRest => cases typed with
      | live known scope saved tail =>
          obtain ⟨middle, frontTyped, outside⟩ := ihRest tail
          exact ⟨middle, .live known scope saved frontTyped, outside⟩
  | spent owner a scope rest ih => cases typed with
      | spent known scope tail =>
          obtain ⟨middle, frontTyped, outside⟩ := ih tail
          exact ⟨middle, .spent known scope frontTyped, outside⟩

/-- Capturing an unwind return marker uses the same handler cut and unchanged
    handler typing. The induction does not inspect intervening frame payloads. -/
theorem handler_cut_ports
    (cut : HandlerCut requested whole cap tail handler)
    (typed : StackPorts signature tickets world whole input result) :
    StackPorts signature tickets world cap input (eraseType handler.answer) ∧
      StackPorts signature tickets world tail (eraseType handler.answer) result ∧
      ScopedPorts.FrameTyped signature tickets world (.handler handler) := by
  induction cut generalizing input result with
  | hit handler tail same => cases typed with
      | push frame rest => cases frame with
          | ordinary frame => exact ⟨.push (.ordinary frame) .nil, rest, frame⟩
  | push entry rest cap tail handler miss next ih => cases typed with
      | push frame rest =>
          obtain ⟨saved, outside, handlerTyped⟩ := ih rest
          exact ⟨.push frame saved, outside, handlerTyped⟩
  | live owner q a saved scope rest cap tail handler next ih => cases typed with
      | live known scope saved rest =>
          obtain ⟨inside, outside, handlerTyped⟩ := ih rest
          exact ⟨.live known scope saved inside, outside, handlerTyped⟩
  | spent owner a scope rest cap tail handler next ih => cases typed with
      | spent known scope rest =>
          obtain ⟨inside, outside, handlerTyped⟩ := ih rest
          exact ⟨.spent known scope inside, outside, handlerTyped⟩

theorem frame_ports_extension (typed : FramePorts signature before world frame input output)
    (extension : TicketExtension before after) : FramePorts signature after world frame input output := by
  cases typed with
  | ordinary frame => exact .ordinary (frame_typed_extension frame extension)
  | unwinding scope callable => exact .unwinding (scope_known_extension scope extension) callable
  | closing scope => exact .closing (scope_known_extension scope extension)
  | retiring known => exact .retiring (extension _ _ _ known)

theorem stack_ports_extension (typed : StackPorts signature before world stack input result)
    (extension : TicketExtension before after) : StackPorts signature after world stack input result := by
  induction typed with
  | nil => exact .nil
  | push frame rest ih => exact .push (frame_ports_extension frame extension) ih
  | live known scope saved rest ihSaved ihRest =>
      exact .live (extension _ _ _ known) (scope_known_extension scope extension) ihSaved ihRest
  | spent known scope rest ih =>
      exact .spent (extension _ _ _ known) (scope_known_extension scope extension) ih

/-- Reuse clause selection and substitution from ordinary port typing. Only
    the retained-stack induction is generalized to the unwind return marker. -/
theorem capture_ports
    (cut : HandlerCut requested whole cap tail handler)
    (typed : MachinePorts signature tickets world
      (.eval ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩) result)
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port),
      let extended := tickets.insert owner output (eraseType handler.answer)
      Transition (.eval ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩)
        (.eval ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩) [.ticket owner] [] ∧
      TicketExtension tickets extended ∧
      MachinePorts signature extended world
        (.eval ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩) result := by
  cases typed with
  | @eval _ _ output _ _ expression stack => cases expression with
      | checked scopeTyped expression =>
          obtain ⟨input, operationType, available, operandTyped⟩ := typed_perform_inversion expression
          have closed := typed_value_closed operandTyped isValue
          obtain ⟨saved, outside, handlerTyped⟩ := handler_cut_ports cut stack
          cases handlerTyped with
          | handler caller clauses coverage unique =>
              have known := operationType
              rw [← ScopedTyping.handler_cut_instance cut] at known
              obtain ⟨parameter, binder, body, selected⟩ := ScopedTyping.clause_at_of_key (coverage _ _ _ known)
              have extension := fresh_ticket_signature_extension (input := output) (answer := eraseType handler.answer) fresh
              have newTicket : (tickets.insert owner output (eraseType handler.answer)) owner = some (output, eraseType handler.answer) := by
                simp [TicketSignatures.insert]
              obtain ⟨clauseInput, clauseOutput, clauseKnown, bodyTyped⟩ := selected_clause_typed selected clauses
              refine ⟨parameter, binder, body, _, .evaluate (.capture requested operation parameter binder owner
                operand body scope whole cap tail handler _ cut selected closed (typed_suffix_ready bodyTyped)) trivial,
                extension, .eval (.checked (.bound newTicket)
                  (selected_clause_substitution_typed selected clauses known operandTyped closed)) ?_⟩
              exact .live (by simpa using newTicket) (scope_known_extension caller extension)
                (by simpa using stack_ports_extension saved extension) (stack_ports_extension outside extension)

/-- Restoring the captured scopes preserves their ports, including cleanup
    return markers and disposal boundaries captured by a callback request. -/
theorem resume_ports {front cap tail : Stack}
    (resolved : scope.resolve binder = some owner)
    (typed : MachinePorts signature tickets world
      (.eval ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩) result) :
    MachinePorts signature tickets world
      (.eval ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩) result := by
  cases typed with
  | eval expression stack => cases expression with
      | checked scopeType expression => cases expression with
          | resume operand effects formed => cases scopeType with
              | bound known =>
                  simp [Execution.Scope.resolve] at resolved
                  subst owner
                  obtain ⟨middle, frontTyped, outside⟩ := stack_ports_decompose front stack
                  cases outside with
                  | live actual caller saved rest =>
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actual))
                      exact .eval (.checked (.bound known) operand)
                        (stack_ports_append saved (stack_ports_append frontTyped (.spent known caller rest)))

/-- Disposal keeps the captured scopes and their existing answer ports. No
    plan, answer conversion, or retyping of an installed handler is needed. -/
theorem discard_ports {front cap tail : Stack}
    (typed : MachinePorts signature tickets world
      (.eval ⟨.discard binder, scope, front.append (.live owner input answer cap callerScope tail)⟩) result) :
    MachinePorts signature tickets world
      (.unwind scope (cap.append (.push (.closing identity scope)
        (front.append (.spent owner answer callerScope tail))))) result := by
  cases typed with
  | eval expression stack => cases expression with
      | checked scopeTyped expression => cases expression with
          | discard effects =>
              obtain ⟨middle, frontTyped, outside⟩ := stack_ports_decompose front stack
              cases outside with
              | live known caller saved rest =>
                  exact .unwind ⟨_, scopeTyped⟩ (stack_ports_append saved
                    (.push (.closing ⟨_, scopeTyped⟩) (stack_ports_append frontTyped (.spent known caller rest))))

#print axioms Ash.OneShot.LexicalUnwind.stack_ports_decompose
#print axioms Ash.OneShot.LexicalUnwind.handler_cut_ports
#print axioms Ash.OneShot.LexicalUnwind.frame_ports_extension
#print axioms Ash.OneShot.LexicalUnwind.stack_ports_extension
#print axioms Ash.OneShot.LexicalUnwind.capture_ports
#print axioms Ash.OneShot.LexicalUnwind.resume_ports
#print axioms Ash.OneShot.LexicalUnwind.discard_ports
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open Instantiation ScopedExpressions ScopedExecution ScopedPorts

/-- Ordinary value returns use the existing expression proofs. The enclosing
    stack may contain unwind markers; only its top frame is inspected. -/
theorem raw_value_ports
    (step : RawStep before after created discharged)
    (closed : ClosedValue before.expression)
    (typed : MachinePorts signature tickets world (.eval before) result) :
    MachinePorts signature tickets world (.eval after) result := by
  cases typed with
  | eval expression stack =>
      cases step with
      | focus plain focus tail => exact False.elim (ScopedPorts.focus_is_not_value focus closed.1)
      | bind | beta | ifTrue | ifFalse | enterHandler | enterCell | enterCleanup
      | capture | resume | discard | readCell | writeCell => cases closed.1
      | plug plain value valueClosed scope tail => cases stack with
          | push frame rest => cases frame with
              | ordinary frame => cases frame with
                  | plain scopeTyped context =>
                      have valueTyped := at_type_closed_value expression valueClosed
                      exact .eval (.checked scopeTyped (context_plug_typed context
                        (typed_value_transport valueTyped valueClosed.1 _ _))) rest
      | leaveHandler handler value valueClosed scope tail => cases stack with
          | push frame rest => cases frame with
              | ordinary frame => cases frame with
                  | handler caller clauses coverage unique =>
                      exact .eval (at_type_value_transport expression valueClosed caller) rest
      | leaveCell identity payload answer savedScope scope value valueClosed tail => cases stack with
          | push frame rest => cases frame with
              | ordinary frame => cases frame with
                  | cell caller noEscape => exact .eval (at_type_value_transport expression valueClosed caller) rest
      | startCleanup action saved savedClosed scope tail => cases stack with
          | push frame rest => cases frame with
              | ordinary frame => cases frame with
                  | armed caller callable =>
                      exact .eval (.checked .none (cleanup_entry_ports callable).1)
                        (.push (.ordinary (.running caller callable (at_type_closed_value expression savedClosed))) rest)
      | finishCleanup action saved savedClosed scope tail => cases stack with
          | push frame rest => cases frame with
              | ordinary frame => cases frame with
                  | running caller callable savedTyped =>
                      obtain ⟨ticket, scopeTyped⟩ := caller
                      exact .eval (.checked scopeTyped (typed_value_transport savedTyped savedClosed.1 ticket [])) rest
      | leaveClause owner answer value valueClosed scope callerScope tail => cases stack with
          | spent known caller rest => exact .eval (at_type_value_transport expression valueClosed caller) rest
      | finishClose identity scope callerScope tail =>
          exact close_value_ports (.eval expression stack)
      | retire owner scope tail => exact retire_value_ports (.eval expression stack)

/-- All value-completion transitions in the new machine preserve ports,
    including returning from a callback directly into abandonment. -/
theorem value_transition_ports
    (step : Transition (.eval before) after created discharged)
    (isValue : before.expression.IsValue)
    (typed : MachinePorts signature tickets world (.eval before) result) :
    MachinePorts signature tickets world after result := by
  cases step with
  | evaluate raw ordinary =>
      have closed : ClosedValue before.expression := by
        cases typed with
        | eval expression stack => exact at_type_value_closed expression isValue
      exact raw_value_ports raw closed typed
  | finishCleanup => exact finish_cleanup_ports typed
  | discard => cases isValue
  | retireValue => exact retire_value_ports typed
  | closeValue => exact close_value_ports typed

/-- Every transition beginning in unwind mode preserves its result port.
    This includes expansion of dormant captures and invocation of a callback. -/
theorem unwind_transition_ports
    (step : Transition (.unwind scope stack) after created discharged)
    (typed : MachinePorts signature tickets world (.unwind scope stack) result) :
    MachinePorts signature tickets world after result := by
  cases step with
  | advance nextStep => cases typed with
      | unwind scope frames =>
          obtain ⟨input, next⟩ := administrative_ports nextStep frames
          exact .unwind scope next
  | startCleanup => exact start_cleanup_ports typed
  | finishClose => exact finish_close_ports typed

#print axioms Ash.OneShot.LexicalUnwind.raw_value_ports
#print axioms Ash.OneShot.LexicalUnwind.value_transition_ports
#print axioms Ash.OneShot.LexicalUnwind.unwind_transition_ports
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open Instantiation ScopedExpressions ScopedExecution ScopedPorts

/-- Resource allocation transports existing frame payload typing unchanged. -/
theorem frame_ports_world_weaken
    (typed : FramePorts signature tickets world frame input output) (larger : world ⊆ next) :
    FramePorts signature tickets next frame input output := by
  cases typed with
  | ordinary frame => exact .ordinary (frame_world_weaken frame larger)
  | unwinding scope callable => exact .unwinding scope (typed_world_weaken callable next larger)
  | closing scope => exact .closing scope
  | retiring known => exact .retiring known

theorem stack_ports_world_weaken
    (typed : StackPorts signature tickets world stack input result) (larger : world ⊆ next) :
    StackPorts signature tickets next stack input result := by
  induction typed with
  | nil => exact .nil
  | push frame rest ih => exact .push (frame_ports_world_weaken frame larger) ih
  | live known scope saved rest ihSaved ihRest => exact .live known scope ihSaved ihRest
  | spent known scope rest ih => exact .spent known scope ih

theorem cell_update_ports
    (update : CellUpdate identity old new before after)
    (typed : StackPorts signature tickets world before input result) :
    StackPorts signature tickets world after input result := by
  induction update generalizing input result with
  | hit => cases typed with
      | push frame rest => cases frame with
          | ordinary frame => cases frame with
              | cell caller noEscape => exact .push (.ordinary (.cell caller noEscape)) rest
  | push miss next ih => cases typed with
      | push frame rest => exact .push frame (ih rest)
  | live next ih => cases typed with
      | live known caller saved rest => exact .live known caller saved (ih rest)
  | spent next ih => cases typed with
      | spent known caller rest => exact .spent known caller (ih rest)

/-- Bind, application, branching and builtin cell operations use the existing
    ordinary step family, with no restriction on enclosing unwind markers. -/
theorem ordinary_step_ports
    (step : ScopedPortJoint.OrdinaryStep before after)
    (typed : MachinePorts (withCellSignatures users) tickets world (.eval before) result) :
    MachinePorts (withCellSignatures users) tickets world (.eval after) result := by
  cases typed with
  | eval expression stack => cases expression with
      | checked scopeTyped expression => cases step with
          | bind closed environment => cases expression with
              | bind initializer suffix =>
                  exact .eval (.checked scopeTyped
                    (typed_substitution suffix (typed_value_transport initializer closed.1 .none []) closed)) stack
          | beta closed closure => cases expression with
              | app function argument available => cases function with
                  | lambda bodyTyped formed =>
                      exact .eval (.checked .none
                        (typed_substitution bodyTyped (typed_value_transport argument closed.1 .none []) closed)) stack
          | ifTrue => cases expression with
              | branch condition yes no => exact .eval (.checked scopeTyped yes) stack
          | ifFalse => cases expression with
              | branch condition yes no => exact .eval (.checked scopeTyped no) stack
          | read selected =>
              obtain ⟨input, operation, available, operand⟩ := typed_perform_inversion expression
              simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
              obtain ⟨rfl, rfl⟩ := operation
              exact .eval (.checked (allowed := []) scopeTyped .integer) (cell_update_ports selected stack)
          | write selected =>
              obtain ⟨input, operation, available, operand⟩ := typed_perform_inversion expression
              simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
              obtain ⟨rfl, rfl⟩ := operation
              exact .eval (.checked (allowed := []) scopeTyped .unit) (cell_update_ports selected stack)

/-- The existing focus elaboration supplies both frame annotations. -/
theorem focus_ports
    (typed : MachinePorts signature tickets world (.eval ⟨whole, scope, tail⟩) result)
    (focus : Focus whole child context) :
    ∃ plain : PlainData,
      Transition (.eval ⟨whole, scope, tail⟩) (.eval ⟨child, scope, .push (.plain plain) tail⟩) [] [] ∧
      MachinePorts signature tickets world (.eval ⟨child, scope, .push (.plain plain) tail⟩) result := by
  cases typed with
  | eval expression stack => cases expression with
      | checked scopeTyped expression =>
          obtain ⟨plain, raw, childTyped, contextTyped, output, shape, savedScope⟩ :=
            typed_focus_progress focus expression (scope_typed_names_match scopeTyped) tail
          have frame : FrameTyped signature tickets world (.plain plain) :=
            .plain (by rw [savedScope]; exact scopeTyped) (by rw [output]; exact contextTyped)
          refine ⟨plain, .evaluate raw ?_, .eval (.checked scopeTyped childTyped) ?_⟩
          · cases focus <;> trivial
          · exact .push (.ordinary frame) (by simpa only [ExecFrame.erase, PlainData.erase, output] using stack)

/-- A handler installation keeps the existing clause typing and declared answer. -/
theorem handler_entry_ports
    (typed : MachinePorts signature tickets world (.eval ⟨.handle source body clauses, scope, tail⟩) result)
    (activation : Nat) :
    ∃ handler : HandlerData, handler.activation = activation ∧
      Transition (.eval ⟨.handle source body clauses, scope, tail⟩)
        (.eval ⟨body, scope, .push (.handler handler) tail⟩) [] [] ∧
      MachinePorts signature tickets world (.eval ⟨body, scope, .push (.handler handler) tail⟩) result := by
  cases typed with
  | @eval _ _ answer _ _ expression stack => cases expression with
      | checked scopeTyped expression => cases expression with
          | @handle _ _ _ effect _ _ _ _ _ bodyTyped clausesTyped coverage unique available =>
              let handler : HandlerData := ⟨activation, effect, clauses, scope, embedPort answer, clauses_have_ticket_barrier clausesTyped⟩
              have frame : FrameTyped signature tickets world (.handler handler) :=
                .handler ⟨_, scopeTyped⟩ (by simpa [handler] using clausesTyped) coverage unique
              refine ⟨handler, rfl, .evaluate (.enterHandler handler body tail) trivial, .eval (.checked scopeTyped bodyTyped) ?_⟩
              simpa [handler, ExecFrame.erase, HandlerData.erase] using
                StackPorts.push (.ordinary frame) (by simpa [handler, ExecFrame.erase, HandlerData.erase] using stack)

/-- Cleanup registers the existing closed callback and creates an armed frame. -/
theorem cleanup_entry_machine_ports
    (typed : MachinePorts signature tickets world (.eval ⟨.cleanup callback body, scope, tail⟩) result)
    (isValue : callback.IsValue) (identity : Nat) :
    ∃ action : ActionData, action.identity = identity ∧
      Transition (.eval ⟨.cleanup callback body, scope, tail⟩)
        (.eval ⟨body, scope, .push (.armed action) tail⟩) [.cleanup identity] [] ∧
      MachinePorts signature tickets world (.eval ⟨body, scope, .push (.armed action) tail⟩) result := by
  cases typed with
  | @eval _ _ answer _ _ expression stack => cases expression with
      | checked scopeTyped expression => cases expression with
          | @cleanup _ _ _ _ _ latent _ _ callbackTyped bodyTyped available =>
              have closed := typed_value_closed callbackTyped isValue
              let action : ActionData := ⟨identity, callback, closed, scope, embedPort answer, latent⟩
              have frame : FrameTyped signature tickets world (.armed action) :=
                .armed ⟨_, scopeTyped⟩ (typed_value_transport callbackTyped isValue .none [])
              refine ⟨action, rfl, .evaluate (.enterCleanup action body tail) trivial, .eval (.checked scopeTyped bodyTyped) ?_⟩
              simpa [action, ExecFrame.erase, ActionData.erase] using
                StackPorts.push (.ordinary frame) (by simpa [action, ExecFrame.erase, ActionData.erase] using stack)

/-- Allocation reuses fresh instantiation and world extension from the existing
    resource typing proof; enclosing scopes may include unwind return markers. -/
theorem resource_entry_ports
    (typed : MachinePorts signature tickets (ScopedTyping.resourceWorld issued)
      (.eval ⟨.resource binder initializer body, scope, tail⟩) result)
    (isValue : initializer.IsValue) (fresh : Owner.resource identity ∉ issued) :
    ∃ payload answer,
      initializer = .integer payload ∧
      Transition (.eval ⟨.resource binder initializer body, scope, tail⟩)
        (.eval ⟨body.instantiate (Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope (embedPort answer)) tail⟩) [.resource identity] [] ∧
      MachinePorts signature tickets (ScopedTyping.resourceWorld (issued ++ [.resource identity]))
        (.eval ⟨body.instantiate (Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope (embedPort answer)) tail⟩) result := by
  cases typed with
  | @eval _ _ answer _ _ expression stack => cases expression with
      | checked scopeTyped expression =>
          obtain ⟨payload, same⟩ : ∃ payload, initializer = .integer payload := by
            cases expression with
            | resource init opened resultBound effectsBound effects => exact typed_integer_value init isValue
          subst initializer
          obtain ⟨residual, bodyTyped, noEscape, noEffectEscape, effects⟩ := resource_body_typed_at_fresh expression fresh
          have larger : ScopedTyping.resourceWorld issued ⊆ ScopedTyping.resourceWorld (issued ++ [.resource identity]) := by
            rw [ScopedTyping.resource_world_append]
            exact List.subset_append_left _ _
          refine ⟨payload, answer, rfl, .evaluate (.enterCell binder identity payload body scope (embedPort answer) tail
            (typed_resource_closed expression)) trivial, .eval (.checked scopeTyped bodyTyped) ?_⟩
          have frame : FrameTyped signature tickets (ScopedTyping.resourceWorld (issued ++ [.resource identity]))
              (.cell identity payload scope (embedPort answer)) :=
            .cell ⟨_, scopeTyped⟩ (by simpa using noEscape)
          simpa [ExecFrame.erase] using StackPorts.push (.ordinary frame)
            (by simpa [ExecFrame.erase] using stack_ports_world_weaken stack larger)

#print axioms Ash.OneShot.LexicalUnwind.frame_ports_world_weaken
#print axioms Ash.OneShot.LexicalUnwind.stack_ports_world_weaken
#print axioms Ash.OneShot.LexicalUnwind.cell_update_ports
#print axioms Ash.OneShot.LexicalUnwind.ordinary_step_ports
#print axioms Ash.OneShot.LexicalUnwind.focus_ports
#print axioms Ash.OneShot.LexicalUnwind.handler_entry_ports
#print axioms Ash.OneShot.LexicalUnwind.cleanup_entry_machine_ports
#print axioms Ash.OneShot.LexicalUnwind.resource_entry_ports
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open Instantiation ScopedExpressions ScopedExecution ScopedPorts

/-- Proof-only projection for reusing effect interfaces. It retains every
    scope and action, and changes only the callback's return-mode tag.
    Port typing, protection and execution always use the original stack. -/
def effectFrameView : ExecFrame → ExecFrame
  | .unwinding action => .armed action
  | frame => frame

def effectView : Stack → Stack
  | .nil => .nil
  | .push frame rest => .push (effectFrameView frame) (effectView rest)
  | .live owner input answer saved scope rest =>
      .live owner input answer (effectView saved) scope (effectView rest)
  | .spent owner answer scope rest => .spent owner answer scope (effectView rest)

@[simp] theorem effect_view_append (front tail : Stack) :
    effectView (front.append tail) = (effectView front).append (effectView tail) := by
  induction front with
  | nil => rfl
  | push frame rest ih => simp [Stack.append, effectView, ih]
  | live owner input answer saved scope rest ihSaved ihRest => simp [Stack.append, effectView, ihRest]
  | spent owner answer scope rest ih => simp [Stack.append, effectView, ih]

@[simp] theorem effect_frame_view_resolve (frame : ExecFrame) :
    (effectFrameView frame).erase.resolve requested = frame.erase.resolve requested := by
  cases frame <;> rfl

/-- This projection changes neither the selected installation nor shadowing. -/
@[simp] theorem effect_view_resolve (stack : Stack) :
    (effectView stack).erase.resolve requested = stack.erase.resolve requested := by
  induction stack with
  | nil => rfl
  | push frame rest ih => simp only [effectView, Stack.erase, Control.resolve, effect_frame_view_resolve, ih]
  | live owner input answer saved scope rest ihSaved ihRest => exact ihRest
  | spent owner answer scope rest ih => exact ih

theorem effect_view_cut (cut : HandlerCut requested whole cap tail handler) :
    HandlerCut requested (effectView whole) (effectView cap) (effectView tail) handler := by
  induction cut with
  | hit handler tail same => exact .hit handler _ same
  | push frame rest cap tail handler miss next ih =>
      apply HandlerCut.push _ _ _ _ _ ?_ ih
      cases frame <;> exact miss
  | live owner input answer saved scope rest cap tail handler next ih => exact .live _ _ _ _ _ _ _ _ _ ih
  | spent owner answer scope rest cap tail handler next ih => exact .spent _ _ _ _ _ _ _ ih

/-- Independent effect interface. Ordinary expressions reuse EffectAtType;
    abandonment has no expression effect row, but retains all scoped callbacks. -/
inductive MachineEffects (signature : Signature) (tickets : EffectTickets) (world : ScopedTyping.World) :
    Machine → List Instance → Prop where
  | eval (expression : EffectAtType signature tickets world scope code input incoming)
      (stack : EffectStack signature tickets world (effectView frames) incoming outgoing) :
      MachineEffects signature tickets world (.eval ⟨code, scope, frames⟩) outgoing
  | unwind (scope : EffectScopeKnown tickets runtimeScope)
      (stack : EffectStack signature tickets world (effectView frames) incoming outgoing) :
      MachineEffects signature tickets world (.unwind runtimeScope frames) outgoing

/-- An effect request still finds the existing nearest exact interpretation.
    A closed outgoing row rules out the exported alternative. -/
theorem machine_request_provided_or_exported
    (typed : MachineEffects signature tickets world
      (.eval ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩) outgoing) :
    (∃ target, stack.erase.resolve requested = some target) ∨ requested ∈ outgoing := by
  cases typed with
  | eval expression control => cases expression with
      | checked scope expression =>
          obtain ⟨input, known, available, operandTyped⟩ := typed_perform_inversion expression
          simpa only [effect_view_resolve] using effect_stack_provides_or_exports control available

/-- The projection embeds ordinary effect typing without changing a source
    judgment. The induction excludes the new tag in old EffectFrame evidence. -/
theorem ordinary_effect_view
    (typed : EffectStack signature tickets world stack incoming outgoing) :
    EffectStack signature tickets world (effectView stack) incoming outgoing := by
  induction typed with
  | nil bound => exact .nil bound
  | @push entry inner outer tail outgoing incoming frame rest bound ih =>
      have same : effectFrameView entry = entry := by cases frame <;> rfl
      exact .push (same.symm ▸ frame) ih bound
  | live known scope saved rest resume close bound ihSaved ihRest =>
      exact .live known scope ihSaved ihRest resume close bound
  | spent known scope rest bound ih => exact .spent known scope ih bound

/-- Dropping only the top scope drops its incoming obligations. A dormant
    continuation exposes its own checked scopes before retiring its owner. -/
theorem administrative_effects (step : Advance before after discharged)
    (typed : EffectStack signature tickets world (effectView before) incoming outgoing) :
    ∃ nextIncoming, EffectStack signature tickets world (effectView after) nextIncoming outgoing := by
  cases step with
  | plain | handler | cell | retire => cases typed with
      | push frame rest bound => exact ⟨_, rest⟩
  | spent => cases typed with
      | spent known scope rest bound => exact ⟨_, rest⟩
  | live => cases typed with
      | live known scope saved rest resume close bound =>
          rename_i contract captured boundary
          refine ⟨captured, ?_⟩
          rw [effect_view_append]
          exact effect_stack_append saved (.push (.retiring known) rest resume)

theorem start_cleanup_effects
    (typed : MachineEffects signature tickets world (.unwind scope (.push (.armed action) rest)) outgoing) :
    MachineEffects signature tickets world
      (.eval ⟨.app action.action .unit, .none, .push (.unwinding action) rest⟩) outgoing := by
  cases typed with
  | unwind current stack => cases stack with
      | push frame tail bound => cases frame with
          | armed scope callable requests =>
              exact .eval (.checked .none (cleanup_entry_ports callable).1)
                (.push (.armed scope callable requests) tail requests)

theorem finish_cleanup_effects
    (typed : MachineEffects signature tickets world
      (.eval ⟨.unit, scope, .push (.unwinding action) rest⟩) outgoing) :
    MachineEffects signature tickets world (.unwind action.scope rest) outgoing := by
  cases typed with
  | eval expression stack => cases stack with
      | push frame tail bound => cases frame with
          | armed scope callable requests => exact .unwind scope tail

theorem close_effects
    (typed : EffectStack signature tickets world (effectView (.push (.closing identity callerScope) tail)) incoming outgoing) :
    MachineEffects signature tickets world (.eval ⟨.unit, callerScope, tail⟩) outgoing := by
  cases typed with
  | push frame rest bound => cases frame with
      | closing caller =>
          obtain ⟨ticket, scope⟩ := caller
          exact .eval (.checked scope (Typed.unit (allowed := [])))
            (effect_stack_input_weaken rest (List.nil_subset _))

theorem unwind_transition_effects
    (step : Transition (.unwind scope stack) after created discharged)
    (typed : MachineEffects signature tickets world (.unwind scope stack) outgoing) :
    MachineEffects signature tickets world after outgoing := by
  cases step with
  | advance nextStep => cases typed with
      | unwind scope frames =>
          obtain ⟨input, next⟩ := administrative_effects nextStep frames
          exact .unwind scope next
  | startCleanup => exact start_cleanup_effects typed
  | finishClose => cases typed with
      | unwind scope frames => exact close_effects frames

/-- Local disposal uses the existing captured effect interface. The closing
    row must cover its outward row; contracts allocated by capture use equal
    resume/close rows, so that obligation is discharged at allocation. -/
theorem discard_effects {front cap tail : Stack}
    (typed : MachineEffects signature tickets world
      (.eval ⟨.discard binder, scope, front.append (.live owner input answer cap callerScope tail)⟩) outgoing)
    (resolved : scope.resolve binder = some owner)
    (closing : ∀ contract, tickets owner = some contract → contract.resumeEffects ⊆ contract.closeEffects) :
    MachineEffects signature tickets world
      (.unwind scope (cap.append (.push (.closing identity scope)
        (front.append (.spent owner answer callerScope tail))))) outgoing := by
  cases typed with
  | eval expression stack => cases expression with
      | checked scopeTyped expression => cases expression with
          | discard allowed => cases scopeTyped with
              | bound known =>
                  simp [Execution.Scope.resolve] at resolved
                  subst owner
                  rw [effect_view_append] at stack
                  obtain ⟨middle, frontTyped, outside⟩ := effect_stack_decompose (effectView front) stack
                  cases outside with
                  | live actual caller saved rest resume close bound =>
                      have same := Option.some.inj (known.symm.trans actual)
                      cases same
                      apply MachineEffects.unwind ⟨_, .bound known⟩
                      rw [effect_view_append]
                      apply effect_stack_append saved
                      exact .push (.closing ⟨_, .bound known⟩)
                        (by simpa [effectView] using effect_stack_append frontTyped (.spent known caller rest bound))
                        ((closing _ known).trans allowed)


/-- Capture reuses the established effect-cut and clause-substitution proofs.
    The allocated continuation has equal resume and closing outward rows. -/
theorem capture_effects
    (cut : HandlerCut requested whole cap tail handler)
    (typed : MachineEffects signature tickets world
      (.eval ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩) outgoing)
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port) (residual : List Instance),
      let contract : ContinuationContract := ⟨output, eraseType handler.answer, residual, residual⟩
      let extended := tickets.insert owner contract
      Transition (.eval ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩)
        (.eval ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩) [.ticket owner] [] ∧
      EffectExtension tickets extended ∧
      MachineEffects signature extended world
        (.eval ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩) outgoing := by
  cases typed with
  | @eval _ _ output _ _ _ expression effectStack => cases expression with
      | checked scopeTyped expression =>
          obtain ⟨input, operationType, available, operandTyped⟩ := typed_perform_inversion expression
          have closed := typed_value_closed operandTyped isValue
          obtain ⟨residual, capturedEffects, outsideEffects, handlerEffects⟩ :=
            handler_cut_effect_decomposition (effect_view_cut cut) effectStack
          cases handlerEffects with
          | handler caller clauses coverage unique =>
              have operationAtHandler := operationType
              rw [← ScopedTyping.handler_cut_instance cut] at operationAtHandler
              obtain ⟨parameter, binder, body, selected⟩ := ScopedTyping.clause_at_of_key (coverage _ _ _ operationAtHandler)
              obtain ⟨clauseInput, clauseOutput, clauseSignature, bodyTyped⟩ := selected_clause_typed selected clauses
              let contract : ContinuationContract := ⟨output, eraseType handler.answer, residual, residual⟩
              let extended := tickets.insert owner contract
              have extension : EffectExtension tickets extended := effect_ticket_insertion_extends fresh
              have newTicket : extended owner = some contract := by simp [extended, EffectTickets.insert]
              refine ⟨parameter, binder, body, output, residual,
                .evaluate (.capture requested operation parameter binder owner operand body scope whole cap tail handler
                  (embedPort output) cut selected closed (typed_suffix_ready bodyTyped)) trivial,
                extension, .eval (.checked (.bound newTicket)
                  (selected_clause_substitution_typed selected clauses operationAtHandler operandTyped closed)) ?_⟩
              exact .live newTicket (effect_scope_known_extension caller extension)
                (effect_stack_extension capturedEffects extension) (effect_stack_extension outsideEffects extension)
                (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)

/-- Resumption restores interpretation scopes through the same effect
    recomposition lemma as ordinary evaluation. -/
theorem resume_effects {front cap tail : Stack}
    (typed : MachineEffects signature tickets world
      (.eval ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩) outgoing)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) :
    MachineEffects signature tickets world
      (.eval ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩) outgoing := by
  cases typed with
  | eval expression stack => cases expression with
      | checked scopeTyped expression => cases expression with
          | resume operand allowed formed => cases scopeTyped with
              | bound known =>
                  simp [Execution.Scope.resolve] at resolved
                  subst owner
                  have restored := resume_effect_recomposition known
                    (by simpa only [effect_view_append, effectView] using stack) allowed
                  exact .eval (.checked (.bound known) (typed_value_transport operand isValue _ []))
                    (by simpa only [effect_view_append, effectView] using restored)


/-- Source expression typing supplies the two initial typing projections.
    Capability, resource-access and completion admission remain independent. -/
theorem initial_machine_typing
    (typed : Typed signature [] TypeEnv.empty .none outgoing code result) :
    MachinePorts signature (fun _ => none) [] (.eval ⟨code, .none, .nil⟩) result ∧
    MachineEffects signature (fun _ => none) [] (.eval ⟨code, .none, .nil⟩) outgoing :=
  ⟨.eval (.checked .none typed) .nil,
    .eval (.checked .none typed) (.nil (List.Subset.refl _))⟩

/-- The closing-row obligation is a fact about allocated contract data. It
    holds for an empty registry and is preserved by equal-row capture records;
    callers need no premise about future executions or generated cleanup plans. -/
theorem closing_rows_insert {tickets : EffectTickets} {contract : ContinuationContract} {identity : Nat}
    (previous : ∀ owner record, tickets owner = some record → record.resumeEffects ⊆ record.closeEffects)
    (covers : contract.resumeEffects ⊆ contract.closeEffects) :
    ∀ owner record, (tickets.insert identity contract) owner = some record →
      record.resumeEffects ⊆ record.closeEffects := by
  intro owner record known
  by_cases same : owner = identity
  · simp only [EffectTickets.insert, same, ↓reduceIte, Option.some.injEq] at known
    subst record
    exact covers
  · simp only [EffectTickets.insert, same, ↓reduceIte] at known
    exact previous owner record known

#print axioms Ash.OneShot.LexicalUnwind.initial_machine_typing
#print axioms Ash.OneShot.LexicalUnwind.closing_rows_insert
#print axioms Ash.OneShot.LexicalUnwind.capture_effects
#print axioms Ash.OneShot.LexicalUnwind.resume_effects
#print axioms Ash.OneShot.LexicalUnwind.effect_view_append
#print axioms Ash.OneShot.LexicalUnwind.effect_frame_view_resolve
#print axioms Ash.OneShot.LexicalUnwind.effect_view_resolve
#print axioms Ash.OneShot.LexicalUnwind.effect_view_cut
#print axioms Ash.OneShot.LexicalUnwind.machine_request_provided_or_exported
#print axioms Ash.OneShot.LexicalUnwind.ordinary_effect_view
#print axioms Ash.OneShot.LexicalUnwind.administrative_effects
#print axioms Ash.OneShot.LexicalUnwind.start_cleanup_effects
#print axioms Ash.OneShot.LexicalUnwind.finish_cleanup_effects
#print axioms Ash.OneShot.LexicalUnwind.close_effects
#print axioms Ash.OneShot.LexicalUnwind.unwind_transition_effects
#print axioms Ash.OneShot.LexicalUnwind.discard_effects
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open Instantiation ScopedExpressions ScopedExecution
open Syntax (resourceDependencies)

/-- Unwinding has no current expression that could carry a released reference.
    Retained payload support is the same structural judgment as evaluation. -/
inductive MachineAccess (ambient : List Nat) : Machine → Prop where
  | eval (supported : AccessValid configuration ambient) : MachineAccess ambient (.eval configuration)
  | unwind (supported : Supported stack.erase ambient) : MachineAccess ambient (.unwind scope stack)

/-- The new disposer retains the enclosing scopes. Only ordinary value release
    and outward transfer of a request operand need extra local access evidence. -/
structure AccessConditions (before : Configuration) (ambient : List Nat) : Prop where
  release : ∀ identity payload answer savedScope scope value tail,
    before = ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ →
    ClosedValue value → identity ∉ resourceDependencies value.dependencies
  capture : ∀ requested operation operand scope whole cap tail handler,
    before = ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ →
    HandlerCut requested whole cap tail handler → ClosedValue operand →
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient

def accessConditions (machine : Machine) (ambient : List Nat) : Prop :=
  match machine with
  | .eval configuration => AccessConditions configuration ambient
  | .unwind _ _ => True

/-- The unused legacy discard branch is contradictory, not an invocation of
    its planner or disposal checker. -/
theorem ordinary_access_conditions
    (checks : AccessConditions before ambient) (allowed : ordinary before.expression) :
    AccessChecks before ambient := by
  refine ⟨checks.release, checks.capture, ?_⟩
  intro binder ticket scope caller input answer front cap tail plan same resolved built
  subst before
  exact False.elim allowed

/-- A local pop preserves support without computing future cleanup order. -/
theorem administrative_access (step : Advance before after discharged)
    (supported : Supported before.erase ambient) : Supported after.erase ambient := by
  cases step with
  | plain | handler | cell | retire => cases supported with
      | push frame rest ambient next access => exact next
  | spent => cases supported with
      | spent owner answer rest ambient next => exact next
  | live => cases supported with
      | live owner input answer saved rest ambient capture next =>
          rw [erase_append]
          apply supported_append
          · simpa [Stack.erase, ExecFrame.erase, CloseItem.frame, Control.visible, Frame.visible] using capture
          · exact .push _ _ _ next (by simp [ExecFrame.erase, CloseItem.frame])

/-- Reuse ordinary resumption's support recomposition: restoration of scopes
    is the same operation. Adding the empty-access close boundary changes no
    resource visibility. There is no disposal-plan premise. -/
theorem discard_access {front cap tail : Stack}
    (supported : Supported (front.append (.live owner input answer cap callerScope tail)).erase ambient) :
    Supported (cap.append (.push (.closing identity scope)
      (front.append (.spent owner answer callerScope tail)))).erase ambient := by
  have resumed := resume_preserves_support
    (by simpa only [erase_append, Stack.erase] using supported)
  obtain ⟨saved, rest⟩ := supported_decompose cap.erase resumed
  simp only [erase_append, Stack.erase, ExecFrame.erase]
  apply supported_append
  · simpa [Control.visible, closeFrame, Frame.visible] using saved
  · exact .push _ _ _ rest (by simp [closeFrame])

/-- Every transition preserves resource support from two local pre-step
    checks. Source derivation of those checks is a separate obligation. -/
theorem transition_access
    (step : Transition before after created discharged)
    (supported : MachineAccess ambient before)
    (checks : accessConditions before ambient) : MachineAccess ambient after := by
  cases step with
  | evaluate raw allowed => cases supported with
      | eval valid => exact .eval (raw_step_preserves_access raw valid (ordinary_access_conditions checks allowed))
  | advance nextStep => cases supported with
      | unwind valid => exact .unwind (administrative_access nextStep valid)
  | startCleanup => cases supported with
      | unwind valid => cases valid with
          | push frame rest ambient next actionAccess =>
              apply MachineAccess.eval
              constructor
              · exact .push _ _ _ next actionAccess
              · simpa [Code.dependencies, resourceDependencies, Stack.erase, ExecFrame.erase,
                  ActionData.erase, Control.visible, Frame.visible] using actionAccess
  | finishCleanup => cases supported with
      | eval valid => cases valid.control with
          | push frame rest ambient next actionAccess => exact .unwind next
  | discard => cases supported with
      | eval valid => exact .unwind (discard_access valid.control)
  | finishClose => cases supported with
      | unwind valid => cases valid with
          | push frame rest ambient next access =>
              exact .eval ⟨next, by simp [Code.dependencies, resourceDependencies]⟩
  | retireValue => cases supported with
      | eval valid => cases valid.control with
          | push frame rest ambient next access =>
              exact .eval ⟨next, by simpa [Stack.erase, ExecFrame.erase, CloseItem.frame,
                Control.visible, Frame.visible] using valid.expression⟩
  | closeValue => cases supported with
      | eval valid => cases valid.control with
          | push frame rest ambient next access =>
              exact .eval ⟨next, by simp [Code.dependencies, resourceDependencies]⟩

#print axioms Ash.OneShot.LexicalUnwind.ordinary_access_conditions
#print axioms Ash.OneShot.LexicalUnwind.administrative_access
#print axioms Ash.OneShot.LexicalUnwind.discard_access
#print axioms Ash.OneShot.LexicalUnwind.transition_access
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open ScopedExpressions ScopedExecution

/-- Scopes which can be abandoned before the selected disposal boundary.
    A started cleanup or another disposal boundary has no constructor here.
    Retirement is permitted because unwinding introduces it locally. -/
inductive UnwindPrefix : Stack → Prop where
  | nil : UnwindPrefix .nil
  | plain (rest : UnwindPrefix tail) : UnwindPrefix (.push (.plain frame) tail)
  | handler (rest : UnwindPrefix tail) : UnwindPrefix (.push (.handler installation) tail)
  | cell (rest : UnwindPrefix tail) : UnwindPrefix (.push (.cell identity payload scope answer) tail)
  | armed (rest : UnwindPrefix tail) : UnwindPrefix (.push (.armed action) tail)
  | retiring (rest : UnwindPrefix tail) : UnwindPrefix (.push (.retiring owner) tail)
  | live (saved : UnwindPrefix captured) (rest : UnwindPrefix tail) :
      UnwindPrefix (.live owner input answer captured scope tail)
  | spent (rest : UnwindPrefix tail) : UnwindPrefix (.spent owner answer scope tail)

theorem unwind_prefix_append (left : UnwindPrefix front) (right : UnwindPrefix tail) :
    UnwindPrefix (front.append tail) := by
  induction left with
  | nil => exact right
  | plain rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | armed rest ih => exact .armed ih
  | retiring rest ih => exact .retiring ih
  | live saved rest ihSaved ihRest => exact .live saved ihRest
  | spent rest ih => exact .spent ih

/-- The existing protection check at discard constructs the structural prefix;
    no additional admission premise or traversal plan is needed. -/
theorem unprotected_unwind_prefix
    (unprotected : ProtectionContexts.protectedMode stack.erase = false) : UnwindPrefix stack := by
  induction stack with
  | nil => exact .nil
  | push frame rest ih =>
      cases frame with
      | plain => exact .plain (ih unprotected)
      | handler => exact .handler (ih unprotected)
      | cell => exact .cell (ih unprotected)
      | armed => exact .armed (ih unprotected)
      | running | unwinding | closing | retiring =>
          simp [Stack.erase, ExecFrame.erase, ProtectionContexts.protectedMode,
            ProtectionContexts.frameProtected, CloseItem.frame, closeFrame] at unprotected
  | live owner input answer saved scope rest ihSaved ihRest =>
      have split : ProtectionContexts.protectedMode saved.erase = false ∧
          ProtectionContexts.protectedMode rest.erase = false := by
        simpa [Stack.erase, ProtectionContexts.protectedMode] using unprotected
      exact .live (ihSaved split.1) (ihRest split.2)
  | spent owner answer scope rest ih => exact .spent (ih unprotected)

/-- The disposal delimiter retains an ordinary caller suffix. Only the preceding scopes
    are abandoned; the caller itself need not be unwindable. -/
inductive UnwindReady : Stack → Prop where
  | boundary (scopes : UnwindPrefix front) :
      UnwindReady (front.append (.push (.closing identity scope) tail))

theorem discard_unwind_ready
    (step : Transition (.eval ⟨.discard binder, scope, stack⟩) (.unwind current after) created discharged) :
    UnwindReady after := by
  cases step with
  | discard binder owner identity scope caller input answer front captured tail resolved unprotected =>
      exact .boundary (unprotected_unwind_prefix unprotected)

/-- Each administrative step preserves the same closing boundary and caller.
    The only expansion is the owned capture plus its local retirement marker. -/
theorem administrative_unwind_ready
    (step : Advance before after discharged) (ready : UnwindReady before) : UnwindReady after := by
  cases ready with
  | @boundary front identity scope tail scopes =>
      cases scopes with
      | nil => cases step
      | plain rest => cases step; exact .boundary rest
      | handler rest => cases step; exact .boundary rest
      | cell rest => cases step; exact .boundary rest
      | armed rest => cases step
      | retiring rest => cases step; exact .boundary rest
      | spent rest => cases step; exact .boundary rest
      | live saved rest =>
          cases step
          simpa only [Stack.append, stack_append_assoc] using
            (UnwindReady.boundary (identity := identity) (scope := scope) (tail := tail)
              (unwind_prefix_append saved (.retiring rest)))

/-- Every structurally ready abandonment state can step. Callback termination
    is not assumed: reaching an armed action enters ordinary evaluation. -/
theorem unwind_progress (ready : UnwindReady stack) :
    ∃ after discharged, Transition (.unwind scope stack) after [] discharged := by
  cases ready with
  | boundary scopes => cases scopes with
      | nil => exact ⟨_, _, .finishClose⟩
      | plain => exact ⟨_, _, .advance .plain⟩
      | handler => exact ⟨_, _, .advance .handler⟩
      | cell => exact ⟨_, _, .advance .cell⟩
      | armed => exact ⟨_, _, .startCleanup⟩
      | retiring => exact ⟨_, _, .advance .retire⟩
      | live => exact ⟨_, _, .advance .live⟩
      | spent => exact ⟨_, _, .advance .spent⟩


/-- The unwind branch has an actual next event and preserves the established
    typing, effect, resource and ownership facets. Callback evaluation is an
    ordinary successor, so neither callback success nor termination is assumed. -/
theorem checked_unwind_progress
    (ready : UnwindReady stack)
    (ports : MachinePorts signature tickets.types world (.unwind scope stack) result)
    (effects : MachineEffects signature tickets world (.unwind scope stack) outgoing)
    (access : MachineAccess ambient (.unwind scope stack))
    (ledger : Ledger (RunState.erase ⟨.unwind scope stack, issued, completed⟩)) :
    ∃ after discharged,
      Event ⟨.unwind scope stack, issued, completed⟩ ⟨after, issued, discharged ++ completed⟩ ∧
      MachinePorts signature tickets.types world after result ∧
      MachineEffects signature tickets world after outgoing ∧
      MachineAccess ambient after ∧
      Ledger (RunState.erase ⟨after, issued, discharged ++ completed⟩) ∧
      (∀ nextScope nextStack, after = .unwind nextScope nextStack → UnwindReady nextStack) := by
  obtain ⟨after, discharged, step⟩ := unwind_progress (scope := scope) ready
  have event : Event ⟨.unwind scope stack, issued, completed⟩ ⟨after, issued, discharged ++ completed⟩ := by
    simpa only [List.append_nil] using
      Event.step (before := ⟨.unwind scope stack, issued, completed⟩) step
        (by simpa only [RunState.erase, List.append_nil] using ledger.2)
  refine ⟨after, discharged, event, unwind_transition_ports step ports,
    unwind_transition_effects step effects, transition_access step access trivial,
    event_preserves_ledger event ledger, ?_⟩
  intro nextScope nextStack same
  cases step with
  | advance next => cases same; exact administrative_unwind_ready next ready
  | startCleanup => cases same
  | finishClose => cases same

#print axioms Ash.OneShot.LexicalUnwind.checked_unwind_progress
#print axioms Ash.OneShot.LexicalUnwind.unwind_prefix_append
#print axioms Ash.OneShot.LexicalUnwind.unprotected_unwind_prefix
#print axioms Ash.OneShot.LexicalUnwind.discard_unwind_ready
#print axioms Ash.OneShot.LexicalUnwind.administrative_unwind_ready
#print axioms Ash.OneShot.LexicalUnwind.unwind_progress
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open ScopedExecution

/-- Structural boundary checks over actual scopes. No callback is invoked,
    removed or reordered by either check. -/
def checkUnwindPrefix : Stack → Bool
  | .nil => true
  | .push (.running _ _ _) _ | .push (.unwinding _) _ | .push (.closing _ _) _ => false
  | .push _ rest => checkUnwindPrefix rest
  | .live _ _ _ saved _ rest => checkUnwindPrefix saved && checkUnwindPrefix rest
  | .spent _ _ _ rest => checkUnwindPrefix rest

def checkUnwindReady : Stack → Bool
  | .nil => false
  | .push (.closing _ _) _ => true
  | .push (.running _ _ _) _ | .push (.unwinding _) _ => false
  | .push _ rest => checkUnwindReady rest
  | .live _ _ _ saved _ rest => checkUnwindPrefix saved && checkUnwindReady rest
  | .spent _ _ _ rest => checkUnwindReady rest

theorem check_unwind_prefix_iff : checkUnwindPrefix stack = true ↔ UnwindPrefix stack := by
  induction stack with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | push frame rest ih =>
      cases frame with
      | plain => exact ⟨fun h => .plain (ih.mp h), fun h => by cases h; exact ih.mpr (by assumption)⟩
      | handler => exact ⟨fun h => .handler (ih.mp h), fun h => by cases h; exact ih.mpr (by assumption)⟩
      | cell => exact ⟨fun h => .cell (ih.mp h), fun h => by cases h; exact ih.mpr (by assumption)⟩
      | armed => exact ⟨fun h => .armed (ih.mp h), fun h => by cases h; exact ih.mpr (by assumption)⟩
      | retiring => exact ⟨fun h => .retiring (ih.mp h), fun h => by cases h; exact ih.mpr (by assumption)⟩
      | running | unwinding | closing => constructor <;> intro h <;> cases h
  | live owner input answer saved scope rest ihSaved ihRest =>
      simp only [checkUnwindPrefix, Bool.and_eq_true, ihSaved, ihRest]
      exact ⟨fun ⟨saved, rest⟩ => .live saved rest, fun h => by cases h; exact ⟨by assumption, by assumption⟩⟩
  | spent owner answer scope rest ih =>
      exact ⟨fun h => .spent (ih.mp h), fun h => by cases h; exact ih.mpr (by assumption)⟩

/-- An open fragment either contains the disposal boundary or passes the
    obligation to its enclosing suffix. This is ordinary stack induction. -/
theorem check_unwind_ready_append (front tail : Stack) :
    checkUnwindReady (front.append tail) =
      (checkUnwindReady front || (checkUnwindPrefix front && checkUnwindReady tail)) := by
  induction front with
  | nil => simp [Stack.append, checkUnwindReady, checkUnwindPrefix]
  | push frame rest ih => cases frame <;> simp [Stack.append, checkUnwindReady, checkUnwindPrefix, ih]
  | live owner input answer saved scope rest ihSaved ihRest =>
      simp only [Stack.append, checkUnwindReady, checkUnwindPrefix, ihRest]
      cases checkUnwindPrefix saved <;> simp
  | spent owner answer scope rest ih => exact ih

theorem check_unwind_ready_iff : checkUnwindReady stack = true ↔ UnwindReady stack := by
  constructor
  · intro checked
    induction stack with
    | nil => cases checked
    | push frame rest ih =>
        cases frame with
        | closing => exact .boundary .nil
        | running | unwinding => cases checked
        | plain =>
            cases ih checked with
            | boundary scopes => exact .boundary (.plain scopes)
        | handler =>
            cases ih checked with
            | boundary scopes => exact .boundary (.handler scopes)
        | cell =>
            cases ih checked with
            | boundary scopes => exact .boundary (.cell scopes)
        | armed =>
            cases ih checked with
            | boundary scopes => exact .boundary (.armed scopes)
        | retiring =>
            cases ih checked with
            | boundary scopes => exact .boundary (.retiring scopes)
    | live owner input answer saved scope rest ihSaved ihRest =>
        have split : checkUnwindPrefix saved = true ∧ checkUnwindReady rest = true := by
          simpa only [checkUnwindReady, Bool.and_eq_true] using checked
        cases ihRest split.2 with
        | boundary scopes => exact .boundary (.live (check_unwind_prefix_iff.mp split.1) scopes)
    | spent owner answer scope rest ih =>
        cases ih checked with
        | boundary scopes => exact .boundary (.spent scopes)
  · intro ready
    cases ready with
    | boundary scopes =>
        rw [check_unwind_ready_append]
        simp [check_unwind_prefix_iff.mpr scopes, checkUnwindReady]

/-- Exact interface decomposition; the captured fragment need not contain
    its own closing boundary. -/
theorem unwind_ready_append_iff (front tail : Stack) :
    UnwindReady (front.append tail) ↔
      UnwindReady front ∨ (UnwindPrefix front ∧ UnwindReady tail) := by
  simp only [← check_unwind_ready_iff, ← check_unwind_prefix_iff,
    check_unwind_ready_append, Bool.or_eq_true, Bool.and_eq_true]

/-- Inserting unwindable clause scopes before the enclosing suffix preserves
    the pending boundary, whether it lies inside or outside the capture. -/
theorem unwind_ready_splice {saved front tail : Stack}
    (ready : UnwindReady (saved.append tail)) (inserted : UnwindPrefix front) :
    UnwindReady (saved.append (front.append tail)) := by
  rcases (unwind_ready_append_iff _ _).mp ready with inside | ⟨openSaved, outside⟩
  · exact (unwind_ready_append_iff _ _).mpr (.inl inside)
  · exact (unwind_ready_append_iff _ _).mpr (.inr ⟨openSaved,
      (unwind_ready_append_iff _ _).mpr (.inr ⟨inserted, outside⟩)⟩)

/-- An exact handler cut exports the boundary obligation through the same
    decomposition as operational capture. Handler selection is unchanged. -/
theorem handler_cut_unwind_boundary
    (cut : HandlerCut requested whole saved tail handler) (ready : UnwindReady whole) :
    UnwindReady saved ∨ (UnwindPrefix saved ∧ UnwindReady tail) := by
  rw [handler_cut_reconstructs cut] at ready
  exact (unwind_ready_append_iff _ _).mp ready


/-- Recomposition behind a captured cleanup return marker. If its disposal
    boundary is already captured, the clause's inserted frames are outside it.
    Otherwise those inserted scopes must themselves support unwinding. This
    is local structural evidence, not an assumed ready successor. -/
theorem callback_resume_ready
    (cut : HandlerCut requested rest saved tail handler)
    (ready : UnwindReady rest)
    (clause : UnwindReady saved ∨ UnwindPrefix front) :
    HandlerCut requested (.push (.unwinding action) rest)
      (.push (.unwinding action) saved) tail handler ∧
    UnwindReady (saved.append (front.append (.spent owner answer caller tail))) := by
  refine ⟨callback_cut cut, ?_⟩
  rcases clause with inside | inserted
  · exact (unwind_ready_append_iff _ _).mpr (.inl inside)
  · have original : UnwindReady (saved.append tail) := (handler_cut_reconstructs cut) ▸ ready
    have safe := unwind_prefix_append inserted (UnwindPrefix.spent (owner := owner)
      (answer := answer) (scope := caller) UnwindPrefix.nil)
    simpa only [Stack.append, stack_append_assoc] using unwind_ready_splice original safe

#print axioms Ash.OneShot.LexicalUnwind.callback_resume_ready
#print axioms Ash.OneShot.LexicalUnwind.check_unwind_prefix_iff
#print axioms Ash.OneShot.LexicalUnwind.check_unwind_ready_append
#print axioms Ash.OneShot.LexicalUnwind.check_unwind_ready_iff
#print axioms Ash.OneShot.LexicalUnwind.unwind_ready_append_iff
#print axioms Ash.OneShot.LexicalUnwind.unwind_ready_splice
#print axioms Ash.OneShot.LexicalUnwind.handler_cut_unwind_boundary
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open ScopedExpressions ScopedExecution
open Syntax (TicketPolicy UsageTickets UsageScopeKnown)

inductive UseMode where
  | ordinary | unwind
  deriving DecidableEq

def retiredDemand : UseMode → Nat → List Nat
  | .ordinary, _ => []
  | .unwind, owner => [owner]

/-- Ordinary code retains its established use checking. In unwind mode only
    an internal retirement claims a ticket; pending ordinary code is skipped. -/
inductive FrameUse (policy : TicketPolicy) (tickets : UsageTickets) :
    ExecFrame → UseMode → UseMode → List Nat → Prop where
  | ordinary (checked : FrameDemand policy tickets frame demand) :
      FrameUse policy tickets frame .ordinary .ordinary demand
  | unwind (checked : FrameDemand policy tickets frame ignored)
      (scopes : UnwindPrefix (.push frame .nil)) :
      FrameUse policy tickets frame .unwind .unwind (ScopedRetirement.scheduled (.push frame .nil))
  | cleanup (checked : FrameDemand policy tickets (.armed action) []) :
      FrameUse policy tickets (.unwinding action) .ordinary .unwind []
  | closing (checked : FrameDemand policy tickets (.closing identity scope) []) :
      FrameUse policy tickets (.closing identity scope) .unwind .ordinary []

/-- Open stack interfaces record both entry and exit mode. A dormant capture
    retains its actual scopes; its exit mode determines the caller's mode.
    This is usage evidence, not an evaluator or a disposal schedule. -/
inductive StackUse (policy : TicketPolicy) (tickets : UsageTickets) :
    Stack → UseMode → UseMode → List Nat → Prop where
  | nil : StackUse policy tickets .nil mode mode []
  | push (frame : FrameUse policy tickets entry before middle first)
      (rest : StackUse policy tickets tail middle after remaining) :
      StackUse policy tickets (.push entry tail) before after (first ++ remaining)
  | live (known : tickets owner = some rights) (scope : UsageScopeKnown tickets caller)
      (saved : StackUse policy tickets captured before middle first)
      (rest : StackUse policy tickets tail middle after remaining) :
      StackUse policy tickets (.live owner input answer captured caller tail) before after
        (retiredDemand before owner ++ first ++ remaining)
  | spent (known : tickets owner = some rights) (scope : UsageScopeKnown tickets caller)
      (rest : StackUse policy tickets tail before after demand) :
      StackUse policy tickets (.spent owner answer caller tail) before after demand

theorem ordinary_stack_use
    (checked : StackUsage policy tickets stack outside demand) :
    StackUse policy tickets stack .ordinary .ordinary demand := by
  induction checked with
  | nil => exact .nil
  | push frame accessible rest ih => exact .push (.ordinary frame) ih
  | live known scope saved rest ihSaved ihRest => exact .live known scope ihSaved ihRest
  | spent known scope rest ih => exact .spent known scope ih

theorem stack_use_append
    (front : StackUse policy tickets left before middle first)
    (tail : StackUse policy tickets right middle after remaining) :
    StackUse policy tickets (left.append right) before after (first ++ remaining) := by
  induction front with
  | nil => exact tail
  | push frame rest ih =>
      simpa only [Stack.append, List.append_assoc] using StackUse.push frame (ih tail)
  | live known scope saved rest ihSaved ihRest =>
      simpa only [Stack.append, List.append_assoc] using StackUse.live known scope saved (ihRest tail)
  | spent known scope rest ih => exact .spent known scope (ih tail)

theorem retiring_frame_use (mode : UseMode) (known : tickets owner = some rights) :
    FrameUse policy tickets (.retiring owner) mode mode [owner] := by
  cases mode with
  | ordinary => exact .ordinary (.retiring known)
  | unwind => exact .unwind (.retiring known) (.retiring .nil)

/-- Unwinding conserves outstanding ticket uses until the corresponding
    retirement. Skipping code neither adds a use nor loses an owned obligation. -/
theorem administrative_usage
    (step : Advance before after discharged)
    (checked : StackUse policy tickets before .unwind finalMode demand) :
    ∃ remaining, StackUse policy tickets after .unwind finalMode remaining ∧
      demand.Perm (discharged.filterMap Syntax.ticketProjection ++ remaining) := by
  cases step with
  | plain | handler | cell => cases checked with
      | push frame rest => cases frame with
          | unwind payload scopes => exact ⟨_, rest, List.Perm.refl _⟩
  | retire => cases checked with
      | push frame rest => cases frame with
          | unwind payload scopes => exact ⟨_, rest, List.Perm.refl _⟩
  | spent => cases checked with
      | spent known scope rest => exact ⟨_, rest, List.Perm.refl _⟩
  | @live owner input answer saved caller rest => cases checked with
      | live known scope capture tail =>
          refine ⟨_, stack_use_append capture (.push (retiring_frame_use _ known) tail), ?_⟩
          simpa only [retiredDemand, Syntax.ticketProjection, List.filterMap_nil, List.nil_append,
            List.append_assoc] using
            ((List.perm_append_comm (l₁ := [owner]) (l₂ := _)).append_right _)

/-- A stack fragment exposes the usage mode at its actual lexical boundary. -/
theorem stack_use_decompose
    (checked : StackUse policy tickets (left.append right) before after demand) :
    ∃ middle first remaining, demand = first ++ remaining ∧
      StackUse policy tickets left before middle first ∧
      StackUse policy tickets right middle after remaining := by
  induction left generalizing before after demand with
  | nil => exact ⟨before, [], demand, rfl, .nil, checked⟩
  | push entry rest ih => cases checked with
      | push frame next =>
          obtain ⟨middle, first, remaining, same, inside, tail⟩ := ih next
          exact ⟨middle, _, remaining, by simp [same, List.append_assoc], .push frame inside, tail⟩
  | live owner input answer saved caller rest ihSaved ihRest => cases checked with
      | live known scope savedChecked next =>
          obtain ⟨middle, first, remaining, same, inside, tail⟩ := ihRest next
          exact ⟨middle, _, remaining, by simp [same, List.append_assoc],
            .live known scope savedChecked inside, tail⟩
  | spent owner answer caller rest ih => cases checked with
      | spent known scope next =>
          obtain ⟨middle, first, remaining, same, inside, tail⟩ := ih next
          exact ⟨middle, first, remaining, same, .spent known scope inside, tail⟩

theorem handler_cut_use
    (cut : HandlerCut requested whole captured tail handler)
    (checked : StackUse policy tickets whole before after demand) :
    ∃ middle first remaining, demand = first ++ remaining ∧
      StackUse policy tickets captured before middle first ∧
      StackUse policy tickets tail middle after remaining := by
  rw [handler_cut_reconstructs cut] at checked
  exact stack_use_decompose checked

/-- An abandonable fragment has no mode-switching boundary. Its abandoned
    demand is exactly its owned tickets, independent of pending ordinary code. -/
theorem prefix_use_unwind
    (scopes : UnwindPrefix stack)
    (checked : StackUse policy tickets stack before after demand) :
    before = after ∧ StackUse policy tickets stack .unwind .unwind (ownedTickets stack) := by
  induction scopes generalizing before after demand with
  | nil => cases checked; exact ⟨rfl, .nil⟩
  | plain scopes ih | handler scopes ih | cell scopes ih | armed scopes ih =>
      cases checked with
      | push frame rest =>
          obtain ⟨same, tail⟩ := ih rest
          cases frame with
          | ordinary checked => exact ⟨same, .push (.unwind checked (by constructor; exact .nil)) tail⟩
          | unwind checked frameScopes => exact ⟨same, .push (.unwind checked frameScopes) tail⟩
  | retiring scopes ih => cases checked with
      | push frame rest =>
          obtain ⟨same, tail⟩ := ih rest
          cases frame with
          | ordinary checked => exact ⟨same, .push (.unwind checked (.retiring .nil)) tail⟩
          | unwind checked frameScopes => exact ⟨same, .push (.unwind checked frameScopes) tail⟩
  | live prefixSaved prefixRest ihSaved ihRest => cases checked with
      | live known scope saved rest =>
          obtain ⟨sameSaved, savedUse⟩ := ihSaved saved
          obtain ⟨sameRest, restUse⟩ := ihRest rest
          exact ⟨sameSaved.trans sameRest, .live known scope savedUse restUse⟩
  | spent scopes ih => cases checked with
      | spent known scope rest =>
          obtain ⟨same, tail⟩ := ih rest
          exact ⟨same, .spent known scope tail⟩

/-- Beginning a callback changes the input usage mode while retaining the
    identical suffix and its outstanding demand. -/
theorem start_cleanup_use
    (checked : StackUse policy tickets (.push (.armed action) rest) .unwind after demand) :
    CodeDemand policy tickets .none (.app action.action .unit) [] ∧
      StackUse policy tickets (.push (.unwinding action) rest) .ordinary after demand := by
  cases checked with
  | push frame tail => cases frame with
      | unwind payload scopes => cases payload with
          | armed scope code =>
              exact ⟨.idle .none (.app code .unit), .push (.cleanup (.armed scope code)) tail⟩

theorem finish_cleanup_use
    (checked : StackUse policy tickets (.push (.unwinding action) rest) .ordinary after demand) :
    StackUse policy tickets rest .unwind after demand := by
  cases checked with
  | push frame tail => cases frame with
      | ordinary impossible => cases impossible
      | cleanup payload => exact tail

theorem finish_close_use
    (checked : StackUse policy tickets (.push (.closing identity caller) rest) .unwind after demand) :
    UsageScopeKnown tickets caller ∧ StackUse policy tickets rest .ordinary after demand := by
  cases checked with
  | push frame tail => cases frame with
      | unwind payload scopes => cases scopes
      | closing payload => cases payload with
          | closing scope => exact ⟨scope, tail⟩

theorem frame_use_extension
    (checked : FrameUse policy before entry input output demand)
    (extension : Syntax.UsageExtension before after) :
    FrameUse policy after entry input output demand := by
  cases checked with
  | ordinary checked => exact .ordinary (frame_demand_extension checked extension)
  | unwind checked scopes => exact .unwind (frame_demand_extension checked extension) scopes
  | cleanup checked => exact .cleanup (frame_demand_extension checked extension)
  | closing checked => exact .closing (frame_demand_extension checked extension)

theorem stack_use_extension
    (checked : StackUse policy before stack input output demand)
    (extension : Syntax.UsageExtension before after) :
    StackUse policy after stack input output demand := by
  induction checked with
  | nil => exact .nil
  | push frame rest ih => exact .push (frame_use_extension frame extension) ih
  | live known scope saved rest ihSaved ihRest =>
      exact .live (extension _ _ known) (Syntax.usage_scope_known_extension scope extension) ihSaved ihRest
  | spent known scope rest ih =>
      exact .spent (extension _ _ known) (Syntax.usage_scope_known_extension scope extension) ih

theorem handler_cut_use_clauses
    (cut : HandlerCut requested whole captured tail handler)
    (checked : StackUse policy tickets whole before after demand) :
    UsageScopeKnown tickets handler.scope ∧ ClausesUse policy handler.clauses := by
  induction cut generalizing before after demand with
  | hit => cases checked with
      | push frame rest => cases frame with
          | ordinary payload | unwind payload scopes => cases payload with
              | handler scope clauses => exact ⟨scope, clauses⟩
  | push entry rest captured tail handler miss next ih => cases checked with
      | push frame rest => exact ih rest
  | live owner input answer saved caller rest captured tail handler next ih => cases checked with
      | live known scope saved rest => exact ih rest
  | spent owner answer caller rest captured tail handler next ih => cases checked with
      | spent known scope rest => exact ih rest

/-- Continuation-use accounting is one facet of the common invariant. Lexical
    accessibility, protection and source admission remain separate obligations. -/
def MachineUse (policy : TicketPolicy) (tickets : UsageTickets) : Machine → Prop
  | .eval configuration => ∃ current pending,
      CodeDemand policy tickets configuration.scope configuration.expression current ∧
      StackUse policy tickets configuration.stack .ordinary .ordinary pending ∧
      (current ++ pending).Perm (ownedTickets configuration.stack)
  | .unwind _ stack => ∃ pending,
      StackUse policy tickets stack .unwind .ordinary pending ∧ pending.Perm (ownedTickets stack)

theorem ordinary_machine_use (checked : ConfigurationUsage policy tickets configuration) :
    MachineUse policy tickets (.eval configuration) := by
  obtain ⟨current, pending, code, stack, accessible, balance, unique⟩ := checked
  exact ⟨current, pending, code, ordinary_stack_use stack, balance⟩

theorem administrative_machine_use
    (step : Advance before after discharged)
    (checked : MachineUse policy tickets (.unwind scope before)) :
    MachineUse policy tickets (.unwind scope after) := by
  obtain ⟨pending, checked, balanced⟩ := checked
  obtain ⟨remaining, checkedAfter, conserved⟩ := administrative_usage step checked
  refine ⟨remaining, checkedAfter, ?_⟩
  have ownership : (ownedTickets before).Perm
      (ownedTickets after ++ discharged.filterMap Syntax.ticketProjection) := by
    simpa only [List.filterMap_append, ← owned_tickets_project] using
      (accounting step).filterMap Syntax.ticketProjection
  have joined := (conserved.symm.trans (balanced.trans ownership)).trans
    (List.perm_append_comm (l₁ := ownedTickets after) (l₂ := discharged.filterMap Syntax.ticketProjection))
  exact (List.perm_append_left_iff _).mp joined

theorem start_cleanup_machine_use
    (checked : MachineUse policy tickets (.unwind scope (.push (.armed action) rest))) :
    MachineUse policy tickets
      (.eval ⟨.app action.action .unit, .none, .push (.unwinding action) rest⟩) := by
  obtain ⟨pending, stack, balance⟩ := checked
  obtain ⟨code, next⟩ := start_cleanup_use stack
  exact ⟨[], pending, code, next, balance⟩

theorem finish_cleanup_machine_use
    (checked : MachineUse policy tickets (.eval ⟨.unit, scope, .push (.unwinding action) rest⟩)) :
    MachineUse policy tickets (.unwind action.scope rest) := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  have same := code_demand_value_is_empty code (by trivial)
  subst current
  exact ⟨pending, finish_cleanup_use stack, balance⟩

theorem finish_close_machine_use
    (checked : MachineUse policy tickets (.unwind scope (.push (.closing identity caller) rest))) :
    MachineUse policy tickets (.eval ⟨.unit, caller, rest⟩) := by
  obtain ⟨pending, stack, balance⟩ := checked
  obtain ⟨scope, next⟩ := finish_close_use stack
  obtain ⟨useScope, checkedScope⟩ := scope
  exact ⟨[], pending, .idle checkedScope .unit, next, balance⟩

theorem capture_machine_use
    (cut : HandlerCut requested whole captured tail handler)
    (clause : Uses policy (.ticket binder rights) .available body .consumed)
    (checked : MachineUse policy tickets
      (.eval ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩))
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    MachineUse policy (UsageTickets.insert tickets owner rights)
      (.eval ⟨body.subst parameter operand, .ticket binder owner,
        .live owner input handler.answer captured handler.scope tail⟩) := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  have sameCurrent := perform_value_demand_empty code isValue
  subst current
  obtain ⟨middle, first, remaining, same, saved, rest⟩ := handler_cut_use cut stack
  obtain ⟨handlerScope, clauses⟩ := handler_cut_use_clauses cut stack
  have extension := Syntax.fresh_usage_insert_extends (rights := rights) fresh
  have known : UsageTickets.insert tickets owner rights owner = some rights := by
    simp [UsageTickets.insert]
  refine ⟨[owner], first ++ remaining, ?_,
    .live known (Syntax.usage_scope_known_extension handlerScope extension)
      (stack_use_extension saved extension) (stack_use_extension rest extension), ?_⟩
  · apply Syntax.CodeDemand.consume known
    apply usage_substitution clause isValue
    cases code with
    | idle scope used => cases used with
        | perform operand => exact value_use_transport isValue operand .none .available
  · have ownership : ownedTickets whole = ownedTickets captured ++ ownedTickets tail := by
      rw [handler_cut_reconstructs cut, owned_tickets_append]
    simpa only [List.nil_append, same, ownership, ownedTickets, List.singleton_append] using balance.cons owner

/-- A demanded live owner cannot simultaneously be scheduled for automatic
    retirement when the complete demand is unique. -/
theorem unused_live_enters_ordinary
    (checked : StackUse policy tickets (.live owner input answer saved caller tail) before after demand)
    (unused : owner ∉ demand) : before = .ordinary := by
  cases checked with
  | live known scope saved rest =>
      cases before with
      | ordinary => rfl
      | unwind => exact False.elim (unused (by simp [retiredDemand]))

/-- Ordinary return uses the original fragment. Unwind return can instead use
    its owned-ticket demand when all its scopes can be abandoned and the old
    demand accounts for precisely those tickets. -/
theorem prefix_use_reentry
    (checked : StackUse policy tickets front .ordinary .ordinary demand)
    (compatible : mode = .ordinary ∨
      (UnwindPrefix front ∧ demand.Perm (ownedTickets front))) :
    ∃ reentered, StackUse policy tickets front mode mode reentered ∧ reentered.Perm demand := by
  rcases compatible with same | ⟨scopes, balance⟩
  · subst mode; exact ⟨demand, checked, List.Perm.refl _⟩
  · cases mode with
    | ordinary => exact ⟨demand, checked, List.Perm.refl _⟩
    | unwind => exact ⟨_, (prefix_use_unwind scopes checked).2, balance.symm⟩

/-- Recomposition uses the actual captured exit mode. The inserted caller
    fragment is checked at that mode, separately from the saved fragment. -/
theorem resume_use_recomposition
    (known : tickets owner = some rights) (scope : UsageScopeKnown tickets caller)
    (saved : StackUse policy tickets captured .ordinary middle captureDemand)
    (rest : StackUse policy tickets tail middle after tailDemand)
    (reentry : StackUse policy tickets front middle middle frontDemand) :
    StackUse policy tickets (captured.append (front.append (.spent owner answer caller tail)))
      .ordinary after (captureDemand ++ frontDemand ++ tailDemand) := by
  simpa only [List.append_assoc] using
    stack_use_append saved (stack_use_append reentry (.spent known scope rest))

/-- Disposal checks and converts only the captured lexical fragment. The
    caller keeps its ordinary usage, and the delimiter switches back to it. -/
theorem discard_use_recomposition
    (known : tickets owner = some rights) (callerScope : UsageScopeKnown tickets caller)
    (scope : UsageScopeKnown tickets runtimeScope)
    (frontChecked : StackUse policy tickets front .ordinary .ordinary frontDemand)
    (saved : StackUse policy tickets captured .ordinary .ordinary captureDemand)
    (rest : StackUse policy tickets tail .ordinary after tailDemand)
    (scopes : UnwindPrefix captured)
    (internal : captureDemand.Perm (ownedTickets captured)) :
    ∃ demand, StackUse policy tickets
      (captured.append (.push (.closing identity runtimeScope)
        (front.append (.spent owner answer caller tail)))) .unwind after demand ∧
      demand.Perm (frontDemand ++ captureDemand ++ tailDemand) := by
  have abandoned := (prefix_use_unwind scopes saved).2
  refine ⟨_, stack_use_append abandoned
    (.push (.closing (.closing scope)) (stack_use_append frontChecked (.spent known callerScope rest))), ?_⟩
  refine ((internal.symm.append_right (frontDemand ++ tailDemand)).trans ?_)
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := captureDemand) (l₂ := frontDemand)).append_right tailDemand

/-- Reuse the existing source use judgment to establish the initial accounting
    facet. This is not yet admission for the other machine invariants. -/
theorem initial_machine_use
    (checked : Uses policy .none .available expression .available) :
    MachineUse policy (fun _ => none) (.eval ⟨expression, .none, .nil⟩) := by
  exact ⟨[], [], .idle .none checked, .nil, List.Perm.refl []⟩

theorem retire_value_machine_use
    (checked : MachineUse policy tickets (.eval ⟨value, scope, .push (.retiring owner) rest⟩))
    (isValue : value.IsValue) :
    MachineUse policy tickets (.eval ⟨value, scope, rest⟩) := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  have same := code_demand_value_is_empty code isValue
  subst current
  cases stack with
  | push frame tail => cases frame with
      | ordinary payload => cases payload with
          | retiring known => exact ⟨[], _, code, tail, balance.cons_inv⟩

theorem close_value_machine_use
    (checked : MachineUse policy tickets (.eval ⟨value, scope, .push (.closing identity caller) rest⟩))
    (isValue : value.IsValue) :
    MachineUse policy tickets (.eval ⟨.unit, caller, rest⟩) := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  have same := code_demand_value_is_empty code isValue
  subst current
  cases stack with
  | push frame tail => cases frame with
      | ordinary payload => cases payload with
          | closing caller =>
              obtain ⟨useScope, checkedScope⟩ := caller
              exact ⟨[], _, .idle checkedScope .unit, tail, balance⟩

theorem focus_machine_use (plain : PlainData)
    (focus : Focus whole child plain.context)
    (checked : MachineUse policy tickets (.eval ⟨whole, plain.scope, tail⟩)) :
    MachineUse policy tickets (.eval ⟨child, plain.scope, .push (.plain plain) tail⟩) := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  obtain ⟨childDemand, frameDemand, same, childCode, frameCode⟩ := focus_splits_code_demand focus code
  subst current
  exact ⟨childDemand, frameDemand ++ pending, childCode,
    .push (.ordinary (.plain frameCode)) stack, by simpa only [List.append_assoc, ownedTickets] using balance⟩

/-- This event-level result checks the inserted fragment at the saved exit
    mode. Its local evidence still has to be obtained from source admission. -/
theorem resume_machine_use_of_fragments
    (code : CodeDemand policy tickets scope (.resume binder value) [owner])
    (isValue : value.IsValue)
    (known : tickets owner = some rights) (callerScope : UsageScopeKnown tickets caller)
    (saved : StackUse policy tickets captured .ordinary middle captureDemand)
    (rest : StackUse policy tickets tail middle .ordinary tailDemand)
    (reentry : StackUse policy tickets front middle middle frontDemand)
    (balance : (owner :: (frontDemand ++ captureDemand ++ tailDemand)).Perm
      (ownedTickets (front.append (.live owner input answer captured caller tail)))) :
    MachineUse policy tickets
      (.eval ⟨value, scope, captured.append (front.append (.spent owner answer caller tail))⟩) := by
  have projected : (frontDemand ++ captureDemand ++ tailDemand).Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail) := by
    apply List.Perm.cons_inv
    exact balance.trans (by simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using List.perm_middle)
  have afterBalance : (captureDemand ++ frontDemand ++ tailDemand).Perm
      (ownedTickets (captured.append (front.append (.spent owner answer caller tail)))) := by
    refine ((List.perm_append_comm (l₁ := captureDemand) (l₂ := frontDemand)).append_right tailDemand).trans
      (projected.trans ?_)
    simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using
      (List.perm_append_comm (l₁ := ownedTickets front) (l₂ := ownedTickets captured)).append_right (ownedTickets tail)
  refine ⟨[], _, ?_, resume_use_recomposition known callerScope saved rest reentry, afterBalance⟩
  cases code with
  | consume known used => cases used with
      | resume permission operand =>
          exact .idle (.bound known) (value_use_transport isValue operand _ .available)

theorem discard_machine_use_of_fragments
    (scope : UsageScopeKnown tickets runtimeScope)
    (known : tickets owner = some rights) (callerScope : UsageScopeKnown tickets caller)
    (frontChecked : StackUse policy tickets front .ordinary .ordinary frontDemand)
    (saved : StackUse policy tickets captured .ordinary .ordinary captureDemand)
    (rest : StackUse policy tickets tail .ordinary .ordinary tailDemand)
    (scopes : UnwindPrefix captured)
    (internal : captureDemand.Perm (ownedTickets captured))
    (balance : (owner :: (frontDemand ++ captureDemand ++ tailDemand)).Perm
      (ownedTickets (front.append (.live owner input answer captured caller tail)))) :
    MachineUse policy tickets
      (.unwind runtimeScope (captured.append (.push (.closing identity runtimeScope)
        (front.append (.spent owner answer caller tail))))) := by
  obtain ⟨demand, checked, reordered⟩ :=
    discard_use_recomposition (identity := identity) known callerScope scope frontChecked saved rest scopes internal
  have projected : (frontDemand ++ captureDemand ++ tailDemand).Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail) := by
    apply List.Perm.cons_inv
    exact balance.trans (by simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using List.perm_middle)
  refine ⟨demand, checked, (reordered.trans projected).trans ?_⟩
  simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using
    (List.perm_append_comm (l₁ := ownedTickets front) (l₂ := ownedTickets captured)).append_right (ownedTickets tail)

#print axioms Ash.OneShot.LexicalUnwind.ordinary_stack_use
#print axioms Ash.OneShot.LexicalUnwind.stack_use_append
#print axioms Ash.OneShot.LexicalUnwind.retiring_frame_use
#print axioms Ash.OneShot.LexicalUnwind.administrative_usage
#print axioms Ash.OneShot.LexicalUnwind.stack_use_decompose
#print axioms Ash.OneShot.LexicalUnwind.handler_cut_use
#print axioms Ash.OneShot.LexicalUnwind.prefix_use_unwind
#print axioms Ash.OneShot.LexicalUnwind.start_cleanup_use
#print axioms Ash.OneShot.LexicalUnwind.finish_cleanup_use
#print axioms Ash.OneShot.LexicalUnwind.finish_close_use
#print axioms Ash.OneShot.LexicalUnwind.frame_use_extension
#print axioms Ash.OneShot.LexicalUnwind.stack_use_extension
#print axioms Ash.OneShot.LexicalUnwind.handler_cut_use_clauses
#print axioms Ash.OneShot.LexicalUnwind.ordinary_machine_use
#print axioms Ash.OneShot.LexicalUnwind.administrative_machine_use
#print axioms Ash.OneShot.LexicalUnwind.start_cleanup_machine_use
#print axioms Ash.OneShot.LexicalUnwind.finish_cleanup_machine_use
#print axioms Ash.OneShot.LexicalUnwind.finish_close_machine_use
#print axioms Ash.OneShot.LexicalUnwind.capture_machine_use
#print axioms Ash.OneShot.LexicalUnwind.unused_live_enters_ordinary
#print axioms Ash.OneShot.LexicalUnwind.prefix_use_reentry
#print axioms Ash.OneShot.LexicalUnwind.resume_use_recomposition
#print axioms Ash.OneShot.LexicalUnwind.discard_use_recomposition
#print axioms Ash.OneShot.LexicalUnwind.initial_machine_use
#print axioms Ash.OneShot.LexicalUnwind.retire_value_machine_use
#print axioms Ash.OneShot.LexicalUnwind.close_value_machine_use
#print axioms Ash.OneShot.LexicalUnwind.focus_machine_use
#print axioms Ash.OneShot.LexicalUnwind.resume_machine_use_of_fragments
#print axioms Ash.OneShot.LexicalUnwind.discard_machine_use_of_fragments
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open ScopedExpressions ScopedExecution
open Syntax (TicketPolicy UsageTickets UsageScopeKnown)

/-- Existing expression dependency evidence also bounds mode-aware demand.
    Unwinding adds only retirement of an already owned continuation. -/
theorem frame_use_pending_or_retiring
    (checked : FrameUse policy tickets frame before after demand) (present : owner ∈ demand) :
    owner ∈ frame.erase.pending ∨ frame = .retiring owner := by
  cases checked with
  | ordinary payload => exact frame_demand_pending_or_retiring payload present
  | unwind payload scopes =>
      cases payload <;> simp only [ScopedRetirement.scheduled, List.not_mem_nil, List.mem_cons,
        or_false] at present
      next known => subst owner; exact Or.inr rfl
  | cleanup | closing => cases present

theorem stack_use_pending_or_owned
    (checked : StackUse policy tickets stack before after demand) :
    demand ⊆ stack.erase.pending ++ ownedTickets stack := by
  induction checked with
  | nil => exact List.nil_subset _
  | @push entry before middle first tail after remaining frame rest ih =>
      intro owner present
      rcases List.mem_append.mp present with here | later
      · rcases frame_use_pending_or_retiring frame here with pending | retiring
        · exact List.mem_append_left _ (List.mem_append_left _ pending)
        · subst retiring
          exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))
      · rcases List.mem_append.mp (ih later) with pending | owned
        · exact List.mem_append_left _ (List.mem_append_right _ pending)
        · cases entry <;> simp_all [Stack.erase, Control.pending, ownedTickets]
  | @live selected rights caller captured beforeMode middle first tail after remaining input answer known scope saved rest ihSaved ihRest =>
      intro owner present
      rcases List.mem_append.mp present with first | outside
      · rcases List.mem_append.mp first with retiring | inside
        · cases beforeMode <;> simp_all [retiredDemand, ownedTickets]
        · rcases List.mem_append.mp (ihSaved inside) with pending | owned
          · exact List.mem_append_left _ (List.mem_append_left _ pending)
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ owned))
      · rcases List.mem_append.mp (ihRest outside) with pending | owned
        · exact List.mem_append_left _ (List.mem_append_right _ pending)
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ owned))
  | spent known scope rest ih => exact ih

theorem stack_use_bound
    (checked : StackUse policy tickets stack before after demand)
    (pending : InternalUses allowed stack.erase.pending)
    (owned : ownedTickets stack ⊆ allowed) : demand ⊆ allowed := by
  intro owner present
  rcases List.mem_append.mp (stack_use_pending_or_owned checked present) with code | retired
  · exact internalUses_subset pending code
  · exact owned retired

theorem internal_stack_use_bound
    (checked : StackUse policy tickets stack before after demand)
    (internal : InternalUses stack.erase.liveTickets stack.erase.pending) : demand ⊆ ownedTickets stack := by
  intro owner present
  rcases List.mem_append.mp (stack_use_pending_or_owned checked present) with code | retired
  · exact recursive_live_tickets_owned stack (internalUses_subset internal code)
  · exact retired

/-- Exact capture accounting is derived by the existing disjoint-demand lemma,
    from finite pending-use bounds and unique ownership. No cleanup plan is used. -/
theorem capture_demand_balance
    (frontUse : StackUse policy tickets front before middle frontDemand)
    (savedUse : StackUse policy tickets captured savedBefore savedAfter captureDemand)
    (tailUse : StackUse policy tickets tail tailBefore after tailDemand)
    (frontBound : InternalUses (ownedTickets front ++ ownedTickets tail) front.erase.pending)
    (internal : InternalUses captured.erase.liveTickets captured.erase.pending)
    (tailBound : InternalUses (ownedTickets tail) tail.erase.pending)
    (balance : (frontDemand ++ captureDemand ++ tailDemand).Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail))
    (unique : (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail).Nodup) :
    captureDemand.Perm (ownedTickets captured) := by
  exact Syntax.balanced_middle_demands balance unique
    (stack_use_bound frontUse frontBound (List.subset_append_left _ _))
    (internal_stack_use_bound savedUse internal)
    (stack_use_bound tailUse tailBound (List.Subset.refl _))

/-- Disposal accounting follows from the predecessor invariant, unique
    ownership, the existing protection guard and finite pending-use bounds.
    Exact capture balance is derived, rather than an admission premise. -/
theorem discard_machine_use
    (checked : MachineUse policy tickets (.eval ⟨.discard binder, runtimeScope,
      front.append (.live owner input answer captured caller tail)⟩))
    (resolved : runtimeScope.resolve binder = some owner)
    (unique : (ownedTickets (front.append (.live owner input answer captured caller tail))).Nodup)
    (unprotected : ProtectionContexts.protectedMode captured.erase = false)
    (frontBound : InternalUses (ownedTickets front ++ ownedTickets tail) front.erase.pending)
    (internal : InternalUses captured.erase.liveTickets captured.erase.pending)
    (tailBound : InternalUses (ownedTickets tail) tail.erase.pending) :
    MachineUse policy tickets (.unwind runtimeScope
      (captured.append (.push (.closing identity runtimeScope)
        (front.append (.spent owner answer caller tail))))) := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  have sameCurrent := discard_code_demand code resolved
  subst current
  have demandedUnique : (owner :: pending).Nodup := balance.symm.nodup unique
  obtain ⟨unused, pendingUnique⟩ := List.nodup_cons.mp demandedUnique
  have projected : pending.Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail) := by
    apply List.Perm.cons_inv
    exact balance.trans (by simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using List.perm_middle)
  obtain ⟨ownerMode, frontDemand, boundaryDemand, same, frontUse, boundary⟩ := stack_use_decompose stack
  have ordinaryMode := unused_live_enters_ordinary boundary
    (fun present => unused (same ▸ List.mem_append_right frontDemand present))
  subst ownerMode
  cases boundary with
  | live known callerScope saved rest =>
      have scopes := unprotected_unwind_prefix unprotected
      obtain ⟨sameMode, abandoned⟩ := prefix_use_unwind scopes saved
      subst sameMode
      have savedBalance := capture_demand_balance frontUse saved rest frontBound internal tailBound
        (by simpa only [same, retiredDemand, List.nil_append, List.append_assoc] using projected)
        (projected.nodup pendingUnique)
      exact discard_machine_use_of_fragments (identity := identity)
        (Syntax.code_demand_scope code) known callerScope frontUse saved rest scopes savedBalance
        (by simpa only [same, retiredDemand, List.nil_append, List.append_assoc, List.singleton_append] using balance)

/-- The return mode is determined by actual lexical boundaries, independently
    of effect rows, ownership identities or successful future execution. -/
def returnMode : Stack → UseMode → UseMode
  | .nil, mode => mode
  | .push (.unwinding _) rest, _ => returnMode rest .unwind
  | .push (.closing _ _) rest, _ => returnMode rest .ordinary
  | .push _ rest, mode => returnMode rest mode
  | .live _ _ _ captured _ rest, mode => returnMode rest (returnMode captured mode)
  | .spent _ _ _ rest, mode => returnMode rest mode

theorem stack_use_return_mode
    (checked : StackUse policy tickets stack before after demand) : returnMode stack before = after := by
  induction checked with
  | nil => rfl
  | push frame rest ih => cases frame with
      | ordinary payload => cases payload <;> exact ih
      | unwind payload scopes => cases payload <;> first | exact ih | cases scopes
      | cleanup | closing => exact ih
  | live known scope saved rest ihSaved ihRest =>
      simpa only [returnMode, ihSaved] using ihRest
  | spent known scope rest ih => exact ih

/-- Local structural premises for inserting a caller fragment after a capture.
    Unwind return checks only the fragments whose pending work is affected. -/
inductive ReentryBounds (front captured tail : Stack) : UseMode → Prop where
  | ordinary : ReentryBounds front captured tail .ordinary
  | unwind (scopes : UnwindPrefix front)
      (inside : InternalUses front.erase.liveTickets front.erase.pending)
      (saved : InternalUses (ownedTickets captured ++ ownedTickets tail) captured.erase.pending)
      (outside : InternalUses (ownedTickets tail) tail.erase.pending) :
      ReentryBounds front captured tail .unwind

/-- The existing reentry accounting argument, exposed independently of its
usage reconstruction so rich source can reuse the same derived balance. -/
theorem reentry_unwind_balance
    (frontUse : StackUse policy tickets front .ordinary .ordinary frontDemand)
    (savedUse : StackUse policy tickets captured .ordinary .unwind captureDemand)
    (tailUse : StackUse policy tickets tail .unwind finalMode tailDemand)
    (bounds : ReentryBounds front captured tail .unwind)
    (balance : (frontDemand ++ captureDemand ++ tailDemand).Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail))
    (unique : (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail).Nodup) :
    frontDemand.Perm (ownedTickets front) := by
  cases bounds with
  | unwind scopes inside saved outside =>
      have exchanged : (captureDemand ++ frontDemand ++ tailDemand).Perm
          (ownedTickets captured ++ ownedTickets front ++ ownedTickets tail) :=
        ((List.perm_append_comm (l₁ := captureDemand) (l₂ := frontDemand)).append_right tailDemand).trans
          (balance.trans ((List.perm_append_comm (l₁ := ownedTickets front)
            (l₂ := ownedTickets captured)).append_right (ownedTickets tail)))
      have exchangedUnique : (ownedTickets captured ++ ownedTickets front ++ ownedTickets tail).Nodup :=
        ((List.perm_append_comm (l₁ := ownedTickets front)
          (l₂ := ownedTickets captured)).append_right (ownedTickets tail)).nodup unique
      exact capture_demand_balance savedUse frontUse tailUse saved inside outside exchanged exchangedUnique
#print axioms Ash.OneShot.LexicalUnwind.reentry_unwind_balance


/-- Reuse disjoint-demand balance with the caller and capture exchanged. -/
theorem reentry_from_bounds
    (frontUse : StackUse policy tickets front .ordinary .ordinary frontDemand)
    (savedUse : StackUse policy tickets captured .ordinary mode captureDemand)
    (tailUse : StackUse policy tickets tail mode .ordinary tailDemand)
    (bounds : ReentryBounds front captured tail mode)
    (balance : (frontDemand ++ captureDemand ++ tailDemand).Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail))
    (unique : (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail).Nodup) :
    ∃ restored, StackUse policy tickets front mode mode restored ∧ restored.Perm frontDemand := by
  cases bounds with
  | ordinary => exact ⟨frontDemand, frontUse, List.Perm.refl _⟩
  | unwind scopes inside saved outside =>
      have balanced := reentry_unwind_balance frontUse savedUse tailUse
        (.unwind scopes inside saved outside) balance unique
      exact prefix_use_reentry frontUse (.inr ⟨scopes, balanced⟩)

/-- Resumption accounting derives the caller's reentry evidence from finite
    checks on predecessor fragments; it never assumes the restored invariant. -/
theorem resume_machine_use
    (checked : MachineUse policy tickets (.eval ⟨.resume binder value, runtimeScope,
      front.append (.live owner input answer captured caller tail)⟩))
    (resolved : runtimeScope.resolve binder = some owner) (isValue : value.IsValue)
    (unique : (ownedTickets (front.append (.live owner input answer captured caller tail))).Nodup)
    (bounds : ReentryBounds front captured tail (returnMode captured .ordinary)) :
    MachineUse policy tickets
      (.eval ⟨value, runtimeScope, captured.append (front.append (.spent owner answer caller tail))⟩) := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  have sameCurrent := resume_code_demand code resolved
  subst current
  have demandedUnique : (owner :: pending).Nodup := balance.symm.nodup unique
  obtain ⟨unused, pendingUnique⟩ := List.nodup_cons.mp demandedUnique
  have projected : pending.Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail) := by
    apply List.Perm.cons_inv
    exact balance.trans (by simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using List.perm_middle)
  obtain ⟨ownerMode, frontDemand, boundaryDemand, same, frontUse, boundary⟩ := stack_use_decompose stack
  have ordinaryMode := unused_live_enters_ordinary boundary
    (fun present => unused (same ▸ List.mem_append_right frontDemand present))
  subst ownerMode
  cases boundary with
  | live known callerScope saved rest =>
      have actualMode := stack_use_return_mode saved
      obtain ⟨restored, reentry, exchanged⟩ := reentry_from_bounds frontUse saved rest (actualMode ▸ bounds)
        (by simpa only [same, retiredDemand, List.nil_append, List.append_assoc] using projected)
        (projected.nodup pendingUnique)
      apply resume_machine_use_of_fragments (input := input) code isValue known callerScope saved rest reentry
      simpa only [List.append_assoc] using ((exchanged.append_right _).cons owner).trans
        (show (owner :: (frontDemand ++ (_ ++ _))).Perm
          (ownedTickets (front.append (.live owner input answer captured caller tail))) from
          by simpa only [same, retiredDemand, List.nil_append, List.append_assoc, List.singleton_append] using balance)

/-- Finite checks over existing lexical fragments, with no execution search. -/
def checkReentryBounds (front captured tail : Stack) : UseMode → Bool
  | .ordinary => true
  | .unwind => checkUnwindPrefix front &&
      ClosingAdmission.checkInternalUses front.erase.liveTickets front.erase.pending &&
      ClosingAdmission.checkInternalUses (ownedTickets captured ++ ownedTickets tail) captured.erase.pending &&
      ClosingAdmission.checkInternalUses (ownedTickets tail) tail.erase.pending

theorem check_reentry_bounds_iff :
    checkReentryBounds front captured tail mode = true ↔ ReentryBounds front captured tail mode := by
  cases mode with
  | ordinary => exact ⟨fun _ => .ordinary, fun _ => rfl⟩
  | unwind =>
      simp only [checkReentryBounds, Bool.and_eq_true, check_unwind_prefix_iff,
        ClosingAdmission.check_internal_uses_iff]
      exact ⟨fun ⟨⟨⟨scopes, inside⟩, saved⟩, outside⟩ => .unwind scopes inside saved outside,
        fun checked => by cases checked with
          | unwind scopes inside saved outside => exact ⟨⟨⟨scopes, inside⟩, saved⟩, outside⟩⟩

theorem unwind_prefix_return_mode (scopes : UnwindPrefix stack) (mode : UseMode) :
    returnMode stack mode = mode := by
  induction scopes with
  | nil => rfl
  | plain scopes ih | handler scopes ih | cell scopes ih | armed scopes ih
  | retiring scopes ih | spent scopes ih => exact ih
  | live saved rest ihSaved ihRest => simpa only [returnMode, ihSaved] using ihRest

/-- The same local reentry bounds used by accounting also supply the boundary
    compatibility needed by a resumed cleanup. An open capture is allowed. -/
theorem callback_resume_ready_from_bounds
    (cut : HandlerCut requested rest saved tail handler)
    (ready : UnwindReady rest)
    (bounds : ReentryBounds front (.push (.unwinding action) saved) tail
      (returnMode (.push (.unwinding action) saved) .ordinary)) :
    UnwindReady (saved.append (front.append (.spent owner answer caller tail))) := by
  apply (callback_resume_ready (action := action) (owner := owner) (answer := answer)
    (caller := caller) cut ready ?_).2
  have separated := (unwind_ready_append_iff saved tail).mp ((handler_cut_reconstructs cut) ▸ ready)
  rcases separated with inside | ⟨openScopes, outside⟩
  · exact .inl inside
  · have mode : returnMode (.push (.unwinding action) saved) .ordinary = .unwind :=
      unwind_prefix_return_mode openScopes .unwind
    rw [mode] at bounds
    cases bounds with
    | unwind scopes inside saved outside => exact .inr scopes

#print axioms Ash.OneShot.LexicalUnwind.frame_use_pending_or_retiring
#print axioms Ash.OneShot.LexicalUnwind.stack_use_pending_or_owned
#print axioms Ash.OneShot.LexicalUnwind.stack_use_bound
#print axioms Ash.OneShot.LexicalUnwind.internal_stack_use_bound
#print axioms Ash.OneShot.LexicalUnwind.capture_demand_balance
#print axioms Ash.OneShot.LexicalUnwind.discard_machine_use
#print axioms Ash.OneShot.LexicalUnwind.stack_use_return_mode
#print axioms Ash.OneShot.LexicalUnwind.reentry_from_bounds
#print axioms Ash.OneShot.LexicalUnwind.resume_machine_use
#print axioms Ash.OneShot.LexicalUnwind.check_reentry_bounds_iff
#print axioms Ash.OneShot.LexicalUnwind.unwind_prefix_return_mode
#print axioms Ash.OneShot.LexicalUnwind.callback_resume_ready_from_bounds
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open ScopedExpressions ScopedExecution
open Syntax (TicketPolicy UsageTickets UsageScopeKnown)

theorem cell_update_stack_use
    (update : CellUpdate identity old new before after)
    (checked : StackUse policy tickets before input output demand) :
    StackUse policy tickets after input output demand := by
  induction update generalizing input output demand with
  | hit => cases checked with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | cell scope => exact .push (.ordinary (.cell scope)) rest
          | unwind payload scopes => cases payload with
              | cell scope => exact .push (.unwind (.cell scope) (.cell .nil)) rest
  | push miss next ih => cases checked with
      | push frame rest => exact .push frame (ih rest)
  | live next ih => cases checked with
      | live known scope saved rest => exact .live known scope saved (ih rest)
  | spent next ih => cases checked with
      | spent known scope rest => exact .spent known scope (ih rest)

/-- Ordinary value transitions reuse established value-demand and context
    replacement proofs; the retained suffix keeps its actual mode interface. -/
theorem raw_value_machine_use
    (step : RawStep before after created discharged) (closed : ClosedValue before.expression)
    (checked : MachineUse policy tickets (.eval before)) : MachineUse policy tickets (.eval after) := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  have currentEmpty := code_demand_value_is_empty code closed.1
  subst current
  cases step with
  | focus plain focus tail => exact False.elim (focus_is_not_value focus closed.1)
  | bind | beta | ifTrue | ifFalse | enterHandler | enterCell | enterCleanup
  | capture | resume | discard | readCell | writeCell => cases closed.1
  | plug plain value valueClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | plain context =>
                  exact ⟨_, _, code_demand_plug_value context valueClosed.1 (code_demand_value_usage code valueClosed.1),
                    rest, balance⟩
  | leaveHandler handler value valueClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | handler caller clauses =>
                  exact ⟨[], _, code_demand_value_transport code valueClosed.1 caller, rest, balance⟩
  | leaveCell identity payload answer savedScope scope value valueClosed tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | cell caller =>
                  exact ⟨[], _, code_demand_value_transport code valueClosed.1 caller, rest, balance⟩
  | startCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | armed caller callable =>
                  exact ⟨[], _, .idle .none (.app callable .unit),
                    .push (.ordinary (.running caller callable (code_demand_value_usage code savedClosed.1))) rest, balance⟩
  | finishCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | running caller callable result =>
                  obtain ⟨useScope, caller⟩ := caller
                  exact ⟨[], _, .idle caller (value_use_transport savedClosed.1 result _ .available), rest, balance⟩
  | leaveClause owner answer value valueClosed scope callerScope tail => cases stack with
      | spent known caller rest =>
          exact ⟨[], _, code_demand_value_transport code valueClosed.1 caller, rest, balance⟩
  | finishClose identity scope callerScope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | closing caller =>
                  exact ⟨[], _, code_demand_value_transport code closed.1 caller, rest, balance⟩
  | retire owner scope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | retiring known => exact ⟨[], _, code, rest, balance.cons_inv⟩

/-- Focusing a resumption operand is ordinary computation. Invoking its
    continuation requires the separately checked lexical return boundary. -/
def computationHead : Code → Prop
  | .resume _ operand => ¬ operand.IsValue
  | .discard _ => False
  | _ => True

/-- Ordinary computation preserves accounting using existing expression-use
    proofs. Actual continuation invocation is handled by its structural rule. -/
theorem raw_computation_machine_use
    (step : RawStep before after created discharged)
    (head : computationHead before.expression)
    (allocation : ∀ owner, Owner.ticket owner ∈ created → tickets owner = none)
    (checked : MachineUse policy tickets (.eval before)) :
    MachineUse policy (advanceUsageTickets policy tickets after created) (.eval after) := by
  have actual := step
  have original := checked
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  cases step with
  | focus plain focus tail => exact focus_machine_use plain focus original
  | bind parameter value body scope tail closed environment =>
      exact ⟨current, pending, bind_code_demand code closed.1, stack, balance⟩
  | beta parameter body value scope tail closed closure =>
      obtain ⟨same, afterCode⟩ := beta_code_demand code closed.1
      subst current
      exact ⟨[], pending, afterCode, stack, balance⟩
  | ifTrue => exact ⟨current, pending, (branch_code_demand code).1, stack, balance⟩
  | ifFalse => exact ⟨current, pending, (branch_code_demand code).2, stack, balance⟩
  | enterHandler handler body tail =>
      obtain ⟨bodyCode, clauses⟩ := handler_code_demand code
      exact ⟨current, pending, bodyCode,
        .push (.ordinary (.handler (Syntax.code_demand_scope code) clauses)) stack, balance⟩
  | enterCell binder identity payload body scope answer tail ready =>
      exact ⟨current, pending, acquisition_preserves_code_demand code _,
        .push (.ordinary (.cell (Syntax.code_demand_scope code))) stack, balance⟩
  | enterCleanup action body tail =>
      obtain ⟨bodyCode, callable⟩ := cleanup_code_demand code action.closed.1
      exact ⟨current, pending, bodyCode,
        .push (.ordinary (.armed (Syntax.code_demand_scope code) callable)) stack, balance⟩
  | capture requested operation parameter binder owner operand body scope whole captured tail handler
      input cut selected closed environment =>
      exact capture_machine_use cut
        (selected_clause_usage selected (handler_cut_use_clauses cut stack).2)
        original closed.1 (allocation owner (by simp))
  | resume binder owner scope caller input answer front captured tail value closed resolved =>
      exact False.elim (head closed.1)
  | discard => exact False.elim head
  | readCell identity payload scope before after update =>
      have same := perform_value_demand_empty code (by trivial)
      subst current
      obtain ⟨useScope, scopeKnown⟩ := Syntax.code_demand_scope code
      exact ⟨[], pending, .idle scopeKnown .integer, cell_update_stack_use update stack,
        by simpa only [cell_update_owned_tickets update] using balance⟩
  | writeCell identity old new scope before after update =>
      have same := perform_value_demand_empty code (by trivial)
      subst current
      obtain ⟨useScope, scopeKnown⟩ := Syntax.code_demand_scope code
      exact ⟨[], pending, .idle scopeKnown .unit, cell_update_stack_use update stack,
        by simpa only [cell_update_owned_tickets update] using balance⟩
  | plug | leaveHandler | leaveCell | startCleanup | finishCleanup | leaveClause | finishClose | retire =>
      apply raw_value_machine_use actual ?_ original
      first | assumption | simp [ClosedValue, Code.IsValue, Code.dependencies, Code.ResourceClosed, Code.freeNames]

/-- One-step use evidence inspects the actual lexical fragments. It has no
    successor invariant, future execution, or cleanup-plan premise. -/
inductive UseTransition : Machine → Machine → List Owner → List Owner → Prop where
  | evaluate (step : RawStep before after created discharged) (head : computationHead before.expression) :
      UseTransition (.eval before) (.eval after) created discharged
  | resume (binder owner : Nat) (scope caller : Scope) (input answer : Ty)
      (front captured tail : Stack) (value : Code) (closed : ClosedValue value)
      (resolved : scope.resolve binder = some owner)
      (bounds : ReentryBounds front captured tail (returnMode captured .ordinary)) :
      UseTransition (.eval ⟨.resume binder value, scope, front.append (.live owner input answer captured caller tail)⟩)
        (.eval ⟨value, scope, captured.append (front.append (.spent owner answer caller tail))⟩) [] [.ticket owner]
  | discard (binder owner identity : Nat) (scope caller : Scope) (input answer : Ty)
      (front captured tail : Stack) (resolved : scope.resolve binder = some owner)
      (unprotected : ProtectionContexts.protectedMode captured.erase = false)
      (frontBound : InternalUses (ownedTickets front ++ ownedTickets tail) front.erase.pending)
      (internal : InternalUses captured.erase.liveTickets captured.erase.pending)
      (tailBound : InternalUses (ownedTickets tail) tail.erase.pending) :
      UseTransition (.eval ⟨.discard binder, scope, front.append (.live owner input answer captured caller tail)⟩)
        (.unwind scope (captured.append (.push (.closing identity scope)
          (front.append (.spent owner answer caller tail))))) [.close identity] [.ticket owner]
  | advance (step : Advance before after discharged) :
      UseTransition (.unwind scope before) (.unwind scope after) [] discharged
  | startCleanup : UseTransition (.unwind scope (.push (.armed action) rest))
      (.eval ⟨.app action.action .unit, .none, .push (.unwinding action) rest⟩) [] []
  | finishCleanup : UseTransition (.eval ⟨.unit, scope, .push (.unwinding action) rest⟩)
      (.unwind action.scope rest) [] [.cleanup action.identity]
  | finishClose : UseTransition (.unwind scope (.push (.closing identity caller) rest))
      (.eval ⟨.unit, caller, rest⟩) [] [.close identity]
  | retireValue (closed : ClosedValue value) :
      UseTransition (.eval ⟨value, scope, .push (.retiring owner) rest⟩)
        (.eval ⟨value, scope, rest⟩) [] [.ticket owner]
  | closeValue (closed : ClosedValue value) :
      UseTransition (.eval ⟨value, scope, .push (.closing identity caller) rest⟩)
        (.eval ⟨.unit, caller, rest⟩) [] [.close identity]

theorem UseTransition.erases (step : UseTransition before after created discharged) :
    Transition before after created discharged := by
  cases step with
  | evaluate raw head =>
      have allowed : ∀ expression, computationHead expression → ordinary expression := by
        intro expression checked
        cases expression <;> simp_all [computationHead, ordinary]
      exact .evaluate raw (allowed _ head)
  | resume binder owner scope caller input answer front captured tail value closed resolved bounds =>
      exact .evaluate (.resume binder owner scope caller input answer front captured tail value closed resolved) trivial
  | discard binder owner identity scope caller input answer front captured tail resolved unprotected frontBound internal tailBound =>
      exact .discard binder owner identity scope caller input answer front captured tail resolved unprotected
  | advance step => exact .advance step
  | startCleanup => exact .startCleanup
  | finishCleanup => exact .finishCleanup
  | finishClose => exact .finishClose
  | retireValue closed => exact .retireValue closed
  | closeValue closed => exact .closeValue closed

def advanceUseTickets (policy : TicketPolicy) (tickets : UsageTickets) (after : Machine)
    (created : List Owner) : UsageTickets :=
  match after with
  | .eval configuration => advanceUsageTickets policy tickets configuration created
  | .unwind _ _ => tickets

/-- Every transition family preserves use accounting with only structural
    predecessor checks. Uniqueness and allocation come from the lifetime ledger. -/
theorem UseTransition.preserves
    (step : UseTransition before after created discharged)
    (allocation : ∀ owner, Owner.ticket owner ∈ created → tickets owner = none)
    (unique : (ownedTickets before.stack).Nodup)
    (checked : MachineUse policy tickets before) :
    MachineUse policy (advanceUseTickets policy tickets after created) after := by
  cases step with
  | evaluate raw head => exact raw_computation_machine_use raw head allocation checked
  | resume binder owner scope caller input answer front captured tail value closed resolved bounds =>
      exact resume_machine_use checked resolved closed.1 unique bounds
  | discard binder owner identity scope caller input answer front captured tail resolved unprotected frontBound internal tailBound =>
      exact discard_machine_use checked resolved unique unprotected frontBound internal tailBound
  | advance step => exact administrative_machine_use step checked
  | startCleanup => exact start_cleanup_machine_use checked
  | finishCleanup => exact finish_cleanup_machine_use checked
  | finishClose => exact finish_close_machine_use checked
  | retireValue closed => exact retire_value_machine_use checked closed.1
  | closeValue closed => exact close_value_machine_use checked closed.1

theorem UseTransition.registry
    (step : UseTransition before after created discharged)
    (history : UsageRegistryHistory tickets issued) :
    UsageRegistryHistory (advanceUseTickets policy tickets after created) (issued ++ created) := by
  cases step with
  | evaluate raw head => exact raw_step_preserves_usage_registry_history raw history
  | resume | advance | startCleanup | finishCleanup | finishClose | retireValue | closeValue =>
      simpa only [advanceUseTickets, advanceUsageTickets, List.append_nil] using history
  | discard =>
      intro owner
      simpa [advanceUseTickets] using history owner

/-- Ticket history extends at allocation; consumed entries remain available
    for typing and interpreting retained lexical interfaces. -/
theorem UseTransition.extension
    (step : UseTransition before after created discharged)
    (allocation : ∀ owner, Owner.ticket owner ∈ created → tickets owner = none) :
    Syntax.UsageExtension tickets (advanceUseTickets policy tickets after created) := by
  cases step with
  | evaluate raw head => exact advance_usage_tickets_extends allocation
  | resume | discard | advance | startCleanup | finishCleanup | finishClose | retireValue | closeValue =>
      exact fun _ _ known => known

structure UseRunState where
  execution : RunState
  tickets : UsageTickets

/-- The event carries structural checks and fresh allocation, never a proof of
    the next state. Source admission must still supply and preserve its checks. -/
inductive UseEvent (policy : TicketPolicy) : UseRunState → UseRunState → Prop where
  | step (transition : UseTransition before.execution.machine machine created discharged)
      (fresh : (before.execution.issued ++ created).Nodup) :
      UseEvent policy before
        ⟨⟨machine, before.execution.issued ++ created, discharged ++ before.execution.completed⟩,
          advanceUseTickets policy before.tickets machine created⟩

def UseRunInvariant (policy : TicketPolicy) (state : UseRunState) : Prop :=
  Ledger state.execution.erase ∧ UsageRegistryHistory state.tickets state.execution.issued ∧
    MachineUse policy state.tickets state.execution.machine

theorem UseEvent.preserves (step : UseEvent policy before after)
    (checked : UseRunInvariant policy before) : UseRunInvariant policy after := by
  obtain ⟨ledger, history, usage⟩ := checked
  have allocation (createdOwners : List Owner) (fresh : (before.execution.issued ++ createdOwners).Nodup) :
      ∀ owner, Owner.ticket owner ∈ createdOwners → before.tickets owner = none := by
    intro owner created
    cases existing : before.tickets owner with
    | none => rfl
    | some rights =>
        have earlier := (history owner).mp ⟨rights, existing⟩
        exact False.elim ((List.nodup_append.mp fresh).2.2 (.ticket owner) earlier
          (.ticket owner) created rfl)
  cases step with
  | step transition fresh =>
      exact ⟨event_preserves_ledger (.step transition.erases fresh) ledger,
        transition.registry history,
        transition.preserves (allocation _ fresh) (owned_tickets_unique (ledger_unique_live ledger)) usage⟩

theorem use_execution_preserves
    (steps : Relation.TransGen (UseEvent policy) before after)
    (checked : UseRunInvariant policy before) : UseRunInvariant policy after := by
  induction steps with
  | single step => exact step.preserves checked
  | tail steps step ih => exact step.preserves ih

theorem focus_computation_head (focus : Focus whole child context) : computationHead whole := by
  cases focus <;> first | trivial | assumption

theorem value_computation_head (value : expression.IsValue) : computationHead expression := by
  cases expression <;> first | trivial | cases value

theorem UseEvent.erases (step : UseEvent policy before after) : Event before.execution after.execution := by
  cases step with
  | step transition fresh => exact .step transition.erases fresh

theorem initial_use_run_invariant
    (source : Uses policy .none .available expression .available) :
    UseRunInvariant policy ⟨⟨.eval ⟨expression, .none, .nil⟩, [], []⟩, fun _ => none⟩ := by
  exact ⟨⟨List.Perm.refl [], List.nodup_nil⟩, empty_usage_registry_history, initial_machine_use source⟩

#print axioms Ash.OneShot.LexicalUnwind.cell_update_stack_use
#print axioms Ash.OneShot.LexicalUnwind.raw_value_machine_use
#print axioms Ash.OneShot.LexicalUnwind.raw_computation_machine_use
#print axioms Ash.OneShot.LexicalUnwind.UseTransition.erases
#print axioms Ash.OneShot.LexicalUnwind.UseTransition.preserves
#print axioms Ash.OneShot.LexicalUnwind.UseTransition.registry
#print axioms Ash.OneShot.LexicalUnwind.UseTransition.extension
#print axioms Ash.OneShot.LexicalUnwind.UseEvent.preserves
#print axioms Ash.OneShot.LexicalUnwind.use_execution_preserves
#print axioms Ash.OneShot.LexicalUnwind.focus_computation_head
#print axioms Ash.OneShot.LexicalUnwind.value_computation_head
#print axioms Ash.OneShot.LexicalUnwind.UseEvent.erases
#print axioms Ash.OneShot.LexicalUnwind.initial_use_run_invariant
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open ScopedExpressions ScopedExecution

def frameTicketUses (frame : ExecFrame) : UseMode → List Nat
  | .ordinary => frame.erase.pending
  | .unwind => []

/-- Access follows lexical suffixes and dormant capture boundaries. Abandoned
    pending code does not request a ticket. Retirement is ownership, not access. -/
inductive TicketAccess : Stack → UseMode → UseMode → List Nat → Prop where
  | nil : TicketAccess .nil mode mode outside
  | push (visible : frameTicketUses frame before ⊆ activeTickets tail ++ outside)
      (rest : TicketAccess tail (returnMode (.push frame .nil) before) after outside) :
      TicketAccess (.push frame tail) before after outside
  | live (saved : TicketAccess captured before middle (activeTickets tail ++ outside))
      (rest : TicketAccess tail middle after outside) :
      TicketAccess (.live owner input answer captured caller tail) before after outside
  | spent (rest : TicketAccess tail before after outside) :
      TicketAccess (.spent owner answer caller tail) before after outside

theorem frame_use_return_mode (checked : FrameUse policy tickets frame before after demand) :
    returnMode (.push frame .nil) before = after :=
  stack_use_return_mode (.push checked .nil)

theorem ticket_access_return_mode (checked : TicketAccess stack before after outside) :
    returnMode stack before = after := by
  induction checked with
  | nil => rfl
  | @push frame before tail outside after visible rest ih => cases frame <;> exact ih
  | live saved rest ihSaved ihRest => simpa only [returnMode, ihSaved] using ihRest
  | spent rest ih => exact ih

/-- Reuse the existing correspondence between ordinary code demand and its
    translated pending names; internal retirements require no visible ticket. -/
theorem frame_pending_subset_active_demand
    (checked : FrameDemand policy tickets frame demand) : frame.erase.pending ⊆ frameActiveDemand frame demand := by
  cases checked with
  | plain code =>
      rename_i data
      intro owner present
      exact (translated_demand_membership code data.translated owner).mpr present
  | handler | cell | armed | running | closing | retiring => exact List.nil_subset _

theorem ordinary_stack_ticket_access
    (checked : StackUsage policy tickets stack outside demand) :
    TicketAccess stack .ordinary .ordinary outside := by
  induction checked with
  | nil => exact .nil
  | push frame visible rest ih =>
      exact .push (List.Subset.trans (frame_pending_subset_active_demand frame) visible)
        (by rw [frame_use_return_mode (.ordinary frame)]; exact ih)
  | live known scope saved rest ihSaved ihRest => exact .live ihSaved ihRest
  | spent known scope rest ih => exact .spent ih

theorem frame_use_access_or_retiring
    (checked : FrameUse policy tickets frame before after demand) (present : owner ∈ demand) :
    owner ∈ frameTicketUses frame before ∨ frame = .retiring owner := by
  cases checked with
  | ordinary payload => exact frame_demand_pending_or_retiring payload present
  | unwind payload scopes =>
      cases payload <;> simp only [ScopedRetirement.scheduled, List.not_mem_nil, List.mem_cons, or_false] at present
      next known => subst owner; exact Or.inr rfl
  | cleanup | closing => cases present

/-- Mode-aware demand obeys the same lexical ownership bound as old StackUsage. -/
theorem stack_use_access_bound
    (checked : StackUse policy tickets stack before after demand)
    (access : TicketAccess stack before after outside) : demand ⊆ ownedTickets stack ++ outside := by
  induction checked generalizing outside with
  | nil => exact List.nil_subset _
  | @push entry before middle first tail after remaining frame rest ih =>
      cases access with
      | push visible tailAccess =>
          rw [frame_use_return_mode frame] at tailAccess
          intro owner present
          rcases List.mem_append.mp present with here | later
          · rcases frame_use_access_or_retiring frame here with active | retiring
            · rcases List.mem_append.mp (visible active) with within | external
              · have owned := active_tickets_owned tail within
                cases entry <;> simp_all [ownedTickets]
              · exact List.mem_append_right _ external
            · subst retiring
              simp [ownedTickets]
          · have bound := ih tailAccess later
            cases entry <;> simp_all [ownedTickets]
  | @live selected rights caller captured before middle first tail after remaining input answer known scope saved rest ihSaved ihRest =>
      cases access with
      | live savedAccess restAccess =>
          have same := (ticket_access_return_mode savedAccess).symm.trans (stack_use_return_mode saved)
          subst same
          intro owner present
          rcases List.mem_append.mp present with first | outside
          · rcases List.mem_append.mp first with retired | inside
            · cases before <;> simp_all [retiredDemand, ownedTickets]
            · rcases List.mem_append.mp (ihSaved savedAccess inside) with within | external
              · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _ within))
              · rcases List.mem_append.mp external with within | external
                · exact List.mem_append_left _ (List.mem_cons_of_mem _
                    (List.mem_append_right _ (active_tickets_owned tail within)))
                · exact List.mem_append_right _ external
          · rcases List.mem_append.mp (ihRest restAccess outside) with within | external
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ within))
            · exact List.mem_append_right _ external
  | spent known scope rest ih => cases access with
      | spent restAccess => exact ih restAccess

/-- The ordinary unconsumed-clause obstruction is ruled out using the same
    ownership contradiction as the existing scoped proof, now with mode access. -/
theorem live_clause_cannot_return
    (isValue : value.IsValue)
    (unique : (ownedTickets (.live owner input answer captured caller tail)).Nodup)
    (access : TicketAccess (.live owner input answer captured caller tail) .ordinary .ordinary []) :
    ¬ MachineUse policy tickets (.eval ⟨value, scope, .live owner input answer captured caller tail⟩) := by
  rintro ⟨current, pending, code, stack, balance⟩
  have same := code_demand_value_is_empty code isValue
  subst current
  cases stack with
  | live known callerScope saved rest =>
      cases access with
      | live savedAccess restAccess =>
          have same := (ticket_access_return_mode savedAccess).symm.trans (stack_use_return_mode saved)
          subst same
          have absent := (List.nodup_cons.mp unique).1
          have demanded := balance.mem_iff.mpr (by simp [ownedTickets] : owner ∈ ownedTickets
            (.live owner input answer captured caller tail))
          simp only [List.nil_append, retiredDemand] at demanded
          rcases List.mem_append.mp demanded with inside | outside
          · rcases List.mem_append.mp (stack_use_access_bound saved savedAccess inside) with captured | external
            · exact absent (List.mem_append_left _ captured)
            · exact absent (List.mem_append_right _ (active_tickets_owned _ (by simpa using external)))
          · exact absent (List.mem_append_right _ (by simpa using stack_use_access_bound rest restAccess outside))

theorem frame_ticket_uses_subset_demand
    (checked : FrameUse policy tickets frame before after demand) :
    frameTicketUses frame before ⊆ demand := by
  cases checked with
  | ordinary payload =>
      exact List.Subset.trans (frame_pending_subset_active_demand payload) (frame_active_demand_subset _ _)
  | unwind | cleanup | closing => exact List.nil_subset _

theorem TicketAccess.weaken
    (checked : TicketAccess stack before after outside) (more : outside ⊆ larger) :
    TicketAccess stack before after larger := by
  induction checked generalizing larger with
  | nil => exact .nil
  | push visible rest ih =>
      apply TicketAccess.push
      · intro owner present
        rcases List.mem_append.mp (visible present) with within | external
        · exact List.mem_append_left _ within
        · exact List.mem_append_right _ (more external)
      · exact ih more
  | live saved rest ihSaved ihRest =>
      apply TicketAccess.live
      · apply ihSaved
        intro owner present
        rcases List.mem_append.mp present with within | external
        · exact List.mem_append_left _ within
        · exact List.mem_append_right _ (more external)
      · exact ihRest more
  | spent rest ih => exact .spent (ih more)

theorem TicketAccess.append
    (front : TicketAccess left before middle (activeTickets right ++ outside))
    (tail : TicketAccess right middle after outside) :
    TicketAccess (left.append right) before after outside := by
  induction left generalizing before middle with
  | nil => cases front; exact tail
  | push entry rest ih => cases front with
      | push visible next =>
          exact .push (by simpa only [active_tickets_append, List.append_assoc] using visible) (ih next tail)
  | live owner input answer saved caller rest ihSaved ihRest => cases front with
      | live captured next =>
          exact .live (by simpa only [active_tickets_append, List.append_assoc] using captured) (ihRest next tail)
  | spent owner answer caller rest ih => cases front with
      | spent next => exact .spent (ih next tail)

theorem TicketAccess.decompose
    (checked : TicketAccess (left.append right) before after outside) :
    ∃ middle, TicketAccess left before middle (activeTickets right ++ outside) ∧
      TicketAccess right middle after outside := by
  induction left generalizing before after outside with
  | nil => exact ⟨before, .nil, checked⟩
  | push frame rest ih => cases checked with
      | push visible tail =>
          obtain ⟨middle, inside, outside⟩ := ih tail
          exact ⟨middle, .push (by simpa only [active_tickets_append, List.append_assoc] using visible) inside, outside⟩
  | live owner input answer saved caller rest ihSaved ihRest => cases checked with
      | live capture tail =>
          obtain ⟨middle, inside, outside⟩ := ihRest tail
          exact ⟨middle, .live (by simpa only [active_tickets_append, List.append_assoc] using capture) inside, outside⟩
  | spent owner answer caller rest ih => cases checked with
      | spent tail =>
          obtain ⟨middle, inside, outside⟩ := ih tail
          exact ⟨middle, .spent inside, outside⟩

/-- An unwindable fragment has no executing free ticket use. Callback code
    begins separately with its closed lexical scope when its marker is entered. -/
theorem unwind_prefix_ticket_access (scopes : UnwindPrefix stack) (outside : List Nat) :
    TicketAccess stack .unwind .unwind outside := by
  induction scopes generalizing outside with
  | nil => exact .nil
  | plain scopes ih | handler scopes ih | cell scopes ih | armed scopes ih | retiring scopes ih =>
      exact .push (List.nil_subset _) (ih outside)
  | live saved rest ihSaved ihRest => exact .live (ihSaved _) (ihRest outside)
  | spent rest ih => exact .spent (ih outside)

/-- Shrink an external interface only for names demanded in the actual mode. -/
theorem ticket_access_change_external
    (checked : StackUse policy tickets stack before after demand)
    (access : TicketAccess stack before after outside)
    (retain : ∀ owner, owner ∈ demand → owner ∈ outside → owner ∈ other) :
    TicketAccess stack before after other := by
  induction checked generalizing outside other with
  | nil => exact .nil
  | push frame rest ih => cases access with
      | push visible tailAccess =>
          rw [frame_use_return_mode frame] at tailAccess
          apply TicketAccess.push
          · intro owner present
            rcases List.mem_append.mp (visible present) with within | external
            · exact List.mem_append_left _ within
            · exact List.mem_append_right _ (retain owner
                (List.mem_append_left _ (frame_ticket_uses_subset_demand frame present)) external)
          · rw [frame_use_return_mode frame]
            exact ih tailAccess (fun owner present external => retain owner (List.mem_append_right _ present) external)
  | live known scope saved rest ihSaved ihRest => cases access with
      | live savedAccess restAccess =>
          have same := (ticket_access_return_mode savedAccess).symm.trans (stack_use_return_mode saved)
          subst same
          apply TicketAccess.live
          · apply ihSaved savedAccess
            intro owner present external
            rcases List.mem_append.mp external with within | external
            · exact List.mem_append_left _ within
            · exact List.mem_append_right _ (retain owner
                (List.mem_append_left _ (List.mem_append_right _ present)) external)
          · exact ihRest restAccess (fun owner present external => retain owner (List.mem_append_right _ present) external)
  | spent known scope rest ih => cases access with
      | spent tail => exact .spent (ih tail retain)

theorem ticket_access_remove_unused
    (checked : StackUse policy tickets stack before after demand)
    (access : TicketAccess stack before after (owner :: outside))
    (unused : owner ∉ demand) : TicketAccess stack before after outside := by
  apply ticket_access_change_external checked access
  intro name present external
  rcases List.mem_cons.mp external with same | remaining
  · subst name; exact False.elim (unused present)
  · exact remaining

theorem administrative_ticket_access
    (step : Advance before after discharged)
    (access : TicketAccess before .unwind finalMode outside) :
    TicketAccess after .unwind finalMode outside := by
  cases step with
  | plain | handler | cell | retire => cases access with
      | push visible rest => exact rest
  | spent => cases access with
      | spent rest => exact rest
  | live => cases access with
      | live saved rest =>
          apply TicketAccess.append (right := .push (.retiring _) _) saved
          exact .push (by unfold frameTicketUses; split <;> exact List.nil_subset _) rest

/-- A handler capture retains exactly the already checked suffix interfaces. -/
theorem capture_ticket_access
    (cut : HandlerCut requested whole captured tail handler)
    (access : TicketAccess whole .ordinary .ordinary outside) :
    TicketAccess (.live owner input handler.answer captured handler.scope tail) .ordinary .ordinary outside := by
  rw [handler_cut_reconstructs cut] at access
  obtain ⟨middle, saved, rest⟩ := access.decompose
  exact .live saved rest

theorem resume_ticket_access_fragments
    (frontUse : StackUse policy tickets front .ordinary .ordinary frontDemand)
    (frontAccess : TicketAccess front .ordinary .ordinary (owner :: (activeTickets tail ++ outside)))
    (savedAccess : TicketAccess captured .ordinary mode (activeTickets tail ++ outside))
    (restAccess : TicketAccess tail mode after outside)
    (unused : owner ∉ frontDemand)
    (bounds : ReentryBounds front captured tail mode) :
    TicketAccess (captured.append (front.append (.spent owner answer caller tail))) .ordinary after outside := by
  have narrow := ticket_access_remove_unused frontUse frontAccess unused
  have reentry : TicketAccess front mode mode (activeTickets tail ++ outside) := by
    cases bounds with
    | ordinary => exact narrow
    | unwind scopes inside saved outside => exact unwind_prefix_ticket_access scopes _
  have callerAccess := TicketAccess.append (right := .spent owner answer caller tail) reentry (.spent restAccess)
  apply TicketAccess.append (right := front.append (.spent owner answer caller tail)) ?_ callerAccess
  apply savedAccess.weaken
  intro name present
  simpa only [active_tickets_append, activeTickets, List.append_assoc] using
    (List.mem_append_right (activeTickets front) present)

theorem discard_ticket_access_fragments
    (frontUse : StackUse policy tickets front .ordinary .ordinary frontDemand)
    (frontAccess : TicketAccess front .ordinary .ordinary (owner :: (activeTickets tail ++ outside)))
    (restAccess : TicketAccess tail .ordinary after outside)
    (unused : owner ∉ frontDemand) (scopes : UnwindPrefix captured) :
    TicketAccess (captured.append (.push (.closing identity runtimeScope)
      (front.append (.spent owner answer caller tail)))) .unwind after outside := by
  have narrow := ticket_access_remove_unused frontUse frontAccess unused
  have callerAccess := TicketAccess.append (right := .spent owner answer caller tail) narrow (.spent restAccess)
  exact TicketAccess.append (unwind_prefix_ticket_access scopes _)
    (.push (List.nil_subset _) callerAccess)

/-- The consumed owner is removed using uniqueness and actual pending demand,
    retaining the original lexical access of every other fragment. -/
theorem resume_ticket_access
    (checked : MachineUse policy tickets (.eval ⟨.resume binder value, runtimeScope,
      front.append (.live owner input answer captured caller tail)⟩))
    (access : TicketAccess (front.append (.live owner input answer captured caller tail)) .ordinary .ordinary [])
    (resolved : runtimeScope.resolve binder = some owner)
    (unique : (ownedTickets (front.append (.live owner input answer captured caller tail))).Nodup)
    (bounds : ReentryBounds front captured tail (returnMode captured .ordinary)) :
    TicketAccess (captured.append (front.append (.spent owner answer caller tail))) .ordinary .ordinary [] := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  have sameCurrent := resume_code_demand code resolved
  subst current
  have unused : owner ∉ pending := (List.nodup_cons.mp (balance.symm.nodup unique)).1
  obtain ⟨ownerMode, frontDemand, boundaryDemand, same, frontUse, boundary⟩ := stack_use_decompose stack
  obtain ⟨accessMode, frontAccess, boundaryAccess⟩ := access.decompose
  have sameAccess := (ticket_access_return_mode frontAccess).symm.trans (stack_use_return_mode frontUse)
  subst accessMode
  have ordinaryMode := unused_live_enters_ordinary boundary
    (fun present => unused (same ▸ List.mem_append_right frontDemand present))
  subst ownerMode
  cases boundary with
  | live known callerScope saved rest => cases boundaryAccess with
      | live savedAccess restAccess =>
          have sameMode := (ticket_access_return_mode savedAccess).symm.trans (stack_use_return_mode saved)
          subst sameMode
          exact resume_ticket_access_fragments frontUse
            (by simpa only [activeTickets, List.cons_append] using frontAccess)
            savedAccess restAccess
            (fun present => unused (same ▸ List.mem_append_left _ present))
            ((stack_use_return_mode saved) ▸ bounds)

theorem discard_ticket_access {front captured tail : Stack}
    (checked : MachineUse policy tickets (.eval ⟨.discard binder, runtimeScope,
      front.append (.live owner input answer captured caller tail)⟩))
    (access : TicketAccess (front.append (.live owner input answer captured caller tail)) .ordinary .ordinary [])
    (resolved : runtimeScope.resolve binder = some owner)
    (unique : (ownedTickets (front.append (.live owner input answer captured caller tail))).Nodup)
    (unprotected : ProtectionContexts.protectedMode captured.erase = false) :
    TicketAccess (captured.append (.push (.closing identity runtimeScope)
      (front.append (.spent owner answer caller tail)))) .unwind .ordinary [] := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  have sameCurrent := discard_code_demand code resolved
  subst current
  have unused : owner ∉ pending := (List.nodup_cons.mp (balance.symm.nodup unique)).1
  obtain ⟨ownerMode, frontDemand, boundaryDemand, same, frontUse, boundary⟩ := stack_use_decompose stack
  obtain ⟨accessMode, frontAccess, boundaryAccess⟩ := access.decompose
  have sameAccess := (ticket_access_return_mode frontAccess).symm.trans (stack_use_return_mode frontUse)
  subst accessMode
  have ordinaryMode := unused_live_enters_ordinary boundary
    (fun present => unused (same ▸ List.mem_append_right frontDemand present))
  subst ownerMode
  cases boundary with
  | live known callerScope saved rest => cases boundaryAccess with
      | live savedAccess restAccess =>
          have sameMode := (ticket_access_return_mode savedAccess).symm.trans (stack_use_return_mode saved)
          subst sameMode
          have scopes := unprotected_unwind_prefix unprotected
          obtain ⟨ordinaryMode, converted⟩ := prefix_use_unwind scopes saved
          subst ordinaryMode
          exact discard_ticket_access_fragments frontUse
            (by simpa only [activeTickets, List.cons_append] using frontAccess)
            restAccess (fun present => unused (same ▸ List.mem_append_left _ present)) scopes

/-- Current code requires visible tickets; unwinding has no current code.
    Stored code is checked at the mode in which its lexical suffix will run. -/
def MachineTicketAccess (policy : Syntax.TicketPolicy) (tickets : Syntax.UsageTickets) : Machine → Prop
  | .eval configuration => ∃ demand,
      CodeDemand policy tickets configuration.scope configuration.expression demand ∧
      demand ⊆ activeTickets configuration.stack ∧
      TicketAccess configuration.stack .ordinary .ordinary []
  | .unwind _ stack => TicketAccess stack .unwind .ordinary []

theorem ordinary_machine_ticket_access
    (checked : ConfigurationUsage policy tickets configuration) :
    MachineTicketAccess policy tickets (.eval configuration) := by
  obtain ⟨current, pending, code, stack, visible, balance, unique⟩ := checked
  exact ⟨current, code, visible, ordinary_stack_ticket_access stack⟩

theorem cell_update_ticket_access
    (update : CellUpdate identity old new before after)
    (access : TicketAccess before input output outside) : TicketAccess after input output outside := by
  induction update generalizing input output outside with
  | hit => cases access with
      | push visible rest =>
          exact .push (by cases input <;> exact List.nil_subset _) rest
  | push miss next ih => cases access with
      | push visible rest =>
          exact .push (by simpa only [cell_update_active_tickets next] using visible) (ih rest)
  | live next ih => cases access with
      | live saved rest =>
          exact .live (by simpa only [cell_update_active_tickets next] using saved) (ih rest)
  | spent next ih => cases access with
      | spent rest => exact .spent (ih rest)

theorem focus_machine_ticket_access (plain : PlainData)
    (focus : Focus whole child plain.context)
    (access : MachineTicketAccess policy tickets (.eval ⟨whole, plain.scope, tail⟩)) :
    MachineTicketAccess policy tickets (.eval ⟨child, plain.scope, .push (.plain plain) tail⟩) := by
  obtain ⟨current, code, visible, stack⟩ := access
  obtain ⟨childDemand, frameDemand, same, childCode, frameCode⟩ := focus_splits_code_demand focus code
  subst current
  refine ⟨childDemand, childCode, (fun owner present => visible (List.mem_append_left _ present)),
    .push ?_ stack⟩
  intro owner present
  exact List.mem_append_left _ (visible (List.mem_append_right _
    ((translated_demand_membership frameCode plain.translated owner).mpr present)))

theorem raw_value_machine_ticket_access
    (step : RawStep before after created discharged) (closed : ClosedValue before.expression)
    (checked : MachineUse policy tickets (.eval before))
    (access : MachineTicketAccess policy tickets (.eval before)) :
    MachineTicketAccess policy tickets (.eval after) := by
  obtain ⟨current, pending, code, stack, balance⟩ := checked
  obtain ⟨accessDemand, accessCode, visible, accessible⟩ := access
  have currentEmpty := code_demand_value_is_empty code closed.1
  subst current
  cases step with
  | focus plain focus tail => exact False.elim (focus_is_not_value focus closed.1)
  | bind | beta | ifTrue | ifFalse | enterHandler | enterCell | enterCleanup
  | capture | resume | discard | readCell | writeCell => cases closed.1
  | plug plain value valueClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | plain context => cases accessible with
                  | push frameVisible tail =>
                      refine ⟨_, code_demand_plug_value context valueClosed.1
                        (code_demand_value_usage code valueClosed.1), ?_, tail⟩
                      intro owner present
                      exact (List.mem_append.mp (frameVisible
                        ((translated_demand_membership context plain.translated owner).mp present))).resolve_right
                        (fun impossible => by cases impossible)
  | leaveHandler handler value valueClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | handler caller clauses => cases accessible with
                  | push frameVisible tail =>
                      exact ⟨[], code_demand_value_transport code valueClosed.1 caller, List.nil_subset _, tail⟩
  | leaveCell identity payload answer savedScope scope value valueClosed tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | cell caller => cases accessible with
                  | push frameVisible tail =>
                      exact ⟨[], code_demand_value_transport code valueClosed.1 caller, List.nil_subset _, tail⟩
  | startCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | armed caller callable => cases accessible with
                  | push frameVisible tail =>
                      exact ⟨[], .idle .none (.app callable .unit), List.nil_subset _, .push (List.nil_subset _) tail⟩
  | finishCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | running caller callable result => cases accessible with
                  | push frameVisible tail =>
                      obtain ⟨useScope, caller⟩ := caller
                      exact ⟨[], .idle caller (value_use_transport savedClosed.1 result _ .available), List.nil_subset _, tail⟩
  | leaveClause owner answer value valueClosed scope callerScope tail => cases stack with
      | spent known caller rest => cases accessible with
          | spent tail => exact ⟨[], code_demand_value_transport code valueClosed.1 caller, List.nil_subset _, tail⟩
  | finishClose identity scope callerScope tail => cases stack with
      | push frame rest => cases frame with
          | ordinary payload => cases payload with
              | closing caller => cases accessible with
                  | push frameVisible tail =>
                      exact ⟨[], code_demand_value_transport code closed.1 caller, List.nil_subset _, tail⟩
  | retire owner scope tail => cases accessible with
      | push frameVisible tail => exact ⟨[], code, List.nil_subset _, tail⟩

theorem raw_computation_machine_ticket_access
    (step : RawStep before after created discharged) (head : computationHead before.expression)
    (allocation : ∀ owner, Owner.ticket owner ∈ created → tickets owner = none)
    (checked : MachineUse policy tickets (.eval before))
    (access : MachineTicketAccess policy tickets (.eval before)) :
    MachineTicketAccess policy (advanceUsageTickets policy tickets after created) (.eval after) := by
  have actual := step
  have original := access
  obtain ⟨current, code, visible, stack⟩ := access
  cases step with
  | focus plain focus tail => exact focus_machine_ticket_access plain focus original
  | bind parameter value body scope tail closed environment =>
      exact ⟨current, bind_code_demand code closed.1, visible, stack⟩
  | beta parameter body value scope tail closed closure =>
      obtain ⟨same, afterCode⟩ := beta_code_demand code closed.1
      subst current
      exact ⟨[], afterCode, List.nil_subset _, stack⟩
  | ifTrue => exact ⟨current, (branch_code_demand code).1, visible, stack⟩
  | ifFalse => exact ⟨current, (branch_code_demand code).2, visible, stack⟩
  | enterHandler handler body tail =>
      exact ⟨current, (handler_code_demand code).1, visible, .push (List.nil_subset _) stack⟩
  | enterCell binder identity payload body scope answer tail ready =>
      exact ⟨current, acquisition_preserves_code_demand code _, visible, .push (List.nil_subset _) stack⟩
  | enterCleanup action body tail =>
      exact ⟨current, (cleanup_code_demand code action.closed.1).1, visible, .push (List.nil_subset _) stack⟩
  | capture requested operation parameter binder owner operand body scope whole captured tail handler
      input cut selected closed environment =>
      obtain ⟨nextDemand, nextPending, nextCode, nextStack, nextBalance⟩ :=
        raw_computation_machine_use actual head allocation checked
      refine ⟨nextDemand, nextCode, ?_, capture_ticket_access cut stack⟩
      cases nextCode with
      | idle scope used => exact List.nil_subset _
      | consume known used => simp [activeTickets]
  | resume binder owner scope caller input answer front captured tail value closed resolved =>
      exact False.elim (head closed.1)
  | discard => exact False.elim head
  | readCell identity payload scope before after update =>
      obtain ⟨useScope, scopeKnown⟩ := Syntax.code_demand_scope code
      exact ⟨[], .idle scopeKnown .integer, List.nil_subset _, cell_update_ticket_access update stack⟩
  | writeCell identity old new scope before after update =>
      obtain ⟨useScope, scopeKnown⟩ := Syntax.code_demand_scope code
      exact ⟨[], .idle scopeKnown .unit, List.nil_subset _, cell_update_ticket_access update stack⟩
  | plug | leaveHandler | leaveCell | startCleanup | finishCleanup | leaveClause | finishClose | retire =>
      apply raw_value_machine_ticket_access actual ?_ checked original
      first | assumption | simp [ClosedValue, Code.IsValue, Code.dependencies, Code.ResourceClosed, Code.freeNames]

/-- Accessibility is preserved by every structurally checked use transition,
    alongside (rather than inferred from) demand/ownership accounting. -/
theorem UseTransition.ticket_access
    (step : UseTransition before after created discharged)
    (allocation : ∀ owner, Owner.ticket owner ∈ created → tickets owner = none)
    (unique : (ownedTickets before.stack).Nodup)
    (checked : MachineUse policy tickets before)
    (access : MachineTicketAccess policy tickets before) :
    MachineTicketAccess policy (advanceUseTickets policy tickets after created) after := by
  cases step with
  | evaluate raw head => exact raw_computation_machine_ticket_access raw head allocation checked access
  | resume binder owner scope caller input answer front captured tail value closed resolved bounds =>
      obtain ⟨current, code, visible, stack⟩ := access
      obtain ⟨nextDemand, nextPending, nextCode, nextStack, nextBalance⟩ :=
        resume_machine_use checked resolved closed.1 unique bounds
      have empty := code_demand_value_is_empty nextCode closed.1
      subst nextDemand
      exact ⟨[], nextCode, List.nil_subset _, resume_ticket_access checked stack resolved unique bounds⟩
  | discard binder owner identity scope caller input answer front captured tail resolved unprotected frontBound internal tailBound =>
      obtain ⟨current, code, visible, stack⟩ := access
      exact discard_ticket_access checked stack resolved unique unprotected
  | advance step => exact administrative_ticket_access step access
  | startCleanup =>
      obtain ⟨pending, stackUse, balance⟩ := checked
      have code := (start_cleanup_use stackUse).1
      cases access with
      | push visible rest => exact ⟨[], code, List.nil_subset _, .push (List.nil_subset _) rest⟩
  | finishCleanup =>
      obtain ⟨current, code, visible, stack⟩ := access
      cases stack with
      | push visible rest => exact rest
  | finishClose =>
      obtain ⟨pending, stackUse, balance⟩ := checked
      obtain ⟨known, tailUse⟩ := finish_close_use stackUse
      obtain ⟨useScope, scopeKnown⟩ := known
      cases access with
      | push visible rest => exact ⟨[], .idle scopeKnown .unit, List.nil_subset _, rest⟩
  | retireValue closed =>
      obtain ⟨current, code, visible, stack⟩ := access
      have empty := code_demand_value_is_empty code closed.1
      subst current
      cases stack with
      | push visible rest => exact ⟨[], code, List.nil_subset _, rest⟩
  | closeValue closed =>
      obtain ⟨current, code, visible, stack⟩ := access
      obtain ⟨nextDemand, nextPending, nextCode, nextStack, nextBalance⟩ := close_value_machine_use checked closed.1
      have empty := code_demand_value_is_empty nextCode (by trivial)
      subst nextDemand
      cases stack with
      | push visible rest => exact ⟨[], nextCode, List.nil_subset _, rest⟩

/-- The existing event ledger/history supplies the uniqueness and freshness
    required by accessibility; no source or successor safety oracle is added. -/
theorem UseEvent.preserves_ticket_access
    (step : UseEvent policy before after)
    (checked : UseRunInvariant policy before)
    (access : MachineTicketAccess policy before.tickets before.execution.machine) :
    MachineTicketAccess policy after.tickets after.execution.machine := by
  obtain ⟨ledger, history, usage⟩ := checked
  have allocation (createdOwners : List Owner) (fresh : (before.execution.issued ++ createdOwners).Nodup) :
      ∀ owner, Owner.ticket owner ∈ createdOwners → before.tickets owner = none := by
    intro owner created
    cases existing : before.tickets owner with
    | none => rfl
    | some rights =>
        have earlier := (history owner).mp ⟨rights, existing⟩
        exact False.elim ((List.nodup_append.mp fresh).2.2 (.ticket owner) earlier
          (.ticket owner) created rfl)
  cases step with
  | step transition fresh =>
      exact transition.ticket_access (allocation _ fresh)
        (owned_tickets_unique (ledger_unique_live ledger)) usage access

theorem use_execution_preserves_ticket_access
    (steps : Relation.TransGen (UseEvent policy) before after)
    (checked : UseRunInvariant policy before)
    (access : MachineTicketAccess policy before.tickets before.execution.machine) :
    UseRunInvariant policy after ∧ MachineTicketAccess policy after.tickets after.execution.machine := by
  induction steps with
  | single step => exact ⟨step.preserves checked, step.preserves_ticket_access checked access⟩
  | tail steps step ih => exact ⟨step.preserves ih.1, step.preserves_ticket_access ih.1 ih.2⟩

theorem initial_machine_ticket_access
    (source : Uses policy .none .available expression .available) :
    MachineTicketAccess policy (fun _ => none) (.eval ⟨expression, .none, .nil⟩) :=
  ⟨[], .idle .none source, List.nil_subset _, .nil⟩

#print axioms Ash.OneShot.LexicalUnwind.frame_use_return_mode
#print axioms Ash.OneShot.LexicalUnwind.ticket_access_return_mode
#print axioms Ash.OneShot.LexicalUnwind.frame_pending_subset_active_demand
#print axioms Ash.OneShot.LexicalUnwind.ordinary_stack_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.frame_use_access_or_retiring
#print axioms Ash.OneShot.LexicalUnwind.stack_use_access_bound
#print axioms Ash.OneShot.LexicalUnwind.live_clause_cannot_return
#print axioms Ash.OneShot.LexicalUnwind.frame_ticket_uses_subset_demand
#print axioms Ash.OneShot.LexicalUnwind.TicketAccess.weaken
#print axioms Ash.OneShot.LexicalUnwind.TicketAccess.append
#print axioms Ash.OneShot.LexicalUnwind.TicketAccess.decompose
#print axioms Ash.OneShot.LexicalUnwind.unwind_prefix_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.ticket_access_change_external
#print axioms Ash.OneShot.LexicalUnwind.ticket_access_remove_unused
#print axioms Ash.OneShot.LexicalUnwind.administrative_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.capture_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.resume_ticket_access_fragments
#print axioms Ash.OneShot.LexicalUnwind.discard_ticket_access_fragments
#print axioms Ash.OneShot.LexicalUnwind.resume_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.discard_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.ordinary_machine_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.cell_update_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.focus_machine_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.raw_value_machine_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.raw_computation_machine_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.UseTransition.ticket_access
#print axioms Ash.OneShot.LexicalUnwind.UseEvent.preserves_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.use_execution_preserves_ticket_access
#print axioms Ash.OneShot.LexicalUnwind.initial_machine_ticket_access
end Ash.OneShot.LexicalUnwind


namespace Ash.OneShot.LexicalUnwind
open ScopedExpressions ScopedExecution

abbrev CaptureModes := Nat → Option Bool

/-- Historical source protection bits refer to the actual saved lexical
    scopes. Running cleanup is read from those scopes, not from permissions. -/
inductive CaptureProtection (modes : CaptureModes) : Stack → Prop where
  | nil : CaptureProtection modes .nil
  | push (rest : CaptureProtection modes tail) : CaptureProtection modes (.push frame tail)
  | live (recorded : modes owner = some (ProtectionContexts.protectedMode captured.erase))
      (saved : CaptureProtection modes captured) (rest : CaptureProtection modes tail) :
      CaptureProtection modes (.live owner input answer captured caller tail)
  | spent (rest : CaptureProtection modes tail) : CaptureProtection modes (.spent owner answer caller tail)

theorem CaptureProtection.extend
    (checked : CaptureProtection before stack)
    (extension : ∀ owner held, before owner = some held → after owner = some held) :
    CaptureProtection after stack := by
  induction checked with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | live recorded saved rest ihSaved ihRest => exact .live (extension _ _ recorded) ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem CaptureProtection.append
    (front : CaptureProtection modes left) (tail : CaptureProtection modes right) :
    CaptureProtection modes (left.append right) := by
  induction front with
  | nil => exact tail
  | push rest ih => exact .push ih
  | live recorded saved rest ihSaved ihRest => exact .live recorded saved ihRest
  | spent rest ih => exact .spent ih

theorem CaptureProtection.decompose
    (checked : CaptureProtection modes (left.append right)) :
    CaptureProtection modes left ∧ CaptureProtection modes right := by
  induction left with
  | nil => exact ⟨.nil, checked⟩
  | push frame rest ih => cases checked with
      | push rest => obtain ⟨inside, outside⟩ := ih rest; exact ⟨.push inside, outside⟩
  | live owner input answer captured caller rest ihSaved ihRest => cases checked with
      | live recorded saved rest =>
          obtain ⟨inside, outside⟩ := ihRest rest
          exact ⟨.live recorded saved inside, outside⟩
  | spent owner answer caller rest ih => cases checked with
      | spent rest => obtain ⟨inside, outside⟩ := ih rest; exact ⟨.spent inside, outside⟩

theorem capture_protection_cut
    (cut : HandlerCut requested whole captured tail handler)
    (checked : CaptureProtection modes whole) :
    CaptureProtection modes captured ∧ CaptureProtection modes tail := by
  rw [handler_cut_reconstructs cut] at checked
  exact checked.decompose

theorem cell_update_capture_protection
    (update : CellUpdate identity old new before after)
    (checked : CaptureProtection modes before) : CaptureProtection modes after := by
  induction update with
  | hit => cases checked with | push rest => exact .push rest
  | push miss next ih => cases checked with | push rest => exact .push (ih rest)
  | live next ih => cases checked with | live recorded saved rest => exact .live recorded saved (ih rest)
  | spent next ih => cases checked with | spent rest => exact .spent (ih rest)

/-- Allocation authenticates a source bit against the actual newly captured
    stack. Other ownership events allocate no continuation protection record. -/
inductive ProtectionAllocation (modes : CaptureModes) : List Owner → Stack → Prop where
  | noTicket (absent : ∀ owner, Owner.ticket owner ∉ created) : ProtectionAllocation modes created stack
  | capture (recorded : modes owner = some (ProtectionContexts.protectedMode captured.erase)) :
      ProtectionAllocation modes [.ticket owner] (.live owner input answer captured caller tail)

theorem raw_step_capture_protection
    (step : RawStep before after created discharged) (allowed : ordinary before.expression)
    (checked : CaptureProtection beforeModes before.stack)
    (extension : ∀ owner held, beforeModes owner = some held → afterModes owner = some held)
    (allocation : ProtectionAllocation afterModes created after.stack) :
    CaptureProtection afterModes after.stack := by
  have retained := checked.extend extension
  cases step with
  | focus | enterHandler | enterCell | enterCleanup => exact .push retained
  | bind | beta | ifTrue | ifFalse => exact retained
  | plug | leaveHandler | leaveCell | finishCleanup | finishClose | retire => cases retained with
      | push rest => exact rest
  | startCleanup => cases retained with
      | push rest => exact .push rest
  | leaveClause => cases retained with
      | spent rest => exact rest
  | capture requested operation parameter binder owner operand body scope whole captured tail handler
      input cut selected closed environment =>
      obtain ⟨saved, rest⟩ := capture_protection_cut cut retained
      cases allocation with
      | noTicket absent => exact False.elim (absent owner (by simp))
      | capture recorded => exact .live recorded saved rest
  | resume binder owner scope caller input answer front captured tail value closed resolved =>
      obtain ⟨frontChecked, boundary⟩ := retained.decompose
      cases boundary with
      | live recorded saved rest => exact saved.append (frontChecked.append (.spent rest))
  | discard => exact False.elim allowed
  | readCell identity payload scope before after update => exact cell_update_capture_protection update retained
  | writeCell identity old new scope before after update => exact cell_update_capture_protection update retained

theorem administrative_capture_protection
    (step : Advance before after discharged) (checked : CaptureProtection modes before) :
    CaptureProtection modes after := by
  cases step with
  | plain | handler | cell | retire => cases checked with | push rest => exact rest
  | spent => cases checked with | spent rest => exact rest
  | live => cases checked with
      | live recorded saved rest => exact saved.append (.push rest)

/-- The same recorded protection bits remain attached to every retained live
    capture through all actual transitions, including lexical unwinding. -/
theorem transition_capture_protection
    (step : Transition before after created discharged)
    (checked : CaptureProtection beforeModes before.stack)
    (extension : ∀ owner held, beforeModes owner = some held → afterModes owner = some held)
    (allocation : ProtectionAllocation afterModes created after.stack) :
    CaptureProtection afterModes after.stack := by
  have retained := checked.extend extension
  cases step with
  | evaluate raw allowed => exact raw_step_capture_protection raw allowed checked extension allocation
  | advance step => exact administrative_capture_protection step retained
  | startCleanup => cases retained with | push rest => exact .push rest
  | finishCleanup | finishClose | retireValue | closeValue => cases retained with | push rest => exact rest
  | discard binder owner identity scope caller input answer front captured tail resolved unprotected =>
      obtain ⟨frontChecked, boundary⟩ := retained.decompose
      cases boundary with
      | live recorded saved rest => exact saved.append (.push (frontChecked.append (.spent rest)))

/-- The source's false protection bit supplies the runtime discard guard for
    the selected lexical owner; no finalizer or handler lookup is inferred. -/
theorem recorded_discard_unprotected {front captured tail : Stack}
    (checked : CaptureProtection modes (front.append (.live owner input answer captured caller tail)))
    (unprotected : modes owner = some false) : ProtectionContexts.protectedMode captured.erase = false := by
  obtain ⟨frontChecked, boundary⟩ := checked.decompose
  cases boundary with
  | live recorded saved rest => exact Option.some.inj (recorded.symm.trans unprotected)

#print axioms Ash.OneShot.LexicalUnwind.CaptureProtection.extend
#print axioms Ash.OneShot.LexicalUnwind.CaptureProtection.append
#print axioms Ash.OneShot.LexicalUnwind.CaptureProtection.decompose
#print axioms Ash.OneShot.LexicalUnwind.capture_protection_cut
#print axioms Ash.OneShot.LexicalUnwind.cell_update_capture_protection
#print axioms Ash.OneShot.LexicalUnwind.raw_step_capture_protection
#print axioms Ash.OneShot.LexicalUnwind.administrative_capture_protection
#print axioms Ash.OneShot.LexicalUnwind.transition_capture_protection
#print axioms Ash.OneShot.LexicalUnwind.recorded_discard_unprotected
end Ash.OneShot.LexicalUnwind
