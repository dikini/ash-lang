import CoreProjectedCellDispatch
import CoreCleanupProjection
import ScopedPortCompletion
import SourcePlannedSourceReduction
import SourceScheduledCleanupInterfaces

/-! A stored callback's static contract supplies its request allowance. Actual
callback reductions retain that allowance at their local prefix. This is
experimental admission evidence; Core cleanup translation alone does not
validate the supplied request metadata. -/
namespace Ash.OneShot.CoreCallbackRequestRoutes
open ScopedExpressions ScopedExecution ProtectionContracts
open ScopedPorts (Port eraseType embedPort)
open SourcePlannedTyping (Operations Contracts)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (Certified)

structure StoredCallback (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (ports : OperationRows operations) (owners : ContractRows contracts)
    (emptyRows : EnvironmentRows (fun _ => none))
    (world : List Nat) (outward : List Instance) (action : ActionData) where
  latent : Footprint
  dependencies : Dependencies
  plan : Plan dependencies
  rows : Rows (signature plan)
  callback : SourcePlannedSources.ValueSummary operations policy contracts world (fun _ => none) [] action.action
    (.function .unit .unit action.requests latent (signature plan))
  authenticated : Auth operations policy ports owners emptyRows callback (.function .unit .unit rows) .pure
  certified : Certified (evidence := declarationPolicy) outward world plan

theorem StoredCallback.initial_source
    (stored : StoredCallback operations policy contracts ports owners emptyRows world outward action) :
    SourcePlannedSources.Expression operations policy contracts world action.requests .none (fun _ => none)
      (.app action.action .unit) .unit []
      (.emitAfter (.sequence (.request [] []) (.request [] [])) [] stored.latent)
      (signature (.sequence .pure (.sequence .pure stored.plan))) :=
  .app (SourcePlannedSources.Values.change_context stored.callback action.closed.1 action.requests .none)
    .unit (List.Subset.refl _)

theorem StoredCallback.initial_auth
    (stored : StoredCallback operations policy contracts ports owners emptyRows world outward action) :
    Auth operations policy ports owners emptyRows stored.initial_source .unit
      (.sequence .pure (.sequence .pure stored.rows)) :=
  .app (stored.authenticated.value_context action.closed.1 action.requests .none) .unit
    (admitted := List.Subset.refl _)

theorem StoredCallback.initial_ports
    (stored : StoredCallback operations policy contracts ports owners emptyRows world outward action) :
    ScopedPorts.Typed operations.erase.erase.ports world ScopedPorts.TypeEnv.empty .none action.requests
      (.app action.action .unit) .unit := by
  exact SourceTemplates.expression_ports
    (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
      (SourcePlannedSources.expression_erase stored.initial_source))) .none

structure CallbackCurrent
    (stored : StoredCallback operations policy contracts ports owners emptyRows originalWorld outward action)
    (tickets : ScopedPorts.EffectTickets) (world : List Nat) (configuration : Configuration) : Prop where
  origin : ∃ created discharged, RawTrace ⟨.app action.action .unit, .none, .nil⟩ configuration created discharged
  typed : ScopedPorts.EffectConfigurationTyped operations.erase.erase.ports tickets world configuration .unit action.requests

theorem StoredCallback.start
    (stored : StoredCallback operations policy contracts ports owners emptyRows world outward action) :
    CallbackCurrent stored contracts.erase.erase.ports world ⟨.app action.action .unit, .none, .nil⟩ := by
  exact ⟨⟨[], [], .refl _⟩, .unit, action.requests, .checked .none stored.initial_ports, .nil, .nil (List.Subset.refl _)⟩

theorem trace_extend (trace : RawTrace first before created discharged)
    (step : RawStep before after newCreated newDischarged) :
    RawTrace first after (created ++ newCreated) (newDischarged ++ discharged) := by
  induction trace with
  | refl => simpa using RawTrace.next step (.refl _)
  | next head rest ih => simpa only [List.append_assoc] using RawTrace.next head (ih step)

private theorem CallbackCurrent.advance
    {stored : StoredCallback operations policy contracts ports owners emptyRows originalWorld outward action}
    (current : CallbackCurrent stored tickets world before)
    (step : RawStep before after created discharged)
    (next : ScopedPorts.EffectConfigurationTyped operations.erase.erase.ports nextTickets nextWorld after .unit action.requests) :
    CallbackCurrent stored nextTickets nextWorld after := by
  obtain ⟨made, done, trace⟩ := current.origin
  exact ⟨⟨_, _, trace_extend trace step⟩, next⟩

theorem CallbackCurrent.beta
    (current : CallbackCurrent stored tickets world ⟨.app (.lambda parameter body) value, scope, tail⟩)
    (closed : ClosedValue value) (closure : ClosedValue (.lambda parameter body)) :
    RawStep ⟨.app (.lambda parameter body) value, scope, tail⟩ ⟨body.subst parameter value, .none, tail⟩ [] [] ∧
      CallbackCurrent stored tickets world ⟨body.subst parameter value, .none, tail⟩ := by
  have step := RawStep.beta parameter body value scope tail closed closure
  exact ⟨step, current.advance step (ScopedPorts.beta_preserves_effect_configuration current.typed closed.1)⟩

theorem CallbackCurrent.bind
    (current : CallbackCurrent stored tickets world ⟨.bind parameter value body, scope, tail⟩)
    (closed : ClosedValue value) (bodyClosed : ClosedExcept parameter body) :
    RawStep ⟨.bind parameter value body, scope, tail⟩ ⟨body.subst parameter value, scope, tail⟩ [] [] ∧
      CallbackCurrent stored tickets world ⟨body.subst parameter value, scope, tail⟩ := by
  have step := RawStep.bind parameter value body scope tail closed bodyClosed
  exact ⟨step, current.advance step (ScopedPorts.bind_preserves_effect_configuration current.typed closed.1)⟩

theorem CallbackCurrent.focus
    (current : CallbackCurrent stored tickets world ⟨whole, scope, tail⟩)
    (focus : Focus whole child context) :
    ∃ plain : PlainData, RawStep ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ [] [] ∧
      CallbackCurrent stored tickets world ⟨child, scope, .push (.plain plain) tail⟩ := by
  obtain ⟨plain, step, next⟩ := ScopedPorts.focus_constructs_effect_configuration current.typed focus
  exact ⟨plain, step, current.advance step next⟩

theorem CallbackCurrent.handler
    (current : CallbackCurrent stored tickets world ⟨.handle effect body clauses, scope, tail⟩)
    (activation : Nat) :
    ∃ handler : HandlerData, handler.activation = activation ∧
      RawStep ⟨.handle effect body clauses, scope, tail⟩ ⟨body, scope, .push (.handler handler) tail⟩ [] [] ∧
      CallbackCurrent stored tickets world ⟨body, scope, .push (.handler handler) tail⟩ := by
  obtain ⟨handler, same, step, next⟩ := ScopedPorts.handler_entry_constructs_effect_configuration current.typed activation
  exact ⟨handler, same, step, current.advance step next⟩

theorem CallbackCurrent.value_step
    (current : CallbackCurrent stored tickets world before)
    (step : RawStep before after created discharged) (closed : ClosedValue before.expression) :
    CallbackCurrent stored tickets world after :=
  current.advance step (ScopedPorts.raw_value_step_preserves_effect_configuration step closed current.typed)

theorem CallbackCurrent.capture
    {handler : HandlerData}
    {stored : StoredCallback operations policy contracts ports owners emptyRows originalWorld outward action}
    (current : CallbackCurrent stored tickets world
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩)
    (cut : HandlerCut requested whole cap tail handler)
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port) (residual : List Instance),
      let contract : ScopedPorts.ContinuationContract := ⟨output, eraseType handler.answer, residual, residual⟩
      let extended := tickets.insert owner contract
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩ [.ticket owner] [] ∧
      ScopedPorts.EffectExtension tickets extended ∧
      CallbackCurrent stored extended world
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩ := by
  obtain ⟨parameter, binder, body, output, residual, step, extension, next⟩ :=
    ScopedPorts.capture_constructs_effect_configuration cut current.typed isValue fresh
  exact ⟨parameter, binder, body, output, residual, step, extension, current.advance step next⟩

theorem CallbackCurrent.request_membership
    (current : CallbackCurrent (outward := outward) (action := action) stored tickets world ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, pending⟩)
    (localMiss : pending.erase.resolve requested = none) : requested ∈ action.requests := by
  rcases ScopedPorts.current_request_is_interpreted_or_exported current.typed with ⟨target, selected⟩ | included
  · rw [localMiss] at selected
    cases selected
  · exact included

theorem CallbackCurrent.route_pair
    (current : CallbackCurrent (outward := outward) (action := action) stored tickets world
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, pending⟩)
    (localMiss : pending.erase.resolve requested = none)
    (closing : SourceRecursiveRoutes.Closing outward (.cleanup action.requests rest) original surviving) :
    ∃ target, SourceResourceRoutes.Route outward (rest.normal ++ original) requested target ∧
      SourceResourceRoutes.Route outward (rest.closing ++ surviving) requested target := by
  cases closing with
  | cleanup routes tail => exact routes requested (current.request_membership localMiss)

theorem route_cell_target
    (route : SourceResourceRoutes.Route outward context requested target)
    (cell : requested = .cell identity) : target = none ∨ target = some identity := by
  induction route with
  | outside => exact .inl rfl
  | cell same => cases Instance.cell.inj (same.symm.trans cell); exact .inr rfl
  | cellMiss different next ih | handler different next ih | cleanup next ih => exact ih cell

theorem CallbackCurrent.cell_route_pair
    (current : CallbackCurrent (outward := outward) (action := action) stored tickets world
      ⟨.perform (Instantiation.freezeEffect (.cell identity)) operation operand, scope, pending⟩)
    (localMiss : pending.erase.resolve (.cell identity) = none)
    (closing : SourceRecursiveRoutes.Closing outward (.cleanup action.requests rest) original surviving)
    (nonexport : .cell identity ∉ outward) :
    SourceResourceRoutes.Route outward (rest.normal ++ original) (.cell identity) (some identity) ∧
      SourceResourceRoutes.Route outward (rest.closing ++ surviving) (.cell identity) (some identity) := by
  obtain ⟨target, before, after⟩ := current.route_pair localMiss closing
  rcases route_cell_target before rfl with absent | same
  · exact False.elim (nonexport (SourceRecursiveRoutes.Route.outside before absent))
  · rw [same] at before after
    exact ⟨before, after⟩

theorem select_of_builtin
    (realized : SourceDependencyCapture.Realizes tables families annotation stack)
    (resolved : stack.erase.resolve requested = some (.builtin identity)) :
    SourceDependencyCapture.select requested operation annotation = some (.builtin identity) := by
  induction realized with
  | nil => cases resolved
  | push frame tail ih =>
      cases frame with
      | plain | cleanup | running | unwinding | closing | retiring =>
          simp only [SourceDependencyCapture.select, ih resolved, Option.map, SourceDependencyCapture.Selection.prepend]
      | @handler data =>
          by_cases same : requested = data.effectInst
          · simp [Stack.erase, ExecFrame.erase, HandlerData.erase, Control.resolve,
              Ash.OneShot.Frame.resolve, same] at resolved
          · have next := ih (by simpa [Stack.erase, ExecFrame.erase, HandlerData.erase,
                Control.resolve, Ash.OneShot.Frame.resolve, same] using resolved)
            simp only [SourceDependencyCapture.select, if_neg same, next, Option.map, SourceDependencyCapture.Selection.prepend]
      | @cell cellIdentity payload caller answer =>
          by_cases same : requested = .cell cellIdentity
          · have equal : cellIdentity = identity := by
              simpa [Stack.erase, ExecFrame.erase, Control.resolve, Ash.OneShot.Frame.resolve, same] using resolved
            subst identity
            simp [SourceDependencyCapture.select, same]
          · have next := ih (by simpa [Stack.erase, ExecFrame.erase, Control.resolve,
                Ash.OneShot.Frame.resolve, same] using resolved)
            simp only [SourceDependencyCapture.select, if_neg same, next, Option.map, SourceDependencyCapture.Selection.prepend]
  | live inside outside ihInside ihOutside =>
      simp only [SourceDependencyCapture.select, ihOutside resolved, Option.map, SourceDependencyCapture.Selection.prepend]
  | spent tail ih =>
      simp only [SourceDependencyCapture.select, ih resolved, Option.map, SourceDependencyCapture.Selection.prepend]

theorem callback_root_scope
    (recursive : SourceRecursiveRoutes.Realizes rest lexical plan)
    (outside : SourceRecursiveRoutes.Scope original outsideTarget.erase) :
    SourceRecursiveRoutes.Scope (rest.normal ++ original)
      (CoreProjectedCellDispatch.lexicalTail data lexical targetClose closeScope outsideTarget).erase := by
  exact .skip rfl (by simpa only [ScopedExecution.erase_append, Stack.erase] using
    recursive.normal_scope.append (SourceRecursiveRoutes.Scope.skip rfl outside))

theorem CallbackCurrent.selected_cell
    (current : CallbackCurrent (outward := outward) (action := data) stored tickets world
      ⟨.perform (Instantiation.freezeEffect (.cell identity)) operation operand, caller, pendingTarget⟩)
    (localMiss : pendingTarget.erase.resolve (.cell identity) = none)
    (closing : SourceRecursiveRoutes.Closing outward (.cleanup data.requests rest) original surviving)
    (rootScope : SourceRecursiveRoutes.Scope (rest.normal ++ original)
      (CoreProjectedCellDispatch.lexicalTail data lexical targetClose closeScope outsideTarget).erase)
    (source : SourceDependencyCapture.Realizes tables families annotation
      (pendingTarget.append (CoreProjectedCellDispatch.lexicalTail data lexical targetClose closeScope outsideTarget)))
    (nonexport : .cell identity ∉ outward) :
    SourceDependencyCapture.select (.cell identity) operation annotation = some (.builtin identity) := by
  have routes := current.cell_route_pair localMiss closing nonexport
  have root := (rootScope.route routes.1).1
  apply select_of_builtin source
  simpa only [ScopedExecution.erase_append, resolve_append, localMiss, Option.map] using root

open CoreValueRelation CoreStrictStack CoreCellWriteFrames CoreRequestFrames CoreCleanupFrames
  CoreCleanupRunFrames CoreUnwindRelation
open Ash.OneShot.CoreCleanupProjection

theorem CallbackCurrent.read_dispatch {base : CoreMachine.State}
    (current : CallbackCurrent (outward := outward) (action := data) stored tickets world
      ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), plain.scope, pendingTarget⟩)
    (localMiss : pendingTarget.erase.resolve (.cell identity) = none)
    (closing : SourceRecursiveRoutes.Closing outward (.cleanup data.requests rest) original surviving)
    (rootScope : SourceRecursiveRoutes.Scope (rest.normal ++ original)
      (CoreProjectedCellDispatch.lexicalTail data lexical targetClose closeScope outsideTarget).erase)
    (nonexport : .cell identity ∉ outward)
    (request : RequestRel graph requestOwners base.heap (.request effect 0 environment) plain)
    (context : plain.context = .perform (Instantiation.freezeEffect (.cell identity)) 0)
    (operand : ValueRel graph owners base.heap value (.resourceRef (.activation identity)))
    (pending : PushedWithMaps graph base.heap pendingMaps pendingTarget)
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action savedEnvironment data.identity) data)
    (cursor : RetainedCursor graph base.heap physical lexical)
    (outside : PushedWithMaps graph base.heap outsideMaps outsideTarget)
    (source : SourceDependencyCapture.Realizes tables families annotation
      (pendingTarget.append (CoreProjectedCellDispatch.lexicalTail data lexical targetClose closeScope outsideTarget)))
    (ledger : Ledger ⟨(pendingTarget.append (CoreProjectedCellDispatch.lexicalTail data lexical targetClose closeScope outsideTarget)).erase,
      issued, completed⟩) :
    ∃ old after, CoreResourceUnwind.StepWitness graph
      (CoreProjectedCellDispatch.beforePoint base effect 0 environment value (.resourceRef (.activation identity)) owners requestOwners plain
        pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget)
      after [] [] ∧ after.state.control = .returned (.integer old) ∧
      after.state.observations = base.observations ++ [.read identity old] := by
  exact CoreProjectedCellDispatch.read_dispatch request context operand pending delayed cursor outside source
    (current.selected_cell localMiss closing rootScope source nonexport) ledger

theorem CallbackCurrent.closed_outward_read_dispatch {base : CoreMachine.State}
    (current : CallbackCurrent (outward := []) (action := data) stored tickets world
      ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), plain.scope, pendingTarget⟩)
    (localMiss : pendingTarget.erase.resolve (.cell identity) = none)
    (closing : SourceRecursiveRoutes.Closing [] (.cleanup data.requests rest) original surviving)
    (rootScope : SourceRecursiveRoutes.Scope (rest.normal ++ original)
      (CoreProjectedCellDispatch.lexicalTail data lexical targetClose closeScope outsideTarget).erase)
    (request : RequestRel graph requestOwners base.heap (.request effect 0 environment) plain)
    (context : plain.context = .perform (Instantiation.freezeEffect (.cell identity)) 0)
    (operand : ValueRel graph owners base.heap value (.resourceRef (.activation identity)))
    (pending : PushedWithMaps graph base.heap pendingMaps pendingTarget)
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action savedEnvironment data.identity) data)
    (cursor : RetainedCursor graph base.heap physical lexical)
    (outside : PushedWithMaps graph base.heap outsideMaps outsideTarget)
    (source : SourceDependencyCapture.Realizes tables families annotation
      (pendingTarget.append (CoreProjectedCellDispatch.lexicalTail data lexical targetClose closeScope outsideTarget)))
    (ledger : Ledger ⟨(pendingTarget.append (CoreProjectedCellDispatch.lexicalTail data lexical targetClose closeScope outsideTarget)).erase,
      issued, completed⟩) :
    ∃ old after, CoreResourceUnwind.StepWitness graph
      (CoreProjectedCellDispatch.beforePoint base effect 0 environment value (.resourceRef (.activation identity)) owners requestOwners plain
        pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget)
      after [] [] ∧ after.state.control = .returned (.integer old) ∧
      after.state.observations = base.observations ++ [.read identity old] :=
  current.read_dispatch localMiss closing rootScope (by simp) request context operand pending delayed cursor outside source ledger

#print axioms CallbackCurrent.capture
#print axioms CallbackCurrent.closed_outward_read_dispatch
#print axioms callback_root_scope
#print axioms CallbackCurrent.selected_cell
#print axioms CallbackCurrent.read_dispatch
#print axioms select_of_builtin
#print axioms trace_extend
#print axioms CallbackCurrent.beta
#print axioms CallbackCurrent.bind
#print axioms CallbackCurrent.focus
#print axioms CallbackCurrent.handler
#print axioms CallbackCurrent.value_step
#print axioms StoredCallback.initial_source
#print axioms StoredCallback.initial_auth
#print axioms StoredCallback.initial_ports
#print axioms StoredCallback.start
#print axioms CallbackCurrent.request_membership
#print axioms CallbackCurrent.route_pair
#print axioms CallbackCurrent.cell_route_pair
#print axioms route_cell_target
end Ash.OneShot.CoreCallbackRequestRoutes
